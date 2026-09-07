import Lean
import ImportGraph.Imports.RequiredModules

/-!
This module supplies Lean-owned audit commands.  Audit runners import its
compiled artifact when available, so a large paper interface is not elaborated
alongside the helper's implementation on every recursive-closure request.  The
runner fingerprints this source and builds the helper explicitly; it is audit
tooling, not a prerequisite of any paper theorem.

For hermetic historical fixtures that lack the module artifact, the Python
runner may still inject this exact source into a temporary audit process.
-/

open Lean Meta Elab Command

namespace AppliedModelingLibAudit.SignatureManifest

private def obj (tag : String) (fields : List (String × Json) := []) : Json :=
  Json.mkObj (("tag", Json.str tag) :: fields)

/--
Workspace for exact SHA-256 requests. The helper is evaluated inside an
already-loaded Lean process, where process pipes are not reliably available in
restricted runtimes. Requests therefore use secure private files and a child
with every standard stream disabled; the configured external `sha256sum`
binary remains the hash implementation and is still identity-pinned by Python.
-/
private structure CanonicalHashWorker where
  hashToolPath : String
  workspace : System.FilePath

private def CanonicalHashWorker.start
    (hashToolPath : String) : IO CanonicalHashWorker := do
  pure { hashToolPath, workspace := ← IO.FS.createTempDir }

private def CanonicalHashWorker.digest
    (worker : CanonicalHashWorker) (input : String) : IO String := do
  let inputPath := worker.workspace / "canonical-input"
  let outputPath := worker.workspace / "canonical-output"
  -- The input write completes before the child opens the private file.
  IO.FS.writeFile inputPath input
  let child ← IO.Process.spawn {
    cmd := "/bin/sh"
    args := #[
      "-c",
      "exec \"$1\" \"$2\" > \"$3\"",
      "econcslib-sha256-file-transport",
      worker.hashToolPath,
      inputPath.toString,
      outputPath.toString]
    stdin := .null
    stdout := .null
    stderr := .null }
  let exitCode ← child.wait
  unless exitCode == 0 do
    throw <| IO.userError s!"sha256sum failed with exit code {exitCode}"
  let output ← IO.FS.readFile outputPath
  let some digest := (output.trimAscii.toString.splitOn " ").head?
    | throw <| IO.userError "sha256sum emitted no digest"
  unless digest.length == 64 && output.startsWith (digest ++ " ") do
    throw <| IO.userError "sha256sum emitted a malformed digest"
  pure digest

private def CanonicalHashWorker.stop
    (worker : CanonicalHashWorker) : IO Unit :=
  IO.FS.removeDirAll worker.workspace

/-- Compute the standard SHA-256 digest of exact canonical UTF-8 bytes. -/
private def canonicalSha256 (hashToolPath input : String) : IO String := do
  let worker ← CanonicalHashWorker.start hashToolPath
  try
    worker.digest input
  finally
    worker.stop

private def canonicalDigest (hashToolPath input : String) : MetaM String :=
  liftM (m := IO) <| canonicalSha256 hashToolPath input

private def binderInfoName : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

private partial def canonicalLevel
    (params : Array Name) (level : Level) : MetaM Json := do
  match level with
  | .zero => pure (obj "zero")
  | .succ inner =>
      pure (obj "succ" [("of", ← canonicalLevel params inner)])
  | .max left right =>
      pure (obj "max" [
        ("left", ← canonicalLevel params left),
        ("right", ← canonicalLevel params right)])
  | .imax left right =>
      pure (obj "imax" [
        ("left", ← canonicalLevel params left),
        ("right", ← canonicalLevel params right)])
  | .param name =>
      match params.findIdx? (fun candidate => candidate == name) with
      | some index =>
          pure (obj "param" [("index", Json.str (toString index))])
      | none => throwError "unregistered universe parameter {name}"
  | .mvar _ =>
      throwError "unresolved universe metavariable in reviewed signature"

private def inAuditClosure
    (auditModules : Array Name) (reviewedModule : Option ModuleIdx)
    (name : Name) : MetaM Bool := do
  let env ← getEnv
  match env.getModuleIdxFor? name with
  | none =>
      pure reviewedModule.isNone
  | some moduleIdx =>
      if auditModules.isEmpty then
          pure (reviewedModule == some moduleIdx)
      else
        let moduleName := env.header.moduleNames[moduleIdx.toNat]!
        pure (auditModules.contains moduleName)

/-!
The memo retains only the compact canonical dependency identity consumed by
current manifests. Earlier implementations also retained a recursively
expanded JSON tree and a legacy byte-stream rope for every dependency. Those
representations had no reader after compact closure fingerprints were adopted
and made large paper surfaces retain several equivalent multi-gigabyte trees.

Declaration names below are process-local memo coordinates only. They never
enter the compact canonical identity or its digest.
-/
private structure CanonicalExprRopeMemoEntry where
  compact : Json

private structure CanonicalExprRopeMemo where
  hashToolPath : String := ""
  hashWorker? : Option CanonicalHashWorker := none
  keys : Std.HashMap String Nat := {}
  entries : Array CanonicalExprRopeMemoEntry := #[]

private abbrev CanonicalExprRopeMemoRef := IO.Ref CanonicalExprRopeMemo

private def canonicalDigestWithMemo
    (memo : CanonicalExprRopeMemoRef) (input : String) : MetaM String := do
  let state ← memo.get
  let worker ← match state.hashWorker? with
  | some worker => pure worker
  | none =>
      let worker ← liftM (m := IO) <|
        CanonicalHashWorker.start state.hashToolPath
      memo.set { state with hashWorker? := some worker }
      pure worker
  liftM (m := IO) <| worker.digest input

private def stopCanonicalHashWorker
    (memo : CanonicalExprRopeMemoRef) : MetaM Bool := do
  let state ← memo.get
  let some worker := state.hashWorker? | return false
  memo.set { state with hashWorker? := none }
  liftM (m := IO) worker.stop
  pure true

private def withCanonicalHashWorker
    (memo : CanonicalExprRopeMemoRef) (action : MetaM α) : MetaM α := do
  try
    let knownVector ← canonicalDigestWithMemo memo "abc"
    unless knownVector ==
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" do
      throwError "signature-manifest SHA-256 worker failed its known vector"
    let result ← action
    unless ← stopCanonicalHashWorker memo do
      throwError "signature-manifest SHA-256 worker was not initialized"
    pure result
  catch exception =>
    try
      let _ ← stopCanonicalHashWorker memo
      pure ()
    catch _ => pure ()
    throw exception

private def canonicalExprRopeMarkerTag :=
  "__econcslib_internal_canonical_rope_ref_v1__"

private def canonicalExprRopeMarker (index : Nat) : Json :=
  Json.arr #[Json.str canonicalExprRopeMarkerTag, Json.str (toString index)]

private def canonicalExprRopeMarkerIndex? : Json → Option Nat
  | .arr values =>
      if values.size != 2 then
        none
      else
        match values[0]!, values[1]! with
        | .str tag, .str index =>
            if tag == canonicalExprRopeMarkerTag then index.toNat? else none
        | _, _ => none
  | _ => none

private partial def canonicalJsonCompact
    (entries : Array CanonicalExprRopeMemoEntry) (value : Json) : MetaM Json := do
  if let some index := canonicalExprRopeMarkerIndex? value then
    let some entry := entries[index]? |
      throwError "unresolved internal compact-canonical reference"
    return entry.compact
  match value with
  | .arr values =>
      return Json.arr (← values.mapM (canonicalJsonCompact entries))
  | .obj fields =>
      let mut compact : List (String × Json) := []
      for (key, child) in fields.toArray do
        compact := (key, ← canonicalJsonCompact entries child) :: compact
      return Json.mkObj compact.reverse
  | other => return other

private def canonicalSemanticDependencyTags : Array String := #[
  "inlined_definition",
  "internal_proof",
  "local_theorem",
  "local_inductive",
  "local_constructor",
  "local_recursor",
  "local_opaque",
  "local_axiom"
]

private def compactCanonicalDependency
    (memo : CanonicalExprRopeMemoRef) (value : Json) : MetaM Json := do
  let tag? := (value.getObjVal? "tag").toOption.bind (·.getStr?.toOption)
  let some tag := tag? | return value
  unless canonicalSemanticDependencyTags.contains tag do
    return value
  let digest ← canonicalDigestWithMemo memo value.compress
  return obj tag [("sha256", Json.str digest)]

private def canonicalExprRopeMemoKey
    (name : Name) (levels : List Level) (recursiveNames : Array Name) :
    String :=
  -- Lean declarations form an acyclic environment graph; recursive groups
  -- are represented explicitly by `recursiveNames`.  The traversal's current
  -- ancestor stack is therefore a cycle-detection guard, not semantic input
  -- to a declaration's canonical expansion.  Keeping it out of this
  -- process-local key lets one exact expansion serve every occurrence.
  (Json.arr #[
    Json.str name.toString,
    Json.arr (levels.toArray.map fun level => Json.str (reprStr level)),
    Json.arr (recursiveNames.map fun recursiveName => Json.str recursiveName.toString)]).compress

private def canonicalExprRopeMemoGet?
    (memo : CanonicalExprRopeMemoRef) (key : String) : MetaM (Option Json) := do
  let state ← memo.get
  let some index := state.keys[key]? | return none
  unless index < state.entries.size do
    throwError "invalid internal canonical-rope memo index"
  return some (canonicalExprRopeMarker index)

private def canonicalExprRopeMemoPut
    (memo : CanonicalExprRopeMemoRef) (key : String) (canonical : Json) :
    MetaM Json := do
  let state ← memo.get
  let compactCanonical ← canonicalJsonCompact state.entries canonical
  let compact ← compactCanonicalDependency memo compactCanonical
  -- Hash-worker startup updates the memo, so extend the refreshed state rather
  -- than overwriting its live child with the pre-digest snapshot.
  let refreshed ← memo.get
  let index := refreshed.entries.size
  memo.set {
    refreshed with
      keys := refreshed.keys.insert key index
      entries := refreshed.entries.push { compact }
  }
  return canonicalExprRopeMarker index

private partial def canonicalExpr
    (params : Array Name) (fvars : Array FVarId) (boundFvars : Array FVarId)
    (auditModulePrefixes : Array Name)
    (reviewedModule : Option ModuleIdx)
    (recursiveNames : Array Name) (unfolding : Array Name) (expr : Expr)
    (ropeMemo? : Option CanonicalExprRopeMemoRef := none) : MetaM Json := do
  match expr with
  | .bvar index =>
      throwError "unexpected raw bound variable #{index} in canonical expression"
  | .fvar id =>
      match fvars.findIdx? (fun candidate => candidate == id) with
      | some index =>
          pure (obj "fvar" [("index", Json.str (toString index))])
      | none =>
          match boundFvars.findIdx? (fun candidate => candidate == id) with
          | some index =>
              pure (obj "bvar" [
                ("index", Json.str (toString (boundFvars.size - index - 1)))])
          | none => throwError "unregistered free variable in reviewed signature"
  | .mvar _ =>
      throwError "unresolved metavariable in reviewed signature"
  | .sort level =>
      pure (obj "sort" [("level", ← canonicalLevel params level)])
  | .const name levels =>
      if unfolding.size >= 128 then
        throwError "reviewed declaration dependency closure exceeds 128 definitions"
      let memoKey := canonicalExprRopeMemoKey name levels recursiveNames
      if let some ropeMemo := ropeMemo? then
        if let some cached ← canonicalExprRopeMemoGet? ropeMemo memoKey then
          return cached
      let canonicalLevels := Json.arr (← levels.toArray.mapM (canonicalLevel params))
      let canonical ← match recursiveNames.findIdx? (fun candidate => candidate.isPrefixOf name) with
      | some index =>
          if recursiveNames[index]! == name then
            pure (obj "recursive" [
              ("index", Json.str (toString index)),
              ("levels", canonicalLevels)])
          else
            if unfolding.contains name then
              throwError "recursive generated helper cycle in reviewed definition body"
            let helperInfo ← getConstInfo name
            match helperInfo with
            | .defnInfo helper =>
                let helperType := helper.type.instantiateLevelParams helper.levelParams levels
                let helperValue := helper.value.instantiateLevelParams helper.levelParams levels
                pure (obj "inlined_definition" [
                  ("type", ← canonicalExpr params #[] #[] auditModulePrefixes reviewedModule recursiveNames (unfolding.push name) helperType ropeMemo?),
                  ("value", ← canonicalExpr params #[] #[] auditModulePrefixes reviewedModule recursiveNames (unfolding.push name) helperValue ropeMemo?)])
            | .ctorInfo ctor =>
                let .inductInfo inductiveInfo ← getConstInfo ctor.induct
                  | throwError "missing inductive for reviewed generated constructor"
                let helperType := helperInfo.type.instantiateLevelParams helperInfo.levelParams levels
                pure (obj "local_constructor" [
                  ("index", Json.str (toString ctor.cidx)),
                  ("type", ← canonicalExpr params #[] #[] auditModulePrefixes reviewedModule inductiveInfo.all.toArray (unfolding.push name) helperType ropeMemo?)])
            | .recInfo recursor =>
                let helperType := helperInfo.type.instantiateLevelParams helperInfo.levelParams levels
                pure (obj "local_recursor" [
                  ("type", ← canonicalExpr params #[] #[] auditModulePrefixes reviewedModule recursor.all.toArray (unfolding.push name) helperType ropeMemo?),
                  ("num_params", Json.str (toString recursor.numParams)),
                  ("num_indices", Json.str (toString recursor.numIndices)),
                  ("num_motives", Json.str (toString recursor.numMotives)),
                  ("num_minors", Json.str (toString recursor.numMinors))])
            | .thmInfo _ =>
                let helperType := helperInfo.type.instantiateLevelParams helperInfo.levelParams levels
                pure (obj "generated_proof" [
                  ("type", ← canonicalExpr params #[] #[] auditModulePrefixes reviewedModule recursiveNames (unfolding.push name) helperType ropeMemo?)])
            | _ =>
                throwError "generated recursive helper is not a reducible definition"
      | none =>
          if name.isInternalDetail then
            if unfolding.contains name then
              throwError "internal helper cycle in reviewed definition body"
            let internalInfo ← getConstInfo name
            let internalType :=
              internalInfo.type.instantiateLevelParams internalInfo.levelParams levels
            let next := unfolding.push name
            match internalInfo with
            | .defnInfo internal =>
                let internalValue :=
                  internal.value.instantiateLevelParams internal.levelParams levels
                pure (obj "inlined_definition" [
                  ("type", ← canonicalExpr params #[] #[] auditModulePrefixes reviewedModule recursiveNames next internalType ropeMemo?),
                  ("value", ← canonicalExpr params #[] #[] auditModulePrefixes reviewedModule recursiveNames next internalValue ropeMemo?)])
            | .thmInfo _ | .opaqueInfo _ =>
                pure (obj "internal_proof" [
                  ("type", ← canonicalExpr params #[] #[] auditModulePrefixes reviewedModule recursiveNames next internalType ropeMemo?)])
            | _ =>
                throwError "unsupported internal constant in reviewed definition body"
          else if (← inAuditClosure auditModulePrefixes reviewedModule name) then
            if unfolding.contains name then
              throwError "local definition cycle in reviewed declaration closure"
            let localInfo ← getConstInfo name
            let localType := localInfo.type.instantiateLevelParams localInfo.levelParams levels
            let next := unfolding.push name
            match localInfo with
            | .defnInfo localDefinition =>
                let localValue :=
                  localDefinition.value.instantiateLevelParams localDefinition.levelParams levels
                pure (obj "inlined_definition" [
                  ("type", ← canonicalExpr params #[] #[] auditModulePrefixes reviewedModule recursiveNames next localType ropeMemo?),
                  ("value", ← canonicalExpr params #[] #[] auditModulePrefixes reviewedModule recursiveNames next localValue ropeMemo?)])
            | .thmInfo _ =>
                pure (obj "local_theorem" [
                  ("type", ← canonicalExpr params #[] #[] auditModulePrefixes reviewedModule recursiveNames next localType ropeMemo?)])
            | .opaqueInfo _ =>
                throwError "opaque local value in reviewed declaration closure"
            | .axiomInfo _ =>
                throwError "axiom constant in reviewed declaration closure"
            | .inductInfo inductiveInfo =>
                let roots := inductiveInfo.all.toArray
                let mut constructors : Array Json := #[]
                for ctorName in inductiveInfo.ctors do
                  let .ctorInfo ctor ← getConstInfo ctorName
                    | throwError "missing constructor in reviewed local inductive"
                  let ctorType := ctor.type.instantiateLevelParams ctor.levelParams levels
                  constructors := constructors.push <|
                    ← canonicalExpr params #[] #[] auditModulePrefixes reviewedModule roots next ctorType ropeMemo?
                pure (obj "local_inductive" [
                  ("type", ← canonicalExpr params #[] #[] auditModulePrefixes reviewedModule roots next localType ropeMemo?),
                  ("num_params", Json.str (toString inductiveInfo.numParams)),
                  ("num_indices", Json.str (toString inductiveInfo.numIndices)),
                  ("constructors", Json.arr constructors)])
            | .ctorInfo ctor =>
                let .inductInfo inductiveInfo ← getConstInfo ctor.induct
                  | throwError "missing inductive for reviewed local constructor"
                pure (obj "local_constructor" [
                  ("index", Json.str (toString ctor.cidx)),
                  ("type", ← canonicalExpr params #[] #[] auditModulePrefixes reviewedModule inductiveInfo.all.toArray next localType ropeMemo?)])
            | .recInfo recursor =>
                pure (obj "local_recursor" [
                  ("type", ← canonicalExpr params #[] #[] auditModulePrefixes reviewedModule recursor.all.toArray next localType ropeMemo?),
                  ("num_params", Json.str (toString recursor.numParams)),
                  ("num_indices", Json.str (toString recursor.numIndices)),
                  ("num_motives", Json.str (toString recursor.numMotives)),
                  ("num_minors", Json.str (toString recursor.numMinors))])
            | .quotInfo _ =>
                throwError "local quotient primitive in reviewed declaration closure"
          else
            pure (obj "const" [
              ("name", Json.str name.toString),
              ("levels", canonicalLevels)])
      match ropeMemo? with
      | some ropeMemo => canonicalExprRopeMemoPut ropeMemo memoKey canonical
      | none => pure canonical
  | .app fn arg =>
      -- Preserve the elaborator's binder role for this application argument.
      -- The Python-side structural matcher uses it to exclude type and
      -- instance metadata from mathematical term evidence.
      let fnType ← inferType fn
      let reducedFnType ← whnf fnType
      let argumentBinderInfo :=
        match reducedFnType with
        | .forallE _ _ _ binderInfo => binderInfoName binderInfo
        | _ => "unknown"
      pure (obj "app" [
        ("fn", ← canonicalExpr params fvars boundFvars auditModulePrefixes reviewedModule recursiveNames unfolding fn ropeMemo?),
        ("arg", ← canonicalExpr params fvars boundFvars auditModulePrefixes reviewedModule recursiveNames unfolding arg ropeMemo?),
        ("arg_binder_info", Json.str argumentBinderInfo)])
  | .lam name domain body binderInfo =>
      let canonicalDomain ←
        canonicalExpr params fvars boundFvars auditModulePrefixes reviewedModule recursiveNames unfolding domain ropeMemo?
      withLocalDecl name binderInfo domain fun binder => do
        let canonicalBody ← canonicalExpr params fvars (boundFvars.push binder.fvarId!)
          auditModulePrefixes reviewedModule recursiveNames unfolding (body.instantiate1 binder) ropeMemo?
        pure (obj "lam" [
          ("binder_info", Json.str (binderInfoName binderInfo)),
          ("domain", canonicalDomain),
          ("body", canonicalBody)])
  | .forallE name domain body binderInfo =>
      let domainIsProposition ← isProp domain
      let canonicalDomain ←
        canonicalExpr params fvars boundFvars auditModulePrefixes reviewedModule recursiveNames unfolding domain ropeMemo?
      withLocalDecl name binderInfo domain fun binder => do
        let canonicalBody ← canonicalExpr params fvars (boundFvars.push binder.fvarId!)
          auditModulePrefixes reviewedModule recursiveNames unfolding (body.instantiate1 binder) ropeMemo?
        pure (obj "forall" [
          ("binder_info", Json.str (binderInfoName binderInfo)),
          ("domain_is_proposition", Json.bool domainIsProposition),
          ("domain", canonicalDomain),
          ("body", canonicalBody)])
  | .letE name type value body nondep =>
      let canonicalType ←
        canonicalExpr params fvars boundFvars auditModulePrefixes reviewedModule recursiveNames unfolding type ropeMemo?
      let canonicalValue ←
        canonicalExpr params fvars boundFvars auditModulePrefixes reviewedModule recursiveNames unfolding value ropeMemo?
      withLetDecl name type value (nondep := nondep) fun binder => do
        let canonicalBody ← canonicalExpr params fvars (boundFvars.push binder.fvarId!)
          auditModulePrefixes reviewedModule recursiveNames unfolding (body.instantiate1 binder) ropeMemo?
        pure (obj "let" [
          ("type", canonicalType),
          ("value", canonicalValue),
          ("body", canonicalBody),
          ("nondep", Json.bool nondep)])
  | .lit literal =>
      pure (obj "lit" [("value", Json.str (reprStr literal))])
  | .mdata _ body =>
      canonicalExpr params fvars boundFvars auditModulePrefixes reviewedModule recursiveNames unfolding body ropeMemo?
  | .proj _ index structExpr =>
      pure (obj "proj" [
        ("index", Json.str (toString index)),
        ("structure", ← canonicalExpr params fvars boundFvars auditModulePrefixes reviewedModule recursiveNames unfolding structExpr ropeMemo?)])

private def canonicalExprCompactWithMemo
    (params : Array Name) (fvars : Array FVarId) (boundFvars : Array FVarId)
    (auditModulePrefixes : Array Name) (reviewedModule : Option ModuleIdx)
    (recursiveNames : Array Name) (unfolding : Array Name) (expr : Expr)
    (memo : CanonicalExprRopeMemoRef) : MetaM Json := do
  let canonical ← canonicalExpr params fvars boundFvars auditModulePrefixes
    reviewedModule recursiveNames unfolding expr (some memo)
  let state ← memo.get
  canonicalJsonCompact state.entries canonical

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def conclusionMode : ConstantInfo → String
  | .defnInfo _ => "type_and_value"
  | _ => "type_only"

/--
Pretty-print a source-review expression without suppressing the domain of a
lambda hidden by notation such as `∃ witness, ...`.  Lean's ordinary printer may
infer that domain from the `Exists` application and omit it, even though the
domain can carry a material source condition.  This uses Lean's own elaborated
expression and delaborator; it does not reconstruct binders from source text.
-/
private def ppSemanticReviewExpr (expression : Expr) : MetaM String := do
  let rendered ← withOptions (fun options =>
    options.setBool `pp.funBinderTypes true |>
      (fun options => options.setBool `pp.letVarTypes true |>
        (fun options => options.setBool `pp.proofs true))) <|
    ppExpr expression
  pure rendered.pretty

private def conclusionAtom
    (info : ConstantInfo) (params : Array Name) (typeBinders : Array Expr)
    (auditModulePrefixes : Array Name) (reviewedModule : Option ModuleIdx)
    (memo : CanonicalExprRopeMemoRef) (resultType : Expr) :
    MetaM (Json × String) := do
  let canonicalType ←
    canonicalExprCompactWithMemo params (typeBinders.map Expr.fvarId!) #[]
      auditModulePrefixes reviewedModule #[] #[] resultType memo
  match info with
  | .defnInfo definition =>
      let value ← whnf <| mkAppN definition.value typeBinders
      let recursiveNames := definition.all.toArray
      let canonicalValue ←
        canonicalExprCompactWithMemo params (typeBinders.map Expr.fvarId!) #[]
          auditModulePrefixes reviewedModule recursiveNames #[] value memo
      let typeDisplay ← ppSemanticReviewExpr resultType
      let valueDisplay ← ppSemanticReviewExpr value
      pure (
        obj "definition" [
          ("type", canonicalType),
          ("value", canonicalValue)],
        s!"{typeDisplay} := {valueDisplay}")
  | .inductInfo inductiveInfo =>
      let roots := inductiveInfo.all.toArray
      let mut constructors : Array Json := #[]
      for ctorName in inductiveInfo.ctors do
        let .ctorInfo ctor ← getConstInfo ctorName
          | throwError "missing constructor in reviewed root inductive"
        constructors := constructors.push <|
          ← canonicalExprCompactWithMemo params #[] #[] auditModulePrefixes
            reviewedModule roots #[] ctor.type memo
      pure (
        obj "inductive" [
          ("type", canonicalType),
          ("num_params", Json.str (toString inductiveInfo.numParams)),
          ("num_indices", Json.str (toString inductiveInfo.numIndices)),
          ("constructors", Json.arr constructors)],
        ← ppSemanticReviewExpr resultType)
  | _ =>
      pure (canonicalType, ← ppSemanticReviewExpr resultType)

/--
Zeta-reduce only result-type `let` bindings before serializing a reviewed
declaration.  A source-facing theorem may name a raw law locally in its
proposition; retaining that name as a de Bruijn variable would make the audit
unable to check that the same law is used by the terminal comparison.  This
never reads a theorem proof body.
-/
private partial def zetaResultType (fuel : Nat) (resultType : Expr) : MetaM Expr := do
  match resultType with
  | .mdata _ body => zetaResultType fuel body
  | .letE _ _ value body _ =>
      if fuel == 0 then
        throwError "result-type zeta reduction exceeded its bounded fuel"
      zetaResultType (fuel - 1) (body.instantiate1 value)
  | _ => pure resultType

/-!
The dependency graph below is deliberately elaboration-owned.  Source syntax
has already disappeared before it runs, so notation, macros, coercions, and
typeclass synthesis contribute the constants and arguments Lean actually
checked.  Declaration spellings are retained only as diagnostic coordinates;
Python hashes the canonical identities and edge topology separately.
-/

private structure SemanticDependencyGraphState where
  nodes : Array Json := #[]
  edges : Array Json := #[]
  failures : Array Json := #[]

private def semanticDependencyOrigin
    (auditModules : Array Name) (rootModule : Option ModuleIdx) (name : Name) :
    MetaM (String × String × Bool) := do
  let env ← getEnv
  match env.getModuleIdxFor? name with
  | some moduleIdx =>
      let moduleName := env.header.moduleNames[moduleIdx.toNat]!
      let owned :=
        if auditModules.isEmpty then rootModule == some moduleIdx
        else auditModules.contains moduleName
      pure (
        if owned then "review_closure" else "imported_terminal",
        moduleName.toString,
        owned)
  | none =>
      let owned := rootModule.isNone || name.isInternalDetail
      pure (
        if owned then "review_closure" else "unresolved",
        if name.isInternalDetail then "<internal>" else "<inline>",
        owned)

private def semanticDependencyCanonicalIdentity
    (auditModules : Array Name) (memo : CanonicalExprRopeMemoRef)
    (name : Name) (info : ConstantInfo) : MetaM Json := do
  let params := info.levelParams.toArray
  let moduleIdx := (← getEnv).getModuleIdxFor? name
  let canonicalType ←
    canonicalExprCompactWithMemo params #[] #[] auditModules moduleIdx #[] #[]
      info.type memo
  match info with
  | .defnInfo definition =>
      pure <| obj "definition" [
        ("type", canonicalType),
        ("value", ← canonicalExprCompactWithMemo params #[] #[] auditModules
          moduleIdx definition.all.toArray #[name] definition.value memo)]
  | .inductInfo inductiveInfo =>
      let roots := inductiveInfo.all.toArray
      let mut constructors : Array Json := #[]
      for constructorName in inductiveInfo.ctors do
        let constructorInfo ← getConstInfo constructorName
        constructors := constructors.push <|
          ← canonicalExprCompactWithMemo params #[] #[] auditModules moduleIdx
            roots #[name] constructorInfo.type memo
      pure <| obj "inductive" [
        ("type", canonicalType),
        ("constructors", Json.arr constructors)]
  | _ =>
      pure <| obj (declarationKind info) [("type", canonicalType)]

private def semanticDependencyFailure
    (state : SemanticDependencyGraphState) (tag : String) (name : Name) :
    SemanticDependencyGraphState :=
  { state with failures := state.failures.push <| Json.mkObj [
      ("tag", Json.str tag),
      ("declaration", Json.str name.toString)] }

private def semanticDependencyEdge
    (state : SemanticDependencyGraphState) (source target : Name)
    (role : String) : SemanticDependencyGraphState :=
  { state with edges := state.edges.push <| Json.mkObj [
      ("source", Json.str source.toString),
      ("target", Json.str target.toString),
      ("role", Json.str role)] }

private def semanticDependencyDirectEdges
    (info : ConstantInfo) : MetaM (Array (String × Name)) := do
  let mut dependencies : Array (String × Name) :=
    info.type.getUsedConstantsAsSet.toArray.map (fun dependency =>
      ("type_uses_constant", dependency))
  match info with
  | .defnInfo definition =>
      dependencies := dependencies ++
        definition.value.getUsedConstantsAsSet.toArray.map (fun dependency =>
          ("value_uses_constant", dependency))
  | .thmInfo theoremInfo =>
      dependencies := dependencies ++
        theoremInfo.value.getUsedConstantsAsSet.toArray.map (fun dependency =>
          ("proof_uses_constant", dependency))
  | .inductInfo inductiveInfo =>
      for constructorName in inductiveInfo.ctors do
        let constructorInfo ← getConstInfo constructorName
        dependencies := dependencies ++
          constructorInfo.type.getUsedConstantsAsSet.toArray.map (fun dependency =>
            ("constructor_type_uses_constant", dependency))
  | _ => pure ()
  pure dependencies

private structure StatementDependencyClosure where
  names : NameSet := {}
  scanFailures : Array Name := #[]

private def statementDependencyClosureFor
    (declName : Name) (auditModules : Array Name)
    (rootModule : Option ModuleIdx) : MetaM StatementDependencyClosure := do
  -- This is the statement-only lane of Lean's elaborated dependency graph.
  -- Direct edges come from `Expr.getUsedConstantsAsSet`; theorem proof bodies
  -- are the sole excluded role. No source spelling or parser participates.
  let mut names : NameSet := {}
  let mut pending : Array Name := #[declName]
  let mut cursor := 0
  let mut scanFailures : Array Name := #[]
  while h : cursor < pending.size do
    let name := pending[cursor]
    cursor := cursor + 1
    if !names.contains name then
      names := names.insert name
      let info? ← try some <$> getConstInfo name catch _ => pure none
      match info? with
      | none => scanFailures := scanFailures.push name
      | some info =>
          let (_, _, owned) ←
            semanticDependencyOrigin auditModules rootModule name
          -- Acceptance recursively expands paper-owned declarations. An
          -- imported declaration is a terminal whose exact compiled module
          -- identity is pinned, so this statement lane must stop there too.
          if owned then
            let dependencies? ← try some <$> semanticDependencyDirectEdges info
              catch _ => pure none
            match dependencies? with
            | none => scanFailures := scanFailures.push name
            | some dependencies =>
                for (role, dependency) in dependencies do
                  if role != "proof_uses_constant" &&
                      !names.contains dependency then
                    pending := pending.push dependency
  pure { names, scanFailures }

private def relationValuedTransitionTypeMatches
    (type : Expr) (expectedState : Option Expr := none) : MetaM Bool := do
  forallTelescopeReducing type fun binders result => do
    if binders.size < 2 || !(← isDefEq result (mkSort .zero)) then
      return false
    let firstStateType ← inferType binders[binders.size - 2]!
    let secondStateType ← inferType binders[binders.size - 1]!
    unless ← isDefEq firstStateType secondStateType do
      return false
    if let some stateType := expectedState then
      unless ← isDefEq firstStateType stateType do
        return false
    return true

private def pathOperatorTypeShape (type : Expr) : MetaM Bool := do
  forallTelescopeReducing type fun binders result => do
    if binders.size < 3 || !(← isDefEq result (mkSort .zero)) then
      return false
    let firstEndpointType ← inferType binders[binders.size - 2]!
    let secondEndpointType ← inferType binders[binders.size - 1]!
    unless ← isDefEq firstEndpointType secondEndpointType do
      return false
    for index in [0:binders.size - 2] do
      let some binder := binders[index]? | return false
      let domain ← inferType binder
      if ← relationValuedTransitionTypeMatches domain (some firstEndpointType) then
        return true
    return false

private def executionStateRefinementTypeShape
    (type : Expr) : MetaM (Bool × Bool) := do
  let hasTransition ← forallTelescopeReducing type fun binders _ => do
    for binder in binders do
      if ← relationValuedTransitionTypeMatches (← inferType binder) then
        return true
    return false
  let hasPathOperator ← pathOperatorTypeShape type
  pure (hasTransition, hasPathOperator)

private structure ExecutionStateRefinementShapeState where
  typeSurfacesScanned : Nat := 0
  scanFailures : Nat := 0
  hasTransition : Bool := false
  hasPathOperator : Bool := false

private def executionStateRefinementShapeFor
    (closure : StatementDependencyClosure) (auditModules : Array Name)
    (rootModule : Option ModuleIdx) : MetaM Json := do
  let mut state : ExecutionStateRefinementShapeState := {}
  for name in closure.names do
    let info? ← try some <$> getConstInfo name catch _ => pure none
    match info? with
    | none => state := { state with scanFailures := state.scanFailures + 1 }
    | some info =>
        let mut surfaces : Array Expr := #[info.type]
        let (_, _, owned) ← semanticDependencyOrigin auditModules rootModule name
        if owned then
          match info with
          | .inductInfo inductiveInfo =>
              for constructorName in inductiveInfo.ctors do
                let constructorInfo? ← try some <$> getConstInfo constructorName
                  catch _ => pure none
                match constructorInfo? with
                | some constructorInfo =>
                    surfaces := surfaces.push constructorInfo.type
                | none =>
                    state := { state with scanFailures := state.scanFailures + 1 }
          | _ => pure ()
        for surface in surfaces do
          let shape? ← try some <$> executionStateRefinementTypeShape surface
            catch _ => pure none
          match shape? with
          | none => state := { state with scanFailures := state.scanFailures + 1 }
          | some (hasTransition, hasPathOperator) =>
              state := {
                state with
                  typeSurfacesScanned := state.typeSurfacesScanned + 1
                  hasTransition := state.hasTransition || hasTransition
                  hasPathOperator := state.hasPathOperator || hasPathOperator }
  let scanComplete := closure.scanFailures.isEmpty && state.scanFailures == 0
  let detected := scanComplete && state.hasTransition && state.hasPathOperator
  pure <| Json.mkObj [
    ("schema", Json.str "2"),
    ("detector_basis", Json.str
      "lean_statement_dependency_graph_structural_v1"),
    ("scan_complete", Json.bool scanComplete),
    ("canonical_nodes_scanned", Json.str (toString state.typeSurfacesScanned)),
    -- Historical compatibility label. This now means any structurally
    -- elaborated path operator `(State → State → Prop) → State → State → Prop`;
    -- no `Relation.ReflTransGen` or local declaration spelling is matched.
    ("has_refl_trans_gen_path", Json.bool state.hasPathOperator),
    ("has_relation_valued_state_transition", Json.bool state.hasTransition),
    ("detected", Json.bool detected)]

private def semanticDependencyGraphFor
    (declName : Name) (auditModules : Array Name)
    (memo : CanonicalExprRopeMemoRef) : MetaM (Json × Json) := do
  let rootModule := (← getEnv).getModuleIdxFor? declName
  -- Lean's environment-owned closure handles SCCs and every elaborated
  -- constant introduced by notation, macros, coercions, and typeclass
  -- synthesis.  Direct `foldConsts` sets below label the edge lane; Python
  -- never reconstructs closure membership from source tokens.
  let transitive ← declName.transitivelyUsedConstants
  -- Compute the statement lane independently. The environment-wide closure
  -- above includes theorem proof bodies; those belong only to realization
  -- reuse.
  let statementClosure ← statementDependencyClosureFor declName auditModules rootModule
  let mut included : NameSet := {}
  let mut state : SemanticDependencyGraphState := {}
  for name in statementClosure.scanFailures do
    state := semanticDependencyFailure state
      "statement_dependency_scan_failed" name
  for name in transitive do
    let (_, _, owned) ← semanticDependencyOrigin auditModules rootModule name
    if owned then
      included := included.insert name
      let info? ← try some <$> getConstInfo name catch _ => pure none
      match info? with
      | some info =>
          let dependencies? ← try some <$> semanticDependencyDirectEdges info
            catch _ => pure none
          match dependencies? with
          | some dependencies =>
              for (_, dependency) in dependencies do
                included := included.insert dependency
          | none =>
              state := semanticDependencyFailure state
                "direct_dependency_scan_failed" name
      | none =>
          state := semanticDependencyFailure state "unresolved_constant" name
  included := included.insert declName
  let mut semanticExternalModuleOrigins : Array String := #[]
  for name in statementClosure.names do
    let (originClass, moduleOrigin, owned) ←
      semanticDependencyOrigin auditModules rootModule name
    if !owned && originClass == "imported_terminal" &&
        !semanticExternalModuleOrigins.contains moduleOrigin then
      semanticExternalModuleOrigins :=
        semanticExternalModuleOrigins.push moduleOrigin
  let mut realizationExternalModuleOrigins : Array String := #[]
  for name in transitive do
    let (originClass, moduleOrigin, owned) ←
      semanticDependencyOrigin auditModules rootModule name
    if !owned && originClass == "imported_terminal" &&
        !realizationExternalModuleOrigins.contains moduleOrigin then
      realizationExternalModuleOrigins :=
        realizationExternalModuleOrigins.push moduleOrigin
  for name in included do
    let info? ← try some <$> getConstInfo name catch _ => pure none
    match info? with
    | none =>
        state := semanticDependencyFailure state "unresolved_constant" name
    | some info =>
        let (originClass, moduleOrigin, _) ←
          semanticDependencyOrigin auditModules rootModule name
        let statementReachable := statementClosure.names.contains name
        let identity? ←
          if statementReachable then
            try
              some <$> semanticDependencyCanonicalIdentity auditModules memo name info
            catch _ => pure none
          else
            -- Proof-only transitive nodes are trusted through Lean's graph and
            -- the exact reached module artifact attached by Python. Expanding
            -- their statement bodies again is redundant, can retain gigabytes
            -- of canonical JSON, and does not add proof validity: Lean has
            -- already checked the root `.olean`. The generic identity keeps
            -- declaration spellings out of evidence while kind, topology, and
            -- exact compiled bytes remain material.
            pure <| some <| Json.mkObj [
              ("tag", Json.str "realization_artifact_terminal_v1")]
        match identity? with
        | none =>
            state := semanticDependencyFailure state
              "canonical_identity_failed" name
        | some identity =>
            state := { state with nodes := state.nodes.push <| Json.mkObj [
              ("declaration", Json.str name.toString),
              ("module_origin", Json.str moduleOrigin),
              ("origin_class", Json.str originClass),
              ("declaration_kind", Json.str (declarationKind info)),
              ("canonical_identity", identity)] }
  for source in included do
    let (_, _, owned) ← semanticDependencyOrigin auditModules rootModule source
    if owned then
      let info? ← try some <$> getConstInfo source catch _ => pure none
      match info? with
      | none => pure ()
      | some info =>
          let dependencies? ← try some <$> semanticDependencyDirectEdges info
            catch _ => pure none
          match dependencies? with
          | none =>
              state := semanticDependencyFailure state
                "direct_dependency_scan_failed" source
          | some dependencies =>
              for (role, target) in dependencies do
                if target != source && included.contains target then
                  state := semanticDependencyEdge state source target role
  let graph := Json.mkObj [
    ("schema", Json.str "1"),
    ("root_declaration", Json.str declName.toString),
    ("complete", Json.bool state.failures.isEmpty),
    ("nodes", Json.arr state.nodes),
    ("edges", Json.arr state.edges),
    ("semantic_external_module_origins", Json.arr <|
      semanticExternalModuleOrigins.qsort (· < ·) |>.map Json.str),
    ("realization_external_module_origins", Json.arr <|
      realizationExternalModuleOrigins.qsort (· < ·) |>.map Json.str),
    ("failures", Json.arr state.failures)]
  pure (graph, ← executionStateRefinementShapeFor statementClosure
    auditModules rootModule)

private structure ElaboratedPropositionGraphState where
  -- Count unique canonical states, not syntax paths. The exhaustive pass
  -- preserves compatible prior receipts when it succeeds. Any incomplete pass
  -- is retried from a clean state with only proposition wrappers unfolded.
  fuel : Nat := 4096
  expandTermDefinitions : Bool := true
  activeDefinitions : Array Name := #[]
  semanticStates : Std.HashMap String String := {}
  nodes : Array Json := #[]
  edges : Array Json := #[]
  failures : Array Json := #[]

private def propositionGraphPath (base suffix : String) : String :=
  if base.isEmpty then suffix else base ++ "/" ++ suffix

private def propositionGraphFailure
    (state : ElaboratedPropositionGraphState) (path tag : String) :
    ElaboratedPropositionGraphState :=
  { state with failures := state.failures.push <| Json.mkObj [
      ("path", Json.str path), ("tag", Json.str tag)] }

private def propositionGraphEdge
    (state : ElaboratedPropositionGraphState) (source target role : String) :
    ElaboratedPropositionGraphState :=
  { state with edges := state.edges.push <| Json.mkObj [
      ("source", Json.str source),
      ("target", Json.str target),
      ("role", Json.str role)] }

private def propositionGraphSemanticStateKey
    (canonical : Json) (kind : String) (activeDefinitions : Array Name) :
    String :=
  -- Declaration names are process-local cycle-context coordinates only. They
  -- never enter a graph node or digest. Exact canonical JSON remains the
  -- semantic identity, while the active stack prevents merging a wrapper
  -- expansion with the same expression reached under different recursion
  -- guards.
  (Json.arr #[
    Json.str kind,
    canonical,
    Json.arr (activeDefinitions.map fun name => Json.str name.toString)]).compress

private def canonicalObjectField? (value : Json) (field : String) : Option Json :=
  (value.getObjVal? field).toOption

private partial def canonicalApplicationSpine?
    (value : Json) : Option (Json × Array Json) := do
  let tag ← (value.getObjVal? "tag").toOption.bind (·.getStr?.toOption)
  if tag != "app" then
    return (value, #[])
  let fn ← canonicalObjectField? value "fn"
  let arg ← canonicalObjectField? value "arg"
  let (head, args) ← canonicalApplicationSpine? fn
  return (head, args.push arg)

private def canonicalApplicationArgument?
    (value : Json) (index : Nat) : Option Json := do
  let (_, args) ← canonicalApplicationSpine? value
  args[index]?

private partial def scanElaboratedPropositionExpr
    (params : Array Name) (outerFVars boundFVars : Array FVarId)
    (auditModules : Array Name) (reviewedModule : Option ModuleIdx)
    (memo : CanonicalExprRopeMemoRef)
    (state : ElaboratedPropositionGraphState) (path : String) (expr : Expr)
    (precomputedCanonical? : Option Json := none) :
    MetaM (ElaboratedPropositionGraphState × String) := do
  let canonical? ← match precomputedCanonical? with
  | some canonical => pure (some canonical)
  | none =>
      try
        some <$> canonicalExprCompactWithMemo params outerFVars boundFVars
          auditModules reviewedModule #[] #[] expr memo
      catch _ => pure none
  let some canonical := canonical? |
    return (propositionGraphFailure state path "canonical_node_failed", path)
  let mut kind : String := match expr with
    | .forallE _ _ _ _ => "forall"
    | .app _ _ => "application"
    | .lam _ _ _ _ => "lambda"
    | .letE _ _ _ _ _ => "let"
    | .mdata _ _ => "metadata"
    | .proj _ _ _ => "projection"
    | .const _ _ => "constant"
    | .fvar _ => "free_variable"
    | .bvar _ => "bound_variable"
    | .sort _ => "sort"
    | .lit _ => "literal"
    | .mvar _ => "metavariable"
  let (_, applicationArgs) := expr.getAppFnArgs
  let headExpr := expr.getAppFn
  let (headName?, headLevels) := match headExpr with
    | .const name levels => (some name, levels)
    | _ => (none, [])
  match expr with
  | .forallE _ domain _ _ =>
      if ← isProp domain then kind := "implication"
  | .app _ _ =>
      match headName? with
      | some name =>
          if name == ``And && applicationArgs.size == 2 then kind := "conjunction"
          else if name == ``Iff && applicationArgs.size == 2 then kind := "iff"
          else if name == ``Exists then kind := "exists"
          else if name == ``Not then kind := "negation"
          else
            let (_, _, owned) ← semanticDependencyOrigin auditModules reviewedModule name
            let info? ← try some <$> getConstInfo name catch _ => pure none
            match owned, info? with
            | true, some (.defnInfo _) =>
                if state.expandTermDefinitions || (← isProp expr) then
                  kind := "transparent_wrapper"
            | _, _ => pure ()
      | none => pure ()
  | .const name _ =>
      let (_, _, owned) ← semanticDependencyOrigin auditModules reviewedModule name
      let info? ← try some <$> getConstInfo name catch _ => pure none
      match owned, info? with
      | true, some (.defnInfo _) =>
          if state.expandTermDefinitions || (← isProp expr) then
            kind := "transparent_wrapper"
      | _, _ => pure ()
  | _ => pure ()
  let semanticStateKey := propositionGraphSemanticStateKey canonical kind
    state.activeDefinitions
  if let some existingPath := state.semanticStates[semanticStateKey]? then
    return (state, existingPath)
  if state.fuel == 0 then
    return (propositionGraphFailure state path "fuel_exhausted", path)
  let mut current : ElaboratedPropositionGraphState := {
    state with
      fuel := state.fuel - 1
      semanticStates := state.semanticStates.insert semanticStateKey path
      nodes := state.nodes.push <| Json.mkObj [
        ("path", Json.str path),
        ("kind", Json.str kind),
        ("canonical", canonical)]
  }
  match expr with
  | .forallE binderName domain body binderInfo =>
      let domainRole := if kind == "implication" then "antecedent" else "domain"
      let bodyRole := if kind == "implication" then "consequent" else "body"
      let domainPath := propositionGraphPath path domainRole
      let bodyPath := propositionGraphPath path bodyRole
      let (afterDomain, domainNode) ← scanElaboratedPropositionExpr
        params outerFVars boundFVars
        auditModules reviewedModule memo current domainPath domain
        (canonicalObjectField? canonical "domain")
      current := propositionGraphEdge afterDomain path domainNode domainRole
      withLocalDecl binderName binderInfo domain fun binder => do
        let (afterBody, bodyNode) ← scanElaboratedPropositionExpr params outerFVars
          (boundFVars.push binder.fvarId!) auditModules reviewedModule memo current
          bodyPath (body.instantiate1 binder)
          (canonicalObjectField? canonical "body")
        return (propositionGraphEdge afterBody path bodyNode bodyRole, path)
  | .app fn arg =>
      if kind == "conjunction" || kind == "iff" then
        let leftPath := propositionGraphPath path "left"
        let rightPath := propositionGraphPath path "right"
        let (afterLeft, leftNode) ← scanElaboratedPropositionExpr
          params outerFVars boundFVars
          auditModules reviewedModule memo current leftPath applicationArgs[0]!
          (canonicalApplicationArgument? canonical 0)
        current := propositionGraphEdge afterLeft path leftNode "left"
        let (afterRight, rightNode) ← scanElaboratedPropositionExpr
          params outerFVars boundFVars auditModules
          reviewedModule memo current rightPath applicationArgs[1]!
          (canonicalApplicationArgument? canonical 1)
        return (propositionGraphEdge afterRight path rightNode "right", path)
      else if kind == "transparent_wrapper" then
        let some name := headName? |
          return (propositionGraphFailure current path "wrapper_head_missing", path)
        if current.activeDefinitions.contains name then
          return (propositionGraphFailure current path "recursive_wrapper", path)
        let .defnInfo definition ← getConstInfo name |
          return (propositionGraphFailure current path "wrapper_definition_missing", path)
        let expandedPath := propositionGraphPath path "expanded_body"
        let instantiatedValue :=
          definition.value.instantiateLevelParams definition.levelParams headLevels
        let expanded ← withTransparency .reducible <|
          whnf (mkAppN instantiatedValue applicationArgs)
        let activeCurrent := { current with
          activeDefinitions := current.activeDefinitions.push name }
        let (expandedState, expandedNode) ← scanElaboratedPropositionExpr
          params outerFVars boundFVars auditModules
          reviewedModule memo activeCurrent expandedPath expanded
        let restoredState := { expandedState with activeDefinitions :=
          (expandedState.activeDefinitions.filter fun candidate => candidate != name) }
        return (propositionGraphEdge restoredState path expandedNode "expanded_body", path)
      else
        let fnPath := propositionGraphPath path "function"
        let argPath := propositionGraphPath path "argument"
        let (afterFn, fnNode) ← scanElaboratedPropositionExpr
          params outerFVars boundFVars
          auditModules reviewedModule memo current fnPath fn
          (canonicalObjectField? canonical "fn")
        current := propositionGraphEdge afterFn path fnNode "function"
        let (afterArg, argNode) ← scanElaboratedPropositionExpr
          params outerFVars boundFVars auditModules
          reviewedModule memo current argPath arg
          (canonicalObjectField? canonical "arg")
        return (propositionGraphEdge afterArg path argNode "argument", path)
  | .lam binderName domain body binderInfo =>
      let domainPath := propositionGraphPath path "domain"
      let bodyPath := propositionGraphPath path "body"
      let (afterDomain, domainNode) ← scanElaboratedPropositionExpr
        params outerFVars boundFVars
        auditModules reviewedModule memo current domainPath domain
        (canonicalObjectField? canonical "domain")
      current := propositionGraphEdge afterDomain path domainNode "domain"
      withLocalDecl binderName binderInfo domain fun binder => do
        let (afterBody, bodyNode) ← scanElaboratedPropositionExpr params outerFVars
          (boundFVars.push binder.fvarId!) auditModules reviewedModule memo current
          bodyPath (body.instantiate1 binder)
          (canonicalObjectField? canonical "body")
        return (propositionGraphEdge afterBody path bodyNode "body", path)
  | .letE binderName type value body nondep =>
      let typePath := propositionGraphPath path "type"
      let valuePath := propositionGraphPath path "value"
      let bodyPath := propositionGraphPath path "body"
      let (afterType, typeNode) ← scanElaboratedPropositionExpr
        params outerFVars boundFVars
        auditModules reviewedModule memo current typePath type
        (canonicalObjectField? canonical "type")
      current := propositionGraphEdge afterType path typeNode "type"
      let (afterValue, valueNode) ← scanElaboratedPropositionExpr
        params outerFVars boundFVars
        auditModules reviewedModule memo current valuePath value
        (canonicalObjectField? canonical "value")
      current := propositionGraphEdge afterValue path valueNode "value"
      withLetDecl binderName type value (nondep := nondep) fun binder => do
        let (afterBody, bodyNode) ← scanElaboratedPropositionExpr params outerFVars
          (boundFVars.push binder.fvarId!) auditModules reviewedModule memo current
          bodyPath (body.instantiate1 binder)
          (canonicalObjectField? canonical "body")
        return (propositionGraphEdge afterBody path bodyNode "body", path)
  | .mdata _ body =>
      let bodyPath := propositionGraphPath path "body"
      let (afterBody, bodyNode) ← scanElaboratedPropositionExpr
        params outerFVars boundFVars auditModules
        reviewedModule memo current bodyPath body (some canonical)
      return (propositionGraphEdge afterBody path bodyNode "body", path)
  | .proj _ _ body =>
      let bodyPath := propositionGraphPath path "projected"
      let (afterBody, bodyNode) ← scanElaboratedPropositionExpr
        params outerFVars boundFVars auditModules
        reviewedModule memo current bodyPath body
        (canonicalObjectField? canonical "structure")
      return (propositionGraphEdge afterBody path bodyNode "projected", path)
  | .const name levels =>
      if kind != "transparent_wrapper" then
        pure (current, path)
      else if current.activeDefinitions.contains name then
        pure (propositionGraphFailure current path "recursive_wrapper", path)
      else
        let .defnInfo definition ← getConstInfo name |
          return (propositionGraphFailure current path "wrapper_definition_missing", path)
        let expandedPath := propositionGraphPath path "expanded_body"
        let expanded := definition.value.instantiateLevelParams
          definition.levelParams levels
        let activeCurrent := { current with
          activeDefinitions := current.activeDefinitions.push name }
        let (expandedState, expandedNode) ← scanElaboratedPropositionExpr
          params outerFVars boundFVars
          auditModules reviewedModule memo activeCurrent expandedPath expanded
        let restoredState := { expandedState with activeDefinitions :=
          (expandedState.activeDefinitions.filter fun candidate => candidate != name) }
        return (propositionGraphEdge restoredState path expandedNode "expanded_body", path)
  | _ => pure (current, path)

private def elaboratedPropositionGraphFor
    (info : ConstantInfo) (params : Array Name) (binders : Array Expr)
    (auditModules : Array Name) (reviewedModule : Option ModuleIdx)
    (memo : CanonicalExprRopeMemoRef) (result : Expr) : MetaM Json := do
  let root ← match info with
    | .defnInfo definition =>
        if ← isDefEq result (mkSort .zero) then
          pure (mkAppN definition.value binders)
        else pure result
    | _ => pure result
  let (legacyState, _) ← scanElaboratedPropositionExpr
    params (binders.map Expr.fvarId!) #[]
    auditModules reviewedModule memo {} "result" root
  let state ← if !legacyState.failures.isEmpty then
    -- The connective DAG needs definitional transparency only for expressions
    -- that currently inhabit `Prop`. Term-valued definitions remain bound by
    -- the exact canonical statement and semantic dependency graph; recursively
    -- unfolding their implementations here duplicates those stronger lanes.
    -- If the richer scan cannot complete for any reason, retry in that minimal
    -- mode. A failure in an actual proposition wrapper remains a failure in the
    -- retry, so this does not turn incomplete proposition structure into credit.
    let (fallbackState, _) ← scanElaboratedPropositionExpr
      params (binders.map Expr.fvarId!) #[] auditModules reviewedModule memo
      ({ fuel := 16384, expandTermDefinitions := false } :
        ElaboratedPropositionGraphState)
      "result" root
    pure fallbackState
  else
    pure legacyState
  pure <| Json.mkObj [
    ("schema", Json.str "1"),
    ("complete", Json.bool state.failures.isEmpty),
    ("nodes", Json.arr state.nodes),
    ("edges", Json.arr state.edges),
    ("failures", Json.arr state.failures)]

/--
For a transparent `Prop`-valued definition, expose a second Lean-owned graph
whose root is the reducibly normalized definition value.  The ordinary
proposition graph deliberately starts from the applied value and can therefore
retain an application/lambda spine.  Assumption-review component receipts need
the logical value root itself so that conjunction coverage is derived from
Lean's elaborated structure rather than guessed from declaration names or
pretty-printed text.
-/
private def elaboratedTransparentResultValueGraphFor
    (info : ConstantInfo) (params : Array Name) (binders : Array Expr)
    (auditModules : Array Name) (reviewedModule : Option ModuleIdx)
    (memo : CanonicalExprRopeMemoRef) (result : Expr) : MetaM Json := do
  match info with
  | .defnInfo definition =>
      if !(← isDefEq result (mkSort .zero)) then
        pure Json.null
      else
        let appliedValue := mkAppN definition.value binders
        let reducedValue ← withTransparency .reducible <| whnf appliedValue
        let (state, _) ← scanElaboratedPropositionExpr
          params (binders.map Expr.fvarId!) #[] auditModules reviewedModule memo
          ({ fuel := 16384, expandTermDefinitions := false } :
            ElaboratedPropositionGraphState)
          "result" reducedValue
        pure <| Json.mkObj [
          ("schema", Json.str "1"),
          ("complete", Json.bool state.failures.isEmpty),
          ("nodes", Json.arr state.nodes),
          ("edges", Json.arr state.edges),
          ("failures", Json.arr state.failures)]
  | _ => pure Json.null

/--
For a transparent proposition definition, retain the outer telescope written
in its elaborated definition value without reducing terminal proposition
wrappers.  This is deliberately distinct from the ordinary signature
manifest: the latter unfolds proposition wrappers so the semantic/dependency
audits cannot hide binders.  A source-facing `Spec` owner instead needs the
definition-value boundary in order to distinguish its written inputs from
binders introduced only by reducing an opaque terminal proposition.

The receipt includes declaration-header binders followed by value binders.  It
therefore also covers `def Spec (x : A) : Prop := forall y, ...` without
reconstructing either binder surface from pretty-printed Lean.
-/
private def transparentValuePresentationTelescopeFor
    (info : ConstantInfo) (params : Array Name)
    (auditModules : Array Name) (reviewedModule : Option ModuleIdx)
    (memo : CanonicalExprRopeMemoRef) : MetaM Json := do
  match info with
  | .defnInfo definition =>
      forallTelescope info.type fun headerBinders terminalType => do
        if !(← isDefEq terminalType (mkSort .zero)) then
          pure Json.null
        else
          -- `forallTelescope` beta-reduces the definition's own lambda
          -- parameters but does not unfold an application in the terminal
          -- proposition.  That is exactly the presentation boundary needed
          -- here; semantic unfolding remains the ordinary manifest's job.
          -- Reduce only the definition's own beta-redexes.  In particular,
          -- this exposes a value lambda for header parameters without
          -- reducing the terminal proposition definition that follows it.
          let appliedValue ← whnf (mkAppN definition.value headerBinders)
          forallTelescope appliedValue fun valueBinders valueResult => do
            let binders := headerBinders ++ valueBinders
            let fvarIds := binders.map Expr.fvarId!
            let mut atoms : Array Json := #[]
            for h : index in [0:binders.size] do
              let localDecl ← binders[index].fvarId!.getDecl
              let domain := localDecl.type
              let role := if (← isProp domain) then "assumption" else "parameter"
              atoms := atoms.push <| Json.mkObj [
                ("ref", Json.str s!"b/{index}"),
                ("role", Json.str role),
                ("binder_info", Json.str (binderInfoName localDecl.binderInfo)),
                ("canonical", ← canonicalExprCompactWithMemo params fvarIds #[]
                  auditModules reviewedModule #[] #[] domain memo),
                ("display", Json.str (← ppSemanticReviewExpr domain))]
            let normalizedResult ← zetaResultType 128 valueResult
            atoms := atoms.push <| Json.mkObj [
              ("ref", Json.str "result"),
              ("role", Json.str "conclusion"),
              ("canonical", ← canonicalExprCompactWithMemo params fvarIds #[]
                auditModules reviewedModule #[] #[] normalizedResult memo),
              ("display", Json.str (← ppSemanticReviewExpr normalizedResult))]
            pure <| Json.mkObj [
              ("schema", Json.str "1"),
              ("reduction", Json.str "definition_value_outer_telescope"),
              ("atoms", Json.arr atoms)]
  | _ => pure Json.null

private def semanticSignatureAtomsFor
    (info : ConstantInfo) (params : Array Name) (binders : Array Expr)
    (auditModulePrefixes : Array Name) (reviewedModule : Option ModuleIdx)
    (compactMemo : CanonicalExprRopeMemoRef) (result : Expr) :
    MetaM (Array Json × Expr) := do
    let fvarIds := binders.map Expr.fvarId!
    let mut atoms : Array Json := #[]
    for h : index in [0:binders.size] do
      let localDecl ← binders[index].fvarId!.getDecl
      let domain := localDecl.type
      let role := if (← isProp domain) then "assumption" else "parameter"
      atoms := atoms.push <| Json.mkObj [
        ("ref", Json.str s!"b/{index}"),
        ("role", Json.str role),
        ("binder_info", Json.str (binderInfoName localDecl.binderInfo)),
        ("canonical", ← canonicalExprCompactWithMemo params fvarIds #[]
          auditModulePrefixes reviewedModule #[] #[] domain compactMemo),
        ("display", Json.str (← ppSemanticReviewExpr domain))]
    let normalizedResult ← zetaResultType 128 result
    let (resultCanonical, resultDisplay) ←
      conclusionAtom info params binders auditModulePrefixes reviewedModule
        compactMemo normalizedResult
    atoms := atoms.push <| Json.mkObj [
      ("ref", Json.str "result"),
      ("role", Json.str "conclusion"),
      ("canonical", resultCanonical),
      ("display", Json.str resultDisplay)]
    pure (atoms, normalizedResult)

private def manifestFor
    (declName : Name) (auditModulePrefixes : Array Name)
    (hashToolPath : String) : MetaM Json := do
  let info ← getConstInfo declName
  let params := info.levelParams.toArray
  let reviewedModule := (← getEnv).getModuleIdxFor? declName
  let compactMemo ← IO.mkRef ({ hashToolPath } : CanonicalExprRopeMemo)
  let buildManifest (binders : Array Expr) (result : Expr) : MetaM Json := do
    let (atoms, normalizedResult) ← semanticSignatureAtomsFor info params binders
      auditModulePrefixes reviewedModule compactMemo result
    let (semanticDependencyGraph, executionStateRefinementShape) ←
      semanticDependencyGraphFor declName auditModulePrefixes compactMemo
    pure <| Json.mkObj [
      ("schema", Json.str "2"),
      ("declaration_kind", Json.str (declarationKind info)),
      ("conclusion_mode", Json.str (conclusionMode info)),
      ("atoms", Json.arr atoms),
      ("elaborated_proposition_graph", ← elaboratedPropositionGraphFor
        info params binders auditModulePrefixes reviewedModule compactMemo
        normalizedResult),
      ("elaborated_transparent_result_value_graph",
        ← elaboratedTransparentResultValueGraphFor info params binders
          auditModulePrefixes reviewedModule compactMemo normalizedResult),
      ("transparent_value_presentation_telescope",
        ← transparentValuePresentationTelescopeFor info params
          auditModulePrefixes reviewedModule compactMemo),
      ("elaborated_execution_state_refinement_shape",
        executionStateRefinementShape),
      ("semantic_dependency_graph", semanticDependencyGraph)]
  -- Proposition wrappers intentionally expose quantified binders hidden behind
  -- a transparent Spec, as theorem auditing depends on those semantic inputs.
  -- Data-valued declarations keep only their nonreducing outer telescope: a
  -- reducible function-valued result's arguments belong to the returned value,
  -- not to the declaration's caller-visible input surface.
  let resultIsProposition ← forallTelescope info.type fun _ result => isProp result
  let action :=
    if resultIsProposition then
      forallTelescopeReducing info.type buildManifest
    else
      forallTelescope info.type buildManifest
  withCanonicalHashWorker compactMemo action

/--
Return the canonical, spelling-independent semantic manifest for one exact
declaration.  This is the shared native API used by the batched declaration
graph.  The command wrappers below remain only as historical and fixture
entrypoints; new closeout consumers should not launch them declaration by
declaration.
-/
def declarationSemanticManifest
    (declName : Name) (auditModules : Array Name)
    (hashToolPath : String) : MetaM Json :=
  manifestFor declName auditModules hashToolPath

/--
Return only the exact Lean-elaborated semantic target signature used by a
declaration manifest.  Terminal migration of historical reviewed-target leaves
needs this mathematical surface, not the retired manifest's dependency and
proof-realization payloads.  This calls the same signature constructor as the
full manifest, so accepted historical signature identities remain comparable.
The caller separately checks every Lean-discovered paper and library
prerequisite.
-/
def declarationSemanticTargetSignature
    (declName : Name) (auditModules : Array Name)
    (hashToolPath : String) : MetaM Json := do
  let info ← getConstInfo declName
  let params := info.levelParams.toArray
  let reviewedModule := (← getEnv).getModuleIdxFor? declName
  let compactMemo ← IO.mkRef ({ hashToolPath } : CanonicalExprRopeMemo)
  let buildSignature (binders : Array Expr) (result : Expr) : MetaM Json := do
    let (atoms, _) ← semanticSignatureAtomsFor info params binders auditModules
      reviewedModule compactMemo result
    pure <| Json.mkObj [
      ("schema", Json.str "2"),
      ("declaration_kind", Json.str (declarationKind info)),
      ("conclusion_mode", Json.str (conclusionMode info)),
      ("atoms", Json.arr atoms)]
  let resultIsProposition ← forallTelescope info.type fun _ result => isProp result
  let action :=
    if resultIsProposition then
      forallTelescopeReducing info.type buildSignature
    else
      forallTelescope info.type buildSignature
  withCanonicalHashWorker compactMemo action

/--
Return exactly the two small Lean-owned surfaces needed by a source reviewer:
the declaration's canonical outer semantic signature and the transparent
definition-value telescope that exposes binders hidden inside a proposition
wrapper.  Unlike `declarationSemanticManifest`, this does not construct the
transitive dependency graph or proposition DAG.  Those obligations are owned
by the declaration graph's recursive display/prerequisite closure, exact
semantic contract, axiom closure, and byte-pinned import closure.
-/
def declarationSemanticReviewClaim
    (declName : Name) (auditModules : Array Name)
    (hashToolPath : String) : MetaM Json := do
  let info ← getConstInfo declName
  let params := info.levelParams.toArray
  let reviewedModule := (← getEnv).getModuleIdxFor? declName
  let compactMemo ← IO.mkRef ({ hashToolPath } : CanonicalExprRopeMemo)
  let buildSignature (binders : Array Expr) (result : Expr) : MetaM Json := do
    let (atoms, _) ← semanticSignatureAtomsFor info params binders auditModules
      reviewedModule compactMemo result
    pure <| Json.mkObj [
      ("schema", Json.str "2"),
      ("declaration_kind", Json.str (declarationKind info)),
      ("conclusion_mode", Json.str (conclusionMode info)),
      ("atoms", Json.arr atoms)]
  withCanonicalHashWorker compactMemo do
    let signature ← forallTelescopeReducing info.type buildSignature
    let presentation ← transparentValuePresentationTelescopeFor info params
      auditModules reviewedModule compactMemo
    match presentation with
    | .obj _ =>
        pure <| Json.mkObj [
          ("schema", Json.str "1"),
          ("signature", signature),
          ("transparent_value_presentation_telescope", presentation)]
    | _ => throwError "semantic review claim has no transparent value telescope"

/--
Recompute the Lean-owned identities that can establish whether a persisted
manifest remains valid after an unrelated declaration changes the containing
module artifact.  This deliberately omits the large atom and proposition-DAG
payloads.  The dependency graph's root identity canonically binds the current
declaration type (and definition value), while the complete graph and execution
shape bind the transitive paper-owned semantics used to derive those payloads.
-/
private def signatureManifestRevalidationFor
    (declName : Name) (auditModulePrefixes : Array Name)
    (hashToolPath : String) : MetaM Json := do
  let info ← getConstInfo declName
  let compactMemo ← IO.mkRef ({ hashToolPath } : CanonicalExprRopeMemo)
  withCanonicalHashWorker compactMemo do
    let (semanticDependencyGraph, executionStateRefinementShape) ←
      semanticDependencyGraphFor declName auditModulePrefixes compactMemo
    pure <| Json.mkObj [
      ("schema", Json.str "1"),
      ("declaration_kind", Json.str (declarationKind info)),
      ("conclusion_mode", Json.str (conclusionMode info)),
      ("elaborated_execution_state_refinement_shape",
        executionStateRefinementShape),
      ("semantic_dependency_graph", semanticDependencyGraph)]

/-- Recompute the compact current-artifact semantic identity for one root. -/
def declarationSemanticRevalidation
    (declName : Name) (auditModules : Array Name)
    (hashToolPath : String) : MetaM Json :=
  signatureManifestRevalidationFor declName auditModules hashToolPath

private def propositionSpecProofMatches
    (specName proofName : Name) : MetaM Bool := do
  let specInfo ← getConstInfo specName
  match specInfo with
  | .defnInfo _ | .inductInfo _ => pure ()
  | _ => return false
  let .thmInfo proofInfo ← getConstInfo proofName
    | return false
  if specInfo.levelParams.length != proofInfo.levelParams.length then
    return false
  let rigidLevels := (List.range specInfo.levelParams.length).map fun index =>
    Level.param (Name.mkSimple s!"_econcs_audit_universe_{index}")
  let specConst := mkConst specName rigidLevels
  let proofConst := mkConst proofName rigidLevels
  let specType ← inferType specConst
  let proofType ← inferType proofConst
  forallTelescope specType fun outerBinders resultType => do
    unless ← isDefEq resultType (mkSort .zero) do
      return false
    let expectedBody := mkAppN specConst outerBinders
    let expectedType ← mkForallFVars outerBinders expectedBody
    withTransparency .all do
      isDefEq proofType expectedType

private def semanticContractMatches
    (specName evidenceName : Name) (refutes : Bool) : MetaM Bool := do
  let specInfo ← getConstInfo specName
  match specInfo with
  | .defnInfo _ | .inductInfo _ => pure ()
  | _ => return false
  let .thmInfo evidenceInfo ← getConstInfo evidenceName
    | return false
  if specInfo.levelParams.length != evidenceInfo.levelParams.length then
    return false
  let rigidLevels := (List.range specInfo.levelParams.length).map fun index =>
    Level.param (Name.mkSimple s!"_econcs_audit_universe_{index}")
  let specConst := mkConst specName rigidLevels
  let evidenceConst := mkConst evidenceName rigidLevels
  let specType ← inferType specConst
  let evidenceType ← inferType evidenceConst
  forallTelescope specType fun outerBinders resultType => do
    unless ← isDefEq resultType (mkSort .zero) do
      return false
    let specBody := mkAppN specConst outerBinders
    let expectedBody :=
      if refutes then mkApp (mkConst ``Not) specBody else specBody
    let expectedType ← mkForallFVars outerBinders expectedBody
    withTransparency .all do
      isDefEq evidenceType expectedType

/-- Check a source-definition realization endpoint.  A source definition is
not an asserted theorem: its endpoint must instead state an equivalence whose
two sides are definitionally equal to the independently written semantic
`Spec`.  This keeps the source meaning on the Spec card and prevents a
definition wrapper from becoming a second paper claim. -/
private def semanticContractDefinitionallyRealizes
    (specName evidenceName : Name) : MetaM Bool := do
  let specInfo ← getConstInfo specName
  match specInfo with
  | .defnInfo _ | .inductInfo _ => pure ()
  | _ => return false
  let .thmInfo evidenceInfo ← getConstInfo evidenceName
    | return false
  if specInfo.levelParams.length != evidenceInfo.levelParams.length then
    return false
  let rigidLevels := (List.range specInfo.levelParams.length).map fun index =>
    Level.param (Name.mkSimple s!"_econcs_audit_universe_{index}")
  let specConst := mkConst specName rigidLevels
  let evidenceConst := mkConst evidenceName rigidLevels
  let evidenceType ← inferType evidenceConst
  forallTelescope evidenceType fun outerBinders resultType => do
    unless resultType.isAppOfArity ``Iff 2 do
      return false
    let specBody := mkAppN specConst outerBinders
    let left := resultType.getArg! 0
    let right := resultType.getArg! 1
    withTransparency .all do
      return (← isDefEq left specBody) && (← isDefEq right specBody)

/-- Return the direct constant head of an elaborated application, if any. -/
/-
One executable recursive terminal is an occurrence in the elaborated Spec
body, not just a recursive definition name.  In particular, two calls to the
same executor can have different full applications or arise on independent
branches of the specification.  Retaining the structural path, complete
application arity, and both the inferred and reduced result types lets the
source-record receipt bind the entire set without turning a local declaration
spelling into an approval rule.
-/
private structure SemanticContractExecutableTerminal where
  declaration : Name
  occurrencePath : Array String
  applicationArity : Nat
  applicationResultType : String
  normalizedResultType : String

private structure SemanticContractTransparencyState where
  completed : Array Name := #[]
  executableRecursiveTerminals : Array SemanticContractExecutableTerminal := #[]
  fuel : Nat
  expanded : Nat := 0
  failure : Option (String × Name) := none

private def semanticContractTransparencyFailure
    (state : SemanticContractTransparencyState) (tag : String) (name : Name) :
    SemanticContractTransparencyState :=
  if state.failure.isSome then state else { state with failure := Option.some (tag, name) }

private def semanticContractTransparencyConsume
    (state : SemanticContractTransparencyState) (name : Name) :
    SemanticContractTransparencyState :=
  if state.fuel == 0 then
    semanticContractTransparencyFailure state "fuel_exhausted" name
  else
    { state with fuel := state.fuel - 1, expanded := state.expanded + 1 }

private def semanticContractTransparencyExecutableRecursiveTerminal
    (state : SemanticContractTransparencyState) (name : Name)
    (occurrencePath : Array String) (expr rawResultType normalizedResultType : Expr) :
    MetaM SemanticContractTransparencyState := do
  let (_, arguments) := expr.getAppFnArgs
  let applicationResultType := (← ppExpr rawResultType).pretty
  let normalizedResultType := (← ppExpr normalizedResultType).pretty
  pure {
    state with executableRecursiveTerminals :=
      state.executableRecursiveTerminals.push {
        declaration := name
        occurrencePath := occurrencePath
        applicationArity := arguments.size
        applicationResultType := applicationResultType
        normalizedResultType := normalizedResultType
      }
  }

private def semanticContractTransparencyOwned
    (auditModules : Array Name) (rootModule : Option ModuleIdx) (name : Name) :
    MetaM Bool := do
  let env ← getEnv
  match env.getModuleIdxFor? name with
  | some moduleIdx =>
      pure (auditModules.contains (env.header.moduleNames[moduleIdx.toNat]!))
  | none =>
      -- Inline-source test fixtures do not have a compiled module origin.  In
      -- that setting every unresolved-origin declaration is conservatively
      -- treated as local.  In compiled paper reviews, compiler-generated
      -- details remain local while ordinary unknown foundations remain outside
      -- the paper closure.
      pure (rootModule.isNone || name.isInternalDetail)

/--
Return the exact elaborated type of an erased proof term, if this application
argument is a proof.  The canonical Spec surface records local proof constants
by this proposition type, not by declaration name or proof body.  Traversing
the type still exposes every mathematical premise (including an opaque local
predicate); traversing the proof implementation would instead make statement
semantics depend on generated `_proof` declarations or on how a valid helper
lemma was decomposed.  Data-valued typeclass and witness arguments are not
proofs and remain fully traversed.
-/
private def semanticContractProofArgumentType? (arg : Expr) : MetaM (Option Expr) := do
  try
    let type ←
      match arg with
      | .fvar id => pure (← id.getDecl).type
      | .const name _ => pure (← getConstInfo name).type
      | _ => inferType arg
    if ← isProp type then pure (some type) else pure none
  catch _ =>
    -- Raw subexpressions under an unapplied lambda can contain loose de Bruijn
    -- indices. They are not independently inferable at this traversal point;
    -- retain the prior fail-closed term traversal for those cases.
    pure none

private def semanticContractPropositionType? (type : Expr) : MetaM Bool := do
  try isProp type catch _ => pure false

/--
Return whether a paper-local theorem constant is the generated projection of a
proof-valued structure field. The proposition carried by that field is already
visited in the structure constructor type. Its projection term is proof
irrelevant, so revisiting the generated theorem body would add no statement
semantics and would incorrectly make ordinary model records opaque to the
closure audit.

This classification comes from Lean's projection metadata and the elaborated
type, never from a declaration-name pattern.
-/
private def semanticContractProofProjection?
    (name : Name) (type : Expr) : MetaM Bool := do
  let some _ ← getProjectionFnInfo? name | return false
  isProp type

/--
Classify a paper-local recursive definition only at its complete application
spine. Looking at a `.const` head alone is unsound: a recursive `Nat → Prop`
wrapper can appear under an application before the walker sees the final
proposition. A fully applied data-valued recursive executor is retained as a
terminal candidate for Python's separately pinned source-model review; every
Prop, function-valued, type-valued, unresolved, or otherwise non-executable
cycle remains a transparency failure.  The declaration's recursive group is
checked directly, rather than waiting until its body re-enters itself, so the
receipt records the call occurrence in the source-facing Spec.
-/
private def semanticContractTransparencyRecursiveApplicationTerminal?
    (auditModules : Array Name) (rootModule : Option ModuleIdx)
    (activeDefinitions : Array Name) (state : SemanticContractTransparencyState)
    (occurrencePath : Array String) (expr : Expr) :
    MetaM (Option SemanticContractTransparencyState) := do
  let (name, _) := expr.getAppFnArgs
  if name.isAnonymous then
    return none
  if !(← semanticContractTransparencyOwned auditModules rootModule name) then
    return none
  let info? ← try some <$> getConstInfo name catch _ => pure none
  let some (.defnInfo definition) := info? | return none
  if !activeDefinitions.contains name && !(← isRecursiveDefinition name) then
    return none
  let resultType? ← try some <$> inferType expr catch _ => pure none
  let some rawResultType := resultType? |
    return some <| semanticContractTransparencyFailure
      state "recursive_local_definition" name
  let resultType? ← try some <$> whnf rawResultType catch _ => pure none
  let some resultType := resultType? |
    return some <| semanticContractTransparencyFailure
      state "recursive_local_definition" name
  match resultType with
  | .forallE .. | .sort _ =>
      return some <| semanticContractTransparencyFailure
        state "recursive_local_definition" name
  | _ =>
      if ← isProp resultType then
        return some <| semanticContractTransparencyFailure
          state "recursive_local_definition" name
      let terminalState ← semanticContractTransparencyExecutableRecursiveTerminal
        state name occurrencePath expr rawResultType resultType
      return some terminalState

private partial def scanSemanticContractTransparencyExpr
    (auditModules : Array Name) (rootModule : Option ModuleIdx)
    (activeDefinitions activeData : Array Name)
    (state : SemanticContractTransparencyState) (occurrencePath : Array String)
    (expr : Expr) :
    MetaM SemanticContractTransparencyState := do
  if state.failure.isSome then
    return state
  match expr with
  | .const name _ =>
      if !(← semanticContractTransparencyOwned auditModules rootModule name) then
        return state
      if activeData.contains name then
        -- Recursive data occurrences are part of the inductive primitive, not
        -- a cycle through a user-defined semantic wrapper.
        return state
      if state.completed.contains name then
        return state
      let info? ← try some <$> getConstInfo name catch _ => pure none
      let some info := info? | return (
        semanticContractTransparencyFailure state "unresolved_local_dependency" name)
      match info with
      | .opaqueInfo _ =>
          return semanticContractTransparencyFailure state "opaque_local_dependency" name
      | .axiomInfo _ =>
          return semanticContractTransparencyFailure state "axiom_local_dependency" name
      | .thmInfo _ =>
          if ← semanticContractProofProjection? name info.type then
            return { state with completed := state.completed.push name }
          return semanticContractTransparencyFailure state "theorem_local_dependency" name
      | .defnInfo _ =>
          if name.isInternalDetail then
            -- Lowered match/projection helpers are compiler detail reached only
            -- after their transparent enclosing definition has been unfolded.
            -- They cannot be user-facing opaque/certificate boundaries; those
            -- ConstantInfo kinds were rejected above.
            return { state with completed := state.completed.push name }
          if activeDefinitions.contains name then
            return semanticContractTransparencyFailure
              state "recursive_local_definition" name
          let next := semanticContractTransparencyConsume state name
          if next.failure.isSome then
            return next
          let scanned ← try
            withNewMCtxDepth do
              let constant ← mkConstWithFreshMVarLevels name
              let constantType ← inferType constant
              forallTelescopeReducing constantType fun binders _ => do
                let mut current := next
                for index in [:binders.size] do
                  let binder := binders[index]!
                  let localDecl ← binder.fvarId!.getDecl
                  current ← scanSemanticContractTransparencyExpr auditModules rootModule
                    (activeDefinitions.push name) activeData current
                    (occurrencePath.push ("definition_binder:" ++ name.toString)
                      |>.push (toString index)) localDecl.type
                if current.failure.isSome then
                  pure current
                else
                  let body ← whnf (mkAppN constant binders)
                  scanSemanticContractTransparencyExpr auditModules rootModule
                    (activeDefinitions.push name) activeData current
                    (occurrencePath.push ("definition_body:" ++ name.toString)) body
          catch _ =>
            pure <| semanticContractTransparencyFailure
              next "unresolved_local_dependency" name
          if scanned.failure.isSome then
            return scanned
          return { scanned with completed := scanned.completed.push name }
      | .inductInfo inductiveInfo =>
          let next := semanticContractTransparencyConsume state name
          if next.failure.isSome then
            return next
          -- A structure/inductive can carry source assumptions in constructor
          -- fields.  Inspect those field types transitively while allowing its
          -- ordinary recursive occurrences as data primitives.
          let mut current ← scanSemanticContractTransparencyExpr auditModules rootModule
            activeDefinitions (activeData.push name) next
            (occurrencePath.push ("inductive_type:" ++ name.toString)) inductiveInfo.type
          for index in [:inductiveInfo.ctors.length] do
            if current.failure.isSome then
              break
            let ctorName := inductiveInfo.ctors[index]!
            let ctorInfo? ← try some <$> getConstInfo ctorName catch _ => pure none
            let some ctorInfo := ctorInfo? | return (
              semanticContractTransparencyFailure current "unresolved_local_dependency" ctorName)
            current ← scanSemanticContractTransparencyExpr auditModules rootModule
              activeDefinitions (activeData.push name) current
              (occurrencePath.push ("inductive_constructor:" ++ name.toString)
                |>.push (toString index)) ctorInfo.type
          if current.failure.isSome then
            return current
          return { current with completed := current.completed.push name }
      | .ctorInfo _ | .recInfo _ | .quotInfo _ =>
          -- Constructor, recursor, and quotient primitives have no hidden
          -- paper definition body.  A local inductive's fields are inspected
          -- above when the inductive itself appears in the semantic surface.
          return { state with completed := state.completed.push name }
  | .app fn arg =>
      match ← semanticContractTransparencyRecursiveApplicationTerminal?
          auditModules rootModule activeDefinitions state occurrencePath expr with
      | some terminalState =>
          -- The terminal's full application result was Lean-classified above.
          -- Its arguments can still carry semantic premises, so walk each one
          -- with the ordinary proof/data distinction before returning.
          let (_, arguments) := expr.getAppFnArgs
          let mut current := terminalState
          for index in [:arguments.size] do
            if current.failure.isNone then
              let argument := arguments[index]!
              match ← semanticContractProofArgumentType? argument with
              | some proofType =>
                  current ← scanSemanticContractTransparencyExpr auditModules rootModule
                    activeDefinitions activeData current
                    (occurrencePath.push "terminal_proof_argument" |>.push (toString index))
                    proofType
              | none =>
                  current ← scanSemanticContractTransparencyExpr auditModules rootModule
                    activeDefinitions activeData current
                    (occurrencePath.push "terminal_data_argument" |>.push (toString index))
                    argument
          pure current
      | none =>
          let afterFn ← scanSemanticContractTransparencyExpr auditModules rootModule
            activeDefinitions activeData state (occurrencePath.push "application_function") fn
          if afterFn.failure.isSome then
            pure afterFn
          else
            match ← semanticContractProofArgumentType? arg with
            | some proofType =>
                scanSemanticContractTransparencyExpr auditModules rootModule
                  activeDefinitions activeData afterFn
                  (occurrencePath.push "application_proof_argument") proofType
            | none =>
                scanSemanticContractTransparencyExpr auditModules rootModule
                  activeDefinitions activeData afterFn
                  (occurrencePath.push "application_data_argument") arg
  | .lam _ domain body _ =>
      let afterDomain ← scanSemanticContractTransparencyExpr auditModules rootModule
        activeDefinitions activeData state (occurrencePath.push "lambda_domain") domain
      scanSemanticContractTransparencyExpr auditModules rootModule
        activeDefinitions activeData afterDomain (occurrencePath.push "lambda_body") body
  | .forallE _ domain body _ =>
      let afterDomain ← scanSemanticContractTransparencyExpr auditModules rootModule
        activeDefinitions activeData state (occurrencePath.push "forall_domain") domain
      scanSemanticContractTransparencyExpr auditModules rootModule
        activeDefinitions activeData afterDomain (occurrencePath.push "forall_body") body
  | .letE _ type value body _ =>
      let afterType ← scanSemanticContractTransparencyExpr auditModules rootModule
        activeDefinitions activeData state (occurrencePath.push "let_type") type
      let afterValue ←
        if ← semanticContractPropositionType? type then
          pure afterType
        else
          scanSemanticContractTransparencyExpr auditModules rootModule
            activeDefinitions activeData afterType (occurrencePath.push "let_value") value
      scanSemanticContractTransparencyExpr auditModules rootModule
        activeDefinitions activeData afterValue (occurrencePath.push "let_body") body
  | .mdata _ body =>
      scanSemanticContractTransparencyExpr auditModules rootModule
        activeDefinitions activeData state (occurrencePath.push "metadata") body
  | .proj _ _ body =>
      scanSemanticContractTransparencyExpr auditModules rootModule
        activeDefinitions activeData state (occurrencePath.push "projection") body
  | _ => pure state

private def parseSemanticContractTransparencyScope
    (raw : String) : Option (Array Name) :=
  match Json.parse raw with
  | .ok (.arr values) =>
      values.foldl
        (fun collected? value =>
          match collected?, value.getStr? with
          | some collected, .ok moduleName =>
              if moduleName.isEmpty then none else some (collected.push moduleName.toName)
          | _, _ => none)
        (some #[])
  | _ => none

private def semanticContractTransparency
    (specName : Name) (auditModules : Array Name) (fuel : Nat) : MetaM SemanticContractTransparencyState := do
  let env ← getEnv
  let rootModule := env.getModuleIdxFor? specName
  let invalidScope :=
    match rootModule with
    | some moduleIdx => !auditModules.contains (env.header.moduleNames[moduleIdx.toNat]!)
    | none => false
  if fuel == 0 || invalidScope then
    return semanticContractTransparencyFailure
      { fuel := fuel } "invalid_transparency_scope" specName
  let info? ← try some <$> getConstInfo specName catch _ => pure none
  let some info := info? | return (
    semanticContractTransparencyFailure { fuel := fuel }
      "unresolved_local_dependency" specName)
  match info with
  | .defnInfo _ => pure ()
  | _ =>
      return semanticContractTransparencyFailure
        { fuel := fuel } "specification_not_transparent_definition" specName
  withNewMCtxDepth do
    let spec ← mkConstWithFreshMVarLevels specName
    let specType ← inferType spec
    forallTelescopeReducing specType fun binders result => do
      let resultIsProp ← isDefEq result (mkSort .zero)
      if !resultIsProp then
        return semanticContractTransparencyFailure
          { fuel := fuel } "specification_not_proposition" specName
      let mut state : SemanticContractTransparencyState := { fuel := fuel }
      for index in [:binders.size] do
        let binder := binders[index]!
        let localDecl ← binder.fvarId!.getDecl
        state ← scanSemanticContractTransparencyExpr auditModules rootModule
          #[specName] #[] state
          #["spec_binder", toString index, "type"] localDecl.type
      if state.failure.isSome then
        return state
      let body ← whnf (mkAppN spec binders)
      scanSemanticContractTransparencyExpr auditModules rootModule
        #[specName] #[] state #["spec_body"] body

/--
The transparency verdict above is intentionally small because older audit
callers consume only a pass/fail receipt.  The closure manifest below is the
corresponding evidence-bearing interface: it records the elaborated `Spec`
surface and every declaration node reached while following it.  In
particular, module ownership is determined from Lean's environment, not from
declaration or binder spelling.

`foundationModules` is a registry of package *module roots* supplied by the
Python wrapper from the reviewed toolchain context.  A declaration loaded
from the current workspace but outside `paperModules` is never a foundation
terminal.  An imported module outside the registered foundation roots is also
left visible and fails closed rather than receiving accidental trust.
-/
private structure SemanticContractClosureScope where
  paperModules : Array Name
  workspaceModules : Array Name
  foundationModules : Array Name
  foreignModelDefinitions : Array Name
  foreignModelModules : Array Name
  hashToolPath : String
  inlinePaperScope : Bool := false

private inductive SemanticContractClosureOrigin where
  | paper
  | workspace
  | foundation
  | foreignModelDefinition
  | external
  | unresolved

private def semanticContractClosureOriginName :
    SemanticContractClosureOrigin → String
  | .paper => "paper"
  | .workspace => "workspace"
  | .foundation => "foundation"
  | .foreignModelDefinition => "foreign_model_definition"
  | .external => "external"
  | .unresolved => "unresolved"

private def semanticContractClosureOrigin
    (scope : SemanticContractClosureScope) (rootModule : Option ModuleIdx)
    (name : Name) : MetaM (SemanticContractClosureOrigin × String) := do
  let env ← getEnv
  match env.getModuleIdxFor? name with
  | some moduleIdx =>
      let moduleName := env.header.moduleNames[moduleIdx.toNat]!
      let moduleOrigin := moduleName.toString
      if scope.paperModules.contains moduleName then
        pure (.paper, moduleOrigin)
      else if let some foundationRoot :=
          scope.foundationModules.find? (fun root => root.isPrefixOf moduleName) then
        -- A package root is the auditable foundation identity here.  Recording
        -- every transitive Mathlib/Batteries leaf would add thousands of
        -- duplicate module pins without changing the Lean-owned reachability
        -- result; library declarations have their own semantic-review lane.
        pure (.foundation, foundationRoot.toString)
      else if scope.foreignModelDefinitions.contains name &&
          scope.foreignModelModules.contains moduleName then
        pure (.foreignModelDefinition, moduleOrigin)
      else if scope.workspaceModules.contains moduleName then
        pure (.workspace, moduleOrigin)
      else
        pure (.external, moduleOrigin)
  | none =>
      -- Inline source is an explicit test-only paper scope supplied by the
      -- wrapper.  A missing module origin in a compiled review remains an
      -- unresolved dependency, except for compiler-internal details reached
      -- after a transparent paper definition has already been expanded.
      if scope.inlinePaperScope && rootModule.isNone then
        pure (.paper, "<inline>")
      else if name.isInternalDetail then
        pure (.paper, "<internal>")
      else
        pure (.unresolved, "")

private structure SemanticContractClosureState where
  completed : Array Name := #[]
  fuel : Nat
  expanded : Nat := 0
  failures : Array (String × Name) := #[]
  reachedModules : Array (String × String) := #[]
  retainDiagnosticNodes : Bool := false
  nodes : Array Json := #[]

private def semanticContractClosureFailure
    (state : SemanticContractClosureState) (tag : String) (name : Name) :
    SemanticContractClosureState :=
  if state.failures.any (fun failure => failure.1 == tag && failure.2 == name) then
    state
  else
    { state with failures := state.failures.push (tag, name) }

private def semanticContractClosureConsume
    (state : SemanticContractClosureState) (name : Name) :
    SemanticContractClosureState :=
  if state.fuel == 0 then
    semanticContractClosureFailure state "fuel_exhausted" name
  else
    { state with fuel := state.fuel - 1, expanded := state.expanded + 1 }

private def semanticContractClosureIdentity (info? : Option ConstantInfo) : Json :=
  match info? with
  | none => obj "unknown_declaration" []
  | some info =>
      let typeHash := Json.str (toString info.type.hash)
      match info with
      | .defnInfo definition =>
          obj "definition" [
            ("declaration_kind", Json.str (declarationKind info)),
            ("declaration_type_hash", typeHash),
            ("declaration_value_hash", Json.str (toString definition.value.hash))]
      | _ =>
          obj "declaration" [
            ("declaration_kind", Json.str (declarationKind info)),
            ("declaration_type_hash", typeHash)]

private def semanticContractClosureRecordNode
    (state : SemanticContractClosureState) (path nodeRole : String)
    (origin : SemanticContractClosureOrigin) (moduleOrigin : String)
    (name : Name) (info? : Option ConstantInfo) : SemanticContractClosureState :=
  let originName := semanticContractClosureOriginName origin
  let key := (originName, moduleOrigin)
  let reachedModules :=
    if moduleOrigin.isEmpty || moduleOrigin == "<inline>" ||
        moduleOrigin == "<internal>" || state.reachedModules.contains key then
      state.reachedModules
    else
      state.reachedModules.push key
  let reached := { state with reachedModules }
  -- Production keeps the full Lean traversal but materializes only terminal
  -- dependencies that can require a source disposition. Paper/foundation
  -- identities are represented by the canonical surface plus exact reached
  -- module pins, so computing thousands of raw Expr-hash diagnostic rows
  -- would add no semantic evidence. Inline fixtures retain the full graph for
  -- focused walker diagnostics.
  let retainTerminal :=
    match origin with
    | .workspace | .foreignModelDefinition | .external | .unresolved => true
    | _ => false
  if state.retainDiagnosticNodes || retainTerminal then
    { reached with nodes := reached.nodes.push <| Json.mkObj [
        ("structural_path", Json.str path),
        ("node_role", Json.str nodeRole),
        ("origin_class", Json.str originName),
        ("module_origin", Json.str moduleOrigin),
        -- Names are diagnostic coordinates; acceptance is structural.
        ("declaration", Json.str name.toString),
        ("canonical_identity", semanticContractClosureIdentity info?)] }
  else
    reached

private def closurePath (base suffix : String) : String :=
  if base.isEmpty then suffix else base ++ "/" ++ suffix

private partial def scanSemanticContractClosureExpr
    (scope : SemanticContractClosureScope) (rootModule : Option ModuleIdx)
    (activeDefinitions activeData : Array Name)
    (state : SemanticContractClosureState) (path : String) (expr : Expr) :
    MetaM SemanticContractClosureState := do
  match expr with
  | .const name _ =>
      let (origin, moduleOrigin) ←
        semanticContractClosureOrigin scope rootModule name
      let info? ← try some <$> getConstInfo name catch _ => pure none
      match origin with
      | .foundation =>
          pure <| semanticContractClosureRecordNode state path "terminal"
            origin moduleOrigin name info?
      | .foreignModelDefinition =>
          match info? with
          | some (.defnInfo _) =>
              pure <| semanticContractClosureRecordNode state path "terminal"
                origin moduleOrigin name info?
          | _ =>
              let next := semanticContractClosureRecordNode state path "terminal"
                origin moduleOrigin name info?
              pure <| semanticContractClosureFailure
                next "foreign_model_dependency_not_definition" name
      | .workspace =>
          let next := semanticContractClosureRecordNode state path "terminal"
            origin moduleOrigin name info?
          pure <| semanticContractClosureFailure
            next "unregistered_workspace_dependency" name
      | .external =>
          let next := semanticContractClosureRecordNode state path "terminal"
            origin moduleOrigin name info?
          pure <| semanticContractClosureFailure
            next "unregistered_imported_dependency" name
      | .unresolved =>
          let next := semanticContractClosureRecordNode state path "terminal"
            origin moduleOrigin name info?
          pure <| semanticContractClosureFailure
            next "unresolved_dependency_origin" name
      | .paper =>
          if activeData.contains name then
            pure <| semanticContractClosureRecordNode state path
              "recursive_data_terminal" origin moduleOrigin name info?
          else if state.completed.contains name then
            pure <| semanticContractClosureRecordNode state path
              "expanded_reference" origin moduleOrigin name info?
          else
            let some info := info? | return (
              semanticContractClosureFailure
                (semanticContractClosureRecordNode state path "terminal"
                  origin moduleOrigin name none)
                "unresolved_local_dependency" name)
            match info with
            | .opaqueInfo _ =>
                let next := semanticContractClosureRecordNode state path "terminal"
                  origin moduleOrigin name (some info)
                pure <| semanticContractClosureFailure
                  next "opaque_local_dependency" name
            | .axiomInfo _ =>
                let next := semanticContractClosureRecordNode state path "terminal"
                  origin moduleOrigin name (some info)
                pure <| semanticContractClosureFailure
                  next "axiom_local_dependency" name
            | .thmInfo _ =>
                if ← semanticContractProofProjection? name info.type then
                  pure <| semanticContractClosureRecordNode
                    { state with completed := state.completed.push name }
                    path "proof_projection" origin moduleOrigin name (some info)
                else
                  let next := semanticContractClosureRecordNode state path "terminal"
                    origin moduleOrigin name (some info)
                  pure <| semanticContractClosureFailure
                    next "theorem_local_dependency" name
            | .defnInfo definition =>
                if activeDefinitions.contains name then
                  let next := semanticContractClosureRecordNode state path "terminal"
                    origin moduleOrigin name (some info)
                  pure <| semanticContractClosureFailure
                    next "recursive_local_definition" name
                else
                  if state.fuel == 0 then
                    let next := semanticContractClosureConsume state name
                    pure <| semanticContractClosureRecordNode next path "expansion"
                      origin moduleOrigin name (some info)
                  else
                    let next := semanticContractClosureConsume state name
                    let recorded := semanticContractClosureRecordNode next path "expansion"
                      origin moduleOrigin name (some info)
                    let scanned ← try
                      withNewMCtxDepth do
                        let constant ← mkConstWithFreshMVarLevels name
                        let constantType ← inferType constant
                        forallTelescopeReducing constantType fun binders _ => do
                          let mut current := recorded
                          for index in [0:binders.size] do
                            let localDecl ← binders[index]!.fvarId!.getDecl
                            current ← scanSemanticContractClosureExpr scope rootModule
                              (activeDefinitions.push name) activeData current
                              (closurePath path s!"definition_binder/{index}") localDecl.type
                          -- Do not `whnf` here: head reduction can unfold a
                          -- chain of paper-local wrappers before each node is
                          -- recorded and charged against the closure budget.
                          let body := mkAppN definition.value binders
                          scanSemanticContractClosureExpr scope rootModule
                            (activeDefinitions.push name) activeData current
                            (closurePath path "definition_body") body
                    catch _ =>
                      pure <| semanticContractClosureFailure
                        recorded "unresolved_local_dependency" name
                    pure { scanned with completed := scanned.completed.push name }
            | .inductInfo inductiveInfo =>
                if state.fuel == 0 then
                  let next := semanticContractClosureConsume state name
                  pure <| semanticContractClosureRecordNode next path "inductive_expansion"
                    origin moduleOrigin name (some info)
                else
                  let next := semanticContractClosureConsume state name
                  let recorded := semanticContractClosureRecordNode next path "inductive_expansion"
                    origin moduleOrigin name (some info)
                  let mut current ← scanSemanticContractClosureExpr scope rootModule
                    activeDefinitions (activeData.push name) recorded
                    (closurePath path "inductive_type") inductiveInfo.type
                  let mut index := 0
                  for ctorName in inductiveInfo.ctors do
                    let ctorInfo? ← try some <$> getConstInfo ctorName catch _ => pure none
                    let some ctorInfo := ctorInfo? | return (
                      semanticContractClosureFailure current
                        "unresolved_local_dependency" ctorName)
                    current ← scanSemanticContractClosureExpr scope rootModule
                      activeDefinitions (activeData.push name) current
                      (closurePath path s!"constructor/{index}") ctorInfo.type
                    index := index + 1
                  pure { current with completed := current.completed.push name }
            | .ctorInfo ctor =>
                let recorded := semanticContractClosureRecordNode state path
                  "constructor_terminal" origin moduleOrigin name (some info)
                scanSemanticContractClosureExpr scope rootModule activeDefinitions
                  (activeData.push ctor.induct) recorded
                  (closurePath path "constructor_type") info.type
            | .recInfo _ | .quotInfo _ =>
                pure <| semanticContractClosureRecordNode state path "derived_terminal"
                  origin moduleOrigin name (some info)
  | .app fn arg =>
      let afterFn ← scanSemanticContractClosureExpr scope rootModule
        activeDefinitions activeData state (closurePath path "fn") fn
      match ← semanticContractProofArgumentType? arg with
      | some proofType =>
          scanSemanticContractClosureExpr scope rootModule activeDefinitions activeData
            afterFn (closurePath path "arg_type") proofType
      | none =>
          scanSemanticContractClosureExpr scope rootModule activeDefinitions activeData
            afterFn (closurePath path "arg") arg
  | .lam _ domain body _ =>
      let afterDomain ← scanSemanticContractClosureExpr scope rootModule
        activeDefinitions activeData state (closurePath path "domain") domain
      scanSemanticContractClosureExpr scope rootModule activeDefinitions activeData
        afterDomain (closurePath path "body") body
  | .forallE _ domain body _ =>
      let afterDomain ← scanSemanticContractClosureExpr scope rootModule
        activeDefinitions activeData state (closurePath path "domain") domain
      scanSemanticContractClosureExpr scope rootModule activeDefinitions activeData
        afterDomain (closurePath path "body") body
  | .letE _ type value body _ =>
      let afterType ← scanSemanticContractClosureExpr scope rootModule
        activeDefinitions activeData state (closurePath path "type") type
      let afterValue ←
        if ← semanticContractPropositionType? type then
          pure afterType
        else
          scanSemanticContractClosureExpr scope rootModule activeDefinitions activeData
            afterType (closurePath path "value") value
      scanSemanticContractClosureExpr scope rootModule activeDefinitions activeData
        afterValue (closurePath path "body") body
  | .mdata _ body =>
      scanSemanticContractClosureExpr scope rootModule activeDefinitions activeData
        state path body
  | .proj _ _ body =>
      scanSemanticContractClosureExpr scope rootModule activeDefinitions activeData
        state (closurePath path "projection") body
  | _ => pure state

private def parseSemanticContractClosureNames (value : Json) : Option (Array Name) :=
  match value with
  | .arr values =>
      values.foldl
        (fun collected? item =>
          match collected?, item.getStr? with
          | some collected, .ok moduleName =>
              if moduleName.isEmpty then none else some (collected.push moduleName.toName)
          | _, _ => none)
        (some #[])
  | _ => none

private def parseSemanticContractClosureScope
    (raw : String) : Option SemanticContractClosureScope := do
  let value ← (Json.parse raw).toOption
  let paperRaw ← (value.getObjVal? "paper_modules").toOption
  let workspaceRaw ← (value.getObjVal? "workspace_modules").toOption
  let foundationRaw ← (value.getObjVal? "foundation_modules").toOption
  let foreignDefinitionsRaw ← (value.getObjVal? "foreign_model_definitions").toOption
  let foreignModulesRaw ← (value.getObjVal? "foreign_model_modules").toOption
  let hashToolRaw ← (value.getObjVal? "hash_tool_path").toOption
  let paperModules ← parseSemanticContractClosureNames paperRaw
  let workspaceModules ← parseSemanticContractClosureNames workspaceRaw
  let foundationModules ← parseSemanticContractClosureNames foundationRaw
  let foreignModelDefinitions ← parseSemanticContractClosureNames foreignDefinitionsRaw
  let foreignModelModules ← parseSemanticContractClosureNames foreignModulesRaw
  let hashToolPath ← hashToolRaw.getStr?.toOption
  guard !hashToolPath.isEmpty
  let inlinePaperScope :=
    ((value.getObjVal? "inline_paper_scope").toOption.bind fun inlineRaw =>
      inlineRaw.getBool?.toOption).getD false
  pure {
    paperModules, workspaceModules, foundationModules, foreignModelDefinitions,
    foreignModelModules, hashToolPath,
    inlinePaperScope }

private def semanticContractClosureState
    (specName : Name) (scope : SemanticContractClosureScope) (fuel : Nat) :
    MetaM SemanticContractClosureState := do
  let env ← getEnv
  let rootModule := env.getModuleIdxFor? specName
  let initial : SemanticContractClosureState := {
    fuel := fuel, retainDiagnosticNodes := scope.inlinePaperScope }
  if fuel == 0 then
    return semanticContractClosureFailure initial "invalid_closure_scope" specName
  match rootModule with
  | some moduleIdx =>
      unless scope.paperModules.contains (env.header.moduleNames[moduleIdx.toNat]!) do
        return semanticContractClosureFailure initial "invalid_closure_scope" specName
  | none =>
      unless scope.inlinePaperScope do
        return semanticContractClosureFailure initial "unresolved_dependency_origin" specName
  let info? ← try some <$> getConstInfo specName catch _ => pure none
  let some info := info? | return (
    semanticContractClosureFailure initial "unresolved_local_dependency" specName)
  match info with
  | .defnInfo definition =>
      withNewMCtxDepth do
        forallTelescopeReducing info.type fun binders result => do
          let resultIsProp ← isDefEq result (mkSort .zero)
          if !resultIsProp then
            return semanticContractClosureFailure initial
              "specification_not_proposition" specName
          let mut state := initial
          for index in [0:binders.size] do
            let localDecl ← binders[index]!.fvarId!.getDecl
            state ← scanSemanticContractClosureExpr scope rootModule #[specName] #[] state
              s!"binder/{index}" localDecl.type
          -- Preserve nested paper-local applications for the closure walker;
          -- reducing this head first would hide intermediate wrappers from
          -- both the node manifest and the bounded-expansion receipt.
          let body := mkAppN definition.value binders
          scanSemanticContractClosureExpr scope rootModule #[specName] #[] state "body" body
  | _ =>
      pure <| semanticContractClosureFailure initial
        "specification_not_transparent_definition" specName

/--
Return a bounded, name-free receipt for one elaborated expression. Transparent
paper dependencies are represented by the digest of their recursively compact
canonical identity, so a shared declaration is hashed once rather than copied
at every occurrence. This is the Lean-side form of the manifest protocol's
existing `_compact_canonical` operation; declaration names are memo coordinates
only and never enter a paper-local semantic digest.
-/
private def semanticContractClosureExprFingerprint
    (params : Array Name) (fvarIds : Array FVarId)
    (auditModules : Array Name) (reviewedModule : Option ModuleIdx)
    (memo : CanonicalExprRopeMemoRef)
    (expr : Expr) : MetaM Json := do
  let compact ← canonicalExprCompactWithMemo params fvarIds #[] auditModules
    reviewedModule #[] #[] expr memo
  let encoded := compact.compress
  let digest ← canonicalDigestWithMemo memo encoded
  pure <| obj "expr_fingerprint" [
    ("canonical_sha256", Json.str digest),
    ("canonical_bytes", Json.str (toString encoded.toUTF8.size))]

/--
Canonical Spec closure surface. This retains binder order/kind and independent
fingerprints of the elaborated declaration type, value, binder domains, and
reduced proposition body without emitting a recursively expanded JSON tree.
-/
private def semanticContractClosureFingerprintSurfaceWithScope
    (specName : Name) (auditModules : Array Name)
    (reviewedModule : Option ModuleIdx) (hashToolPath : String) :
    MetaM (Option Json) := do
  let surface? ← try
    withNewMCtxDepth do
      let info ← getConstInfo specName
      let .defnInfo definition := info | throwError "Spec is not a definition"
      let params := info.levelParams.toArray
      let compactMemo ← IO.mkRef ({ hashToolPath } : CanonicalExprRopeMemo)
      withCanonicalHashWorker compactMemo do
        forallTelescopeReducing info.type fun binders result => do
          unless ← isDefEq result (mkSort .zero) do
            throwError "Spec is not proposition-valued"
          let fvarIds := binders.map Expr.fvarId!
          let mut binderDomains : Array Json := #[]
          for index in [0:binders.size] do
            let localDecl ← binders[index]!.fvarId!.getDecl
            binderDomains := binderDomains.push <| Json.mkObj [
              ("index", Json.str (toString index)),
              ("binder_info", Json.str (binderInfoName localDecl.binderInfo)),
              ("domain_is_proposition", Json.bool (← isProp localDecl.type)),
              ("fingerprint", ← semanticContractClosureExprFingerprint
                params fvarIds auditModules reviewedModule compactMemo
                localDecl.type)]
          let body ← whnf (mkAppN definition.value binders)
          pure <| some <| obj "spec_surface_fingerprints" [
            ("schema", Json.str "3"),
            ("binder_domains", Json.arr binderDomains),
            ("body_fingerprint", ← semanticContractClosureExprFingerprint
              params fvarIds auditModules reviewedModule compactMemo body)]
  catch _ => pure none
  pure surface?

private def semanticContractClosureFingerprintSurface
    (specName : Name) (scope : SemanticContractClosureScope) :
    MetaM (String × Option Json) := do
  let rootModule := (← getEnv).getModuleIdxFor? specName
  let surface ← semanticContractClosureFingerprintSurfaceWithScope
    specName scope.paperModules rootModule scope.hashToolPath
  match surface with
  | some surface =>
      pure ("closure_fingerprints", some surface)
  | none =>
      -- A rejected closure still receives a bounded diagnostic identity. With
      -- no paper module authorized for expansion, an opaque or otherwise
      -- blocked local declaration remains a named terminal rather than being
      -- reopened. Passing receipts always use the name-free compact surface.
      let fallbackModule := (← getEnv).getModuleIdxFor? ``Nat
      let fallback ← semanticContractClosureFingerprintSurfaceWithScope
        specName #[] fallbackModule scope.hashToolPath
      pure ("terminal_fingerprints", fallback)

/-!
Production source-to-Spec correspondence needs Lean to identify the recursive
*statement* dependency closure, not to materialize every recursively expanded
expression or walk the proof body of an imported theorem. The latter duplicated
the semantic display already produced for human review and could retain
gigabytes for a large imported paper interface. Lean's elaborated-expression
utility `Expr.getUsedConstantsAsSet`, together with Lean environment module
origins, supplies every direct edge; this helper performs the recursive walk
inside Lean, excludes only theorem proof-body edges, and handles cycles.

The compact surface below fingerprints the exact elaborated declaration type
and value.  The separate raw-source screen remains responsible for the
human-readable fully expanded proposition; its current digest is checked
before a correspondence record can be issued.  Thus this compact route does
not replace semantic review with a declaration name or a paraphrase.
-/
private def semanticContractClosureLeanUtilityState
    (specName : Name) (scope : SemanticContractClosureScope) (fuel : Nat) :
    MetaM SemanticContractClosureState := do
  let env ← getEnv
  let rootModule := env.getModuleIdxFor? specName
  let initial : SemanticContractClosureState := { fuel := fuel }
  match rootModule with
  | some moduleIdx =>
      unless scope.paperModules.contains (env.header.moduleNames[moduleIdx.toNat]!) do
        return semanticContractClosureFailure initial "invalid_closure_scope" specName
  | none =>
      return semanticContractClosureFailure initial "unresolved_dependency_origin" specName
  let info? ← try some <$> getConstInfo specName catch _ => pure none
  let some info := info? | return (
    semanticContractClosureFailure initial "unresolved_local_dependency" specName)
  let .defnInfo _ := info | return (
    semanticContractClosureFailure initial "specification_not_transparent_definition" specName)
  let isProp ← withNewMCtxDepth do
    forallTelescopeReducing info.type fun _ result =>
      isDefEq result (mkSort .zero)
  unless isProp do
    return semanticContractClosureFailure initial "specification_not_proposition" specName
  -- This is the recursive statement graph walk. Python receives only the
  -- compact, Lean-classified result and never reconstructs membership. A
  -- source `Spec` is a proposition, so a theorem's proof implementation is
  -- not source semantics and must not pull its full proof dependency cone
  -- into the source-to-Spec receipt.
  let statementClosure ←
    statementDependencyClosureFor specName scope.paperModules rootModule
  let names := statementClosure.names
  let mut state := initial
  for failedName in statementClosure.scanFailures do
    state := semanticContractClosureFailure
      state "statement_dependency_scan_failed" failedName
  let mut paperModules : Array String := #[]
  let mut foundationModules : Array String := #[]
  let mut foreignModelModules : Array String := #[]
  -- Do not materialize one receipt node per traversed declaration. Lean has
  -- still visited every statement dependency in `names`; the compact receipt retains
  -- each reached paper module (byte-pinned by Python) and each approved
  -- foundation package root.  This is a serialization reduction, not a
  -- shallower graph walk.
  for name in names do
    let (origin, moduleOrigin) ← semanticContractClosureOrigin scope rootModule name
    match origin with
    | .paper =>
        if !paperModules.contains moduleOrigin then
          paperModules := paperModules.push moduleOrigin
    | .foundation =>
        if !foundationModules.contains moduleOrigin then
          foundationModules := foundationModules.push moduleOrigin
    | .foreignModelDefinition =>
        let currentInfo? ← try some <$> getConstInfo name catch _ => pure none
        match currentInfo? with
        | some (.defnInfo _) =>
            let recorded := semanticContractClosureRecordNode state
              "lean_statement_dependency/foreign_model_definition"
              "lean_statement_terminal" origin moduleOrigin name currentInfo?
            state := recorded
            if !foreignModelModules.contains moduleOrigin then
              foreignModelModules := foreignModelModules.push moduleOrigin
        | _ =>
            let recorded := semanticContractClosureRecordNode state
              "lean_statement_dependency/foreign_model_definition"
              "lean_statement_terminal" origin moduleOrigin name currentInfo?
            state := semanticContractClosureFailure
              recorded "foreign_model_dependency_not_definition" name
    | .workspace =>
        let currentInfo? ← try some <$> getConstInfo name catch _ => pure none
        let recorded := semanticContractClosureRecordNode state
          "lean_statement_dependency/workspace" "lean_statement_terminal"
          origin moduleOrigin name currentInfo?
        state := semanticContractClosureFailure
          recorded "unregistered_workspace_dependency" name
    | .external =>
        let currentInfo? ← try some <$> getConstInfo name catch _ => pure none
        let recorded := semanticContractClosureRecordNode state
          "lean_statement_dependency/external" "lean_statement_terminal"
          origin moduleOrigin name currentInfo?
        state := semanticContractClosureFailure
          recorded "unregistered_imported_dependency" name
    | .unresolved =>
        let currentInfo? ← try some <$> getConstInfo name catch _ => pure none
        let recorded := semanticContractClosureRecordNode state
          "lean_statement_dependency/unresolved" "lean_statement_terminal"
          origin moduleOrigin name currentInfo?
        state := semanticContractClosureFailure
          recorded "unresolved_dependency_origin" name
  let sortedPaperModules := paperModules.qsort (· < ·)
  let sortedFoundationModules := foundationModules.qsort (· < ·)
  let sortedForeignModelModules := foreignModelModules.qsort (· < ·)
  if sortedPaperModules.size > state.fuel then
    state := semanticContractClosureFailure state "fuel_exhausted" specName
  else
    state := {
      state with
      fuel := state.fuel - sortedPaperModules.size
      expanded := state.expanded + sortedPaperModules.size }
  for moduleOrigin in sortedPaperModules do
    state := { state with reachedModules := state.reachedModules.push (
      semanticContractClosureOriginName .paper, moduleOrigin) }
  for moduleOrigin in sortedFoundationModules do
    state := { state with reachedModules := state.reachedModules.push (
      semanticContractClosureOriginName .foundation, moduleOrigin) }
  for moduleOrigin in sortedForeignModelModules do
    let entry := (semanticContractClosureOriginName .foreignModelDefinition, moduleOrigin)
    if !state.reachedModules.contains entry then
      state := { state with reachedModules := state.reachedModules.push entry }
  pure state

private def semanticContractClosureLeanUtilityManifest
    (specName : Name) (scope : SemanticContractClosureScope) (fuel : Nat) :
    MetaM Json := do
  let state ← semanticContractClosureLeanUtilityState specName scope fuel
  let (surfaceMode, surface) ←
    semanticContractClosureFingerprintSurface specName scope
  let state :=
    if surface.isSome then state
    else semanticContractClosureFailure state "specification_surface_unavailable" specName
  let failures := state.failures.map fun failure => Json.mkObj [
    ("tag", Json.str failure.1),
    ("declaration", Json.str failure.2.toString)]
  pure <| Json.mkObj [
    ("schema", Json.str "1"),
    ("spec", Json.str specName.toString),
    ("passes", Json.bool state.failures.isEmpty),
    ("expanded", Json.str (toString state.expanded)),
    ("surface_mode", Json.str surfaceMode),
    ("surface", surface.getD Json.null),
    ("nodes", Json.arr state.nodes),
    ("reached_modules", Json.arr (state.reachedModules.map fun entry => Json.mkObj [
      ("origin_class", Json.str entry.1),
      ("module_origin", Json.str entry.2)])),
    ("failures", Json.arr failures),
    ("scope", Json.mkObj [
      ("paper_modules", Json.arr (scope.paperModules.map fun name => Json.str name.toString)),
      ("workspace_modules", Json.arr (scope.workspaceModules.map fun name => Json.str name.toString)),
      ("foundation_modules", Json.arr (scope.foundationModules.map fun name => Json.str name.toString)),
      ("foreign_model_definitions", Json.arr
        (scope.foreignModelDefinitions.map fun name => Json.str name.toString)),
      ("foreign_model_modules", Json.arr
        (scope.foreignModelModules.map fun name => Json.str name.toString)),
      ("hash_tool_path", Json.str scope.hashToolPath),
      ("inline_paper_scope", Json.bool scope.inlinePaperScope)])]

private def semanticContractClosureManifest
    (specName : Name) (scope : SemanticContractClosureScope) (fuel : Nat) :
    MetaM Json := do
  if !scope.inlinePaperScope then
    return ← semanticContractClosureLeanUtilityManifest specName scope fuel
  let knownVector ← canonicalDigest scope.hashToolPath "abc"
  unless knownVector ==
      "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" do
    throwError "semantic-contract SHA-256 tool failed its known vector"
  let state ← semanticContractClosureState specName scope fuel
  let (surfaceMode, surface) ←
    semanticContractClosureFingerprintSurface specName scope
  let failures := state.failures.map fun failure => Json.mkObj [
    ("tag", Json.str failure.1),
    ("declaration", Json.str failure.2.toString)]
  pure <| Json.mkObj [
    ("schema", Json.str "1"),
    ("spec", Json.str specName.toString),
    ("passes", Json.bool state.failures.isEmpty),
    ("expanded", Json.str (toString state.expanded)),
    ("surface_mode", Json.str surfaceMode),
    ("surface", surface.getD Json.null),
    ("nodes", Json.arr state.nodes),
    ("reached_modules", Json.arr (state.reachedModules.map fun entry => Json.mkObj [
      ("origin_class", Json.str entry.1),
      ("module_origin", Json.str entry.2)])),
    ("failures", Json.arr failures),
    ("scope", Json.mkObj [
      ("paper_modules", Json.arr (scope.paperModules.map fun name => Json.str name.toString)),
      ("workspace_modules", Json.arr (scope.workspaceModules.map fun name => Json.str name.toString)),
      ("foundation_modules", Json.arr (scope.foundationModules.map fun name => Json.str name.toString)),
      ("foreign_model_definitions", Json.arr
        (scope.foreignModelDefinitions.map fun name => Json.str name.toString)),
      ("foreign_model_modules", Json.arr
        (scope.foreignModelModules.map fun name => Json.str name.toString)),
      ("hash_tool_path", Json.str scope.hashToolPath),
      ("inline_paper_scope", Json.bool scope.inlinePaperScope)])]

/--
Return whether a candidate declaration can eliminate an instance of the
reviewed source-input type.  This comparison is deliberately made on Lean's
elaborated types, with reducible aliases unfolded by definitional equality;
neither declaration nor binder spelling participates in the decision.

An additional proposition-valued candidate binder is a required proof premise,
not harmless setup, so it rejects the route.  Extra non-proposition binders are
reported instead of silently treated as source-type parameters: a caller can
then distinguish a direct contradiction from a theorem that also needs data
not supplied by the reviewed input.
-/
private def sourcePremiseFalseEliminator
    (reviewedName candidateName : Name) : MetaM (Option Json) :=
  withNewMCtxDepth do
    let reviewedConst ← mkConstWithFreshMVarLevels reviewedName
    let reviewedType ← inferType reviewedConst
    let (reviewedArgs, _, _) ← forallMetaTelescopeReducing reviewedType
    let reviewedInput := mkAppN reviewedConst reviewedArgs

    let candidateConst ← mkConstWithFreshMVarLevels candidateName
    let candidateType ← inferType candidateConst
    let (candidateArgs, _, candidateResult) ←
      forallMetaTelescopeReducing candidateType
    let candidateIsFalse ← withTransparency .all do
      isDefEq candidateResult (mkConst ``False)
    unless candidateIsFalse do
      return none

    let mut matchedIndex? : Option Nat := none
    for index in [0:candidateArgs.size] do
      let candidateDomain ← inferType candidateArgs[index]!
      let doesMatch ← withTransparency .all do
        isDefEq candidateDomain reviewedInput
      if doesMatch && matchedIndex?.isNone then
        matchedIndex? := some index
    let some matchedIndex := matchedIndex? | return none

    let mut extraProofIndices : Array Json := #[]
    let mut extraDataIndices : Array Json := #[]
    let instantiatedReviewedArgs ← reviewedArgs.mapM instantiateMVars
    for index in [0:candidateArgs.size] do
      if index != matchedIndex then
        let candidateDomain ← inferType candidateArgs[index]!
        if ← isProp candidateDomain then
          extraProofIndices := extraProofIndices.push <|
            Json.str (toString index)
        else
          let candidateArgument ← instantiateMVars candidateArgs[index]!
          let candidateArgumentIsReviewedParameter :=
            instantiatedReviewedArgs.any (· == candidateArgument)
          if !candidateArgumentIsReviewedParameter then
            extraDataIndices := extraDataIndices.push <|
              Json.str (toString index)
    if !extraProofIndices.isEmpty then
      return none

    pure <| some <| Json.mkObj [
      ("candidate", Json.str candidateName.toString),
      ("matched_binder_index", Json.str (toString matchedIndex)),
      ("candidate_only_data_binder_indices", Json.arr extraDataIndices),
      ("direct_eliminator", Json.bool extraDataIndices.isEmpty)]

/--
Return whether a constructor-like declaration can produce the exact elaborated
type of one reviewed theorem binder.  The reviewed declaration's universe
parameters and binder locals are rigid; only the candidate's own binders and
universe parameters may be instantiated.  This rules out, for example, using
an inhabitant of `MallowsSpec 0` as a constructor for a binder of type
`MallowsSpec n` at arbitrary `n`.

The caller may use source spelling only to locate the reviewed declaration and
binder.  The acceptance decision is Lean's definitional equality on
the elaborated types, including all parameters and universe levels.
-/
private def constructorResultTypeMatches
    (reviewedName binderName candidateName : Name) : MetaM Bool :=
  withNewMCtxDepth do
    let reviewedInfo ← getConstInfo reviewedName
    let rigidLevels := (List.range reviewedInfo.levelParams.length).map fun index =>
      Level.param (Name.mkSimple s!"_econcs_audit_constructor_universe_{index}")
    let reviewedConst := mkConst reviewedName rigidLevels
    let reviewedType ← inferType reviewedConst
    forallTelescopeReducing reviewedType fun reviewedBinders _ => do
      let mut targetBinder? : Option Expr := none
      for binder in reviewedBinders do
        let localDecl ← binder.fvarId!.getDecl
        if localDecl.userName == binderName then
          if targetBinder?.isSome then
            return false
          targetBinder? := some binder
      let some targetBinder := targetBinder? | return false
      let targetType ← inferType targetBinder
      let candidateConst ← mkConstWithFreshMVarLevels candidateName
      let candidateType ← inferType candidateConst
      let (_, _, candidateResult) ← forallMetaTelescopeReducing candidateType
      withTransparency .all do
        isDefEq candidateResult targetType

/-- Versioned, finite set of representation types allowed to receive automatic
data credit.  Every other structure/inductive is routed to source/Lean closure
even when its currently visible fields look data-like.  This keeps a local
``Certified f law`` wrapper from becoming data merely because its proof is
indexed by earlier data. -/
/-
`structural_data` is deliberately not a syntactic "not Prop" test.  It is a
small, versioned representation-invariant allowlist.  Both the declaration
FQN and the module that owns that declaration are checked: an imported/local
`Finset` lookalike must not inherit raw-data credit from its spelling.

Keep this list in lockstep with the digest-pinned Python transport.  The
entries are representation heads whose recursively trusted arguments cannot
make an inhabitant a certificate for a paper proposition.  Every type
argument is checked first, so a nonstructural or empty argument cannot receive
automatic data credit through a trusted container.  Every other Type wrapper
is routed to an explicit source/Lean closure, even if it currently has only
data fields.
-/
private def foundationStructuralDataHeads : Array (Name × String) := #[
  (`Nat, "Init.Prelude"),
  (`Int, "Init.Prelude"),
  (`Finset, "Mathlib.Data.Finset.Defs"),
  (`List, "Init.Prelude"),
  (`Array, "Init.Prelude"),
  (`Option, "Init.Prelude"),
  (`Prod, "Init.Prelude"),
  (`Sum, "Init.Prelude"),
  (`Bool, "Init.Prelude"),
  (`Char, "Init.Prelude"),
  (`String, "Init.Prelude"),
  (`Float, "Init.Prelude"),
  (`UInt8, "Init.Prelude"),
  (`UInt16, "Init.Prelude"),
  (`UInt32, "Init.Prelude"),
  (`UInt64, "Init.Prelude"),
  (`USize, "Init.Prelude"),
  (`Real, "Mathlib.Data.Real.Basic"),
  (Name.mkSimple "NNReal", "Mathlib.Data.NNReal.Defs")]

private def foundationStructuralDataAllowlistVersion : String :=
  "foundation-structural-data-v4"

private structure FieldPayloadSafety where
  safety : String
  route : String
  reasonCodes : Array String
  foundationModule : String := ""
  foundationHead : String := ""

private def fieldPayloadSafety
    (safety route : String) (reasonCodes : Array String := #[])
    (foundationModule : String := "") (foundationHead : String := "") : FieldPayloadSafety :=
  { safety, route, reasonCodes, foundationModule, foundationHead }

private def propositionLikeResult (value : Expr) : MetaM Bool := do
  if ← isProp value then
    return true
  let reduced ← whnf value
  match reduced with
  | .sort .zero => return true
  | _ => return false

private def terminalFunctionResult (type : Expr) : MetaM Expr := do
  forallTelescopeReducing type fun _ result => pure result

private def trustedFoundationStructuralDataHead
    (name : Name) : MetaM (Option (String × String)) := do
  let some (_, expectedModule) :=
    foundationStructuralDataHeads.find? (fun (head, _) => head == name)
    | return none
  let env ← getEnv
  let some moduleIndex := env.getModuleIdxFor? name | return none
  let moduleName := env.header.moduleNames[moduleIndex.toNat]!
  if moduleName.toString == expectedModule then
    return some (expectedModule, name.toString)
  return none

private def trustedFoundationStructuralDataTermConstant
    (name : Name) : MetaM Bool := do
  let env ← getEnv
  let some moduleIndex := env.getModuleIdxFor? name | return false
  let moduleName := env.header.moduleNames[moduleIndex.toNat]!
  -- Dependent indices routinely contain foundational constructors and
  -- numeral elaboration constants.  Admit only constants owned by the exact
  -- modules already trusted for structural representation heads; a paper or
  -- imported definition/opaque can hide a proposition behind an otherwise
  -- data-typed index and must therefore receive an explicit closure route.
  pure <| foundationStructuralDataHeads.any fun (_, trustedModule) =>
    moduleName.toString == trustedModule

mutual

private partial def proofDependentTermPayload
    (reason : String) : FieldPayloadSafety :=
  fieldPayloadSafety "requires_source_or_lean_closure"
    "proof_dependent_term" #[reason]

private partial def combineTermPayloadSafety
    (left right : FieldPayloadSafety) : FieldPayloadSafety :=
  if left.safety == "unknown" || right.safety == "unknown" then
    fieldPayloadSafety "unknown" "unsafe_term_component" #["unknown_term_component"]
  else if left.safety != "structural_data" || right.safety != "structural_data" then
    proofDependentTermPayload "nonstructural_term_component"
  else
    fieldPayloadSafety "structural_data" "term_expression"

/--
Inspect a term used as a dependent type index.  Looking only at its inferred
sort is unsound: `Fin (if P then 1 else 0)` has a Nat index while inhabiting
the field proves `P`.  This traversal is intentionally semantic and
conservative.  It rejects proof terms, proposition-valued terms, and every
application/lambda/let that contains one; ordinary data fvars/literals such
as the `n` in `Fin n` remain structurally safe as *index terms*. The enclosing
`Fin` carrier itself is not an automatic structural-data representation.
-/
private partial def termPayloadSafety
    (term : Expr) (fuel : Nat) : MetaM FieldPayloadSafety := do
  if fuel == 0 then
    return fieldPayloadSafety "unknown" "term_fuel_exhausted" #["term_fuel_exhausted"]
  let instantiated ← instantiateMVars term
  if ← isProp instantiated then
    return proofDependentTermPayload "proposition_term"
  let termType ← whnf (← inferType instantiated)
  if ← isProp termType then
    return proofDependentTermPayload "proof_term"
  match instantiated with
  | .fvar _ =>
      -- A data-valued local can safely appear as the `n` in `Fin n`.  For a
      -- local function, even a `Nat -> Nat`, its values can constrain an
      -- enclosing dependent index. Treat every function-valued local as a
      -- source/Lean-closure obligation rather than proving totality here.
      match termType with
      | .forallE _ _ _ _ =>
          return proofDependentTermPayload "function_term_index"
      | _ =>
          let safety ← recursiveFieldPayloadSafety termType (fuel - 1)
          if safety.safety == "structural_data" then
            return fieldPayloadSafety "structural_data" "data_term_fvar"
          if safety.safety == "unknown" then
            return fieldPayloadSafety "unknown" "unknown_term_fvar" #["unknown_term_fvar"]
          return proofDependentTermPayload "nonstructural_term_fvar"
  | .lit _ => return fieldPayloadSafety "structural_data" "literal_term"
  | .const name _ =>
      if ← trustedFoundationStructuralDataTermConstant name then
        -- Preserve ordinary foundational constructors and numeral elaboration
        -- terms. Their module provenance is tied to the same finite
        -- representation allowlist as the enclosing type heads.
        return fieldPayloadSafety "structural_data" "foundation_term_constant"
      -- A closed paper/imported definition or opaque can encode a proposition
      -- in a data-valued dependent index (for example, `Fin hiddenIndex`).
      -- Its type alone cannot establish that the index is ordinary data.
      return proofDependentTermPayload "nonfoundation_constant_index"
  | .app fn argument =>
      let fnSafety ← termPayloadSafety fn (fuel - 1)
      let argumentSafety ← termPayloadSafety argument (fuel - 1)
      return combineTermPayloadSafety fnSafety argumentSafety
  | .lam name domain body binderInfo =>
      let domainSafety ← recursiveFieldPayloadSafety domain (fuel - 1)
      if domainSafety.safety != "structural_data" then
        return proofDependentTermPayload "nonstructural_lambda_domain"
      withLocalDecl name binderInfo domain fun binder =>
        termPayloadSafety (body.instantiate1 binder) (fuel - 1)
  | .forallE name domain body binderInfo =>
      let domainSafety ← recursiveFieldPayloadSafety domain (fuel - 1)
      if domainSafety.safety != "structural_data" then
        return proofDependentTermPayload "nonstructural_forall_domain"
      withLocalDecl name binderInfo domain fun binder =>
        termPayloadSafety (body.instantiate1 binder) (fuel - 1)
  | .letE name type value body nondep =>
      let typeSafety ← recursiveFieldPayloadSafety type (fuel - 1)
      if typeSafety.safety != "structural_data" then
        return proofDependentTermPayload "nonstructural_let_type"
      let valueSafety ← termPayloadSafety value (fuel - 1)
      if valueSafety.safety != "structural_data" then
        return valueSafety
      withLetDecl name type value (nondep := nondep) fun binder =>
        termPayloadSafety (body.instantiate1 binder) (fuel - 1)
  | .mdata _ body => termPayloadSafety body (fuel - 1)
  | .proj _ _ structExpr => termPayloadSafety structExpr (fuel - 1)
  | .sort _ =>
      -- A sort used as a dependent term index is not a concrete
      -- representation witness.  The outer type-argument route normally
      -- handles it; retain a fail-closed case for elaborated edge shapes.
      return proofDependentTermPayload "sort_term_index"
  | .bvar _ =>
      return fieldPayloadSafety "unknown" "unbound_term_index" #["unbound_term_index"]
  | .mvar _ =>
      return fieldPayloadSafety "unknown" "unresolved_term_index" #["unresolved_term_index"]

private partial def safetyOfTypeArgument
    (argument : Expr) (fuel : Nat) : MetaM FieldPayloadSafety := do
  let argumentType ← whnf (← inferType argument)
  match argumentType with
  | .sort _ => recursiveFieldPayloadSafety argument fuel
  | _ =>
      let termSafety ← termPayloadSafety argument (fuel - 1)
      if termSafety.safety != "structural_data" then
        return termSafety
      if ← propositionLikeResult argument then
        return fieldPayloadSafety "requires_source_or_lean_closure"
          "proposition_parameter" #["proposition_parameter"]
      let terminal ← terminalFunctionResult argumentType
      if ← propositionLikeResult terminal then
        return fieldPayloadSafety "requires_source_or_lean_closure"
          "prop_valued_parameter" #["prop_valued_parameter"]
      return fieldPayloadSafety "structural_data" "term_parameter"

/--
Classify direct proof payload safety from elaborated types, never from a field
or constructor label.  Foundation representation types are a deliberately
small trusted allowlist; their actual type arguments are recursively checked.
All other inductive/structure wrappers require their own audited source/Lean
closure, and opaque/unresolved heads fail closed.
-/
private partial def recursiveFieldPayloadSafety
    (fieldType : Expr) (fuel : Nat := 24) : MetaM FieldPayloadSafety := do
  if fuel == 0 then
    return fieldPayloadSafety "unknown" "fuel_exhausted" #["fuel_exhausted"]
  let instantiated ← instantiateMVars fieldType
  if ← isProp instantiated then
    return fieldPayloadSafety "proof_payload" "direct_proposition"
      #["direct_proposition"]
  let reduced ← withTransparency .reducible <| whnf instantiated
  if ← isProp reduced then
    return fieldPayloadSafety "proof_payload" "direct_proposition"
      #["direct_proposition"]
  match reduced with
  | .sort _ =>
      -- A stored proposition or carrier is model data chosen by the caller,
      -- not a proof payload and not ordinary structural representation data.
      -- It remains an explicit semantic-review obligation.
      return fieldPayloadSafety "requires_semantic_route"
        "sort_carrier" #["sort_carrier"]
  | .forallE _ _ _ _ =>
      let terminal ← terminalFunctionResult reduced
      if ← propositionLikeResult terminal then
        return fieldPayloadSafety "requires_semantic_route"
          "predicate_or_relation" #["prop_valued_function"]
      -- A non-Prop function may have an empty codomain (`Nat -> Fin 0`) or
      -- otherwise encode a theorem through its values. No automatic data
      -- credit is sound without a separate totality/source-model closure.
      return fieldPayloadSafety "requires_source_or_lean_closure"
        "function_payload" #["function_payload_requires_closure"]
  | .fvar _ =>
      let typeOfType ← whnf (← inferType reduced)
      match typeOfType with
      | .sort _ =>
          -- A caller-controlled Type parameter is not a finite foundational
          -- representation.  Treat it like every other non-allowlisted
          -- wrapper; a source/Lean closure can still approve it explicitly.
          return fieldPayloadSafety "requires_source_or_lean_closure"
            "unbounded_type_parameter" #["unbounded_type_parameter"]
      | _ =>
          return fieldPayloadSafety "unknown" "unresolved_type_parameter"
            #["unresolved_type_parameter"]
  | _ =>
      let (typeName, arguments) := reduced.getAppFnArgs
      if !typeName.isAnonymous then
          let mut argumentSafety : Array FieldPayloadSafety := #[]
          for argument in arguments do
            argumentSafety := argumentSafety.push
              (← safetyOfTypeArgument argument (fuel - 1))
          if argumentSafety.any (fun result => result.safety == "unknown") then
            -- An opaque dependent argument cannot receive raw data credit,
            -- but it can still be reviewed through an explicit source or Lean
            -- closure. Do not erase the field before that review occurs.
            return fieldPayloadSafety "requires_source_or_lean_closure"
              "unsafe_type_argument" #["unknown_type_argument"]
          if argumentSafety.any (fun result => result.safety != "structural_data") then
            return fieldPayloadSafety "requires_source_or_lean_closure"
              "unsafe_type_argument" #["nonstructural_type_argument"]
          if let some (moduleName, headName) ← trustedFoundationStructuralDataHead typeName then
            return fieldPayloadSafety "structural_data"
              "foundation_representation_invariant"
              #[foundationStructuralDataAllowlistVersion] moduleName headName
          let info ← getConstInfo typeName
          match info with
          | .inductInfo _ =>
              return fieldPayloadSafety "requires_source_or_lean_closure"
                "nonfoundation_inductive" #["nonfoundation_wrapper"]
          | .quotInfo _ =>
              return fieldPayloadSafety "requires_source_or_lean_closure"
                "nonfoundation_quotient" #["nonfoundation_wrapper"]
          | _ =>
              return fieldPayloadSafety "requires_source_or_lean_closure"
                "opaque_or_unresolved_head"
                #["opaque_or_unresolved_head"]
      else
        return fieldPayloadSafety "requires_source_or_lean_closure"
          "unresolved_type_head"
          #["unresolved_type_head"]

end

private def canonicalFieldType
    (fieldType : Expr) (binders : Array Expr) : MetaM String := do
  -- `reprStr` includes fresh fvar IDs, so it is not an evidence identity.
  -- Reuse the manifest's alpha-normal form while explicitly excluding every
  -- module from local-definition expansion; field safety must be about this
  -- elaborated type, not source names or an accidental reduction closure.
  let env ← getEnv
  -- A synthetic *present* module index prevents `canonicalExpr`'s normal
  -- source-local fallback from unfolding an opaque declaration in an inline
  -- test/current module.  The explicit nonmatching audit prefix keeps every
  -- head opaque for this identity calculation.
  let externalModule := env.getModuleIdxFor? `Nat
  let canonical ← canonicalExpr #[] (binders.map Expr.fvarId!) #[]
    #[`AppliedModelingLibAudit.NoFieldSafetyLocalExpansion] externalModule #[] #[] fieldType
  pure canonical.compress

private def fieldReceiptForType
    (fieldType : Expr) (binders : Array Expr) : MetaM (String × FieldPayloadSafety × String) := do
  let valueSort := if ← isProp fieldType then "true" else "false"
  let safety ← try
    recursiveFieldPayloadSafety fieldType
  catch _ =>
    pure <| fieldPayloadSafety "unknown" "payload_analysis_exception"
      #["payload_analysis_exception"]
  let normalized ← withTransparency .reducible <| whnf fieldType
  let normalizedText ← try
    canonicalFieldType normalized binders
  catch _ =>
    pure ""
  -- A telescope-local field can be classified by Lean even when the generic
  -- expression serializer intentionally declines to render its full type.
  -- Keep the receipt transport nonempty without treating this marker as a
  -- structural type identity: the exact constructor/projection slot, actual
  -- value sort, and Lean-derived safety route remain independently bound.
  let normalizedText :=
    if normalizedText.isEmpty then
      "unserializable_elaborated_field_type:" ++ valueSort ++ ":" ++
        safety.safety ++ ":" ++ safety.route
    else normalizedText
  return (valueSort, safety, normalizedText)

private def constructorArgumentFieldReceipt
    (constructorName : Name) (fieldIndex : Nat) : MetaM (Option (String × FieldPayloadSafety × String)) := do
  let .ctorInfo constructorInfo ← getConstInfo constructorName
    | return none
  if fieldIndex >= constructorInfo.numFields then
    return none
  withNewMCtxDepth do
    forallTelescopeReducing constructorInfo.type fun binders _ => do
      -- The parser excludes source-visible binders that occur only as an
      -- indexed result parameter.  `fieldIndex` is therefore an exact Lean
      -- stored-field ordinal and this `numParams + fieldIndex` lookup cannot
      -- shift a result index onto a later field.
      let telescopeIndex := constructorInfo.numParams + fieldIndex
      if telescopeIndex >= binders.size then
        return none
      fieldReceiptForType (← inferType binders[telescopeIndex]!) binders

private def projectionFieldReceipt
    (projectionName : Name) (fieldIndex : Nat) : MetaM (Option (String × FieldPayloadSafety × String)) := do
  let some projectionInfo ← getProjectionFnInfo? projectionName
    | return none
  if projectionInfo.i != fieldIndex then
    return none
  withNewMCtxDepth do
    let projection ← mkConstWithFreshMVarLevels projectionName
    let projectionType ← inferType projection
    forallTelescopeReducing projectionType fun binders _ => do
      let requiredArguments := projectionInfo.numParams + 1
      if binders.size < requiredArguments then
        return none
      let fieldValue := mkAppN projection (binders.extract 0 requiredArguments)
      fieldReceiptForType (← inferType fieldValue) binders

private def parseRecursiveFieldPropositionSortRequests
    (raw : String) : Option (Array (String × String × Name × Nat)) := do
  let value ← (Json.parse raw).toOption
  match value with
  | .arr values =>
      let mut requests : Array (String × String × Name × Nat) := #[]
      for value in values do
        let rawSchema ← (value.getObjVal? "schema").toOption
        let rawIdentity ← (value.getObjVal? "field_identity_sha256").toOption
        let rawKind ← (value.getObjVal? "kind").toOption
        let rawIndex ← (value.getObjVal? "field_index").toOption
        let schema ← rawSchema.getStr?.toOption
        let identity ← rawIdentity.getStr?.toOption
        let kind ← rawKind.getStr?.toOption
        let indexText ← rawIndex.getStr?.toOption
        let index ← indexText.toNat?
        if schema != "1" || identity.isEmpty || requests.any (fun (seen, _, _, _) => seen == identity) then
          failure
        let declarationKey := if kind == "projection" then "declaration" else "constructor"
        let rawDeclaration ← (value.getObjVal? declarationKey).toOption
        let declaration ← rawDeclaration.getStr?.toOption
        if (kind != "projection" && kind != "constructor_argument") || declaration.isEmpty then
          failure
        requests := requests.push (identity, kind, declaration.toName, index)
      pure requests
  | _ => none

private def typeWitnessReceiptForType
    (path : String) (witnessType : Expr) (binders : Array Expr) : MetaM Json := do
  let (valueSort, safety, normalizedType) ← fieldReceiptForType witnessType binders
  let reducedWitness ← withTransparency .reducible <| whnf witnessType
  let witnessTypeHead := match reducedWitness.getAppFn with
    | .const name _ => name.toString
    | _ => ""
  let status := if safety.safety == "unknown" then "error" else "ok"
  pure <| Json.mkObj [
    ("path", Json.str path),
    -- This helper is called only after the logical traversal has selected a
    -- witness that the theorem must produce. Forall/implication domains and
    -- the proposition beneath `Not` are traversed as assumptions instead and
    -- never reach this constructor. Keep that Lean-owned role explicit so a
    -- later source parser cannot turn a merely lexical `Nonempty` occurrence
    -- back into result-certificate evidence.
    ("occurrence_role", Json.str "provided_result"),
    -- The declaration identity is presentation glue for attaching recursively
    -- exposed local fields. Positivity comes from `occurrence_role` and the
    -- elaborated traversal, never from this name or a suffix convention.
    ("witness_type_head", Json.str witnessTypeHead),
    ("value_sort", Json.str valueSort),
    ("payload_safety", Json.str safety.safety),
    ("status", Json.str status),
    ("route", Json.str safety.route),
    ("normalized_type", Json.str normalizedType),
    ("reason_codes", Json.arr (safety.reasonCodes.map Json.str)),
    ("foundation_module", Json.str safety.foundationModule),
    ("foundation_head", Json.str safety.foundationHead),
    ("foundation_allowlist_version", Json.str foundationStructuralDataAllowlistVersion)]

private def declarationInReviewedModule
    (reviewedModule : Option ModuleIdx) (name : Name) : MetaM Bool := do
  let env ← getEnv
  match reviewedModule, env.getModuleIdxFor? name with
  | some expected, some actual => pure (expected == actual)
  | _, _ => pure false

/-
Nested paper-facing endpoints can legitimately contain several layers of
logical wrappers before a Type-valued witness is reached.  The 512-step budget
is large enough for those structural proposition trees, while retaining a
finite fail-closed boundary for recursive or adversarial declarations.
-/
private def typeWitnessPayloadTraversalBudget : Nat := 512

/--
Find Type-valued witnesses hidden beneath the elaborated proposition result of
a reviewed declaration.  The traversal is structural: it recognizes `Nonempty`
and `Exists` by their Lean constants, follows proposition arguments, and
opens only proposition inductives defined in the reviewed module.  A source
label such as `Certificate` never participates in this decision.
-/
private partial def typeWitnessReceiptsInProposition
    (proposition : Expr) (binders : Array Expr) (path : String)
    (reviewedModule : Option ModuleIdx)
    (fuel : Nat := typeWitnessPayloadTraversalBudget) : MetaM (Array Json) := do
  if fuel == 0 then
    throwError "type-witness payload traversal exhausted its bounded fuel at {path}"
  let reduced ← withTransparency .reducible <| whnf proposition
  match reduced with
  | .forallE name domain body binderInfo =>
      withLocalDecl name binderInfo domain fun binder =>
        typeWitnessReceiptsInProposition (body.instantiate1 binder)
          (binders.push binder) (path ++ "/forall") reviewedModule (fuel - 1)
  | _ =>
      let (head, arguments) := reduced.getAppFnArgs
      if head == `Nonempty then
        match arguments.back? with
        | some witness =>
            return #[← typeWitnessReceiptForType
              (path ++ "/nonempty") witness binders]
        | none => return #[]
      else if head == `Exists then
        match arguments.back? with
        | none => return #[]
        | some motive =>
          let motiveType ← whnf (← inferType motive)
          match motiveType with
          | .forallE name domain _ binderInfo =>
              -- `Exists` may bind a proof, not a Type-valued certificate.
              -- Its body can still contain a material Type witness, so skip
              -- only the proof binder and continue the structural traversal.
              let witnesses ←
                if ← isProp domain then
                  pure #[]
                else
                  pure #[← typeWitnessReceiptForType
                    (path ++ "/exists") domain binders]
              match (← whnf motive) with
              | .lam _ _ body _ =>
                  withLocalDecl name binderInfo domain fun binder => do
                    let nested ← typeWitnessReceiptsInProposition
                      (body.instantiate1 binder) (binders.push binder)
                      (path ++ "/exists_body") reviewedModule (fuel - 1)
                    return witnesses ++ nested
              | _ => return witnesses
          | _ => return #[]
      else
        let mut receipts : Array Json := #[]
        -- An arbitrary proposition wrapper can hide a Type-valued certificate
        -- in a parameter even when its constructors are imported or opaque.
        -- Record every elaborated Sort-valued argument before optionally
        -- opening reviewed-local constructors below.
        for index in [0:arguments.size] do
          let argument := arguments[index]!
          let argumentType ← whnf (← inferType argument)
          match argumentType with
          | .sort _ =>
              if !(← isProp argument) then
                receipts := receipts.push (← typeWitnessReceiptForType
                  (path ++ s!"/type_argument_{index}") argument binders)
          | _ => pure ()
        -- Logical connective arguments are propositions themselves. Descend
        -- through their elaborated values rather than guessing from notation.
        for index in [0:arguments.size] do
          let argument := arguments[index]!
          if ← isProp argument then
            receipts := receipts ++ (← typeWitnessReceiptsInProposition argument binders
              (path ++ s!"/prop_argument_{index}") reviewedModule (fuel - 1))
        if !head.isAnonymous && (← declarationInReviewedModule reviewedModule head) then
          let env ← getEnv
          match env.constants.find? head with
          | some (.inductInfo inductiveInfo) =>
              for constructorName in inductiveInfo.ctors do
                let .ctorInfo constructorInfo ← getConstInfo constructorName
                  | continue
                receipts := receipts ++ (← withNewMCtxDepth do
                  forallTelescopeReducing constructorInfo.type fun constructorBinders _ => do
                    let mut constructorReceipts : Array Json := #[]
                    for fieldIndex in [0:constructorInfo.numFields] do
                      let binderIndex := constructorInfo.numParams + fieldIndex
                      if binderIndex < constructorBinders.size then
                        let fieldType ← inferType constructorBinders[binderIndex]!
                        if ← isProp fieldType then
                          constructorReceipts := constructorReceipts ++
                            (← typeWitnessReceiptsInProposition fieldType
                              constructorBinders
                              (path ++ s!"/constructor_{constructorInfo.cidx}_field_{fieldIndex}")
                              reviewedModule (fuel - 1))
                        else
                          constructorReceipts := constructorReceipts.push
                            (← typeWitnessReceiptForType
                              (path ++ s!"/constructor_{constructorInfo.cidx}_field_{fieldIndex}")
                              fieldType constructorBinders)
                    return constructorReceipts)
          | _ => pure ()
        return receipts

private def typeWitnessPayloadReceiptsForDeclaration
    (declarationName : Name) : MetaM (Option (Array Json)) := do
  let env ← getEnv
  let reviewedModule := env.getModuleIdxFor? declarationName
  let _ ← getConstInfo declarationName
  let declaration ← mkConstWithFreshMVarLevels declarationName
  let declarationType ← inferType declaration
  withNewMCtxDepth do
    forallTelescopeReducing declarationType fun binders result => do
      some <$> typeWitnessReceiptsInProposition result binders "result"
        reviewedModule

private def parseTypeWitnessPayloadRequests (raw : String) : Option (Array Name) := do
  let value ← (Json.parse raw).toOption
  match value with
  | .arr values =>
      let mut names : Array Name := #[]
      for value in values do
        let text ← value.getStr?.toOption
        if text.isEmpty || names.contains text.toName then
          failure
        names := names.push text.toName
      pure names
  | _ => none

private def constructorFieldSlotCount (constructorName : Name) : MetaM (Option Json) := do
  let info ← getConstInfo constructorName
  let numFields? ←
    match info with
    | .ctorInfo constructorInfo =>
        pure (some constructorInfo.numFields)
    | _ =>
        -- Lean records/classes expose a generated ``<Record>.mk`` definition,
        -- not an ``CtorInfo``.  Resolve that exact constructor spelling back to
        -- its owning elaborated ``StructureInfo`` and count its stored fields.
        -- This is a Meta-owned slot fact, not a parser count or field-label
        -- heuristic.  Other non-constructor definitions remain rejected.
        let structureName := constructorName.getPrefix
        if constructorName != structureName.append `mk then
          pure none
        else
          let env ← getEnv
          let some structureInfo := getStructureInfo? env structureName
            | pure none
          pure (some structureInfo.fieldNames.size)
  let some numFields := numFields? | return none
  pure <| some <| Json.mkObj [
    ("constructor", Json.str constructorName.toString),
    ("num_fields", Json.str (toString numFields))]

private def inductiveConstructorFieldSlotCounts
    (inductiveName : Name) : MetaM (Option Json) := do
  let .inductInfo inductiveInfo ← getConstInfo inductiveName
    | return none
  let constructors ← inductiveInfo.ctors.toArray.mapM fun constructorName => do
    let count? ← constructorFieldSlotCount constructorName
    match count? with
    | some count => pure count
    | none => throwError "inductive constructor is unavailable"
  pure <| some <| Json.mkObj [
    ("inductive", Json.str inductiveName.toString),
    ("constructors", Json.arr constructors)]

private def sourcePremiseFalseEliminators
    (reviewedNames : Array Name) (auditModulePrefixes : Array Name) : MetaM Json := do
  let env ← getEnv
  let reviewedModules := reviewedNames.map (env.getModuleIdxFor?)
  let mut candidatesByReviewed : Array (Array Json) := reviewedNames.map (fun _ => #[])
  -- Scan the environment once.  A source-record audit commonly has several
  -- record roots, and repeating the full imported environment traversal per
  -- root would make a narrow semantic check unexpectedly expensive.
  for (candidateName, candidateInfo) in env.constants do
    match candidateInfo with
    | .thmInfo _ | .defnInfo _ | .axiomInfo _ | .opaqueInfo _ =>
        for index in [0:reviewedNames.size] do
          let reviewedName := reviewedNames[index]!
          let reviewedModule := reviewedModules[index]!
          if candidateName != reviewedName &&
              (← inAuditClosure auditModulePrefixes reviewedModule candidateName) then
            if let some candidate ← sourcePremiseFalseEliminator reviewedName candidateName then
              candidatesByReviewed := candidatesByReviewed.set! index
                ((candidatesByReviewed[index]!).push candidate)
    | _ => pure ()
  let reviewedInputs := reviewedNames.zip candidatesByReviewed |>.map fun (reviewed, candidates) =>
    Json.mkObj [
      ("reviewed", Json.str reviewed.toString),
      ("candidates", Json.arr candidates)]
  pure <| Json.mkObj [
    ("reviewed_inputs", Json.arr reviewedInputs)]

syntax (name := signatureManifestCmd) "#signature_manifest " str str str : command

syntax (name := signatureManifestRevalidationCmd)
  "#signature_manifest_revalidation " str str str : command

elab_rules : command
  | `(#signature_manifest $decl:str $scope:str $hashTool:str) => do
      let declName := decl.getString.toName
      let scopeName := scope.getString
      let hashToolPath := hashTool.getString
      let auditModulePrefixes :=
        if scopeName.isEmpty then #[]
        else (scopeName.split (· == ',')).toArray.map (fun slice => slice.toString.toName)
      let manifest? ← try
        let knownVector ← liftTermElabM <| canonicalDigest hashToolPath "abc"
        unless knownVector ==
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" do
          throwError "signature-manifest SHA-256 tool failed its known vector"
        some <$> liftTermElabM
          (manifestFor declName auditModulePrefixes hashToolPath)
      catch exception =>
        let message ← exception.toMessageData.toString
        IO.println s!"LEAN_SIGNATURE_MANIFEST_DIAGNOSTIC:{declName}:{message}"
        pure none
      match manifest? with
      | some manifest =>
          IO.println s!"LEAN_SIGNATURE_MANIFEST:{declName}:{manifest.compress}"
      | none =>
          IO.println s!"LEAN_SIGNATURE_MANIFEST_ERROR:{declName}"

elab_rules : command
  | `(#signature_manifest_revalidation $decl:str $scope:str $hashTool:str) => do
      let declName := decl.getString.toName
      let scopeName := scope.getString
      let hashToolPath := hashTool.getString
      let auditModulePrefixes :=
        if scopeName.isEmpty then #[]
        else (scopeName.split (· == ',')).toArray.map (fun slice => slice.toString.toName)
      let receipt? ← try
        let knownVector ← liftTermElabM <| canonicalDigest hashToolPath "abc"
        unless knownVector ==
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" do
          throwError "signature-manifest SHA-256 tool failed its known vector"
        some <$> liftTermElabM
          (signatureManifestRevalidationFor
            declName auditModulePrefixes hashToolPath)
      catch exception =>
        let message ← exception.toMessageData.toString
        IO.println s!"LEAN_SIGNATURE_MANIFEST_REVALIDATION_DIAGNOSTIC:{declName}:{message}"
        pure none
      match receipt? with
      | some receipt =>
          IO.println s!"LEAN_SIGNATURE_MANIFEST_REVALIDATION:{declName}:{receipt.compress}"
      | none =>
          IO.println s!"LEAN_SIGNATURE_MANIFEST_REVALIDATION_ERROR:{declName}"

syntax (name := propositionSpecProofMatchCmd)
  "#proposition_spec_proof_match " str str : command

syntax (name := semanticContractMatchCmd)
  "#semantic_contract_match " str str str : command

syntax (name := semanticContractTransparencyCmd)
  "#semantic_contract_transparency " str str str : command

syntax (name := semanticContractClosureCmd)
  "#semantic_contract_closure " str str str : command

syntax (name := sourcePremiseFalseScanCmd)
  "#source_premise_false_scan " str str : command

syntax (name := constructorResultTypeMatchCmd)
  "#constructor_result_type_match " str str str : command

syntax (name := recursiveFieldPropositionSortCmd)
  "#recursive_field_proposition_sort " str : command

syntax (name := constructorFieldSlotCountCmd)
  "#constructor_field_slot_counts " str : command

syntax (name := inductiveConstructorFieldSlotCountCmd)
  "#inductive_constructor_field_slot_counts " str : command

syntax (name := typeWitnessPayloadSafetyCmd)
  "#type_witness_payload_safety " str : command

elab_rules : command
  | `(#proposition_spec_proof_match $spec:str $proof:str) => do
      let specName := spec.getString.toName
      let proofName := proof.getString.toName
      let doesMatch ← try
        liftTermElabM (propositionSpecProofMatches specName proofName)
      catch _ =>
        pure false
      let result := Json.mkObj [
        ("spec", Json.str specName.toString),
        ("proof", Json.str proofName.toString),
        ("matches", Json.bool doesMatch)]
      IO.println s!"LEAN_PROPOSITION_SPEC_PROOF_MATCH:{result.compress}"
  | `(#semantic_contract_match $spec:str $evidence:str $mode:str) => do
      let specName := spec.getString.toName
      let evidenceName := evidence.getString.toName
      let modeName := mode.getString
      let doesMatch ←
        if modeName == "proves" || modeName == "refutes" then
          try
            liftTermElabM <|
              semanticContractMatches specName evidenceName (modeName == "refutes")
          catch _ =>
            pure false
        else if modeName == "definitionally_realizes" then
          try
            liftTermElabM <| semanticContractDefinitionallyRealizes specName evidenceName
          catch _ =>
            pure false
        else
          pure false
      let result := Json.mkObj [
        ("spec", Json.str specName.toString),
        ("evidence", Json.str evidenceName.toString),
        ("mode", Json.str modeName),
        ("matches", Json.bool doesMatch)]
      IO.println s!"LEAN_SEMANTIC_CONTRACT_MATCH:{result.compress}"
  | `(#semantic_contract_transparency $spec:str $scope:str $fuel:str) => do
      let specName := spec.getString.toName
      let scope? := parseSemanticContractTransparencyScope scope.getString
      let fuel? := fuel.getString.toNat?
      let state ←
        match scope?, fuel? with
        | some auditModules, some requestedFuel =>
            try
              liftTermElabM <| semanticContractTransparency
                specName auditModules requestedFuel
            catch _ =>
              pure <| semanticContractTransparencyFailure
                { fuel := requestedFuel } "unresolved_local_dependency" specName
        | _, _ =>
            pure <| semanticContractTransparencyFailure
              { fuel := 0 } "invalid_transparency_scope" specName
      let terminalReceipts := state.executableRecursiveTerminals.map fun terminal =>
        Json.mkObj [
          ("declaration", Json.str terminal.declaration.toString),
          ("occurrence_path", Json.arr <|
            terminal.occurrencePath.map Json.str),
          ("application_arity", Json.str (toString terminal.applicationArity)),
          ("application_result_type", Json.str terminal.applicationResultType),
          ("normalized_result_type", Json.str terminal.normalizedResultType)]
      let (failureTag, failureName) :=
        match state.failure with
        | some (tag, name) => (tag, name.toString)
        | none =>
            match state.executableRecursiveTerminals[0]? with
            | some terminal => ("recursive_executable_terminal", terminal.declaration.toString)
            | none => ("", "")
      let result := Json.mkObj [
        ("spec", Json.str specName.toString),
        ("passes", Json.bool <|
          state.failure.isNone && state.executableRecursiveTerminals.isEmpty),
        ("failure_tag", Json.str failureTag),
        ("failure_declaration", Json.str failureName),
        ("recursive_executable_terminal_schema", Json.str "1"),
        ("recursive_executable_terminals", Json.arr terminalReceipts),
        ("expanded", Json.str (toString state.expanded))]
      IO.println s!"LEAN_SEMANTIC_CONTRACT_TRANSPARENCY:{result.compress}"
  | `(#semantic_contract_closure $spec:str $scope:str $fuel:str) => do
      let specName := spec.getString.toName
      let scope? := parseSemanticContractClosureScope scope.getString
      let fuel? := fuel.getString.toNat?
      let result? ←
        match scope?, fuel? with
        | some closureScope, some requestedFuel =>
            try
              some <$> liftTermElabM
                (semanticContractClosureManifest specName closureScope requestedFuel)
            catch exception =>
              let message ← exception.toMessageData.toString
              let diagnostic := Json.mkObj [
                ("spec", Json.str specName.toString),
                ("message", Json.str message)]
              IO.println s!"LEAN_SEMANTIC_CONTRACT_CLOSURE_ERROR:{diagnostic.compress}"
              pure none
        | _, _ => pure none
      match result? with
      | some result =>
          IO.println s!"LEAN_SEMANTIC_CONTRACT_CLOSURE:{result.compress}"
      | none =>
          IO.println "LEAN_SEMANTIC_CONTRACT_CLOSURE_ERROR"
  | `(#source_premise_false_scan $reviewed:str $scope:str) => do
      let reviewedNames? :=
        match Json.parse reviewed.getString with
        | .ok (.arr values) =>
            values.foldl
              (fun collected? value =>
                match collected?, value.getStr? with
                | some collected, .ok name =>
                    if !name.isEmpty then some (collected.push name.toName)
                    else none
                | _, _ => none)
              (some #[])
        | _ => none
      let scopeName := scope.getString
      let auditModulePrefixes :=
        if scopeName.isEmpty then #[ ]
        else (scopeName.split (· == ',')).toArray.map (fun slice => slice.toString.toName)
      let result? ← try
        match reviewedNames? with
        | some reviewedNames =>
            some <$> liftTermElabM
              (sourcePremiseFalseEliminators reviewedNames auditModulePrefixes)
        | none => pure none
      catch _ =>
        pure none
      match result? with
      | some result =>
          IO.println s!"LEAN_SOURCE_PREMISE_FALSE_SCAN:{result.compress}"
      | none =>
          IO.println "LEAN_SOURCE_PREMISE_FALSE_SCAN_ERROR"
  | `(#constructor_result_type_match $reviewed:str $binderName:str $candidate:str) => do
      let reviewedName := reviewed.getString.toName
      let candidateName := candidate.getString.toName
      let targetBinderName := binderName.getString.toName
      let doesMatch ←
        try
          liftTermElabM <|
            constructorResultTypeMatches reviewedName targetBinderName candidateName
        catch _ =>
          pure false
      let result := Json.mkObj [
        ("reviewed", Json.str reviewedName.toString),
        ("binder", Json.str targetBinderName.toString),
        ("candidate", Json.str candidateName.toString),
        ("matches", Json.bool doesMatch)]
      IO.println s!"LEAN_CONSTRUCTOR_RESULT_TYPE_MATCH:{result.compress}"
  | `(#recursive_field_proposition_sort $fields:str) => do
      let requests? := parseRecursiveFieldPropositionSortRequests fields.getString
      let results? ← try
        match requests? with
        | some requests =>
            some <$> liftTermElabM (requests.mapM fun (identity, kind, declaration, index) => do
              let receipt? ←
                if kind == "projection" then
                  projectionFieldReceipt declaration index
                else
                  constructorArgumentFieldReceipt declaration index
              let (valueSort, safety, normalizedType, status) :=
                match receipt? with
                | some (valueSort, safety, normalizedType) =>
                    let status := if safety.safety == "unknown" then "error" else "ok"
                    (valueSort, safety, normalizedType, status)
                | none =>
                    ("unknown", fieldPayloadSafety "unknown" "invalid_field_locator"
                      #["invalid_field_locator"], "", "error")
              pure <| Json.mkObj [
                ("field_identity_sha256", Json.str identity),
                ("kind", Json.str kind),
                (if kind == "projection" then "declaration" else "constructor",
                  Json.str declaration.toString),
                ("field_index", Json.str (toString index)),
                ("value_sort", Json.str valueSort),
                ("payload_safety", Json.str safety.safety),
                ("status", Json.str status),
                ("route", Json.str safety.route),
                ("normalized_type", Json.str normalizedType),
                ("reason_codes", Json.arr (safety.reasonCodes.map Json.str)),
                ("foundation_module", Json.str safety.foundationModule),
                ("foundation_head", Json.str safety.foundationHead),
                ("foundation_allowlist_version", Json.str foundationStructuralDataAllowlistVersion)])
        | none => pure none
      catch _ =>
        pure none
      match results? with
      | some results =>
          IO.println s!"LEAN_RECURSIVE_FIELD_PROPOSITION_SORT:{(Json.mkObj [("fields", Json.arr results)]).compress}"
      | none =>
          IO.println "LEAN_RECURSIVE_FIELD_PROPOSITION_SORT_ERROR"
  | `(#constructor_field_slot_counts $constructors:str) => do
      let requested? := parseTypeWitnessPayloadRequests constructors.getString
      let results? ← try
        match requested? with
        | some requested =>
            some <$> liftTermElabM (requested.mapM fun constructorName => do
              let count? ← constructorFieldSlotCount constructorName
              match count? with
              | some count => pure count
              | none => throwError "unknown constructor")
        | none => pure none
      catch _ =>
        pure none
      match results? with
      | some results =>
          IO.println s!"LEAN_CONSTRUCTOR_FIELD_SLOT_COUNTS:{(Json.mkObj [("constructors", Json.arr results)]).compress}"
      | none =>
          IO.println "LEAN_CONSTRUCTOR_FIELD_SLOT_COUNTS_ERROR"
  | `(#inductive_constructor_field_slot_counts $inductives:str) => do
      let requested? := parseTypeWitnessPayloadRequests inductives.getString
      let results? ← try
        match requested? with
        | some requested =>
            some <$> liftTermElabM (requested.mapM fun inductiveName => do
              let counts? ← inductiveConstructorFieldSlotCounts inductiveName
              match counts? with
              | some counts => pure counts
              | none => throwError "unknown inductive")
        | none => pure none
      catch _ =>
        pure none
      match results? with
      | some results =>
          IO.println s!"LEAN_INDUCTIVE_CONSTRUCTOR_FIELD_SLOT_COUNTS:{(Json.mkObj [("inductives", Json.arr results)]).compress}"
      | none =>
          IO.println "LEAN_INDUCTIVE_CONSTRUCTOR_FIELD_SLOT_COUNTS_ERROR"
  | `(#type_witness_payload_safety $declarations:str) => do
      let requested? := parseTypeWitnessPayloadRequests declarations.getString
      let results? ← try
        match requested? with
        | some requested =>
            some <$> liftTermElabM (requested.mapM fun declarationName => do
              let witnesses? ← typeWitnessPayloadReceiptsForDeclaration declarationName
              match witnesses? with
              | some witnesses => pure <| Json.mkObj [
                  ("declaration", Json.str declarationName.toString),
                  ("witnesses", Json.arr witnesses)]
              | none => throwError "unknown reviewed declaration")
        | none => pure none
      catch _ =>
        pure none
      match results? with
      | some results =>
          IO.println s!"LEAN_TYPE_WITNESS_PAYLOAD_SAFETY:{(Json.mkObj [("declarations", Json.arr results)]).compress}"
      | none =>
          IO.println "LEAN_TYPE_WITNESS_PAYLOAD_SAFETY_ERROR"
end AppliedModelingLibAudit.SignatureManifest
