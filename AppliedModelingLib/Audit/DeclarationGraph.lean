import Lean
import Lean.Util.CollectAxioms
import AppliedModelingLib.Audit.SignatureManifest

/-!
# Lean-owned closeout declaration graph

This deliberately small module is the native post-elaboration discovery
boundary for paper closeout.  It answers environment questions in one loaded
paper process instead of making Python parse Lean source or launching one
process per question.  Python supplies qualified routing coordinates and
validates the typed response; it never infers semantic dependencies from
source spelling.
-/

open Lean Meta Elab Command

namespace AppliedModelingLibAudit.DeclarationGraph

structure SemanticContract where
  specification : Name
  evidence : Name
  mode : String
deriving BEq

structure InventoryRequest where
  inventoryModules : Array Name
  paperModules : Array Name
  workspaceModules : Array Name
  foundationModules : Array Name
  foundationPolicyId : String
  foundationRegistrySha256 : String
  promotedFoundationDeclarations : Array Name
  specifications : Array Name
  semanticDeclarations : Array Name
  proofPairs : Array (Name × Name)
  semanticContracts : Array SemanticContract
  axiomRoots : Array Name
  semanticSignatureDeclarations : Array Name
  semanticReviewClaimDeclarations : Array Name
  semanticManifestDeclarations : Array Name
  rootSemanticManifestDeclarations : Array Name
  semanticRevalidationDeclarations : Array Name
  semanticManifestModules : Array Name
  semanticHashToolPath : String
  includeSemanticDisplays : Bool
  includeAxiomClosure : Bool

private def parseNames (value : Json) : Option (Array Name) := do
  let .arr values := value | failure
  let mut names : Array Name := #[]
  for value in values do
    let raw ← value.getStr?.toOption
    guard (!raw.isEmpty)
    let name := raw.toName
    guard (!names.contains name)
    names := names.push name
  pure <| names.qsort fun left right => left.toString < right.toString

private def parseProofPairs (value : Json) : Option (Array (Name × Name)) := do
  let .arr values := value | failure
  let mut pairs : Array (Name × Name) := #[]
  for value in values do
    let specification ← (value.getObjVal? "specification").toOption
      >>= (fun item => item.getStr?.toOption)
    let proof ← (value.getObjVal? "proof").toOption
      >>= (fun item => item.getStr?.toOption)
    guard (!specification.isEmpty && !proof.isEmpty)
    let pair := (specification.toName, proof.toName)
    guard (!pairs.contains pair)
    pairs := pairs.push pair
  pure <| pairs.qsort fun left right =>
    left.1.toString < right.1.toString ||
      (left.1 == right.1 && left.2.toString < right.2.toString)

private def parseSemanticContracts (value : Json) : Option (Array SemanticContract) := do
  let .arr values := value | failure
  let mut contracts : Array SemanticContract := #[]
  for value in values do
    let specification ← (value.getObjVal? "specification").toOption
      >>= (fun item => item.getStr?.toOption)
    let evidence ← (value.getObjVal? "evidence").toOption
      >>= (fun item => item.getStr?.toOption)
    let mode ← (value.getObjVal? "mode").toOption
      >>= (fun item => item.getStr?.toOption)
    guard (!specification.isEmpty && !evidence.isEmpty)
    guard (mode == "proves" || mode == "refutes" ||
      mode == "definitionally_realizes")
    let contract := {
      specification := specification.toName
      evidence := evidence.toName
      mode }
    guard (!contracts.contains contract)
    contracts := contracts.push contract
  pure <| contracts.qsort fun left right =>
    left.specification.toString < right.specification.toString ||
      (left.specification == right.specification &&
        (left.evidence.toString < right.evidence.toString ||
          (left.evidence == right.evidence && left.mode < right.mode)))

private def parseRequest (raw : String) : Option InventoryRequest := do
  let value ← (Json.parse raw).toOption
  let inventoryModules ← parseNames <| ←
    (value.getObjVal? "inventory_modules").toOption
  let paperModules ← parseNames <| ←
    (value.getObjVal? "paper_modules").toOption
  let workspaceModules ← parseNames <| ←
    (value.getObjVal? "workspace_modules").toOption
  let foundationModules ← parseNames <| ←
    (value.getObjVal? "foundation_modules").toOption
  let foundationPolicyId ← (←
    (value.getObjVal? "foundation_policy_id").toOption).getStr?.toOption
  let foundationRegistrySha256 ← (←
    (value.getObjVal? "foundation_registry_sha256").toOption).getStr?.toOption
  let promotedFoundationDeclarations ← parseNames <| ←
    (value.getObjVal? "promoted_foundation_declarations").toOption
  let specifications ← parseNames <| ←
    (value.getObjVal? "specifications").toOption
  let semanticDeclarations ← parseNames <| ←
    (value.getObjVal? "semantic_declarations").toOption
  let proofPairs ← parseProofPairs <| ←
    (value.getObjVal? "proof_pairs").toOption
  let semanticContracts ← parseSemanticContracts <| ←
    (value.getObjVal? "semantic_contracts").toOption
  let axiomRoots ← parseNames <| ←
    (value.getObjVal? "axiom_roots").toOption
  let semanticSignatureDeclarations ← parseNames <| ←
    (value.getObjVal? "semantic_signature_declarations").toOption
  let semanticReviewClaimDeclarations ← parseNames <| ←
    (value.getObjVal? "semantic_review_claim_declarations").toOption
  let semanticManifestDeclarations ← parseNames <| ←
    (value.getObjVal? "semantic_manifest_declarations").toOption
  let rootSemanticManifestDeclarations ← parseNames <| ←
    (value.getObjVal? "root_semantic_manifest_declarations").toOption
  let semanticRevalidationDeclarations ← parseNames <| ←
    (value.getObjVal? "semantic_revalidation_declarations").toOption
  let semanticManifestModules ← parseNames <| ←
    (value.getObjVal? "semantic_manifest_modules").toOption
  let semanticHashToolPath ← (←
    (value.getObjVal? "semantic_hash_tool_path").toOption).getStr?.toOption
  let includeSemanticDisplays ← (←
    (value.getObjVal? "include_semantic_displays").toOption).getBool?.toOption
  let includeAxiomClosure ← (←
    (value.getObjVal? "include_axiom_closure").toOption).getBool?.toOption
  guard (!paperModules.isEmpty)
  guard (inventoryModules.all paperModules.contains)
  guard (paperModules.all workspaceModules.contains)
  guard (!foundationModules.isEmpty)
  guard (!foundationPolicyId.isEmpty)
  guard (foundationRegistrySha256.length == 64 &&
    foundationRegistrySha256.all fun character =>
      character.isDigit || ('a' ≤ character && character ≤ 'f'))
  guard ((semanticSignatureDeclarations.isEmpty &&
      semanticReviewClaimDeclarations.isEmpty &&
      semanticManifestDeclarations.isEmpty &&
      rootSemanticManifestDeclarations.isEmpty &&
      semanticRevalidationDeclarations.isEmpty) || !semanticHashToolPath.isEmpty)
  pure {
    inventoryModules
    paperModules
    workspaceModules
    foundationModules
    foundationPolicyId
    foundationRegistrySha256
    promotedFoundationDeclarations
    specifications
    semanticDeclarations
    proofPairs
    semanticContracts
    axiomRoots
    semanticSignatureDeclarations
    semanticReviewClaimDeclarations
    semanticManifestDeclarations
    rootSemanticManifestDeclarations
    semanticRevalidationDeclarations
    semanticManifestModules
    semanticHashToolPath
    includeSemanticDisplays
    includeAxiomClosure }

private def declarationModuleName? (name : Name) : MetaM (Option Name) := do
  let env ← getEnv
  pure <| (env.getModuleIdxFor? name).map fun moduleIdx =>
    env.header.moduleNames[moduleIdx.toNat]!

private def rangeJson (ranges : DeclarationRanges) : Json :=
  Json.mkObj [
    ("line_start", Json.num ranges.range.pos.line),
    ("column_start", Json.num ranges.range.pos.column),
    ("line_end", Json.num ranges.range.endPos.line),
    ("column_end", Json.num ranges.range.endPos.column)]

private def positionLE (left right : Position) : Bool :=
  left.line < right.line ||
    (left.line == right.line && left.column ≤ right.column)

private def rangeContains (outer inner : DeclarationRange) : Bool :=
  positionLE outer.pos inner.pos && positionLE inner.endPos outer.endPos

/-- Collapse compiler-generated children to their source-presented inductive
or structure owner using Lean metadata and Lean's declaration-range extension.
Constructors, recursors, and projections have explicit environment metadata.
A generated declaration with a source range can inherit the unique same-module
inductive whose Lean-reported source range contains it.  A range-less
transparent definition remains its own direct review declaration rather than
receiving an owner from its spelling.  All other declarations remain
independently visible, and ambiguous containment fails closed. -/
def reviewOwner (declaration : Name) : MetaM Name := do
  let env ← getEnv
  match env.find? declaration with
  | some (.ctorInfo constructorInfo) => pure constructorInfo.induct
  | some (.recInfo recursorInfo) =>
      match recursorInfo.rules.head? with
      | some rule =>
          match env.find? rule.ctor with
          | some (.ctorInfo constructorInfo) => pure constructorInfo.induct
          | _ => pure declaration
      | none => pure declaration
  | _ =>
      match env.getProjectionFnInfo? declaration with
      | some projectionInfo =>
          match env.find? projectionInfo.ctorName with
          | some (.ctorInfo constructorInfo) => pure constructorInfo.induct
          | _ => pure declaration
      | none =>
          let declarationRanges? ← findDeclarationRanges? declaration
          let declarationModule? ← declarationModuleName? declaration
          let containingInductiveOwner : MetaM (Option Name) := do
            let some declarationRanges := declarationRanges? | return none
            let some declarationModule := declarationModule? | return none
            let some moduleIdx := env.header.moduleNames.findIdx? (fun candidate =>
                candidate == declarationModule) | return none
            let entries := declRangeExt.getModuleEntries (level := .server) env moduleIdx
            let mut candidates : Array Name := #[]
            for (candidate, _) in entries do
              if candidate != declaration then
                match env.find? candidate with
                | some (.inductInfo _) =>
                    match ← findDeclarationRanges? candidate with
                    | some ownerRanges =>
                        if rangeContains ownerRanges.range declarationRanges.range &&
                            !candidates.contains candidate then
                          candidates := candidates.push candidate
                    | none => pure ()
                | _ => pure ()
            pure <| if candidates.size == 1 then candidates[0]? else none
          pure <| (← containingInductiveOwner).getD declaration

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def directDependencies (info : ConstantInfo) : MetaM (Array (String × Name)) := do
  let mut dependencies := info.type.getUsedConstantsAsSet.toArray.map fun name =>
    ("type_uses_constant", name)
  match info with
  | .defnInfo definition =>
      dependencies := dependencies ++ definition.value.getUsedConstantsAsSet.toArray.map
        fun name => ("value_uses_constant", name)
  | .thmInfo theoremInfo =>
      dependencies := dependencies ++ theoremInfo.value.getUsedConstantsAsSet.toArray.map
        fun name => ("proof_uses_constant", name)
  | .inductInfo inductiveInfo =>
      for constructor in inductiveInfo.ctors do
        let constructorInfo ← getConstInfo constructor
        dependencies := dependencies ++ constructorInfo.type.getUsedConstantsAsSet.toArray.map
          fun name => ("constructor_type_uses_constant", name)
  | _ => pure ()
  pure dependencies

private def dependencyJson
    (paperModules : Array Name) (role : String) (dependency : Name) : MetaM Json := do
  let owner ← reviewOwner dependency
  let moduleName? ← declarationModuleName? owner
  pure <| Json.mkObj [
    ("role", Json.str role),
    ("declaration", Json.str dependency.toString),
    ("review_owner_declaration", Json.str owner.toString),
    ("module", Json.str <| moduleName?.map Name.toString |>.getD ""),
    ("paper_owned", Json.bool <| moduleName?.any paperModules.contains)]

private def node
    (paperModules axiomRoots : Array Name) (declaration : Name) : MetaM Json := do
  let info ← getConstInfo declaration
  let owner ← reviewOwner declaration
  let moduleName? ← declarationModuleName? declaration
  let ownerModuleName? ← declarationModuleName? owner
  let ranges? ← findDeclarationRanges? declaration
  let ownerRanges? ← findDeclarationRanges? owner
  let dependencies := (← directDependencies info).qsort fun left right =>
    left.1 < right.1 || (left.1 == right.1 && left.2.toString < right.2.toString)
  let mut rows : Array Json := #[]
  let mut previous : Option (String × Name) := none
  for dependencyEntry in dependencies do
    let (role, dependency) := dependencyEntry
    if previous != some dependencyEntry && dependency != declaration then
      rows := rows.push <| ← dependencyJson paperModules role dependency
    previous := some dependencyEntry
  let valueHasSorry := (info.value? true).any Expr.hasSorry
  let axioms := (← if axiomRoots.contains declaration then
    collectAxioms declaration
  else
    pure #[]).qsort fun left right => left.toString < right.toString
  pure <| Json.mkObj [
    ("declaration", Json.str declaration.toString),
    ("review_owner_declaration", Json.str owner.toString),
    ("generated_from_owner", Json.bool <| owner != declaration),
    ("module", Json.str <| moduleName?.map Name.toString |>.getD ""),
    ("owner_module", Json.str <| ownerModuleName?.map Name.toString |>.getD ""),
    ("paper_owned", Json.bool <| moduleName?.any paperModules.contains),
    ("declaration_kind", Json.str <| declarationKind info),
    ("is_unsafe", Json.bool info.isUnsafe),
    ("is_transparent_definition", Json.bool <| match info with
      | .defnInfo _ => true | _ => false),
    ("is_opaque", Json.bool <| match info with
      | .opaqueInfo _ => true | _ => false),
    ("is_axiom", Json.bool <| match info with
      | .axiomInfo _ => true | _ => false),
    ("value_has_sorry", Json.bool valueHasSorry),
    ("source_presented", Json.bool <| owner == declaration && ranges?.isSome),
    ("source_range", ranges?.map rangeJson |>.getD Json.null),
    ("owner_source_range", ownerRanges?.map rangeJson |>.getD Json.null),
    ("type_display", Json.str ((← ppExpr info.type).pretty)),
    ("direct_dependencies", Json.arr rows),
    ("axiom_closure_checked", Json.bool <| axiomRoots.contains declaration),
    ("axiom_closure", Json.arr <| axioms.map fun name => Json.str name.toString)]

private def sourceDeclarations
    (modules : Array Name) : MetaM (Array Name × Nat × Nat) := do
  let env ← getEnv
  let mut declarations : Array Name := #[]
  let mut rangeEntryCount := 0
  let mut generatedCount := 0
  for moduleName in modules do
    let some moduleIdx := env.header.moduleNames.findIdx? (fun candidate =>
        candidate == moduleName) |
      throwError "declaration inventory module is not imported: {moduleName}"
    let entries := declRangeExt.getModuleEntries (level := .server) env moduleIdx
    rangeEntryCount := rangeEntryCount + entries.size
    for (declaration, _) in entries do
      let owner ← reviewOwner declaration
      if owner != declaration then generatedCount := generatedCount + 1
      if !declarations.contains owner then
        let ownerModule? ← declarationModuleName? owner
        let ownerRanges? ← findDeclarationRanges? owner
        if ownerModule?.any modules.contains && ownerRanges?.isSome then
          declarations := declarations.push owner
  pure (
    declarations.qsort fun left right => left.toString < right.toString,
    rangeEntryCount,
    generatedCount)

private def appendName (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name

/-- Keep material lambda domains visible in the source-review display.  The
ordinary delaborator may print `∃ witness, ...` while inferring the witness type
from the elaborated `Exists` application; that can hide source conditions
carried by a dependent witness type. -/
private def ppSemanticReviewExpr (expression : Expr) : MetaM String := do
  let rendered ← withOptions (fun options =>
    options.setBool `pp.funBinderTypes true |>
      (fun options => options.setBool `pp.letVarTypes true) |>
      (fun options => options.setBool `pp.proofs true)) <|
    ppExpr expression
  pure rendered.pretty

private def declarationIsOwnedByPaper
    (paperModules : Array Name) (name : Name) : MetaM Bool := do
  let moduleName? ← declarationModuleName? name
  pure <| moduleName?.any paperModules.contains

private def declarationIsOwnedByWorkspace
    (workspaceModules : Array Name) (name : Name) : MetaM Bool := do
  let moduleName? ← declarationModuleName? name
  pure <| moduleName?.any workspaceModules.contains

private def partitionSemanticDeclarations
    (paperModules workspaceModules declarations : Array Name) :
    MetaM (Array Name × Array Name) := do
  let mut paperRoots : Array Name := #[]
  let mut libraryRoots : Array Name := #[]
  for requested in declarations do
    let owner ← reviewOwner requested
    if ← declarationIsOwnedByPaper paperModules owner then
      paperRoots := appendName paperRoots owner
    else if ← declarationIsOwnedByWorkspace workspaceModules owner then
      libraryRoots := appendName libraryRoots owner
    else
      throwError "source-semantic declaration is not owned by the frozen repository import closure: {owner}"
  pure (
    paperRoots.qsort fun left right => left.toString < right.toString,
    libraryRoots.qsort fun left right => left.toString < right.toString)

private structure DisplayDependencies where
  paperDeclarations : Array Name := #[]
  libraryDeclarations : Array Name := #[]
  erasedProofValues : Array Name := #[]

private partial def workspaceDeclarationsInDisplay
    (paperModules workspaceModules explicitSemanticRoots : Array Name)
    (expression : Expr) : MetaM DisplayDependencies := do
  -- Proof terms must remain in Lean's proof and axiom closure, but an ordinary
  -- proved helper is not a second source-semantic concept merely because a
  -- definition carries it as a proof argument.  Erase only that proof value
  -- from the human semantic frontier and recursively traverse its complete
  -- proposition type instead.  A theorem selected by an exact source route is
  -- preserved regardless of declaration kind.  Axioms and opaque constants
  -- are never erased, so an unproved or external boundary remains visible.
  let mut pending := expression.getUsedConstantsAsSet.toArray
  let mut visited : Array Name := #[]
  let mut paperDeclarations : Array Name := #[]
  let mut libraryDeclarations : Array Name := #[]
  let mut erasedProofValues : Array Name := #[]
  while !pending.isEmpty do
    let requested := pending[0]!
    pending := pending.extract 1 pending.size
    if !requested.isAnonymous && !visited.contains requested then
      visited := visited.push requested
      if ← declarationIsOwnedByWorkspace workspaceModules requested then
        let owner ← reviewOwner requested
        visited := appendName visited owner
        if ← declarationIsOwnedByWorkspace workspaceModules owner then
          let info ← getConstInfo owner
          let paperOwned ← declarationIsOwnedByPaper paperModules owner
          if explicitSemanticRoots.contains owner then
            if paperOwned then
              paperDeclarations := appendName paperDeclarations owner
            else
              libraryDeclarations := appendName libraryDeclarations owner
          else
            match info with
            | .defnInfo definition =>
                -- A transparent workspace definition without a Lean source
                -- range is compiler lowering, not an authored semantic
                -- declaration.  It cannot become a human card.  Lean still
                -- follows its elaborated type and value to source-presented
                -- declarations, so this is graph discovery rather than a
                -- display-normalization exception.
                if (← findDeclarationRanges? owner).isNone then
                  for dependency in definition.type.getUsedConstantsAsSet.toArray do
                    if !visited.contains dependency && !pending.contains dependency then
                      pending := pending.push dependency
                  for dependency in definition.value.getUsedConstantsAsSet.toArray do
                    if !visited.contains dependency && !pending.contains dependency then
                      pending := pending.push dependency
                else if paperOwned then
                  paperDeclarations := appendName paperDeclarations owner
                else
                  libraryDeclarations := appendName libraryDeclarations owner
            | .thmInfo theoremInfo =>
                erasedProofValues := appendName erasedProofValues owner
                -- Proof values are not human semantic cards.  Their elaborated
                -- proposition type may nevertheless contain a material model
                -- declaration, so Lean follows that exact type directly.  Do
                -- not unfold it through repository-defined display policy.
                for dependency in theoremInfo.type.getUsedConstantsAsSet.toArray do
                  if !visited.contains dependency && !pending.contains dependency then
                    pending := pending.push dependency
            | _ =>
                if paperOwned then
                  paperDeclarations := appendName paperDeclarations owner
                else
                  libraryDeclarations := appendName libraryDeclarations owner
  pure {
    paperDeclarations := paperDeclarations.qsort fun left right =>
      left.toString < right.toString
    libraryDeclarations := libraryDeclarations.qsort fun left right =>
      left.toString < right.toString
    erasedProofValues := erasedProofValues.qsort fun left right =>
      left.toString < right.toString }

private def workspaceDeclarationsInDisplays
    (paperModules workspaceModules explicitSemanticRoots : Array Name)
    (expressions : Array Expr) :
    MetaM DisplayDependencies := do
  let mut result : DisplayDependencies := {}
  for expression in expressions do
    let current ← workspaceDeclarationsInDisplay paperModules workspaceModules
      explicitSemanticRoots expression
    for declaration in current.paperDeclarations do
      result := { result with
        paperDeclarations := appendName result.paperDeclarations declaration }
    for declaration in current.libraryDeclarations do
      result := { result with
        libraryDeclarations := appendName result.libraryDeclarations declaration }
    for declaration in current.erasedProofValues do
      result := { result with
        erasedProofValues := appendName result.erasedProofValues declaration }
  pure {
    paperDeclarations := result.paperDeclarations.qsort fun left right =>
      left.toString < right.toString
    libraryDeclarations := result.libraryDeclarations.qsort fun left right =>
      left.toString < right.toString
    erasedProofValues := result.erasedProofValues.qsort fun left right =>
      left.toString < right.toString }

private structure SpecificationDisplayResult where
  payload : Json
  directBody : Expr

private def specDisplay
    (specification : Name)
    (paperModules workspaceModules semanticTerminals explicitLibrarySemanticRoots : Array Name) :
    MetaM SpecificationDisplayResult :=
  withNewMCtxDepth do
    let info ← getConstInfo specification
    let .defnInfo definition := info |
      throwError "semantic-review target is not a transparent definition: {specification}"
    forallTelescopeReducing info.type fun binders result => do
      unless ← isDefEq result (mkSort .zero) do
        throwError "semantic-review target is not proposition-valued: {specification}"
      -- The PaperInterface must deliberately write a bounded semantic body.
      -- Render that direct body once and let the Lean-owned graph enumerate
      -- any remaining material declarations as separate prerequisite cards.
      -- A renderer must not recursively unfold implementation definitions to
      -- make an opaque or oversized interface look source-like.
      let directBody ← mkForallFVars binders (mkAppN definition.value binders).headBeta
      let dependencies ← workspaceDeclarationsInDisplay paperModules workspaceModules
        (semanticTerminals ++ explicitLibrarySemanticRoots) directBody
      let payload := Json.mkObj [
        ("specification", Json.str specification.toString),
        ("complete", Json.bool true),
        -- The root `Spec` body is shown directly.  This legacy-shaped field
        -- records that one direct declaration body, not recursive reduction.
        ("expansion_count", Json.str "1"),
        ("expanded_declarations", Json.arr <|
          #[Json.str specification.toString]),
        ("prerequisite_declarations", Json.arr <|
          dependencies.paperDeclarations.qsort (fun left right =>
            left.toString < right.toString) |>.map fun name => Json.str name.toString),
        ("library_declarations", Json.arr <|
          dependencies.libraryDeclarations.map fun name => Json.str name.toString),
        ("erased_proof_declarations", Json.arr <|
          dependencies.erasedProofValues.map fun name => Json.str name.toString),
        ("blocked_declarations", Json.arr #[]),
        ("display", Json.str (← ppSemanticReviewExpr directBody))]
      pure { payload, directBody }

/-- Render the named projection surface of a Lean structure.

The constructor telescope alone preserves a structure's field types but loses
the field labels that connect a source-model record to the symbols used in a
paper.  Lean's elaborated `StructureInfo` supplies both the ordered field names
and their exact projection declarations, without parsing source text. -/
private def structureFieldDisplays (structureName : Name) : MetaM (Array (String × Expr)) := do
  let env ← getEnv
  let some structureInfo := getStructureInfo? env structureName | pure #[]
  let mut displays : Array (String × Expr) := #[]
  for index in [:structureInfo.fieldNames.size] do
    let fieldName := structureInfo.fieldNames[index]!
    let some projectionName := structureInfo.getProjFn? index
      | throwError "structure field projection is unavailable: {structureName}.{fieldName}"
    let projectionInfo ← getConstInfo projectionName
    displays := displays.push
      (s!"field {fieldName}:\n{(← ppSemanticReviewExpr projectionInfo.type)}",
        projectionInfo.type)
  pure displays

private def directDeclarationDisplay
    (declaration : Name) :
    MetaM (String × String × Array Expr × Bool) := do
  -- Materiality is selected by the Lean-owned semantic traversal before this
  -- renderer is called.  Once selected, a review row must have a stable name
  -- that another module and a human-facing packet can address.  Lean private
  -- and compiler-internal names are intentionally unstable under unrelated
  -- source edits; fail here instead of letting Python infer this condition
  -- from spelling or preserve an unauditable `_private` card.
  if declaration.isInternalDetail then
    throwError "material semantic declaration is private or compiler-internal and cannot be a stable review target: {declaration}; refactor it as a named non-private declaration, or classify it out of the material semantic surface by its actual role"
  let info ← getConstInfo declaration
  match info with
  | .defnInfo definition =>
      forallTelescopeReducing info.type fun binders result => do
        let typeExpression ← mkForallFVars binders result
        let body := (mkAppN definition.value binders).headBeta
        let valueExpression ← mkLambdaFVars binders body
        pure (
          "definition",
          s!"type:\n{(← ppSemanticReviewExpr typeExpression)}\n\nvalue:\n{(← ppSemanticReviewExpr valueExpression)}",
          #[typeExpression, valueExpression],
          true)
  | .opaqueInfo _ =>
      pure ("opaque_definition", (← ppSemanticReviewExpr info.type), #[info.type], false)
  | .inductInfo inductiveInfo =>
      let fieldDisplays ← structureFieldDisplays declaration
      if !fieldDisplays.isEmpty then
        -- A structure's constructor telescope redundantly concatenates every
        -- field and can trigger printer elision even when each labeled field
        -- is fully readable.  The projection surface below is complete and
        -- more useful to a source-model reviewer, so use it as the direct
        -- display rather than preserving that redundant aggregate telescope.
        pure (
          "non_definition",
          String.intercalate "\n\n" (fieldDisplays.map Prod.fst).toList,
          fieldDisplays.map Prod.snd,
          false)
      else
        let outer := info.type
        let mut expressions := #[outer]
        let mut parts := #[s!"type:\n{(← ppSemanticReviewExpr outer)}"]
        for constructorName in inductiveInfo.ctors do
          let constructorInfo ← getConstInfo constructorName
          let constructorType := constructorInfo.type
          expressions := expressions.push constructorType
          parts := parts.push s!"constructor {constructorName}:\n{(← ppSemanticReviewExpr constructorType)}"
        pure (
          "non_definition",
          String.intercalate "\n\n" parts.toList,
          expressions,
          false)
  | _ =>
      pure ("non_definition", (← ppSemanticReviewExpr info.type), #[info.type], false)

private def paperDeclarationDisplay
    (declaration : Name)
    (paperModules workspaceModules explicitSemanticRoots : Array Name) :
    MetaM Json :=
  withNewMCtxDepth do
    let (kind, display, dependencyExpressions, rootExpanded) ←
      directDeclarationDisplay declaration
    let dependencies ←
      workspaceDeclarationsInDisplays paperModules workspaceModules
        explicitSemanticRoots dependencyExpressions
    pure <| Json.mkObj [
      ("declaration", Json.str declaration.toString),
      ("declaration_kind", Json.str kind),
      ("root_expanded", Json.bool rootExpanded),
      ("direct_paper_declarations", Json.arr <|
        (dependencies.paperDeclarations.filter fun name => name != declaration).map
          fun name => Json.str name.toString),
      ("direct_library_declarations", Json.arr <|
        dependencies.libraryDeclarations.map fun name => Json.str name.toString),
      ("erased_proof_declarations", Json.arr <|
        dependencies.erasedProofValues.map fun name => Json.str name.toString),
      ("display", Json.str display)]

private def namesInField (item : Json) (field : String) : Array Name :=
  match (item.getObjVal? field).toOption with
  | some (.arr values) => values.foldl (init := #[]) fun names value =>
      match value.getStr?.toOption with
      | some raw => if names.contains raw.toName then names else names.push raw.toName
      | none => names
  | _ => #[]

private def namesFromItemsField (payload : Json) (field : String) : Array Name :=
  match (payload.getObjVal? "items").toOption with
  | some (.arr items) => items.foldl (init := #[]) fun names item =>
      (names ++ namesInField item field).foldl (init := #[]) fun unique name =>
        if unique.contains name then unique else unique.push name
  | _ => #[]

private def displayName (item : Json) : String :=
  ((item.getObjVal? "declaration").toOption.bind (fun value =>
    value.getStr?.toOption)).getD ""

private def declarationNamesFromItems (payload : Json) : Array Name :=
  match (payload.getObjVal? "items").toOption with
  | some (.arr items) => items.foldl (init := #[]) fun names item =>
      let raw := displayName item
      if raw.isEmpty then names
      else
        let name := raw.toName
        if names.contains name then names else names.push name
  | _ => #[]

private def paperDeclarationDisplays
    (roots paperModules workspaceModules explicitSemanticRoots : Array Name) :
    MetaM Json := do
  let mut pending := roots
  let mut visited : Array Name := #[]
  let mut items : Array Json := #[]
  while !pending.isEmpty && visited.size < 512 do
    let declaration := pending[0]!
    pending := pending.extract 1 pending.size
    if !visited.contains declaration then
      let item ← paperDeclarationDisplay declaration paperModules workspaceModules
        explicitSemanticRoots
      visited := visited.push declaration
      items := items.push item
      for dependency in namesInField item "direct_paper_declarations" do
        if !visited.contains dependency && !pending.contains dependency then
          pending := pending.push dependency
  unless pending.isEmpty do
    throwError "paper semantic-prerequisite closure exceeds 512 declarations"
  pure <| Json.mkObj [
    ("schema", Json.str "2"),
    ("items", Json.arr <| items.qsort fun left right =>
      displayName left < displayName right)]

private def libraryDeclarationDisplay
    (declaration : Name)
    (paperModules workspaceModules explicitSemanticRoots : Array Name) : MetaM Json :=
  withNewMCtxDepth do
    let owner ← reviewOwner declaration
    let some sourceModule ← findModuleOf? owner |
      throwError "could not identify source module for {owner}"
    let some sourceRanges ← findDeclarationRanges? owner |
      throwError "could not identify source range for {owner}"
    let (kind, display, dependencyExpressions, rootExpanded) ←
      directDeclarationDisplay owner
    let dependencies ←
      workspaceDeclarationsInDisplays paperModules workspaceModules
        explicitSemanticRoots dependencyExpressions
    let directDependencies := (dependencies.libraryDeclarations.filter fun dependency =>
      dependency != owner).qsort
          fun left right => left.toString < right.toString
    pure <| Json.mkObj [
      ("declaration", Json.str owner.toString),
      ("review_owner_declaration", Json.str owner.toString),
      ("source_module", Json.str sourceModule.toString),
      ("source_line_start", Json.num sourceRanges.range.pos.line),
      ("source_column_start", Json.num sourceRanges.range.pos.column),
      ("source_line_end", Json.num sourceRanges.range.endPos.line),
      ("source_column_end", Json.num sourceRanges.range.endPos.column),
      ("declaration_kind", Json.str kind),
      ("root_expanded", Json.bool rootExpanded),
      ("direct_library_declarations", Json.arr <|
        directDependencies.map fun name => Json.str name.toString),
      ("erased_proof_declarations", Json.arr <|
        dependencies.erasedProofValues.map fun name => Json.str name.toString),
      ("display", Json.str display)]

private def libraryDeclarationDisplays
    (roots explicitSemanticRoots paperModules workspaceModules : Array Name) : MetaM Json := do
  let mut pending := roots
  let mut visited : Array Name := #[]
  let mut items : Array Json := #[]
  while !pending.isEmpty && visited.size < 512 do
    let requested := pending[0]!
    pending := pending.extract 1 pending.size
    let declaration ← reviewOwner requested
    if !visited.contains declaration then
      let item ← libraryDeclarationDisplay declaration paperModules workspaceModules
        explicitSemanticRoots
      visited := visited.push declaration
      items := items.push item
      for dependency in namesInField item "direct_library_declarations" do
        if !visited.contains dependency && !pending.contains dependency then
          pending := pending.push dependency
  unless pending.isEmpty do
    throwError "library semantic-prerequisite closure exceeds 512 declarations"
  pure <| Json.mkObj [
    ("schema", Json.str "3"),
    ("items", Json.arr <| items.qsort fun left right =>
      displayName left < displayName right)]

/-! The foundation frontier is a preview, not an acceptance credential.  Lean
walks the already-normalized source-facing propositions, classifies constants
from compiled module ownership, and records any explicitly promoted imported
concepts.  Python may select qualified promotion roots and validate this typed
payload, but it does not discover or classify semantic dependencies. -/

private structure FrontierNames where
  material : Array Name := #[]
  erasedProofValues : Array Name := #[]

private partial def frontierNamesInExpressions
    (expressions : Array Expr) : MetaM FrontierNames := do
  let mut pending : Array Name := #[]
  for expression in expressions do
    for declaration in expression.getUsedConstantsAsSet.toArray do
      pending := appendName pending declaration
  let mut visited : Array Name := #[]
  let mut material : Array Name := #[]
  let mut erasedProofValues : Array Name := #[]
  while !pending.isEmpty do
    let declaration := pending[0]!
    pending := pending.extract 1 pending.size
    if !visited.contains declaration then
      visited := visited.push declaration
      let info? ← try
        some <$> getConstInfo declaration
      catch _ => pure none
      let proofValue ← match info? with
        | some _ => try
            let constant ← mkConstWithFreshMVarLevels declaration
            isProof constant
          catch _ => pure false
        | none => pure false
      if proofValue then
        erasedProofValues := appendName erasedProofValues declaration
        if let some info := info? then
          -- The proof implementation is irrelevant, but its complete
          -- proposition remains part of the semantic frontier.
          for dependency in info.type.getUsedConstantsAsSet.toArray do
            if !visited.contains dependency then
              pending := appendName pending dependency
      else
        let owner ← try reviewOwner declaration catch _ => pure declaration
        material := appendName material owner
  pure {
    material := material.qsort fun left right => left.toString < right.toString
    erasedProofValues := erasedProofValues.qsort fun left right =>
      left.toString < right.toString }

private structure FrontierPartition where
  foundation : Array Name := #[]
  paper : Array Name := #[]
  domain : Array Name := #[]
  unregistered : Array Name := #[]

private def foundationRootFor
    (foundationModules : Array Name) (moduleName : Name) : Option Name :=
  foundationModules.find? fun root => root.isPrefixOf moduleName

private def partitionFrontierNames
    (paperModules workspaceModules foundationModules declarations : Array Name) :
    MetaM FrontierPartition := do
  let mut partition : FrontierPartition := {}
  for declaration in declarations do
    let moduleName? ← declarationModuleName? declaration
    match moduleName? with
    | some moduleName =>
        if paperModules.contains moduleName then
          partition := { partition with
            paper := appendName partition.paper declaration }
        else if workspaceModules.contains moduleName then
          partition := { partition with
            domain := appendName partition.domain declaration }
        else if (foundationRootFor foundationModules moduleName).isSome then
          partition := { partition with
            foundation := appendName partition.foundation declaration }
        else
          partition := { partition with
            unregistered := appendName partition.unregistered declaration }
    | none =>
        partition := { partition with
          unregistered := appendName partition.unregistered declaration }
  pure {
    foundation := partition.foundation.qsort fun left right => left.toString < right.toString
    paper := partition.paper.qsort fun left right => left.toString < right.toString
    domain := partition.domain.qsort fun left right => left.toString < right.toString
    unregistered := partition.unregistered.qsort fun left right =>
      left.toString < right.toString }

private def frontierNameJson
    (foundationModules : Array Name) (declaration : Name) : MetaM Json := do
  let moduleName? ← declarationModuleName? declaration
  let packageRoot? := moduleName?.bind (foundationRootFor foundationModules)
  let kind ← try
    pure <| declarationKind (← getConstInfo declaration)
  catch _ => pure "unresolved"
  pure <| Json.mkObj [
    ("declaration", Json.str declaration.toString),
    ("module", Json.str <| moduleName?.map Name.toString |>.getD ""),
    ("package_root", Json.str <| packageRoot?.map Name.toString |>.getD ""),
    ("declaration_kind", Json.str kind)]

private def frontierNamesJson
    (foundationModules declarations : Array Name) : MetaM Json :=
  Json.arr <$> declarations.mapM (frontierNameJson foundationModules)

private structure FoundationPromotionDisplay where
  payload : Json
  declaration : Name
  directPromotedChildren : Array Name

private def foundationPromotionDisplay
    (request : InventoryRequest) (promoted directSpecRoots : Array Name)
    (declaration : Name) : MetaM FoundationPromotionDisplay :=
  withNewMCtxDepth do
    let owner ← reviewOwner declaration
    let some moduleName ← declarationModuleName? owner |
      throwError "promoted foundation declaration has no compiled module: {owner}"
    let some packageRoot := foundationRootFor request.foundationModules moduleName |
      throwError "promoted declaration is not owned by a registered foundation package: {owner}"
    let info ← getConstInfo owner
    let (kind, display, dependencyExpressions, rootExpanded) ← match info with
      | .defnInfo definition =>
          forallTelescopeReducing info.type fun binders _ => do
            let body := (mkAppN definition.value binders).headBeta
            let expression ← mkLambdaFVars binders body
            pure ("definition", (← ppSemanticReviewExpr expression), #[expression], true)
      | .inductInfo inductiveInfo =>
          let mut expressions := #[info.type]
          let mut parts := #[s!"type:\n{(← ppSemanticReviewExpr info.type)}"]
          for constructorName in inductiveInfo.ctors do
            let constructorInfo ← getConstInfo constructorName
            expressions := expressions.push constructorInfo.type
            parts := parts.push s!"constructor {constructorName}:\n{(← ppSemanticReviewExpr constructorInfo.type)}"
          pure ("inductive", String.intercalate "\n\n" parts.toList, expressions, false)
      | _ =>
          pure (declarationKind info, (← ppSemanticReviewExpr info.type), #[info.type], false)
    let names ← frontierNamesInExpressions dependencyExpressions
    let partition ← partitionFrontierNames
      request.paperModules request.workspaceModules request.foundationModules names.material
    let directFoundation := partition.foundation.filter fun dependency =>
      dependency != owner
    let directPromotedChildren := directFoundation.filter promoted.contains
    let payload := Json.mkObj [
      ("declaration", Json.str owner.toString),
      ("module", Json.str moduleName.toString),
      ("package_root", Json.str packageRoot.toString),
      ("declaration_kind", Json.str kind),
      ("root_expanded", Json.bool rootExpanded),
      ("direct_source_occurrence", Json.bool <| directSpecRoots.contains owner),
      ("direct_foundation_declarations", ←
        frontierNamesJson request.foundationModules directFoundation),
      ("direct_domain_declarations", ←
        frontierNamesJson request.foundationModules partition.domain),
      ("direct_paper_declarations", ←
        frontierNamesJson request.foundationModules partition.paper),
      ("unregistered_external_declarations", ←
        frontierNamesJson request.foundationModules partition.unregistered),
      ("erased_proof_values", ←
        frontierNamesJson request.foundationModules names.erasedProofValues),
      ("display", Json.str display)]
    pure { payload, declaration := owner, directPromotedChildren }

private def foundationFrontierPreview
    (request : InventoryRequest)
    (specificationDisplays : Array SpecificationDisplayResult) : MetaM Json := do
  let mut promoted : Array Name := #[]
  for requested in request.promotedFoundationDeclarations do
    let owner ← reviewOwner requested
    promoted := appendName promoted owner
  promoted := promoted.qsort fun left right => left.toString < right.toString
  if promoted.size > 200 then
    throwError "foundation semantic expansion exceeds 200 promoted declarations"

  let mut specificationRows : Array Json := #[]
  let mut directSpecRoots : Array Name := #[]
  let mut conventionalRoots : Array Name := #[]
  let mut domainRoots : Array Name := #[]
  let mut unregisteredRoots : Array Name := #[]
  let mut promotedOccurrenceCount := 0
  for (specification, result) in request.specifications.zip specificationDisplays do
    let names ← frontierNamesInExpressions #[result.directBody]
    let partition ← partitionFrontierNames
      request.paperModules request.workspaceModules request.foundationModules names.material
    let promotedHere := partition.foundation.filter promoted.contains
    let conventionalHere := partition.foundation.filter fun declaration =>
      !promoted.contains declaration
    promotedOccurrenceCount := promotedOccurrenceCount + promotedHere.size
    for declaration in promotedHere do
      directSpecRoots := appendName directSpecRoots declaration
    for declaration in conventionalHere do
      conventionalRoots := appendName conventionalRoots declaration
    for declaration in partition.domain do
      domainRoots := appendName domainRoots declaration
    for declaration in partition.unregistered do
      unregisteredRoots := appendName unregisteredRoots declaration
    specificationRows := specificationRows.push <| Json.mkObj [
      ("specification", Json.str specification.toString),
      ("conventional_foundation_occurrences", ←
        frontierNamesJson request.foundationModules conventionalHere),
      ("promoted_foundation_occurrences", ←
        frontierNamesJson request.foundationModules promotedHere),
      ("paper_semantic_roots", ←
        frontierNamesJson request.foundationModules partition.paper),
      ("domain_semantic_roots", ←
        frontierNamesJson request.foundationModules partition.domain),
      ("unregistered_external_occurrences", ←
        frontierNamesJson request.foundationModules partition.unregistered),
      ("erased_proof_values", ←
        frontierNamesJson request.foundationModules names.erasedProofValues)]

  let mut promotionRows : Array Json := #[]
  let mut promotionEdges : Array (Name × Array Name) := #[]
  for declaration in promoted do
    let result ← foundationPromotionDisplay request promoted directSpecRoots declaration
    promotionRows := promotionRows.push result.payload
    promotionEdges := promotionEdges.push
      (result.declaration, result.directPromotedChildren)

  -- Every configured expansion must be a direct source occurrence or be
  -- reached through another configured expansion.  This prevents a qualified
  -- name from silently manufacturing an unrelated review row.
  let mut depths : Array (Name × Nat) := directSpecRoots.map fun name => (name, 0)
  let mut changed := true
  while changed do
    changed := false
    for (parent, children) in promotionEdges do
      if let some (_, parentDepth) := depths.find? fun item => item.1 == parent then
        for child in children do
          if !(depths.any fun item => item.1 == child) then
            depths := depths.push (child, parentDepth + 1)
            changed := true
  let unreachable := promoted.filter fun declaration =>
    !(depths.any fun item => item.1 == declaration)
  unless unreachable.isEmpty do
    throwError "promoted foundation declaration is not reached by a selected Spec: {unreachable[0]!}"
  let maximumDepth := depths.foldl (init := 0) fun depth item => max depth item.2
  let reuseCount := promotedOccurrenceCount - directSpecRoots.size
  pure <| Json.mkObj [
    ("schema", Json.str "1"),
    ("acceptance_credential", Json.bool false),
    ("foundation_policy_id", Json.str request.foundationPolicyId),
    ("foundation_registry_sha256", Json.str request.foundationRegistrySha256),
    ("foundation_module_roots", Json.arr <|
      request.foundationModules.map fun name => Json.str name.toString),
    ("specifications", Json.arr specificationRows),
    ("promoted_expansions", Json.arr promotionRows),
    ("summary", Json.mkObj [
      ("specification_count", Json.num specificationRows.size),
      ("conventional_foundation_root_count", Json.num conventionalRoots.size),
      ("promoted_root_count", Json.num directSpecRoots.size),
      ("promoted_expansion_row_count", Json.num promotionRows.size),
      ("maximum_promoted_depth", Json.num maximumDepth),
      ("promoted_reuse_count", Json.num reuseCount),
      ("domain_root_count", Json.num domainRoots.size),
      ("unregistered_external_root_count", Json.num unregisteredRoots.size)])]

private def specProofMatches (specification proof : Name) : MetaM Bool := do
  let specificationInfo ← getConstInfo specification
  match specificationInfo with
  | .defnInfo _ | .inductInfo _ => pure ()
  | _ => return false
  let .thmInfo proofInfo ← getConstInfo proof | return false
  if specificationInfo.levelParams.length != proofInfo.levelParams.length then
    return false
  let levels := (List.range specificationInfo.levelParams.length).map fun index =>
    Level.param (Name.mkSimple s!"_econcs_inventory_universe_{index}")
  let specificationType ← inferType (mkConst specification levels)
  let proofType ← inferType (mkConst proof levels)
  forallTelescope specificationType fun binders result => do
    unless ← isDefEq result (mkSort .zero) do return false
    let expectedType ← mkForallFVars binders (mkAppN (mkConst specification levels) binders)
    withTransparency .all do isDefEq proofType expectedType

private def semanticContractMatches
    (specification evidence : Name) (refutes : Bool) : MetaM Bool := do
  let specificationInfo ← getConstInfo specification
  match specificationInfo with
  | .defnInfo _ | .inductInfo _ => pure ()
  | _ => return false
  let .thmInfo evidenceInfo ← getConstInfo evidence | return false
  if specificationInfo.levelParams.length != evidenceInfo.levelParams.length then
    return false
  let levels := (List.range specificationInfo.levelParams.length).map fun index =>
    Level.param (Name.mkSimple s!"_econcs_inventory_universe_{index}")
  let specificationType ← inferType (mkConst specification levels)
  let evidenceType ← inferType (mkConst evidence levels)
  forallTelescope specificationType fun binders result => do
    unless ← isDefEq result (mkSort .zero) do return false
    let body := mkAppN (mkConst specification levels) binders
    let expectedBody := if refutes then mkApp (mkConst ``Not) body else body
    let expectedType ← mkForallFVars binders expectedBody
    withTransparency .all do isDefEq evidenceType expectedType

private def semanticContractDefinitionallyRealizes
    (specification evidence : Name) : MetaM Bool := do
  let specificationInfo ← getConstInfo specification
  match specificationInfo with
  | .defnInfo _ | .inductInfo _ => pure ()
  | _ => return false
  let .thmInfo evidenceInfo ← getConstInfo evidence | return false
  if specificationInfo.levelParams.length != evidenceInfo.levelParams.length then
    return false
  let levels := (List.range specificationInfo.levelParams.length).map fun index =>
    Level.param (Name.mkSimple s!"_econcs_inventory_universe_{index}")
  let specificationConst := mkConst specification levels
  let evidenceType ← inferType (mkConst evidence levels)
  forallTelescope evidenceType fun binders result => do
    unless result.isAppOfArity ``Iff 2 do return false
    let body := mkAppN specificationConst binders
    let left := result.getArg! 0
    let right := result.getArg! 1
    withTransparency .all do
      return (← isDefEq left body) && (← isDefEq right body)

private def semanticContractDoesMatch (contract : SemanticContract) : MetaM Bool :=
  if contract.mode == "proves" || contract.mode == "refutes" then
    semanticContractMatches contract.specification contract.evidence
      (contract.mode == "refutes")
  else if contract.mode == "definitionally_realizes" then
    semanticContractDefinitionallyRealizes contract.specification contract.evidence
  else
    pure false

private def semanticResultSection
    (declarations : Array Name) (payloadField : String)
    (produce : Name → MetaM Json) : MetaM Json := do
  let mut items : Array Json := #[]
  let mut errors : Array Json := #[]
  for declaration in declarations do
    try
      let payload ← produce declaration
      items := items.push <| Json.mkObj [
        ("declaration", Json.str declaration.toString),
        (payloadField, payload)]
    catch exception =>
      errors := errors.push <| Json.mkObj [
        ("declaration", Json.str declaration.toString),
        ("message", Json.str <| ← exception.toMessageData.toString)]
  pure <| Json.mkObj [
    ("schema", Json.str "1"),
    ("items", Json.arr items),
    ("errors", Json.arr errors)]

private def inventory (request : InventoryRequest) : MetaM Json := do
  let (sourceNames, rangeEntryCount, generatedCount) ←
    sourceDeclarations request.inventoryModules
  -- First let Lean discover the exact semantic surface reached by the selected
  -- review claims.  Nodes are then emitted for that closure only.  Enumerating
  -- every declaration in every owning module both admits unrelated helpers to
  -- the audit denominator and makes a single review claim scale with the whole
  -- paper implementation rather than with its actual semantics.
  let (paperSemanticDeclarations, librarySemanticDeclarations) ←
    partitionSemanticDeclarations request.paperModules request.workspaceModules
      request.semanticDeclarations
  let specificationDisplayResults ← if request.includeSemanticDisplays then
    request.specifications.mapM fun specification =>
      specDisplay specification request.paperModules request.workspaceModules
        paperSemanticDeclarations librarySemanticDeclarations
  else
    pure #[]
  let specificationDisplays := specificationDisplayResults.map
    SpecificationDisplayResult.payload
  let specificationDisplaySection := Json.mkObj [
    ("schema", Json.str "2"), ("items", Json.arr specificationDisplays)]
  let foundationFrontier ← foundationFrontierPreview
    request specificationDisplayResults
  let paperRoots := (paperSemanticDeclarations ++
    namesFromItemsField specificationDisplaySection "prerequisite_declarations").foldl
      (init := #[]) fun names name => if names.contains name then names else names.push name
  let paperDisplays ← if request.includeSemanticDisplays && !paperRoots.isEmpty then
    paperDeclarationDisplays paperRoots request.paperModules request.workspaceModules
      (paperSemanticDeclarations ++ librarySemanticDeclarations)
  else
    pure <| Json.mkObj [("schema", Json.str "2"), ("items", Json.arr #[])]
  -- A transparent source-facing Spec can reach reusable definitions through a
  -- paper-local semantic prerequisite.  Close the library surface over those
  -- paper displays in this same Meta transaction; otherwise a later gate has
  -- to launch a second Lean pass merely to discover the omitted dependency.
  let libraryRoots := (librarySemanticDeclarations ++
    namesFromItemsField specificationDisplaySection "library_declarations" ++
    namesFromItemsField paperDisplays "direct_library_declarations").foldl
      (init := #[]) fun names name => if names.contains name then names else names.push name
  let libraryDisplays ←
    if request.includeSemanticDisplays && !libraryRoots.isEmpty then
      libraryDeclarationDisplays libraryRoots librarySemanticDeclarations
        request.paperModules request.workspaceModules
    else
      pure <| Json.mkObj [("schema", Json.str "3"), ("items", Json.arr #[])]
  let paperDisplayNames := declarationNamesFromItems paperDisplays
  let libraryDisplayNames := declarationNamesFromItems libraryDisplays
  let proofNames := request.proofPairs.map Prod.snd
  let contractEvidenceNames := request.semanticContracts.map fun contract =>
    contract.evidence
  let nodeNames := (sourceNames ++ request.specifications ++
    request.semanticDeclarations ++
    paperDisplayNames ++ libraryDisplayNames ++ request.axiomRoots ++
    contractEvidenceNames ++
    namesFromItemsField specificationDisplaySection "erased_proof_declarations" ++
    namesFromItemsField paperDisplays "erased_proof_declarations" ++
    namesFromItemsField libraryDisplays "erased_proof_declarations").foldl
      (init := #[]) fun names name => if names.contains name then names else names.push name
  let axiomRoots := if request.includeAxiomClosure then
    (request.specifications ++ proofNames ++ contractEvidenceNames ++
      request.axiomRoots).foldl (init := #[]) fun names name =>
      if names.contains name then names else names.push name
  else #[]
  let nodes ← (nodeNames.qsort fun left right =>
    left.toString < right.toString).mapM (node request.paperModules axiomRoots)
  let pairs ← request.proofPairs.mapM fun (specification, proof) => do
    let doesMatch ← specProofMatches specification proof
    let proofInfo ← getConstInfo proof
    let proofAxioms := (← if request.includeAxiomClosure then
      collectAxioms proof
    else
      pure #[]).qsort fun left right => left.toString < right.toString
    pure <| Json.mkObj [
      ("specification", Json.str specification.toString),
      ("proof", Json.str proof.toString),
      ("matches", Json.bool doesMatch),
      ("proof_is_unsafe", Json.bool proofInfo.isUnsafe),
      ("proof_value_has_sorry", Json.bool <| (proofInfo.value? true).any Expr.hasSorry),
      ("proof_axiom_closure_checked", Json.bool request.includeAxiomClosure),
      ("proof_axiom_closure", Json.arr <|
        proofAxioms.map fun name => Json.str name.toString)]
  let contracts ← request.semanticContracts.mapM fun contract => do
    let doesMatch ← semanticContractDoesMatch contract
    let evidenceInfo ← getConstInfo contract.evidence
    let evidenceAxioms := (← if request.includeAxiomClosure then
      collectAxioms contract.evidence
    else
      pure #[]).qsort fun left right => left.toString < right.toString
    pure <| Json.mkObj [
      ("specification", Json.str contract.specification.toString),
      ("evidence", Json.str contract.evidence.toString),
      ("mode", Json.str contract.mode),
      ("matches", Json.bool doesMatch),
      ("evidence_is_unsafe", Json.bool evidenceInfo.isUnsafe),
      ("evidence_value_has_sorry", Json.bool <| (evidenceInfo.value? true).any Expr.hasSorry),
      ("evidence_axiom_closure_checked", Json.bool request.includeAxiomClosure),
      ("evidence_axiom_closure", Json.arr <|
        evidenceAxioms.map fun name => Json.str name.toString)]
  let semanticManifests ← semanticResultSection
    request.semanticManifestDeclarations "manifest" fun declaration =>
      AppliedModelingLibAudit.SignatureManifest.declarationSemanticManifest
        declaration request.semanticManifestModules request.semanticHashToolPath
  -- Every declaration whose rendered semantics enters a source-to-Lean
  -- judgment also gets one Lean-owned, renderer-independent signature in the
  -- same transaction.  Discovered prerequisite names cannot be supplied by
  -- Python before this graph walk; Lean adds them only after owning the exact
  -- display closure above.
  let semanticSignatureDeclarations :=
    (request.semanticSignatureDeclarations ++
      request.semanticReviewClaimDeclarations ++
      paperDisplayNames ++ libraryDisplayNames).foldl
        (init := #[]) fun names name =>
          if names.contains name then names else names.push name
  let semanticSignatures ← semanticResultSection
    (semanticSignatureDeclarations.qsort fun left right =>
      left.toString < right.toString) "signature" fun declaration =>
      AppliedModelingLibAudit.SignatureManifest.declarationSemanticTargetSignature
        declaration request.semanticManifestModules request.semanticHashToolPath
  let semanticReviewClaims ← semanticResultSection
    request.semanticReviewClaimDeclarations "claim" fun declaration =>
      AppliedModelingLibAudit.SignatureManifest.declarationSemanticReviewClaim
        declaration request.semanticManifestModules request.semanticHashToolPath
  let rootSemanticManifests ← semanticResultSection
    request.rootSemanticManifestDeclarations "manifest" fun declaration =>
      AppliedModelingLibAudit.SignatureManifest.declarationSemanticManifest
        declaration #[] request.semanticHashToolPath
  let semanticRevalidations ← semanticResultSection
    request.semanticRevalidationDeclarations "receipt" fun declaration =>
      AppliedModelingLibAudit.SignatureManifest.declarationSemanticRevalidation
        declaration request.semanticManifestModules request.semanticHashToolPath
  pure <| Json.mkObj [
    ("schema", Json.str "4"),
    ("inventory_modules", Json.arr <|
      request.inventoryModules.map fun name => Json.str name.toString),
    ("paper_modules", Json.arr <|
      request.paperModules.map fun name => Json.str name.toString),
    ("workspace_modules", Json.arr <|
      request.workspaceModules.map fun name => Json.str name.toString),
    ("module_range_entry_count", Json.num rangeEntryCount),
    ("generated_constant_count", Json.num generatedCount),
    ("source_declarations", Json.arr <|
      sourceNames.map fun name => Json.str name.toString),
    ("declarations", Json.arr nodes),
    ("proof_pairs", Json.arr pairs),
    ("semantic_contracts", Json.arr contracts),
    ("semantic_signatures", semanticSignatures),
    ("semantic_review_claims", semanticReviewClaims),
    ("semantic_manifests", semanticManifests),
    ("root_semantic_manifests", rootSemanticManifests),
    ("semantic_revalidations", semanticRevalidations),
    ("foundation_frontier_preview", foundationFrontier),
    ("transparent_spec_displays", specificationDisplaySection),
    ("paper_prerequisite_displays", paperDisplays),
    ("library_prerequisite_displays", libraryDisplays)]

syntax (name := declarationGraphInventoryCmd)
  "#econcslib_declaration_inventory " str : command

elab_rules : command
  | `(#econcslib_declaration_inventory $request:str) => do
      let result? ← try
        match parseRequest request.getString with
        | some parsed => some <$> liftTermElabM (inventory parsed)
        | none => pure none
      catch exception =>
        let message ← exception.toMessageData.toString
        let diagnostic := Json.mkObj [("message", Json.str message)]
        IO.println s!"LEAN_ECONCSLIB_DECLARATION_INVENTORY_DIAGNOSTIC:{diagnostic.compress}"
        pure none
      match result? with
      | some result =>
          IO.println s!"LEAN_ECONCSLIB_DECLARATION_INVENTORY:{result.compress}"
      | none =>
          IO.println "LEAN_ECONCSLIB_DECLARATION_INVENTORY_ERROR"

end AppliedModelingLibAudit.DeclarationGraph
