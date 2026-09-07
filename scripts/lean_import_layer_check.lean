import Lean.Elab.Command
import ImportGraph.Imports.ImportGraph
import AppliedModelingLib.Foundations
import AppliedModelingLib.Algorithms
import AppliedModelingLib.Learning
import AppliedModelingLib.Privacy
import AppliedModelingLib.Queueing
import AppliedModelingLib.GameTheory
import AppliedModelingLib.SocialChoice
import AppliedModelingLib.MechanismDesign
import AppliedModelingLib.Markets
import AppliedModelingLib.Alignment
import AppliedModelingLib.Applications

/-!
# Shared-library import-layer check

Lean's loaded environment is the sole source of module edges.  This check does
not parse import text and does not classify declaration semantics from types.
It enforces only the small architectural rules justified for every module in a
top-level layer; finer semantic placement remains a reviewed reorganization
decision.
-/

open Lean Elab Command

private def projectRoot : Name := `AppliedModelingLib
private def foundationsRoot : Name := `AppliedModelingLib.Foundations
private def algorithmsRoot : Name := `AppliedModelingLib.Algorithms
private def learningRoot : Name := `AppliedModelingLib.Learning
private def auditRoot : Name := `AppliedModelingLib.Audit

private def isProjectModule (module : Name) : Bool :=
  projectRoot.isPrefixOf module

private def algorithmsMayImport (module : Name) : Bool :=
  foundationsRoot.isPrefixOf module ||
    algorithmsRoot.isPrefixOf module ||
    learningRoot.isPrefixOf module

private def violationReason? (source target : Name) : Option String :=
  if !isProjectModule source || !isProjectModule target then
    none
  else if foundationsRoot.isPrefixOf source &&
      !foundationsRoot.isPrefixOf target then
    some "mathematical foundations import a higher project layer"
  else if !auditRoot.isPrefixOf source && auditRoot.isPrefixOf target then
    some "semantic library code imports audit tooling"
  else if algorithmsRoot.isPrefixOf source && !algorithmsMayImport target then
    some "domain-neutral algorithms import a domain or application layer"
  else
    none

#guard (violationReason?
  `AppliedModelingLib.Foundations.Probability.Example
  `AppliedModelingLib.Applications.Example).isSome
#guard (violationReason?
  `AppliedModelingLib.Algorithms.Example
  `AppliedModelingLib.Applications.Example).isSome
#guard (violationReason?
  `AppliedModelingLib.Learning.Example
  `AppliedModelingLib.Audit.Example).isSome
#guard (violationReason?
  `AppliedModelingLib.Applications.Example
  `AppliedModelingLib.Foundations.Probability.Example).isNone

elab "#check_shared_library_import_layers" : command => do
  let env ← getEnv
  let mut violations : Array (Name × Name × String) := #[]
  for source in env.header.moduleNames do
    for target in env.importsOf source do
      if let some reason := violationReason? source target then
        violations := violations.push (source, target, reason)
  let sortedViolations := violations.qsort fun left right =>
    left.1.toString < right.1.toString ||
      (left.1.toString = right.1.toString &&
        left.2.1.toString < right.2.1.toString)
  for (source, target, reason) in sortedViolations do
    logError m!"{source} imports {target}: {reason}"
  unless sortedViolations.isEmpty do
    throwError "shared-library import-layer check failed"

#check_shared_library_import_layers
