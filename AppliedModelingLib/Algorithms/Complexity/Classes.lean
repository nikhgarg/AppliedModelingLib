import Mathlib.Data.Set.Defs

/-!
# Abstract Complexity-Class Interfaces

This module provides a lightweight vocabulary for paper formalizations that
need to state complexity-class consequences without developing a full machine
model, running-time model, or randomized computation library.

The definitions are intentionally abstract: external sources may supply the
actual Karp reductions, polynomial-time certificates, or NP/ZPP hardness
theorems as hypotheses, while paper-local reductions can transport those
consequences through compiled Lean encodings.
-/

namespace AppliedModelingLib
namespace Complexity

universe u v

/-- A decision problem, or language, over an instance type. -/
abbrev DecisionProblem (Instance : Type u) := Instance → Prop

/--
An abstract pair of complexity classes over a common language universe.

This is only a light-weight interface for naming class-equality consequences;
the structure does not claim a particular machine model for either class.
-/
structure ComplexityClassModel (Instance : Type u) where
  NP : Set (DecisionProblem Instance)
  ZPP : Set (DecisionProblem Instance)

namespace ComplexityClassModel

variable {Instance : Type u}

/-- The abstract class-equality consequence usually written as `NP = ZPP`. -/
def npEqZPP (M : ComplexityClassModel Instance) : Prop :=
  M.NP = M.ZPP

theorem npEqZPP_of_eq {M : ComplexityClassModel Instance} (h : M.NP = M.ZPP) :
    M.npEqZPP := h

theorem eq_of_npEqZPP {M : ComplexityClassModel Instance} (h : M.npEqZPP) :
    M.NP = M.ZPP := h

end ComplexityClassModel

/-- Complement of a decision problem/language. -/
def complementProblem {Instance : Type u}
    (problem : DecisionProblem Instance) : DecisionProblem Instance :=
  fun input => ¬ problem input

/-- The class of complements of languages in a class. -/
def ComplementClass {Instance : Type u}
    (C : Set (DecisionProblem Instance)) : Set (DecisionProblem Instance) :=
  {problem | ∃ source ∈ C, problem = complementProblem source}

/--
Abstract randomized-class vocabulary for source notes that mention `P`, `RP`,
`co-RP`, and `co-NP` without developing machine semantics.

The fields are the standard containment/equality facts needed to derive the
collapse consequences often cited around `NP = ZPP`.
-/
structure RandomizedComplexityClassModel (Instance : Type u) extends
    ComplexityClassModel Instance where
  P : Set (DecisionProblem Instance)
  RP : Set (DecisionProblem Instance)
  coRP : Set (DecisionProblem Instance)
  coNP : Set (DecisionProblem Instance)
  P_subset_ZPP : P ⊆ ZPP
  ZPP_subset_NP : ZPP ⊆ NP
  RP_subset_NP : RP ⊆ NP
  ZPP_eq_RP_inter_coRP : ZPP = RP ∩ coRP
  coRP_eq_complement_RP : coRP = ComplementClass RP
  coNP_eq_complement_NP : coNP = ComplementClass NP
  ZPP_complement_closed : ComplementClass ZPP = ZPP

namespace RandomizedComplexityClassModel

variable {Instance : Type u}

/-- The abstract `P = NP` statement in a randomized class model. -/
def pEqNP (M : RandomizedComplexityClassModel Instance) : Prop :=
  M.P = M.NP

/-- The source note's easy implication: `P = NP` implies `NP = ZPP`. -/
theorem npEqZPP_of_pEqNP {M : RandomizedComplexityClassModel Instance}
    (h : M.pEqNP) : M.toComplexityClassModel.npEqZPP := by
  rw [pEqNP] at h
  ext problem
  constructor
  · intro hNP
    exact M.P_subset_ZPP (by simpa [h] using hNP)
  · intro hZPP
    exact M.ZPP_subset_NP hZPP

/-- Under `NP = ZPP`, the abstract randomized model has `NP = RP`. -/
theorem npEqRP_of_npEqZPP {M : RandomizedComplexityClassModel Instance}
    (h : M.toComplexityClassModel.npEqZPP) :
    M.NP = M.RP := by
  rw [ComplexityClassModel.npEqZPP] at h
  ext problem
  constructor
  · intro hNP
    have hZPP : problem ∈ M.ZPP := by simpa [h] using hNP
    have hInter : problem ∈ M.RP ∩ M.coRP := by
      simpa [M.ZPP_eq_RP_inter_coRP] using hZPP
    exact hInter.1
  · intro hRP
    exact M.RP_subset_NP hRP

/-- Under `NP = ZPP`, the abstract randomized model has `co-NP = NP`. -/
theorem coNPEqNP_of_npEqZPP {M : RandomizedComplexityClassModel Instance}
    (h : M.toComplexityClassModel.npEqZPP) :
    M.coNP = M.NP := by
  calc
    M.coNP = ComplementClass M.NP := M.coNP_eq_complement_NP
    _ = ComplementClass M.ZPP := by rw [h]
    _ = M.ZPP := M.ZPP_complement_closed
    _ = M.NP := h.symm

/-- Under `NP = ZPP`, the abstract randomized model has `NP = co-RP`. -/
theorem npEqCoRP_of_npEqZPP {M : RandomizedComplexityClassModel Instance}
    (h : M.toComplexityClassModel.npEqZPP) :
    M.NP = M.coRP := by
  rw [ComplexityClassModel.npEqZPP] at h
  ext problem
  constructor
  · intro hNP
    have hZPP : problem ∈ M.ZPP := by simpa [h] using hNP
    have hInter : problem ∈ M.RP ∩ M.coRP := by
      simpa [M.ZPP_eq_RP_inter_coRP] using hZPP
    exact hInter.2
  · intro hcoRP
    have hComp : problem ∈ ComplementClass M.RP := by
      simpa [M.coRP_eq_complement_RP] using hcoRP
    rcases hComp with ⟨source, hsource, rfl⟩
    have hcoNP : complementProblem source ∈ M.coNP := by
      simpa [M.coNP_eq_complement_NP] using
        (show complementProblem source ∈ ComplementClass M.NP from
          ⟨source, M.RP_subset_NP hsource, rfl⟩)
    simpa [coNPEqNP_of_npEqZPP (M := M) h] using hcoNP

/--
The source note's collapse package: `NP = ZPP` implies the abstract equalities
`NP = RP`, `NP = co-RP`, and `NP = co-NP`.
-/
theorem randomized_collapse_of_npEqZPP
    {M : RandomizedComplexityClassModel Instance}
    (h : M.toComplexityClassModel.npEqZPP) :
    M.NP = M.RP ∧ M.NP = M.coRP ∧ M.NP = M.coNP := by
  exact ⟨npEqRP_of_npEqZPP h, npEqCoRP_of_npEqZPP h,
    (coNPEqNP_of_npEqZPP h).symm⟩

end RandomizedComplexityClassModel

/--
A many-one reduction between decision problems.

This is only correctness of the instance map; feasibility is separated below so
paper developments can keep computational assumptions explicit.
-/
structure ManyOneReduction
    {Source : Type u} {Target : Type v}
    (source : DecisionProblem Source) (target : DecisionProblem Target) where
  map : Source → Target
  correct : ∀ x, source x ↔ target (map x)

/--
An abstract polynomial-time many-one reduction.

The `polynomialTime` field is a proposition supplied by whatever computational
model a downstream development chooses to use.
-/
structure PolynomialTimeReduction
    {Source : Type u} {Target : Type v}
    (source : DecisionProblem Source) (target : DecisionProblem Target) where
  reduction : ManyOneReduction source target
  PolynomialTime : (Source → Target) → Prop
  polynomialTime : PolynomialTime reduction.map

namespace PolynomialTimeReduction

variable {Source : Type u} {Target : Type v}
variable {source : DecisionProblem Source} {target : DecisionProblem Target}

/-- Correctness of the underlying many-one map. -/
theorem correct (r : PolynomialTimeReduction source target) (x : Source) :
    source x ↔ target (r.reduction.map x) :=
  r.reduction.correct x

end PolynomialTimeReduction

/--
Generic external reduction-consequence package: a compiled many-one reduction
from `source` to `target` transfers an external source-hardness fact into a
declared target consequence.
-/
structure ExternalReductionConsequence
    {Source : Type u} {Target : Type v}
    (source : DecisionProblem Source) (target : DecisionProblem Target) where
  SourceHard : Prop
  Consequence : Prop
  consequence_of_reduction :
    ManyOneReduction source target → SourceHard → Consequence

namespace ExternalReductionConsequence

variable {Source : Type u} {Target : Type v}
variable {source : DecisionProblem Source} {target : DecisionProblem Target}

/-- Apply an external reduction-consequence package to a compiled many-one reduction. -/
theorem apply (C : ExternalReductionConsequence source target)
    (r : ManyOneReduction source target) (hsource : C.SourceHard) :
    C.Consequence :=
  C.consequence_of_reduction r hsource

end ExternalReductionConsequence

/--
Generic external polynomial-reduction consequence package. The running-time
model is still abstract and lives inside `PolynomialTimeReduction`.
-/
structure ExternalPolynomialReductionConsequence
    {Source : Type u} {Target : Type v}
    (source : DecisionProblem Source) (target : DecisionProblem Target) where
  SourceHard : Prop
  Consequence : Prop
  consequence_of_reduction :
    PolynomialTimeReduction source target → SourceHard → Consequence

namespace ExternalPolynomialReductionConsequence

variable {Source : Type u} {Target : Type v}
variable {source : DecisionProblem Source} {target : DecisionProblem Target}

/-- Apply an external polynomial-reduction consequence package to a compiled reduction. -/
theorem apply (C : ExternalPolynomialReductionConsequence source target)
    (r : PolynomialTimeReduction source target) (hsource : C.SourceHard) :
    C.Consequence :=
  C.consequence_of_reduction r hsource

end ExternalPolynomialReductionConsequence

/--
An abstract hardness predicate closed under compiled many-one reductions.

This is the minimal reusable shape for paper folders that want to say a source
hardness result transfers through a Lean-verified reduction while leaving the
actual complexity class semantics external.
-/
structure ReductionClosedHardness where
  Hard : {Instance : Type u} → DecisionProblem Instance → Prop
  hard_of_manyOne :
    ∀ {Source Target : Type u}
      {source : DecisionProblem Source} {target : DecisionProblem Target},
      ManyOneReduction source target → Hard source → Hard target

namespace ReductionClosedHardness

variable {Source Target : Type u}
variable {source : DecisionProblem Source} {target : DecisionProblem Target}

/-- Apply reduction-closed hardness along a compiled many-one reduction. -/
theorem apply (H : ReductionClosedHardness)
    (r : ManyOneReduction source target) (hsource : H.Hard source) :
    H.Hard target :=
  H.hard_of_manyOne r hsource

end ReductionClosedHardness

/--
An abstract hardness predicate closed under compiled polynomial-time reductions.
The machine model remains external through `PolynomialTimeReduction`.
-/
structure PolynomialReductionClosedHardness where
  Hard : {Instance : Type u} → DecisionProblem Instance → Prop
  hard_of_polynomial :
    ∀ {Source Target : Type u}
      {source : DecisionProblem Source} {target : DecisionProblem Target},
      PolynomialTimeReduction source target → Hard source → Hard target

namespace PolynomialReductionClosedHardness

variable {Source Target : Type u}
variable {source : DecisionProblem Source} {target : DecisionProblem Target}

/-- Apply reduction-closed hardness along a compiled polynomial-time reduction. -/
theorem apply (H : PolynomialReductionClosedHardness)
    (r : PolynomialTimeReduction source target) (hsource : H.Hard source) :
    H.Hard target :=
  H.hard_of_polynomial r hsource

end PolynomialReductionClosedHardness

/--
Generic external solver-hardness package: every feasible solver satisfying
`Solves` implies a declared complexity consequence.
-/
structure ExternalSolverConsequence (Solver : Type u) where
  Solves : Solver → Prop
  Feasible : Solver → Prop
  Consequence : Prop
  consequence_of_solver :
    ∀ solver, Solves solver → Feasible solver → Consequence

namespace ExternalSolverConsequence

variable {Solver : Type u}

/-- Apply an external solver-hardness package to a concrete solver. -/
theorem apply (C : ExternalSolverConsequence Solver)
    (solver : Solver) (hsolves : C.Solves solver) (hfeasible : C.Feasible solver) :
    C.Consequence :=
  C.consequence_of_solver solver hsolves hfeasible

end ExternalSolverConsequence

end Complexity
end AppliedModelingLib
