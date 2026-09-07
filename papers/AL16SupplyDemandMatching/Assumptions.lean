import AL16SupplyDemandMatching.MainTheorems

/-!
# Paper Assumptions: A Supply and Demand Framework for Two-Sided Matching Markets

The current PG-focused Azevedo-Leshno layer exposes the single downstream
source boundary as a record.  Each field is one of the cutoff-market facts used
by the Peng-Garg papers: stable matchings are represented by market-clearing
cutoffs, market-clearing cutoffs induce stable matchings, market-clearing
cutoffs are nonempty and form a complete lattice, and market clearing has the
exact-fill capacity semantics used downstream.
-/

namespace AL16SupplyDemandMatching

open AppliedModelingLib.Matching

universe u v

variable {Student : Type u} {College : Type v}
variable (M : CutoffMarket Student College)

/--
Generic Azevedo-Leshno cutoff-market source model.

This is the source-shaped AL boundary before any downstream exact-fill
specialization: market clearing is tied to weak capacity feasibility and to
equality only at colleges whose cutoff coordinate is positive, matching
Definition 2.
-/
structure CutoffMarketGenericSourceModel
    (leCutoff : M.Cutoff → M.Cutoff → Prop)
    (cutoffValue : M.Cutoff → College → ℝ) : Prop where
  /-- Stable matchings are exactly represented by market-clearing cutoffs. -/
  stable_iff_marketClearing_cutoff :
    ∀ μ : M.Matching,
      definition1_stableMatching M μ ↔
        ∃ P : M.Cutoff,
          definition2_marketClearingCutoff M P ∧
            cutoffDemandRepresentsMatching M μ P
  /-- Every market-clearing cutoff induces a stable matching. -/
  marketClearing_induces_stable :
    ∀ P : M.Cutoff,
      definition2_marketClearingCutoff M P →
        ∃ μ : M.Matching,
          definition1_stableMatching M μ ∧
            cutoffDemandRepresentsMatching M μ P
  /-- At least one market-clearing cutoff exists. -/
  nonempty_marketClearing :
    ∃ P : M.Cutoff, definition2_marketClearingCutoff M P
  /-- Market-clearing cutoffs form a complete lattice under the source order. -/
  complete_marketClearing :
    CompleteLatticeOn (definition2_marketClearingCutoff M) leCutoff
  /--
  Definition 2 capacity semantics: weak feasibility for every college and
  exact fill only at positive cutoff coordinates.
  -/
  definition2_source_equations :
    ∀ P : M.Cutoff,
      definition2_marketClearingCutoff M P ↔
        (∀ c : College, M.aggregateDemand P c ≤ M.capacity c) ∧
          (∀ c : College, 0 < cutoffValue P c →
            M.aggregateDemand P c = M.capacity c)

/--
Compact Azevedo-Leshno plus downstream exact-fill cutoff-market source model.

This is the intended single AL boundary for the PG23/PG24 route.  It is not an
opaque consequence package: the fields are the source-level mathematical facts
that must eventually be proved from the full continuum-economy model plus the
additional exact-fill specialization required by the downstream PG route.
-/
structure CutoffMarketConsequenceSourceModel
    (leCutoff : M.Cutoff → M.Cutoff → Prop) : Prop where
  /-- Stable matchings are exactly represented by market-clearing cutoffs. -/
  stable_iff_marketClearing_cutoff :
    ∀ μ : M.Matching,
      definition1_stableMatching M μ ↔
        ∃ P : M.Cutoff,
          definition2_marketClearingCutoff M P ∧
            cutoffDemandRepresentsMatching M μ P
  /-- Every market-clearing cutoff induces a stable matching. -/
  marketClearing_induces_stable :
    ∀ P : M.Cutoff,
      definition2_marketClearingCutoff M P →
        ∃ μ : M.Matching,
          definition1_stableMatching M μ ∧
            cutoffDemandRepresentsMatching M μ P
  /-- At least one market-clearing cutoff exists. -/
  nonempty_marketClearing :
    ∃ P : M.Cutoff, definition2_marketClearingCutoff M P
  /-- Market-clearing cutoffs form a complete lattice under the source order. -/
  complete_marketClearing :
    CompleteLatticeOn (definition2_marketClearingCutoff M) leCutoff
  /-- Market clearing fills each college exactly. -/
  exact_fill :
    ∀ P : M.Cutoff, definition2_marketClearingCutoff M P →
      ∀ c : College, M.aggregateDemand P c = M.capacity c

/--
Derive the bundled downstream A-L consequence package from the explicit source
model record.
-/
def cutoffMarketConsequences_of_source_model
    {leCutoff : M.Cutoff → M.Cutoff → Prop}
    (H : CutoffMarketConsequenceSourceModel M leCutoff) :
    CutoffMarketConsequences M :=
  cutoffMarketConsequences_of_source_components M
    H.stable_iff_marketClearing_cutoff
    H.marketClearing_induces_stable
    leCutoff
    H.nonempty_marketClearing
    H.complete_marketClearing
    H.exact_fill

/--
Derive the older downstream source-model record from the generic AL source
model plus a separately supplied exact-fill specialization.
-/
def cutoffMarketConsequenceSourceModel_of_generic_source_model_and_exact_fill
    {leCutoff : M.Cutoff → M.Cutoff → Prop}
    {cutoffValue : M.Cutoff → College → ℝ}
    (H : CutoffMarketGenericSourceModel M leCutoff cutoffValue)
    (hexact_fill :
      ∀ P : M.Cutoff, definition2_marketClearingCutoff M P →
        ∀ c : College, M.aggregateDemand P c = M.capacity c) :
    CutoffMarketConsequenceSourceModel M leCutoff where
  stable_iff_marketClearing_cutoff := H.stable_iff_marketClearing_cutoff
  marketClearing_induces_stable := H.marketClearing_induces_stable
  nonempty_marketClearing := H.nonempty_marketClearing
  complete_marketClearing := H.complete_marketClearing
  exact_fill := hexact_fill

/--
Build the bundled downstream A-L consequence package from a generic source
model and a separately visible exact-fill specialization.
-/
def cutoffMarketConsequences_of_generic_source_model_and_exact_fill
    {leCutoff : M.Cutoff → M.Cutoff → Prop}
    {cutoffValue : M.Cutoff → College → ℝ}
    (H : CutoffMarketGenericSourceModel M leCutoff cutoffValue)
    (hexact_fill :
      ∀ P : M.Cutoff, definition2_marketClearingCutoff M P →
        ∀ c : College, M.aggregateDemand P c = M.capacity c) :
    CutoffMarketConsequences M :=
  cutoffMarketConsequences_of_source_model M
    (cutoffMarketConsequenceSourceModel_of_generic_source_model_and_exact_fill
      M H hexact_fill)

end AL16SupplyDemandMatching
