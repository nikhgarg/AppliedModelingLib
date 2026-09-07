import AppliedModelingLib.Markets.Matching.ContinuumCutoff

/-!
# Azevedo-Leshno Cutoff-Market Surface

This file records only the Azevedo-Leshno results currently needed by the two
Peng-Garg matching-market papers.  The reusable mathematical interface lives in
`AppliedModelingLib.Markets.Matching.ContinuumCutoff`; this paper file supplies
source-facing wrappers and names.

The full Azevedo-Leshno paper contains additional uniqueness, convergence, and
application results.  Those are intentionally out of scope for the current
PG23/PG24 top-down route.
-/

namespace AL16SupplyDemandMatching

open AppliedModelingLib.Matching

universe u v

variable {Student : Type u} {College : Type v}
variable (M : CutoffMarket Student College)

/-- A-L Definition 1 surface: a source matching is stable. -/
abbrev definition1_stableMatching (μ : M.Matching) : Prop :=
  M.Stable μ

/-- A-L Definition 2 surface: a cutoff vector is market clearing. -/
abbrev definition2_marketClearingCutoff (P : M.Cutoff) : Prop :=
  M.MarketClearing P

/--
The A-L cutoff-market consequences needed by the Peng-Garg matching papers.

This is intentionally a transparent package, not a new mathematical
assumption: each field is one of the concrete A-L-style interfaces that the
downstream papers use.
-/
structure CutoffMarketConsequences where
  /-- Stable matchings are exactly represented by market-clearing cutoffs. -/
  supplyDemand : SupplyDemandInterface M
  /-- Market-clearing cutoffs form the complete lattice used in equal-cutoff proofs. -/
  lattice : CutoffLatticeInterface M
  /-- Market clearing gives exact per-college capacity fill. -/
  exactFill : MarketClearingCapacityInterface M

/--
Build the bundled downstream A-L consequence package from explicit source
components.  This keeps the package auditable: each field is one of the
paper-facing source facts rather than an opaque certificate.
-/
def cutoffMarketConsequences_of_source_components
    (hstable_iff :
      ∀ μ : M.Matching,
        M.Stable μ ↔
          ∃ P : M.Cutoff, M.MarketClearing P ∧ M.RepresentedByCutoff μ P)
    (hmarketClearing_induces_stable :
      ∀ P : M.Cutoff,
        M.MarketClearing P →
          ∃ μ : M.Matching, M.Stable μ ∧ M.RepresentedByCutoff μ P)
    (leCutoff : M.Cutoff → M.Cutoff → Prop)
    (hnonempty_marketClearing : ∃ P : M.Cutoff, M.MarketClearing P)
    (hcomplete_marketClearing :
      CompleteLatticeOn M.MarketClearing leCutoff)
    (hexact_fill :
      ∀ P : M.Cutoff, M.MarketClearing P →
        ∀ c : College, M.aggregateDemand P c = M.capacity c) :
    CutoffMarketConsequences M :=
  { supplyDemand :=
      { stable_iff_exists_marketClearing_cutoff := hstable_iff
        marketClearing_induces_stable := hmarketClearing_induces_stable }
    lattice :=
      { leCutoff := leCutoff
        nonempty_marketClearing := hnonempty_marketClearing
        complete_marketClearing := hcomplete_marketClearing }
    exactFill :=
      { marketClearing_aggregateDemand_eq_capacity := hexact_fill } }

/--
A-L market-clearing capacity accounting: at a market-clearing cutoff,
aggregate demand for each college equals that college's capacity.
-/
theorem marketClearingCutoff_aggregateDemand_eq_capacity
    (K : MarketClearingCapacityInterface M) {P : M.Cutoff}
    (hP : definition2_marketClearingCutoff M P) (c : College) :
    M.aggregateDemand P c = M.capacity c :=
  K.aggregateDemand_eq_capacity hP c

/--
A-L market-clearing capacity accounting summed over a finite block of colleges.
-/
theorem marketClearingCutoff_aggregateDemand_sum_eq_capacity_sum
    (K : MarketClearingCapacityInterface M) {P : M.Cutoff}
    (hP : definition2_marketClearingCutoff M P) (active : Finset College) :
    Finset.sum active (fun c => M.aggregateDemand P c) =
      Finset.sum active (fun c => M.capacity c) :=
  K.aggregateDemand_sum_eq_capacity_sum hP active

/-- A-L cutoff-induced demand representation. -/
abbrev cutoffDemandRepresentsMatching (μ : M.Matching) (P : M.Cutoff) : Prop :=
  M.RepresentedByCutoff μ P

/--
A-L Lemma 1 constructive bridge: choose a market-clearing cutoff representing
a given stable matching.
-/
noncomputable def stableMatchingMarketClearingCutoff
    (I : SupplyDemandInterface M) {μ : M.Matching}
    (hμ : definition1_stableMatching M μ) : M.Cutoff :=
  I.marketClearingCutoffOfStable hμ

/-- The chosen cutoff of a stable matching is market clearing. -/
theorem stableMatchingMarketClearingCutoff_marketClearing
    (I : SupplyDemandInterface M) {μ : M.Matching}
    (hμ : definition1_stableMatching M μ) :
    definition2_marketClearingCutoff M
      (stableMatchingMarketClearingCutoff M I hμ) :=
  I.marketClearingCutoffOfStable_marketClearing hμ

/--
The selected cutoff of a stable matching inherits exact-fill capacity
accounting.
-/
theorem stableMatchingMarketClearingCutoff_aggregateDemand_eq_capacity
    (I : SupplyDemandInterface M) (K : MarketClearingCapacityInterface M)
    {μ : M.Matching} (hμ : definition1_stableMatching M μ)
    (c : College) :
    M.aggregateDemand (stableMatchingMarketClearingCutoff M I hμ) c =
      M.capacity c :=
  K.marketClearingCutoffOfStable_aggregateDemand_eq_capacity I hμ c

/--
The selected cutoff of a stable matching inherits exact-fill capacity
accounting summed over any finite block of colleges.
-/
theorem stableMatchingMarketClearingCutoff_aggregateDemand_sum_eq_capacity_sum
    (I : SupplyDemandInterface M) (K : MarketClearingCapacityInterface M)
    {μ : M.Matching} (hμ : definition1_stableMatching M μ)
    (active : Finset College) :
    Finset.sum active
        (fun c =>
          M.aggregateDemand (stableMatchingMarketClearingCutoff M I hμ) c) =
      Finset.sum active (fun c => M.capacity c) :=
  K.marketClearingCutoffOfStable_aggregateDemand_sum_eq_capacity_sum
    I hμ active

/--
The selected cutoff of a stable matching inherits exact-fill capacity
accounting from the bundled A-L cutoff-market consequences.
-/
theorem cutoffMarketConsequences_stableMatchingMarketClearingCutoff_aggregateDemand_eq_capacity
    (A : CutoffMarketConsequences M)
    {μ : M.Matching} (hμ : definition1_stableMatching M μ)
    (c : College) :
    M.aggregateDemand
        (stableMatchingMarketClearingCutoff M A.supplyDemand hμ) c =
      M.capacity c :=
  stableMatchingMarketClearingCutoff_aggregateDemand_eq_capacity
    M A.supplyDemand A.exactFill hμ c

/--
The selected cutoff of a stable matching inherits finite-block exact-fill
capacity accounting from the bundled A-L cutoff-market consequences.
-/
theorem cutoffMarketConsequences_stableMatchingMarketClearingCutoff_aggregateDemand_sum_eq_capacity_sum
    (A : CutoffMarketConsequences M)
    {μ : M.Matching} (hμ : definition1_stableMatching M μ)
    (active : Finset College) :
    Finset.sum active
        (fun c =>
          M.aggregateDemand
            (stableMatchingMarketClearingCutoff M A.supplyDemand hμ) c) =
      Finset.sum active (fun c => M.capacity c) :=
  stableMatchingMarketClearingCutoff_aggregateDemand_sum_eq_capacity_sum
    M A.supplyDemand A.exactFill hμ active

/-- The chosen cutoff of a stable matching represents that matching. -/
theorem stableMatchingMarketClearingCutoff_represents
    (I : SupplyDemandInterface M) {μ : M.Matching}
    (hμ : definition1_stableMatching M μ) :
    cutoffDemandRepresentsMatching M μ
      (stableMatchingMarketClearingCutoff M I hμ) :=
  I.marketClearingCutoffOfStable_represents hμ

/--
Any property of all market-clearing cutoffs applies to the chosen cutoff of a
stable matching.
-/
theorem stableMatchingMarketClearingCutoff_property
    (I : SupplyDemandInterface M) {μ : M.Matching}
    (hμ : definition1_stableMatching M μ) {property : M.Cutoff → Prop}
    (hproperty :
      ∀ P : M.Cutoff, definition2_marketClearingCutoff M P → property P) :
    property (stableMatchingMarketClearingCutoff M I hμ) :=
  I.property_marketClearingCutoffOfStable hμ hproperty

/--
When the market-clearing cutoff is unique, the cutoff selected from Lemma 1 is
the same for every stable matching.
-/
theorem stableMatchingMarketClearingCutoff_eq_of_unique_marketClearing
    (I : SupplyDemandInterface M) {μ ν : M.Matching}
    (hμ : definition1_stableMatching M μ)
    (hν : definition1_stableMatching M ν)
    (hunique :
      ∀ P Q : M.Cutoff,
        definition2_marketClearingCutoff M P →
          definition2_marketClearingCutoff M Q → P = Q) :
    stableMatchingMarketClearingCutoff M I hμ =
      stableMatchingMarketClearingCutoff M I hν :=
  I.marketClearingCutoffOfStable_eq_of_unique_marketClearing hμ hν hunique

/--
A-L Lemma 1, stable-to-cutoff direction: a stable matching has a
market-clearing cutoff representation.
-/
theorem lemma1_supplyDemand_stable_exists_marketClearing_cutoff
    (I : SupplyDemandInterface M) {μ : M.Matching}
    (hμ : definition1_stableMatching M μ) :
    ∃ P : M.Cutoff,
      definition2_marketClearingCutoff M P ∧
        cutoffDemandRepresentsMatching M μ P :=
  I.exists_marketClearing_cutoff_of_stable hμ

/--
A-L Lemma 1, cutoff-to-stable direction: demand at a market-clearing cutoff is
stable.
-/
theorem lemma1_supplyDemand_stable_of_marketClearing_cutoff
    (I : SupplyDemandInterface M) {μ : M.Matching} {P : M.Cutoff}
    (hP : definition2_marketClearingCutoff M P)
    (hrep : cutoffDemandRepresentsMatching M μ P) :
    definition1_stableMatching M μ :=
  I.stable_of_marketClearing_cutoff hP hrep

/--
A-L Lemma 1, bundled statement: stable matchings are exactly represented
market-clearing cutoff-demand matchings.
-/
theorem lemma1_supplyDemand_iff
    (I : SupplyDemandInterface M) (μ : M.Matching) :
    definition1_stableMatching M μ ↔
      ∃ P : M.Cutoff,
        definition2_marketClearingCutoff M P ∧
          cutoffDemandRepresentsMatching M μ P :=
  I.stable_iff_exists_marketClearing_cutoff μ

/--
A-L Theorem A.1 surface: the market-clearing cutoffs form a complete lattice
under the exported cutoff order.
-/
theorem theoremA1_marketClearing_cutoffs_complete_lattice
    (L : CutoffLatticeInterface M) :
    CompleteLatticeOn (definition2_marketClearingCutoff M) L.leCutoff :=
  L.complete_marketClearing

/-- A-L Theorem A.1 named greatest market-clearing cutoff. -/
noncomputable def greatestMarketClearingCutoff
    (L : CutoffLatticeInterface M) : M.Cutoff :=
  L.greatestMarketClearingCutoff

/-- A-L Theorem A.1 named least market-clearing cutoff. -/
noncomputable def leastMarketClearingCutoff
    (L : CutoffLatticeInterface M) : M.Cutoff :=
  L.leastMarketClearingCutoff

/-- A-L Theorem A.1 consequence: a greatest market-clearing cutoff exists. -/
theorem theoremA1_exists_greatest_marketClearing_cutoff
    (L : CutoffLatticeInterface M) :
    ∃ top : M.Cutoff,
      definition2_marketClearingCutoff M top ∧
        ∀ P : M.Cutoff,
          definition2_marketClearingCutoff M P → L.leCutoff P top :=
  L.exists_greatest_marketClearing

/-- A-L Theorem A.1 consequence: a least market-clearing cutoff exists. -/
theorem theoremA1_exists_least_marketClearing_cutoff
    (L : CutoffLatticeInterface M) :
    ∃ bot : M.Cutoff,
      definition2_marketClearingCutoff M bot ∧
        ∀ P : M.Cutoff,
          definition2_marketClearingCutoff M P → L.leCutoff bot P :=
  L.exists_least_marketClearing

/-- The named greatest cutoff is market clearing. -/
theorem greatestMarketClearingCutoff_marketClearing
    (L : CutoffLatticeInterface M) :
    definition2_marketClearingCutoff M
      (greatestMarketClearingCutoff M L) :=
  L.greatestMarketClearingCutoff_marketClearing

/-- Every market-clearing cutoff is below the named greatest cutoff. -/
theorem le_greatestMarketClearingCutoff
    (L : CutoffLatticeInterface M) {P : M.Cutoff}
    (hP : definition2_marketClearingCutoff M P) :
    L.leCutoff P (greatestMarketClearingCutoff M L) :=
  L.le_greatestMarketClearingCutoff hP

/-- The named least cutoff is market clearing. -/
theorem leastMarketClearingCutoff_marketClearing
    (L : CutoffLatticeInterface M) :
    definition2_marketClearingCutoff M
      (leastMarketClearingCutoff M L) :=
  L.leastMarketClearingCutoff_marketClearing

/-- The named least cutoff is below every market-clearing cutoff. -/
theorem leastMarketClearingCutoff_le
    (L : CutoffLatticeInterface M) {P : M.Cutoff}
    (hP : definition2_marketClearingCutoff M P) :
    L.leCutoff (leastMarketClearingCutoff M L) P :=
  L.leastMarketClearingCutoff_le hP

/--
A-L Theorem A.1 consequence used in PG23 Lemma 2: if the least and greatest
market-clearing cutoffs supplied by the lattice theorem coincide, then the
market-clearing cutoff is unique.
-/
theorem theoremA1_unique_marketClearing_cutoff_of_least_greatest_eq
    (L : CutoffLatticeInterface M)
    {bot top : M.Cutoff}
    (hbot :
      definition2_marketClearingCutoff M bot ∧
        ∀ P : M.Cutoff,
          definition2_marketClearingCutoff M P → L.leCutoff bot P)
    (htop :
      definition2_marketClearingCutoff M top ∧
        ∀ P : M.Cutoff,
          definition2_marketClearingCutoff M P → L.leCutoff P top)
    (h_eq : bot = top) :
    ∀ P Q : M.Cutoff,
      definition2_marketClearingCutoff M P →
        definition2_marketClearingCutoff M Q → P = Q :=
  L.unique_marketClearing_of_least_greatest_eq hbot htop h_eq

/--
Bundled A-L cutoff-market consequence: if the least and greatest
market-clearing cutoffs coincide, every market-clearing cutoff is the same.
-/
theorem cutoffMarketConsequences_unique_marketClearing_cutoff_of_least_greatest_eq
    (A : CutoffMarketConsequences M)
    {bot top : M.Cutoff}
    (hbot :
      definition2_marketClearingCutoff M bot ∧
        ∀ P : M.Cutoff,
          definition2_marketClearingCutoff M P → A.lattice.leCutoff bot P)
    (htop :
      definition2_marketClearingCutoff M top ∧
        ∀ P : M.Cutoff,
          definition2_marketClearingCutoff M P → A.lattice.leCutoff P top)
    (h_eq : bot = top) :
    ∀ P Q : M.Cutoff,
      definition2_marketClearingCutoff M P →
        definition2_marketClearingCutoff M Q → P = Q :=
  theoremA1_unique_marketClearing_cutoff_of_least_greatest_eq
    M A.lattice hbot htop h_eq

/--
Bundled A-L coordinate-symmetry uniqueness consequence.  The A-L lattice
supplies the market-clearing cutoff extrema; a paper-specific coordinate
representation, swap closure, and strict scalar clearing equation identify
those extrema, so every market-clearing cutoff is unique.
-/
theorem cutoffMarketConsequences_unique_marketClearing_cutoff_of_coordinate_symmetry_strict_antitone_scalar_clearing
    (A : CutoffMarketConsequences M)
    {CollegeCoord : Type v} [DecidableEq CollegeCoord]
    (coord : M.Cutoff → CollegeCoord → ℝ)
    (hcoord_ext : ∀ P Q : M.Cutoff, coord P = coord Q → P = Q)
    (horder :
      ∀ P Q : M.Cutoff,
        A.lattice.leCutoff P Q → CoordinatewiseLe (coord P) (coord Q))
    (hswap :
      ∀ P : M.Cutoff, M.MarketClearing P → ∀ c d : CollegeCoord,
        ∃ Q : M.Cutoff,
          M.MarketClearing Q ∧ coord Q = coordinateSwap (coord P) c d)
    {demand : ℝ → ℝ} {supply : ℝ}
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → (∀ c, coord P c = x) → demand x = supply)
    (hstrict : ∀ x y : ℝ, x < y → demand y < demand x) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  A.lattice.unique_marketClearing_of_coordinate_symmetry_strict_antitone_scalar_clearing
    coord hcoord_ext horder hswap hclearing hstrict

/--
A-L existence consequence needed by downstream PG papers: the lattice theorem
gives a market-clearing cutoff, and the supply/demand lemma turns that cutoff
into a stable matching.
-/
theorem exists_stableMatching_of_supplyDemand_and_lattice
    (I : SupplyDemandInterface M) (L : CutoffLatticeInterface M) :
    ∃ μ : M.Matching, definition1_stableMatching M μ :=
  I.exists_stable_of_cutoffLattice L

/--
Bundled A-L existence consequence: the cutoff-market consequences give a
stable matching.
-/
theorem exists_stableMatching_of_cutoffMarketConsequences
    (A : CutoffMarketConsequences M) :
    ∃ μ : M.Matching, definition1_stableMatching M μ :=
  exists_stableMatching_of_supplyDemand_and_lattice
    M A.supplyDemand A.lattice

end AL16SupplyDemandMatching
