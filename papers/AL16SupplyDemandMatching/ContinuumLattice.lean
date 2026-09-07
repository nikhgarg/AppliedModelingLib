import AppliedModelingLib.Markets.Matching.ContinuumCutoff
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IsLUB

/-!
# Finite Cutoff-Lattice Step for Azevedo--Leshno

This module formalizes the finite `sup`/`inf` part of the proof of Azevedo and
Leshno's Theorem A.1.  The source cutoff domain is the cube `[0, 1]^C`, not an
unrestricted real-valued function space.  Market clearing has Definition 2's
weak capacity inequality and its equality condition at positive coordinates.

The source proof at `docs/source_microsoft_2013.txt:2041-2060` first compares
college demand and unmatched mass under two clearing cutoffs.  Conservation of
total mass makes those weak comparisons equalities, which closes clearing under
coordinatewise `sup`; the `inf` argument is dual.  The later arbitrary-family
step (`:2061-2068`) constructs finite envelopes in the source cube and uses
an explicit sequential demand-continuity premise to close clearing at their
limits.  Neither step accepts a supplied lattice conclusion.
-/

open scoped BigOperators Topology

namespace AL16SupplyDemandMatching

open AppliedModelingLib.Matching
open Filter

universe v

variable {College : Type v} [Fintype College]

/-- Source cutoff vectors lie in `[0, 1]^C`. -/
abbrev AL16Cutoff (College : Type v) := College → Set.Icc (0 : ℝ) 1

/-- Real coordinate of an A-L cutoff vector. -/
def al16CutoffValue (P : AL16Cutoff College) (c : College) : ℝ := P c

/-- Definition 2 market clearing over the explicit source cutoff coordinates. -/
def al16SourceMarketClearing
    (demand : AL16Cutoff College → College → ℝ) (capacity : College → ℝ)
    (P : AL16Cutoff College) : Prop :=
  (∀ c : College, demand P c ≤ capacity c) ∧
    ∀ c : College, 0 < al16CutoffValue P c → demand P c = capacity c

/--
Finite exact-fill specialization for Definition 2. If a clearing cutoff's total
college demand equals total capacity, then the weak per-college capacity
inequalities are all equalities.
-/
theorem al16MarketClearing_exactFill_of_totalDemand_eq_capacitySum
    (demand : AL16Cutoff College → College → ℝ) (capacity : College → ℝ)
    {P : AL16Cutoff College}
    (hP : al16SourceMarketClearing demand capacity P)
    (hsum : (∑ c : College, demand P c) = ∑ c : College, capacity c) :
    ∀ c : College, demand P c = capacity c := by
  have hpoint :=
    (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (fun c _ => hP.1 c)).mp hsum
  intro c
  exact hpoint c (Finset.mem_univ c)

/--
Finite exact-fill specialization for the common PG use case. Unit mass
partition, zero outside demand, and total capacity equal to the unit mass force
Definition 2 clearing to fill every college exactly.
-/
theorem al16MarketClearing_exactFill_of_noOutside_totalCapacity
    (demand : AL16Cutoff College → College → ℝ)
    (outside : AL16Cutoff College → ℝ) (capacity : College → ℝ)
    {P : AL16Cutoff College}
    (hmass : outside P + ∑ c : College, demand P c = 1)
    (hP : al16SourceMarketClearing demand capacity P)
    (houtside_zero : outside P = 0)
    (hcapacity_sum : (∑ c : College, capacity c) = 1) :
    ∀ c : College, demand P c = capacity c := by
  apply al16MarketClearing_exactFill_of_totalDemand_eq_capacitySum
    demand capacity hP
  linarith

private theorem component_eq_of_mass_conservation
    (demand : AL16Cutoff College → College → ℝ)
    (outside : AL16Cutoff College → ℝ)
    {P Q : AL16Cutoff College}
    (hmass : ∀ R : AL16Cutoff College, outside R + ∑ c, demand R c = 1)
    (houtside : outside P ≤ outside Q)
    (hdemand : ∀ c : College, demand P c ≤ demand Q c) :
    ∀ c : College, demand P c = demand Q c := by
  have hsum_le : (∑ c, demand P c) ≤ ∑ c, demand Q c := by
    exact Finset.sum_le_sum fun c _ => hdemand c
  have hsum_eq : (∑ c, demand P c) = ∑ c, demand Q c := by
    linarith [hmass P, hmass Q]
  have hpoint :=
    (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (fun c _ => hdemand c)).mp hsum_eq
  intro c
  exact hpoint c (Finset.mem_univ c)

omit [Fintype College] in
private theorem demand_le_sup_of_marketClearing
    (demand : AL16Cutoff College → College → ℝ)
    (capacity : College → ℝ)
    (hdemand_sup : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand Q c ≤ demand (P ⊔ Q) c)
    {P Q : AL16Cutoff College}
    (hP : al16SourceMarketClearing demand capacity P)
    (hQ : al16SourceMarketClearing demand capacity Q) :
    ∀ c : College, demand P c ≤ demand (P ⊔ Q) c := by
  intro c
  by_cases hPQ : al16CutoffValue P c ≤ al16CutoffValue Q c
  · by_cases hQpos : 0 < al16CutoffValue Q c
    · calc
        demand P c ≤ capacity c := hP.1 c
        _ = demand Q c := (hQ.2 c hQpos).symm
        _ ≤ demand (P ⊔ Q) c := hdemand_sup P Q c hPQ
    · have hQ_nonpos : al16CutoffValue Q c ≤ 0 := le_of_not_gt hQpos
      have hP_nonneg : 0 ≤ al16CutoffValue P c := (P c).property.1
      have hQ_nonneg : 0 ≤ al16CutoffValue Q c := (Q c).property.1
      have hP_zero : al16CutoffValue P c = 0 :=
        le_antisymm (hPQ.trans hQ_nonpos) hP_nonneg
      have hQ_zero : al16CutoffValue Q c = 0 :=
        le_antisymm hQ_nonpos hQ_nonneg
      have hQP : al16CutoffValue Q c ≤ al16CutoffValue P c := by
        simp [hP_zero, hQ_zero]
      simpa [sup_comm] using hdemand_sup Q P c hQP
  · have hQP : al16CutoffValue Q c ≤ al16CutoffValue P c :=
      le_of_lt (lt_of_not_ge hPQ)
    simpa [sup_comm] using hdemand_sup Q P c hQP

private theorem demand_eq_of_marketClearing
    (demand : AL16Cutoff College → College → ℝ)
    (outside : AL16Cutoff College → ℝ)
    (capacity : College → ℝ)
    (hmass : ∀ R : AL16Cutoff College, outside R + ∑ c, demand R c = 1)
    (houtside_sup : ∀ P Q : AL16Cutoff College, outside P ≤ outside (P ⊔ Q))
    (hdemand_sup : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand Q c ≤ demand (P ⊔ Q) c)
    {P Q : AL16Cutoff College}
    (hP : al16SourceMarketClearing demand capacity P)
    (hQ : al16SourceMarketClearing demand capacity Q) :
    ∀ c : College, demand P c = demand Q c := by
  have hP_le : ∀ c : College, demand P c ≤ demand (P ⊔ Q) c :=
    demand_le_sup_of_marketClearing demand capacity hdemand_sup hP hQ
  have hP_eq_sup : ∀ c : College, demand P c = demand (P ⊔ Q) c :=
    component_eq_of_mass_conservation demand outside hmass
      (houtside_sup P Q) hP_le
  have hQ_le : ∀ c : College, demand Q c ≤ demand (P ⊔ Q) c := by
    simpa [sup_comm] using
      demand_le_sup_of_marketClearing demand capacity hdemand_sup hQ hP
  have hQ_eq_sup : ∀ c : College, demand Q c = demand (P ⊔ Q) c :=
    component_eq_of_mass_conservation demand outside hmass
      (by simpa [sup_comm] using houtside_sup Q P) hQ_le
  intro c
  exact (hP_eq_sup c).trans (hQ_eq_sup c).symm

/--
The equal-college-demand step used twice in the source proof: first inside
Theorem A1's finite lattice argument, and then explicitly for Theorem A2's
rural-hospitals conclusion.  It exposes only the source comparison premises and
two Definition-2 clearing cutoffs, not a lattice or rural-hospitals package.
-/
theorem al16SourceMarketClearing_aggregateDemand_eq_of_sup_primitives
    (demand : AL16Cutoff College → College → ℝ)
    (outside : AL16Cutoff College → ℝ)
    (capacity : College → ℝ)
    (hmass : ∀ R : AL16Cutoff College, outside R + ∑ c, demand R c = 1)
    (houtside_sup : ∀ P Q : AL16Cutoff College, outside P ≤ outside (P ⊔ Q))
    (hdemand_sup : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand Q c ≤ demand (P ⊔ Q) c)
    {P Q : AL16Cutoff College}
    (hP : al16SourceMarketClearing demand capacity P)
    (hQ : al16SourceMarketClearing demand capacity Q) :
    ∀ c : College, demand P c = demand Q c :=
  demand_eq_of_marketClearing demand outside capacity hmass houtside_sup
    hdemand_sup hP hQ

/--
The corresponding equality between a clearing cutoff and the coordinatewise
`sup` of two clearing cutoffs.  This is the exact equality used in Theorem A2's
underfilled-college set argument.
-/
theorem al16SourceMarketClearing_aggregateDemand_eq_sup_of_sup_primitives
    (demand : AL16Cutoff College → College → ℝ)
    (outside : AL16Cutoff College → ℝ)
    (capacity : College → ℝ)
    (hmass : ∀ R : AL16Cutoff College, outside R + ∑ c, demand R c = 1)
    (houtside_sup : ∀ P Q : AL16Cutoff College, outside P ≤ outside (P ⊔ Q))
    (hdemand_sup : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand Q c ≤ demand (P ⊔ Q) c)
    {P Q : AL16Cutoff College}
    (hP : al16SourceMarketClearing demand capacity P)
    (hQ : al16SourceMarketClearing demand capacity Q) :
    ∀ c : College, demand P c = demand (P ⊔ Q) c :=
  component_eq_of_mass_conservation demand outside hmass
    (houtside_sup P Q)
    (demand_le_sup_of_marketClearing demand capacity hdemand_sup hP hQ)

/--
The binary `sup` step in the proof of A-L Theorem A.1.

`hmass` is the source partition of unit mass into unmatched and college demand;
`houtside_sup` and `hdemand_sup` are exactly the source's comparison facts for
the coordinatewise larger cutoff.  No lattice, existence, or exact-fill
conclusion is accepted as a premise.
-/
theorem al16SourceMarketClearing_sup_closed_of_demand_primitives
    (demand : AL16Cutoff College → College → ℝ)
    (outside : AL16Cutoff College → ℝ)
    (capacity : College → ℝ)
    (hmass : ∀ P : AL16Cutoff College, outside P + ∑ c, demand P c = 1)
    (houtside_sup : ∀ P Q : AL16Cutoff College, outside P ≤ outside (P ⊔ Q))
    (hdemand_sup : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand Q c ≤ demand (P ⊔ Q) c)
    {P Q : AL16Cutoff College}
    (hP : al16SourceMarketClearing demand capacity P)
    (hQ : al16SourceMarketClearing demand capacity Q) :
    al16SourceMarketClearing demand capacity (P ⊔ Q) := by
  have hP_eq : ∀ c : College, demand P c = demand (P ⊔ Q) c :=
    component_eq_of_mass_conservation demand outside hmass
      (houtside_sup P Q)
      (demand_le_sup_of_marketClearing demand capacity hdemand_sup hP hQ)
  have hQ_eq : ∀ c : College, demand Q c = demand (P ⊔ Q) c := by
    simpa [sup_comm] using
      (component_eq_of_mass_conservation demand outside hmass
        (houtside_sup Q P)
        (demand_le_sup_of_marketClearing demand capacity hdemand_sup hQ hP))
  constructor
  · intro c
    rw [← hP_eq c]
    exact hP.1 c
  · intro c hpos
    by_cases hPQ : al16CutoffValue P c ≤ al16CutoffValue Q c
    · have hQpos : 0 < al16CutoffValue Q c := by
        rw [show al16CutoffValue (P ⊔ Q) c = al16CutoffValue Q c by
          change ((↑((P ⊔ Q) c) : ℝ) = (↑(Q c) : ℝ))
          change max (↑(P c) : ℝ) (↑(Q c) : ℝ) = (↑(Q c) : ℝ)
          exact max_eq_right hPQ] at hpos
        exact hpos
      rw [← hQ_eq c]
      exact hQ.2 c hQpos
    · have hQP : al16CutoffValue Q c ≤ al16CutoffValue P c :=
        le_of_lt (lt_of_not_ge hPQ)
      have hPpos : 0 < al16CutoffValue P c := by
        rw [show al16CutoffValue (P ⊔ Q) c = al16CutoffValue P c by
          change ((↑((P ⊔ Q) c) : ℝ) = (↑(P c) : ℝ))
          change max (↑(P c) : ℝ) (↑(Q c) : ℝ) = (↑(P c) : ℝ)
          exact max_eq_left hQP] at hpos
        exact hpos
      rw [← hP_eq c]
      exact hP.2 c hPpos

/--
The binary `inf` step in the proof of A-L Theorem A.1.

The first two comparison premises are reused to obtain the source's rural
hospitals equality of college demand at two clearing cutoffs.  The remaining
two premises are the dual `inf` comparison facts.  As in the source proof,
mass conservation turns the coordinatewise weak comparison into equality.
-/
theorem al16SourceMarketClearing_inf_closed_of_demand_primitives
    (demand : AL16Cutoff College → College → ℝ)
    (outside : AL16Cutoff College → ℝ)
    (capacity : College → ℝ)
    (hmass : ∀ P : AL16Cutoff College, outside P + ∑ c, demand P c = 1)
    (houtside_sup : ∀ P Q : AL16Cutoff College, outside P ≤ outside (P ⊔ Q))
    (hdemand_sup : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand Q c ≤ demand (P ⊔ Q) c)
    (houtside_inf : ∀ P Q : AL16Cutoff College, outside (P ⊓ Q) ≤ outside P)
    (hdemand_inf : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand (P ⊓ Q) c ≤ demand P c)
    {P Q : AL16Cutoff College}
    (hP : al16SourceMarketClearing demand capacity P)
    (hQ : al16SourceMarketClearing demand capacity Q) :
    al16SourceMarketClearing demand capacity (P ⊓ Q) := by
  have hPQ_eq : ∀ c : College, demand P c = demand Q c :=
    demand_eq_of_marketClearing demand outside capacity hmass
      houtside_sup hdemand_sup hP hQ
  have hmin_le_P : ∀ c : College, demand (P ⊓ Q) c ≤ demand P c := by
    intro c
    by_cases hPQ : al16CutoffValue P c ≤ al16CutoffValue Q c
    · exact hdemand_inf P Q c hPQ
    · have hQP : al16CutoffValue Q c ≤ al16CutoffValue P c :=
        le_of_lt (lt_of_not_ge hPQ)
      calc
        demand (P ⊓ Q) c ≤ demand Q c := by
          simpa [inf_comm] using hdemand_inf Q P c hQP
        _ = demand P c := (hPQ_eq c).symm
  have hmin_eq_P : ∀ c : College, demand (P ⊓ Q) c = demand P c :=
    component_eq_of_mass_conservation demand outside hmass
      (houtside_inf P Q) hmin_le_P
  constructor
  · intro c
    rw [hmin_eq_P c]
    exact hP.1 c
  · intro c hpos
    by_cases hPQ : al16CutoffValue P c ≤ al16CutoffValue Q c
    · have hPpos : 0 < al16CutoffValue P c := by
        rw [show al16CutoffValue (P ⊓ Q) c = al16CutoffValue P c by
          change ((↑((P ⊓ Q) c) : ℝ) = (↑(P c) : ℝ))
          change min (↑(P c) : ℝ) (↑(Q c) : ℝ) = (↑(P c) : ℝ)
          exact min_eq_left hPQ] at hpos
        exact hpos
      rw [hmin_eq_P c]
      exact hP.2 c hPpos
    · have hQP : al16CutoffValue Q c ≤ al16CutoffValue P c :=
        le_of_lt (lt_of_not_ge hPQ)
      have hQpos : 0 < al16CutoffValue Q c := by
        rw [show al16CutoffValue (P ⊓ Q) c = al16CutoffValue Q c by
          change ((↑((P ⊓ Q) c) : ℝ) = (↑(Q c) : ℝ))
          change min (↑(P c) : ℝ) (↑(Q c) : ℝ) = (↑(Q c) : ℝ)
          exact min_eq_right hQP] at hpos
        exact hpos
      have hPpos : 0 < al16CutoffValue P c := lt_of_lt_of_le hQpos hQP
      rw [hmin_eq_P c]
      exact hP.2 c hPpos

/--
Every nonempty finite coordinatewise supremum of clearing cutoffs clears.

This is the induction recorded in the last sentence of the finite part of the
source proof of Theorem A.1 (`docs/source_microsoft_2013.txt:2057-2060`).
-/
theorem al16SourceMarketClearing_finset_sup_closed_of_demand_primitives
    (demand : AL16Cutoff College → College → ℝ)
    (outside : AL16Cutoff College → ℝ)
    (capacity : College → ℝ)
    (hmass : ∀ P : AL16Cutoff College, outside P + ∑ c, demand P c = 1)
    (houtside_sup : ∀ P Q : AL16Cutoff College, outside P ≤ outside (P ⊔ Q))
    (hdemand_sup : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand Q c ≤ demand (P ⊔ Q) c)
    (s : Finset (AL16Cutoff College))
    (hs : s.Nonempty)
    (hclear : ∀ P ∈ s, al16SourceMarketClearing demand capacity P) :
    al16SourceMarketClearing demand capacity (s.sup' hs id) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hs).elim
  | @insert a s ha ih =>
      by_cases hs_empty : s = ∅
      · subst s
        simpa using hclear a (by simp)
      · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs_empty
        rw [Finset.sup'_insert hsne id]
        exact al16SourceMarketClearing_sup_closed_of_demand_primitives
          demand outside capacity hmass houtside_sup hdemand_sup
          (hclear a (by simp))
          (ih hsne (fun P hP => hclear P (Finset.mem_insert_of_mem hP)))

/--
Every nonempty finite coordinatewise infimum of clearing cutoffs clears.

This is the dual induction in the finite part of the source proof of Theorem
A.1 (`docs/source_microsoft_2013.txt:2057-2060`).
-/
theorem al16SourceMarketClearing_finset_inf_closed_of_demand_primitives
    (demand : AL16Cutoff College → College → ℝ)
    (outside : AL16Cutoff College → ℝ)
    (capacity : College → ℝ)
    (hmass : ∀ P : AL16Cutoff College, outside P + ∑ c, demand P c = 1)
    (houtside_sup : ∀ P Q : AL16Cutoff College, outside P ≤ outside (P ⊔ Q))
    (hdemand_sup : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand Q c ≤ demand (P ⊔ Q) c)
    (houtside_inf : ∀ P Q : AL16Cutoff College, outside (P ⊓ Q) ≤ outside P)
    (hdemand_inf : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand (P ⊓ Q) c ≤ demand P c)
    (s : Finset (AL16Cutoff College))
    (hs : s.Nonempty)
    (hclear : ∀ P ∈ s, al16SourceMarketClearing demand capacity P) :
    al16SourceMarketClearing demand capacity (s.inf' hs id) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hs).elim
  | @insert a s ha ih =>
      by_cases hs_empty : s = ∅
      · subst s
        simpa using hclear a (by simp)
      · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs_empty
        rw [Finset.inf'_insert hsne id]
        exact al16SourceMarketClearing_inf_closed_of_demand_primitives
          demand outside capacity hmass houtside_sup hdemand_sup houtside_inf hdemand_inf
          (hclear a (by simp))
          (ih hsne (fun P hP => hclear P (Finset.mem_insert_of_mem hP)))

/-- Coordinatewise order on the source cutoff cube. -/
def al16CutoffLe (P Q : AL16Cutoff College) : Prop :=
  ∀ c : College, al16CutoffValue P c ≤ al16CutoffValue Q c

/-- Ambient, not market-clearing, least-upper-bound property for cutoff vectors. -/
def al16IsPointwiseLeastUpperBound (S : Set (AL16Cutoff College))
    (P : AL16Cutoff College) : Prop :=
  (∀ Q : AL16Cutoff College, S Q → al16CutoffLe Q P) ∧
    ∀ R : AL16Cutoff College,
      (∀ Q : AL16Cutoff College, S Q → al16CutoffLe Q R) → al16CutoffLe P R

/-- Ambient, not market-clearing, greatest-lower-bound property for cutoffs. -/
def al16IsPointwiseGreatestLowerBound (S : Set (AL16Cutoff College))
    (P : AL16Cutoff College) : Prop :=
  (∀ Q : AL16Cutoff College, S Q → al16CutoffLe P Q) ∧
    ∀ R : AL16Cutoff College,
      (∀ Q : AL16Cutoff College, S Q → al16CutoffLe R Q) → al16CutoffLe R P

/-- Coordinatewise sequential convergence of source cutoff vectors. -/
def al16CoordinatewiseTendsto
    (P : ℕ → AL16Cutoff College) (Q : AL16Cutoff College) : Prop :=
  ∀ c : College,
    Tendsto (fun n => al16CutoffValue (P n) c) atTop
      (𝓝 (al16CutoffValue Q c))

omit [Fintype College] in
private theorem al16CutoffLe_refl (P : AL16Cutoff College) : al16CutoffLe P P :=
  fun _ => le_rfl

omit [Fintype College] in
private theorem al16CutoffLe_trans {P Q R : AL16Cutoff College}
    (hPQ : al16CutoffLe P Q) (hQR : al16CutoffLe Q R) : al16CutoffLe P R :=
  fun c => (hPQ c).trans (hQR c)

omit [Fintype College] in
private theorem al16CutoffLe_antisymm {P Q : AL16Cutoff College}
    (hPQ : al16CutoffLe P Q) (hQP : al16CutoffLe Q P) : P = Q := by
  funext c
  apply Subtype.ext
  exact le_antisymm (hPQ c) (hQP c)

/--
Continuity closes Definition 2 market clearing under a coordinatewise sequence
of clearing cutoffs.  This is the closedness argument invoked at
`docs/source_microsoft_2013.txt:2064-2068`, written directly rather than
accepted as a closed-set conclusion.
-/
theorem al16SourceMarketClearing_of_coordinatewise_limit
    (demand : AL16Cutoff College → College → ℝ)
    (capacity : College → ℝ)
    (hdemand_continuous :
      ∀ (P : ℕ → AL16Cutoff College) (Q : AL16Cutoff College),
        al16CoordinatewiseTendsto P Q →
          ∀ c : College,
            Tendsto (fun n => demand (P n) c) atTop (𝓝 (demand Q c)))
    (P : ℕ → AL16Cutoff College)
    (Q : AL16Cutoff College)
    (hclear : ∀ n, al16SourceMarketClearing demand capacity (P n))
    (hlim : al16CoordinatewiseTendsto P Q) :
    al16SourceMarketClearing demand capacity Q := by
  constructor
  · intro c
    apply le_of_tendsto (hdemand_continuous P Q hlim c)
    exact Filter.Eventually.of_forall fun n => (hclear n).1 c
  · intro c hQpos
    have hPpos : ∀ᶠ n in atTop, 0 < al16CutoffValue (P n) c :=
      (tendsto_order.1 (hlim c)).1 0 hQpos
    have hDemandEq : ∀ᶠ n in atTop, demand (P n) c = capacity c :=
      hPpos.mono fun n hn => (hclear n).2 c hn
    apply tendsto_nhds_unique (hdemand_continuous P Q hlim c)
    exact tendsto_const_nhds.congr' (hDemandEq.mono fun n hn => hn.symm)

/--
Sequential closedness, stated directly as a proof input, is enough for the
arbitrary-family part of A-L Theorem A.1.  This variant is useful for source
models whose demand is continuous only on the part of the cutoff cube where
clearing limits are known to lie.
-/
theorem al16SourceMarketClearing_isLeastUpperBound_of_finite_sup_envelopes_of_limit_closed
    (demand : AL16Cutoff College → College → ℝ)
    (outside : AL16Cutoff College → ℝ)
    (capacity : College → ℝ)
    (hmass : ∀ P : AL16Cutoff College, outside P + ∑ c, demand P c = 1)
    (houtside_sup : ∀ P Q : AL16Cutoff College, outside P ≤ outside (P ⊔ Q))
    (hdemand_sup : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand Q c ≤ demand (P ⊔ Q) c)
    (hclosed :
      ∀ (P : ℕ → AL16Cutoff College) (Q : AL16Cutoff College),
        (∀ n, al16SourceMarketClearing demand capacity (P n)) →
          al16CoordinatewiseTendsto P Q →
            al16SourceMarketClearing demand capacity Q)
    (S : Set (AL16Cutoff College))
    (Pstar : AL16Cutoff College)
    (U : ℕ → {s : Finset (AL16Cutoff College) // s.Nonempty})
    (hS : ∀ P : AL16Cutoff College, S P → al16SourceMarketClearing demand capacity P)
    (hPstar : al16IsPointwiseLeastUpperBound S Pstar)
    (hU_mem : ∀ n P, P ∈ (U n).1 → S P)
    (hU_tendsto : al16CoordinatewiseTendsto
      (fun n => ((U n).1).sup' (U n).2 id) Pstar) :
    IsLeastUpperBoundOn (al16SourceMarketClearing demand capacity) al16CutoffLe S Pstar := by
  have hseq_clear :
      ∀ n, al16SourceMarketClearing demand capacity (((U n).1).sup' (U n).2 id) := by
    intro n
    exact al16SourceMarketClearing_finset_sup_closed_of_demand_primitives
      demand outside capacity hmass houtside_sup hdemand_sup (U n).1 (U n).2
      (fun P hP => hS P (hU_mem n P hP))
  have hPstar_clear : al16SourceMarketClearing demand capacity Pstar :=
    hclosed (fun n => ((U n).1).sup' (U n).2 id) Pstar hseq_clear hU_tendsto
  constructor
  · constructor
    · exact hPstar_clear
    · intro P hPS _hPclear
      exact hPstar.1 P hPS
  · intro R hR
    apply hPstar.2 R
    intro P hPS
    exact hR.2 P hPS (hS P hPS)

/--
The dual arbitrary-infimum closure step with sequential closedness supplied
directly instead of via global demand continuity.
-/
theorem al16SourceMarketClearing_isGreatestLowerBound_of_finite_inf_envelopes_of_limit_closed
    (demand : AL16Cutoff College → College → ℝ)
    (outside : AL16Cutoff College → ℝ)
    (capacity : College → ℝ)
    (hmass : ∀ P : AL16Cutoff College, outside P + ∑ c, demand P c = 1)
    (houtside_sup : ∀ P Q : AL16Cutoff College, outside P ≤ outside (P ⊔ Q))
    (hdemand_sup : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand Q c ≤ demand (P ⊔ Q) c)
    (houtside_inf : ∀ P Q : AL16Cutoff College, outside (P ⊓ Q) ≤ outside P)
    (hdemand_inf : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand (P ⊓ Q) c ≤ demand P c)
    (hclosed :
      ∀ (P : ℕ → AL16Cutoff College) (Q : AL16Cutoff College),
        (∀ n, al16SourceMarketClearing demand capacity (P n)) →
          al16CoordinatewiseTendsto P Q →
            al16SourceMarketClearing demand capacity Q)
    (S : Set (AL16Cutoff College))
    (Pstar : AL16Cutoff College)
    (U : ℕ → {s : Finset (AL16Cutoff College) // s.Nonempty})
    (hS : ∀ P : AL16Cutoff College, S P → al16SourceMarketClearing demand capacity P)
    (hPstar : al16IsPointwiseGreatestLowerBound S Pstar)
    (hU_mem : ∀ n P, P ∈ (U n).1 → S P)
    (hU_tendsto : al16CoordinatewiseTendsto
      (fun n => ((U n).1).inf' (U n).2 id) Pstar) :
    IsGreatestLowerBoundOn (al16SourceMarketClearing demand capacity) al16CutoffLe S Pstar := by
  have hseq_clear :
      ∀ n, al16SourceMarketClearing demand capacity (((U n).1).inf' (U n).2 id) := by
    intro n
    exact al16SourceMarketClearing_finset_inf_closed_of_demand_primitives
      demand outside capacity hmass houtside_sup hdemand_sup houtside_inf hdemand_inf
      (U n).1 (U n).2 (fun P hP => hS P (hU_mem n P hP))
  have hPstar_clear : al16SourceMarketClearing demand capacity Pstar :=
    hclosed (fun n => ((U n).1).inf' (U n).2 id) Pstar hseq_clear hU_tendsto
  constructor
  · constructor
    · exact hPstar_clear
    · intro P hPS _hPclear
      exact hPstar.1 P hPS
  · intro R hR
    apply hPstar.2 R
    intro P hPS
    exact hR.2 P hPS (hS P hPS)

/-- Real coordinate values attained by a family of source cutoffs. -/
def al16CutoffCoordinateValues (S : Set (AL16Cutoff College)) (c : College) : Set ℝ :=
  (fun P : AL16Cutoff College => al16CutoffValue P c) '' S

omit [Fintype College] in
private theorem al16CutoffCoordinateValues_nonempty
    (S : Set (AL16Cutoff College)) (hS : S.Nonempty) (c : College) :
    (al16CutoffCoordinateValues S c).Nonempty := by
  rcases hS with ⟨P, hP⟩
  exact ⟨al16CutoffValue P c, ⟨P, hP, rfl⟩⟩

omit [Fintype College] in
private theorem al16CutoffCoordinateValues_bddAbove
    (S : Set (AL16Cutoff College)) (c : College) :
    BddAbove (al16CutoffCoordinateValues S c) := by
  refine ⟨1, ?_⟩
  intro x hx
  rcases hx with ⟨P, _hP, rfl⟩
  exact (P c).property.2

omit [Fintype College] in
private theorem al16CutoffCoordinateValues_bddBelow
    (S : Set (AL16Cutoff College)) (c : College) :
    BddBelow (al16CutoffCoordinateValues S c) := by
  refine ⟨0, ?_⟩
  intro x hx
  rcases hx with ⟨P, _hP, rfl⟩
  exact (P c).property.1

/-- Coordinatewise ambient supremum of a nonempty source-cutoff family. -/
noncomputable def al16PointwiseSup (S : Set (AL16Cutoff College))
    (hS : S.Nonempty) : AL16Cutoff College := fun c =>
  ⟨sSup (al16CutoffCoordinateValues S c), by
    have hSnonempty := hS
    rcases hS with ⟨P, hP⟩
    have hmem : al16CutoffValue P c ∈ al16CutoffCoordinateValues S c :=
      ⟨P, hP, rfl⟩
    constructor
    · exact (P c).property.1.trans
        (le_csSup (al16CutoffCoordinateValues_bddAbove S c) hmem)
    · exact csSup_le (al16CutoffCoordinateValues_nonempty S hSnonempty c) (by
        intro x hx
        rcases hx with ⟨Q, _hQ, rfl⟩
        exact (Q c).property.2)⟩

omit [Fintype College] in
private theorem al16CutoffValue_pointwiseSup (S : Set (AL16Cutoff College))
    (hS : S.Nonempty) (c : College) :
    al16CutoffValue (al16PointwiseSup S hS) c =
      sSup (al16CutoffCoordinateValues S c) := rfl

omit [Fintype College] in
private theorem al16PointwiseSup_isLeastUpperBound
    (S : Set (AL16Cutoff College)) (hS : S.Nonempty) :
    al16IsPointwiseLeastUpperBound S (al16PointwiseSup S hS) := by
  constructor
  · intro P hP c
    rw [al16CutoffValue_pointwiseSup]
    apply le_csSup (al16CutoffCoordinateValues_bddAbove S c)
    exact ⟨P, hP, rfl⟩
  · intro R hR c
    rw [al16CutoffValue_pointwiseSup]
    apply csSup_le (al16CutoffCoordinateValues_nonempty S hS c)
    intro x hx
    rcases hx with ⟨P, hP, rfl⟩
    exact hR P hP c

omit [Fintype College] in
private theorem al16CutoffLe_to_le {P Q : AL16Cutoff College}
    (h : al16CutoffLe P Q) : P ≤ Q := by
  intro c
  exact h c

/-- Coordinatewise ambient infimum of a nonempty source-cutoff family. -/
noncomputable def al16PointwiseInf (S : Set (AL16Cutoff College))
    (hS : S.Nonempty) : AL16Cutoff College := fun c =>
  ⟨sInf (al16CutoffCoordinateValues S c), by
    have hSnonempty := hS
    rcases hS with ⟨P, hP⟩
    have hmem : al16CutoffValue P c ∈ al16CutoffCoordinateValues S c :=
      ⟨P, hP, rfl⟩
    constructor
    · exact le_csInf (al16CutoffCoordinateValues_nonempty S hSnonempty c) (by
        intro x hx
        rcases hx with ⟨Q, _hQ, rfl⟩
        exact (Q c).property.1)
    · exact (csInf_le (al16CutoffCoordinateValues_bddBelow S c) hmem).trans
        (P c).property.2⟩

omit [Fintype College] in
private theorem al16CutoffValue_pointwiseInf (S : Set (AL16Cutoff College))
    (hS : S.Nonempty) (c : College) :
    al16CutoffValue (al16PointwiseInf S hS) c =
      sInf (al16CutoffCoordinateValues S c) := rfl

omit [Fintype College] in
private theorem al16PointwiseInf_isGreatestLowerBound
    (S : Set (AL16Cutoff College)) (hS : S.Nonempty) :
    al16IsPointwiseGreatestLowerBound S (al16PointwiseInf S hS) := by
  constructor
  · intro P hP c
    rw [al16CutoffValue_pointwiseInf]
    apply csInf_le (al16CutoffCoordinateValues_bddBelow S c)
    exact ⟨P, hP, rfl⟩
  · intro R hR c
    rw [al16CutoffValue_pointwiseInf]
    apply le_csInf (al16CutoffCoordinateValues_nonempty S hS c)
    intro x hx
    rcases hx with ⟨P, hP, rfl⟩
    exact hR P hP c

/--
Every nonempty family in the source cube has a coordinatewise supremum
approximated by finite envelopes drawn from that family.

This proves the finite-approximation assertion used at
`docs/source_microsoft_2013.txt:2063-2065`; only the finite college carrier
and the cutoff bounds `[0,1]` are used here.
-/
theorem al16FiniteSupEnvelopeApproximation
    (S : Set (AL16Cutoff College)) (hS : S.Nonempty) :
    ∃ Pstar : AL16Cutoff College,
      ∃ U : ℕ → {s : Finset (AL16Cutoff College) // s.Nonempty},
        al16IsPointwiseLeastUpperBound S Pstar ∧
          (∀ n P, P ∈ (U n).1 → S P) ∧
            al16CoordinatewiseTendsto
              (fun n => ((U n).1).sup' (U n).2 id) Pstar := by
  classical
  have hseq : ∀ c : College, ∃ u : ℕ → ℝ,
      Monotone u ∧
        Tendsto u atTop (𝓝 (sSup (al16CutoffCoordinateValues S c))) ∧
          ∀ n : ℕ, u n ∈ al16CutoffCoordinateValues S c := by
    intro c
    exact exists_seq_tendsto_sSup
      (al16CutoffCoordinateValues_nonempty S hS c)
      (al16CutoffCoordinateValues_bddAbove S c)
  choose u _hu_mono hu_tend hu_mem using hseq
  have hselect : ∀ c : College, ∀ n : ℕ,
      ∃ P : AL16Cutoff College, S P ∧ al16CutoffValue P c = u c n := by
    intro c n
    rcases hu_mem c n with ⟨P, hP, hvalue⟩
    exact ⟨P, hP, hvalue⟩
  choose select hselect_mem hselect_value using hselect
  let P0 : AL16Cutoff College := Classical.choose hS
  have hP0_mem : S P0 := Classical.choose_spec hS
  let U : ℕ → {s : Finset (AL16Cutoff College) // s.Nonempty} := fun n =>
    ⟨insert P0 (Finset.univ.image fun c => select c n),
      ⟨P0, Finset.mem_insert_self _ _⟩⟩
  have hU_mem : ∀ n P, P ∈ (U n).1 → S P := by
    intro n P hP
    change P ∈ insert P0 (Finset.univ.image fun c => select c n) at hP
    rcases Finset.mem_insert.mp hP with rfl | hP
    · exact hP0_mem
    · rcases Finset.mem_image.mp hP with ⟨c, _hc, rfl⟩
      exact hselect_mem c n
  refine ⟨al16PointwiseSup S hS, U, al16PointwiseSup_isLeastUpperBound S hS,
    hU_mem, ?_⟩
  intro d
  have hselect_tend :
      Tendsto (fun n => al16CutoffValue (select d n) d) atTop
        (𝓝 (al16CutoffValue (al16PointwiseSup S hS) d)) := by
    rw [al16CutoffValue_pointwiseSup]
    exact (hu_tend d).congr' (Filter.Eventually.of_forall fun n =>
      (hselect_value d n).symm)
  have hlower :
      (fun n => al16CutoffValue (select d n) d) ≤
        (fun n => al16CutoffValue (((U n).1).sup' (U n).2 id) d) := by
    intro n
    have hmem : select d n ∈ (U n).1 := by
      simp [U]
    have hle : select d n ≤ ((U n).1).sup' (U n).2 id :=
      Finset.le_sup' id hmem
    exact hle d
  have hupper :
      (fun n => al16CutoffValue (((U n).1).sup' (U n).2 id) d) ≤
        (fun _ => al16CutoffValue (al16PointwiseSup S hS) d) := by
    intro n
    have hle : ((U n).1).sup' (U n).2 id ≤ al16PointwiseSup S hS :=
      Finset.sup'_le (U n).2 id (fun P hP =>
        al16CutoffLe_to_le
          ((al16PointwiseSup_isLeastUpperBound S hS).1 P (hU_mem n P hP)))
    exact hle d
  exact hselect_tend.squeeze tendsto_const_nhds hlower hupper

/-- The dual finite-envelope approximation for a coordinatewise infimum. -/
theorem al16FiniteInfEnvelopeApproximation
    (S : Set (AL16Cutoff College)) (hS : S.Nonempty) :
    ∃ Pstar : AL16Cutoff College,
      ∃ U : ℕ → {s : Finset (AL16Cutoff College) // s.Nonempty},
        al16IsPointwiseGreatestLowerBound S Pstar ∧
          (∀ n P, P ∈ (U n).1 → S P) ∧
            al16CoordinatewiseTendsto
              (fun n => ((U n).1).inf' (U n).2 id) Pstar := by
  classical
  have hseq : ∀ c : College, ∃ u : ℕ → ℝ,
      Antitone u ∧
        Tendsto u atTop (𝓝 (sInf (al16CutoffCoordinateValues S c))) ∧
          ∀ n : ℕ, u n ∈ al16CutoffCoordinateValues S c := by
    intro c
    exact exists_seq_tendsto_sInf
      (al16CutoffCoordinateValues_nonempty S hS c)
      (al16CutoffCoordinateValues_bddBelow S c)
  choose u _hu_anti hu_tend hu_mem using hseq
  have hselect : ∀ c : College, ∀ n : ℕ,
      ∃ P : AL16Cutoff College, S P ∧ al16CutoffValue P c = u c n := by
    intro c n
    rcases hu_mem c n with ⟨P, hP, hvalue⟩
    exact ⟨P, hP, hvalue⟩
  choose select hselect_mem hselect_value using hselect
  let P0 : AL16Cutoff College := Classical.choose hS
  have hP0_mem : S P0 := Classical.choose_spec hS
  let U : ℕ → {s : Finset (AL16Cutoff College) // s.Nonempty} := fun n =>
    ⟨insert P0 (Finset.univ.image fun c => select c n),
      ⟨P0, Finset.mem_insert_self _ _⟩⟩
  have hU_mem : ∀ n P, P ∈ (U n).1 → S P := by
    intro n P hP
    change P ∈ insert P0 (Finset.univ.image fun c => select c n) at hP
    rcases Finset.mem_insert.mp hP with rfl | hP
    · exact hP0_mem
    · rcases Finset.mem_image.mp hP with ⟨c, _hc, rfl⟩
      exact hselect_mem c n
  refine ⟨al16PointwiseInf S hS, U, al16PointwiseInf_isGreatestLowerBound S hS,
    hU_mem, ?_⟩
  intro d
  have hselect_tend :
      Tendsto (fun n => al16CutoffValue (select d n) d) atTop
        (𝓝 (al16CutoffValue (al16PointwiseInf S hS) d)) := by
    rw [al16CutoffValue_pointwiseInf]
    exact (hu_tend d).congr' (Filter.Eventually.of_forall fun n =>
      (hselect_value d n).symm)
  have hlower :
      (fun _ => al16CutoffValue (al16PointwiseInf S hS) d) ≤
        (fun n => al16CutoffValue (((U n).1).inf' (U n).2 id) d) := by
    intro n
    have hle : al16PointwiseInf S hS ≤ ((U n).1).inf' (U n).2 id :=
      Finset.le_inf' (U n).2 id (fun P hP =>
        al16CutoffLe_to_le
          ((al16PointwiseInf_isGreatestLowerBound S hS).1 P (hU_mem n P hP)))
    exact hle d
  have hupper :
      (fun n => al16CutoffValue (((U n).1).inf' (U n).2 id) d) ≤
        (fun n => al16CutoffValue (select d n) d) := by
    intro n
    have hmem : select d n ∈ (U n).1 := by
      simp [U]
    have hle : ((U n).1).inf' (U n).2 id ≤ select d n :=
      Finset.inf'_le id hmem
    exact hle d
  exact tendsto_const_nhds.squeeze hselect_tend hlower hupper

/--
The arbitrary-supremum closure step of A-L Theorem A.1 from visible continuum
proof data.

`hPstar` is only the ambient pointwise least-upper-bound fact in `[0,1]^C`.
`U` is the source's sequence of nonempty finite subsets of `S`, and
`hU_tendsto` says their finite envelopes converge coordinatewise to that
ambient supremum.  The conclusion that the ambient supremum clears is proved
here from finite closure and demand continuity; it is not an input.
-/
theorem al16SourceMarketClearing_isLeastUpperBound_of_finite_sup_envelopes
    (demand : AL16Cutoff College → College → ℝ)
    (outside : AL16Cutoff College → ℝ)
    (capacity : College → ℝ)
    (hmass : ∀ P : AL16Cutoff College, outside P + ∑ c, demand P c = 1)
    (houtside_sup : ∀ P Q : AL16Cutoff College, outside P ≤ outside (P ⊔ Q))
    (hdemand_sup : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand Q c ≤ demand (P ⊔ Q) c)
    (hdemand_continuous :
      ∀ (P : ℕ → AL16Cutoff College) (Q : AL16Cutoff College),
        al16CoordinatewiseTendsto P Q →
          ∀ c : College,
            Tendsto (fun n => demand (P n) c) atTop (𝓝 (demand Q c)))
    (S : Set (AL16Cutoff College))
    (Pstar : AL16Cutoff College)
    (U : ℕ → {s : Finset (AL16Cutoff College) // s.Nonempty})
    (hS : ∀ P : AL16Cutoff College, S P → al16SourceMarketClearing demand capacity P)
    (hPstar : al16IsPointwiseLeastUpperBound S Pstar)
    (hU_mem : ∀ n P, P ∈ (U n).1 → S P)
    (hU_tendsto : al16CoordinatewiseTendsto
      (fun n => ((U n).1).sup' (U n).2 id) Pstar) :
    IsLeastUpperBoundOn (al16SourceMarketClearing demand capacity) al16CutoffLe S Pstar := by
  have hseq_clear :
      ∀ n, al16SourceMarketClearing demand capacity (((U n).1).sup' (U n).2 id) := by
    intro n
    exact al16SourceMarketClearing_finset_sup_closed_of_demand_primitives
      demand outside capacity hmass houtside_sup hdemand_sup (U n).1 (U n).2
      (fun P hP => hS P (hU_mem n P hP))
  have hPstar_clear : al16SourceMarketClearing demand capacity Pstar :=
    al16SourceMarketClearing_of_coordinatewise_limit demand capacity
      hdemand_continuous (fun n => ((U n).1).sup' (U n).2 id) Pstar hseq_clear
      hU_tendsto
  constructor
  · constructor
    · exact hPstar_clear
    · intro P hPS _hPclear
      exact hPstar.1 P hPS
  · intro R hR
    apply hPstar.2 R
    intro P hPS
    exact hR.2 P hPS (hS P hPS)

/--
The arbitrary-infimum closure step of A-L Theorem A.1 from visible continuum
proof data.  It is dual to the finite-sup-envelope result above.
-/
theorem al16SourceMarketClearing_isGreatestLowerBound_of_finite_inf_envelopes
    (demand : AL16Cutoff College → College → ℝ)
    (outside : AL16Cutoff College → ℝ)
    (capacity : College → ℝ)
    (hmass : ∀ P : AL16Cutoff College, outside P + ∑ c, demand P c = 1)
    (houtside_sup : ∀ P Q : AL16Cutoff College, outside P ≤ outside (P ⊔ Q))
    (hdemand_sup : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand Q c ≤ demand (P ⊔ Q) c)
    (houtside_inf : ∀ P Q : AL16Cutoff College, outside (P ⊓ Q) ≤ outside P)
    (hdemand_inf : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand (P ⊓ Q) c ≤ demand P c)
    (hdemand_continuous :
      ∀ (P : ℕ → AL16Cutoff College) (Q : AL16Cutoff College),
        al16CoordinatewiseTendsto P Q →
          ∀ c : College,
            Tendsto (fun n => demand (P n) c) atTop (𝓝 (demand Q c)))
    (S : Set (AL16Cutoff College))
    (Pstar : AL16Cutoff College)
    (U : ℕ → {s : Finset (AL16Cutoff College) // s.Nonempty})
    (hS : ∀ P : AL16Cutoff College, S P → al16SourceMarketClearing demand capacity P)
    (hPstar : al16IsPointwiseGreatestLowerBound S Pstar)
    (hU_mem : ∀ n P, P ∈ (U n).1 → S P)
    (hU_tendsto : al16CoordinatewiseTendsto
      (fun n => ((U n).1).inf' (U n).2 id) Pstar) :
    IsGreatestLowerBoundOn (al16SourceMarketClearing demand capacity) al16CutoffLe S Pstar := by
  have hseq_clear :
      ∀ n, al16SourceMarketClearing demand capacity (((U n).1).inf' (U n).2 id) := by
    intro n
    exact al16SourceMarketClearing_finset_inf_closed_of_demand_primitives
      demand outside capacity hmass houtside_sup hdemand_sup houtside_inf hdemand_inf
      (U n).1 (U n).2 (fun P hP => hS P (hU_mem n P hP))
  have hPstar_clear : al16SourceMarketClearing demand capacity Pstar :=
    al16SourceMarketClearing_of_coordinatewise_limit demand capacity
      hdemand_continuous (fun n => ((U n).1).inf' (U n).2 id) Pstar hseq_clear
      hU_tendsto
  constructor
  · constructor
    · exact hPstar_clear
    · intro P hPS _hPclear
      exact hPstar.1 P hPS
  · intro R hR
    apply hPstar.2 R
    intro P hPS
    exact hR.2 P hPS (hS P hPS)

/--
The ambient coordinatewise supremum of a nonempty family of clearing cutoffs
is itself clearing and is its least upper bound.  This packages the exact
`sSup` operation used by the source, rather than only exposing an unspecified
least upper bound supplied by `CompleteLatticeOn`.
-/
theorem al16SourceMarketClearing_pointwiseSup_of_continuum_primitives
    (demand : AL16Cutoff College → College → ℝ)
    (outside : AL16Cutoff College → ℝ)
    (capacity : College → ℝ)
    (hmass : ∀ P : AL16Cutoff College, outside P + ∑ c, demand P c = 1)
    (houtside_sup : ∀ P Q : AL16Cutoff College, outside P ≤ outside (P ⊔ Q))
    (hdemand_sup : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand Q c ≤ demand (P ⊔ Q) c)
    (hdemand_continuous :
      ∀ (P : ℕ → AL16Cutoff College) (Q : AL16Cutoff College),
        al16CoordinatewiseTendsto P Q →
          ∀ c : College,
            Tendsto (fun n => demand (P n) c) atTop (𝓝 (demand Q c)))
    (S : Set (AL16Cutoff College))
    (hS : S.Nonempty)
    (hclear : ∀ P : AL16Cutoff College, S P →
      al16SourceMarketClearing demand capacity P) :
    al16IsPointwiseLeastUpperBound S (al16PointwiseSup S hS) ∧
      IsLeastUpperBoundOn
        (al16SourceMarketClearing demand capacity) al16CutoffLe S
        (al16PointwiseSup S hS) := by
  rcases al16FiniteSupEnvelopeApproximation S hS with
    ⟨Pstar, U, hPstar, hU_mem, hU_tendsto⟩
  have hexact := al16PointwiseSup_isLeastUpperBound S hS
  have hPstar_eq : Pstar = al16PointwiseSup S hS :=
    al16CutoffLe_antisymm (hPstar.2 _ hexact.1) (hexact.2 _ hPstar.1)
  subst Pstar
  exact ⟨hexact,
    al16SourceMarketClearing_isLeastUpperBound_of_finite_sup_envelopes
      demand outside capacity hmass houtside_sup hdemand_sup hdemand_continuous
      S (al16PointwiseSup S hS) U hclear hPstar hU_mem hU_tendsto⟩

/--
The ambient coordinatewise infimum of a nonempty family of clearing cutoffs is
itself clearing and is its greatest lower bound.  This is the exact `sInf`
counterpart of `al16SourceMarketClearing_pointwiseSup_of_continuum_primitives`.
-/
theorem al16SourceMarketClearing_pointwiseInf_of_continuum_primitives
    (demand : AL16Cutoff College → College → ℝ)
    (outside : AL16Cutoff College → ℝ)
    (capacity : College → ℝ)
    (hmass : ∀ P : AL16Cutoff College, outside P + ∑ c, demand P c = 1)
    (houtside_sup : ∀ P Q : AL16Cutoff College, outside P ≤ outside (P ⊔ Q))
    (hdemand_sup : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand Q c ≤ demand (P ⊔ Q) c)
    (houtside_inf : ∀ P Q : AL16Cutoff College, outside (P ⊓ Q) ≤ outside P)
    (hdemand_inf : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand (P ⊓ Q) c ≤ demand P c)
    (hdemand_continuous :
      ∀ (P : ℕ → AL16Cutoff College) (Q : AL16Cutoff College),
        al16CoordinatewiseTendsto P Q →
          ∀ c : College,
            Tendsto (fun n => demand (P n) c) atTop (𝓝 (demand Q c)))
    (S : Set (AL16Cutoff College))
    (hS : S.Nonempty)
    (hclear : ∀ P : AL16Cutoff College, S P →
      al16SourceMarketClearing demand capacity P) :
    al16IsPointwiseGreatestLowerBound S (al16PointwiseInf S hS) ∧
      IsGreatestLowerBoundOn
        (al16SourceMarketClearing demand capacity) al16CutoffLe S
        (al16PointwiseInf S hS) := by
  rcases al16FiniteInfEnvelopeApproximation S hS with
    ⟨Pstar, U, hPstar, hU_mem, hU_tendsto⟩
  have hexact := al16PointwiseInf_isGreatestLowerBound S hS
  have hPstar_eq : Pstar = al16PointwiseInf S hS :=
    al16CutoffLe_antisymm (hexact.2 _ hPstar.1) (hPstar.2 _ hexact.1)
  subst Pstar
  exact ⟨hexact,
    al16SourceMarketClearing_isGreatestLowerBound_of_finite_inf_envelopes
      demand outside capacity hmass houtside_sup hdemand_sup houtside_inf hdemand_inf
      hdemand_continuous S (al16PointwiseInf S hS) U hclear hPstar hU_mem hU_tendsto⟩

/--
The complete-lattice portion of A-L Theorem A.1 from its visible continuum
proof obligations.

For every nonempty cutoff family, this module constructs the finite-envelope
approximations used at `docs/source_microsoft_2013.txt:2061-2068` from the
finite college carrier and the source cube `[0,1]^C`.  They do not say that the
ambient bounds are market clearing.  Lean derives that conclusion from the
already-proved finite closure and the explicit sequential demand-continuity
premise.
-/
theorem al16SourceMarketClearing_completeLattice_of_continuum_primitives
    (demand : AL16Cutoff College → College → ℝ)
    (outside : AL16Cutoff College → ℝ)
    (capacity : College → ℝ)
    (hnonempty : ∃ P : AL16Cutoff College,
      al16SourceMarketClearing demand capacity P)
    (hmass : ∀ P : AL16Cutoff College, outside P + ∑ c, demand P c = 1)
    (houtside_sup : ∀ P Q : AL16Cutoff College, outside P ≤ outside (P ⊔ Q))
    (hdemand_sup : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand Q c ≤ demand (P ⊔ Q) c)
    (houtside_inf : ∀ P Q : AL16Cutoff College, outside (P ⊓ Q) ≤ outside P)
    (hdemand_inf : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand (P ⊓ Q) c ≤ demand P c)
    (hdemand_continuous :
      ∀ (P : ℕ → AL16Cutoff College) (Q : AL16Cutoff College),
        al16CoordinatewiseTendsto P Q →
          ∀ c : College,
            Tendsto (fun n => demand (P n) c) atTop (𝓝 (demand Q c))) :
    CompleteLatticeOn (al16SourceMarketClearing demand capacity) al16CutoffLe where
  exists_valid := hnonempty
  le_refl := fun _ => al16CutoffLe_refl _
  le_trans := fun _ _ _ hPQ hQR => al16CutoffLe_trans hPQ hQR
  le_antisymm := fun _ _ hPQ hQP => al16CutoffLe_antisymm hPQ hQP
  sup_exists := by
    intro S hS
    let T : Set (AL16Cutoff College) :=
      fun P => S P ∧ al16SourceMarketClearing demand capacity P
    have hT : T.Nonempty := by
      rcases hS with ⟨P, hPS, hPclear⟩
      exact ⟨P, hPS, hPclear⟩
    rcases al16FiniteSupEnvelopeApproximation T hT with
      ⟨Pstar, U, hPstar, hU_mem, hU_tendsto⟩
    have hTlub :=
      al16SourceMarketClearing_isLeastUpperBound_of_finite_sup_envelopes
        demand outside capacity hmass houtside_sup hdemand_sup hdemand_continuous T
        Pstar U (fun P hP => hP.2) hPstar hU_mem hU_tendsto
    refine ⟨Pstar, ?_⟩
    constructor
    · constructor
      · exact hTlub.1.1
      · intro P hPS hPclear
        exact hTlub.1.2 P ⟨hPS, hPclear⟩ hPclear
    · intro R hR
      apply hTlub.2 R
      constructor
      · exact hR.1
      · intro P hPT _hPclear
        exact hR.2 P hPT.1 hPT.2
  inf_exists := by
    intro S hS
    let T : Set (AL16Cutoff College) :=
      fun P => S P ∧ al16SourceMarketClearing demand capacity P
    have hT : T.Nonempty := by
      rcases hS with ⟨P, hPS, hPclear⟩
      exact ⟨P, hPS, hPclear⟩
    rcases al16FiniteInfEnvelopeApproximation T hT with
      ⟨Pstar, U, hPstar, hU_mem, hU_tendsto⟩
    have hTglb :=
      al16SourceMarketClearing_isGreatestLowerBound_of_finite_inf_envelopes
        demand outside capacity hmass houtside_sup hdemand_sup houtside_inf hdemand_inf
        hdemand_continuous T Pstar U (fun P hP => hP.2) hPstar hU_mem hU_tendsto
    refine ⟨Pstar, ?_⟩
    constructor
    · constructor
      · exact hTglb.1.1
      · intro P hPS hPclear
        exact hTglb.1.2 P ⟨hPS, hPclear⟩ hPclear
    · intro R hR
      apply hTglb.2 R
      constructor
      · exact hR.1
      · intro P hPT _hPclear
        exact hR.2 P hPT.1 hPT.2

/--
A-L Theorem A.1's complete-lattice step with sequential closedness supplied
directly.  This is equivalent to the continuity-based theorem above when global
demand continuity is available, but also covers models where clearing limits are
known to stay in a continuity region.
-/
theorem al16SourceMarketClearing_completeLattice_of_continuum_primitives_of_limit_closed
    (demand : AL16Cutoff College → College → ℝ)
    (outside : AL16Cutoff College → ℝ)
    (capacity : College → ℝ)
    (hnonempty : ∃ P : AL16Cutoff College,
      al16SourceMarketClearing demand capacity P)
    (hmass : ∀ P : AL16Cutoff College, outside P + ∑ c, demand P c = 1)
    (houtside_sup : ∀ P Q : AL16Cutoff College, outside P ≤ outside (P ⊔ Q))
    (hdemand_sup : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand Q c ≤ demand (P ⊔ Q) c)
    (houtside_inf : ∀ P Q : AL16Cutoff College, outside (P ⊓ Q) ≤ outside P)
    (hdemand_inf : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand (P ⊓ Q) c ≤ demand P c)
    (hclosed :
      ∀ (P : ℕ → AL16Cutoff College) (Q : AL16Cutoff College),
        (∀ n, al16SourceMarketClearing demand capacity (P n)) →
          al16CoordinatewiseTendsto P Q →
            al16SourceMarketClearing demand capacity Q) :
    CompleteLatticeOn (al16SourceMarketClearing demand capacity) al16CutoffLe where
  exists_valid := hnonempty
  le_refl := fun _ => al16CutoffLe_refl _
  le_trans := fun _ _ _ hPQ hQR => al16CutoffLe_trans hPQ hQR
  le_antisymm := fun _ _ hPQ hQP => al16CutoffLe_antisymm hPQ hQP
  sup_exists := by
    intro S hS
    let T : Set (AL16Cutoff College) :=
      fun P => S P ∧ al16SourceMarketClearing demand capacity P
    have hT : T.Nonempty := by
      rcases hS with ⟨P, hPS, hPclear⟩
      exact ⟨P, hPS, hPclear⟩
    rcases al16FiniteSupEnvelopeApproximation T hT with
      ⟨Pstar, U, hPstar, hU_mem, hU_tendsto⟩
    have hTlub :=
      al16SourceMarketClearing_isLeastUpperBound_of_finite_sup_envelopes_of_limit_closed
        demand outside capacity hmass houtside_sup hdemand_sup hclosed T
        Pstar U (fun P hP => hP.2) hPstar hU_mem hU_tendsto
    refine ⟨Pstar, ?_⟩
    constructor
    · constructor
      · exact hTlub.1.1
      · intro P hPS hPclear
        exact hTlub.1.2 P ⟨hPS, hPclear⟩ hPclear
    · intro R hR
      apply hTlub.2 R
      constructor
      · exact hR.1
      · intro P hPT _hPclear
        exact hR.2 P hPT.1 hPT.2
  inf_exists := by
    intro S hS
    let T : Set (AL16Cutoff College) :=
      fun P => S P ∧ al16SourceMarketClearing demand capacity P
    have hT : T.Nonempty := by
      rcases hS with ⟨P, hPS, hPclear⟩
      exact ⟨P, hPS, hPclear⟩
    rcases al16FiniteInfEnvelopeApproximation T hT with
      ⟨Pstar, U, hPstar, hU_mem, hU_tendsto⟩
    have hTglb :=
      al16SourceMarketClearing_isGreatestLowerBound_of_finite_inf_envelopes_of_limit_closed
        demand outside capacity hmass houtside_sup hdemand_sup houtside_inf hdemand_inf
        hclosed T Pstar U (fun P hP => hP.2) hPstar hU_mem hU_tendsto
    refine ⟨Pstar, ?_⟩
    constructor
    · constructor
      · exact hTglb.1.1
      · intro P hPS hPclear
        exact hTglb.1.2 P ⟨hPS, hPclear⟩ hPclear
    · intro R hR
      apply hTglb.2 R
      constructor
      · exact hR.1
      · intro P hPT _hPclear
        exact hR.2 P hPT.1 hPT.2

/--
Theorem A.1's nonempty complete-lattice conclusion from the preceding
continuum primitives.  The initial clearing witness remains visible because
the source proof begins by establishing nonemptiness separately.
-/
theorem al16TheoremA1_of_continuum_primitives
    (demand : AL16Cutoff College → College → ℝ)
    (outside : AL16Cutoff College → ℝ)
    (capacity : College → ℝ)
    (hmass : ∀ P : AL16Cutoff College, outside P + ∑ c, demand P c = 1)
    (houtside_sup : ∀ P Q : AL16Cutoff College, outside P ≤ outside (P ⊔ Q))
    (hdemand_sup : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand Q c ≤ demand (P ⊔ Q) c)
    (houtside_inf : ∀ P Q : AL16Cutoff College, outside (P ⊓ Q) ≤ outside P)
    (hdemand_inf : ∀ P Q : AL16Cutoff College, ∀ c : College,
      al16CutoffValue P c ≤ al16CutoffValue Q c →
        demand (P ⊓ Q) c ≤ demand P c)
    (hdemand_continuous :
      ∀ (P : ℕ → AL16Cutoff College) (Q : AL16Cutoff College),
        al16CoordinatewiseTendsto P Q →
          ∀ c : College,
            Tendsto (fun n => demand (P n) c) atTop (𝓝 (demand Q c)))
    (hnonempty : ∃ P : AL16Cutoff College, al16SourceMarketClearing demand capacity P) :
    (∃ P : AL16Cutoff College, al16SourceMarketClearing demand capacity P) ∧
      CompleteLatticeOn (al16SourceMarketClearing demand capacity) al16CutoffLe :=
  ⟨hnonempty,
    al16SourceMarketClearing_completeLattice_of_continuum_primitives demand outside
      capacity hnonempty hmass houtside_sup hdemand_sup houtside_inf hdemand_inf
      hdemand_continuous⟩

end AL16SupplyDemandMatching
