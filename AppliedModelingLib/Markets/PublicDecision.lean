import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic.Linarith

/-!
# Public Decision Markets

Reusable finite definitions for public decision-making markets with binary
issues. This module is intentionally theorem-light: it provides finite
public-decision and pairwise-expansion objects, with small algebraic lemmas
that are independent of any particular Fisher-market existence theory.

## Main declarations

- `BinaryInstance`: finite agents, finite binary issues, and each agent's
  preferred alternative on each issue.
- `Outcome.Valid`: public outcomes satisfying one unit of probability per issue.
- `DisagreementGood`: the unordered pairwise goods used by pairwise issue
  expansion.
- `expandBundle` / `contractBundle`: expansion and contraction maps on one
  bundle.
- `IsAlphaApprox`: multiplicative welfare-approximation predicate.
- `approx_iff_of_value_preserving_maps`: abstract welfare-approximation
  transfer lemma used by reduction proofs.
-/

namespace AppliedModelingLib
namespace PublicDecision

open scoped BigOperators

variable {Agent Issue Good A B : Type*}

/-- A finite binary public-decision instance: `pref i j` is agent `i`'s preferred side. -/
structure BinaryInstance (Agent Issue : Type*) where
  pref : Agent → Issue → Bool

/-- A bundle gives one nonnegative quantity per issue. -/
abbrev Bundle (Issue : Type*) := Issue → ℝ

/-- A public outcome gives one probability for each side of each binary issue. -/
abbrev Outcome (Issue : Type*) := Issue → Bool → ℝ

/-- An allocation gives each agent a quantity of each private good. -/
abbrev Allocation (Agent Good : Type*) := Agent → Good → ℝ

/-- Prices for private goods. -/
abbrev Prices (Good : Type*) := Good → ℝ

/-- Dot-product cost of a bundle at a price vector. -/
def Cost [Fintype Good] (x : Good → ℝ) (p : Prices Good) : ℝ :=
  ∑ g, x g * p g

/-- Personalized per-agent per-issue prices for public decision markets. -/
abbrev PersonalizedPrices (Agent Issue : Type*) := Agent → Issue → ℝ

/-- Utility type for public bundles. -/
abbrev Utility (Agent Issue : Type*) := Agent → Bundle Issue → ℝ

namespace Outcome

/-- Valid public outcomes allocate at most one unit of probability per issue. -/
def Valid (z : Outcome Issue) : Prop :=
  ∀ j, 0 ≤ z j false ∧ 0 ≤ z j true ∧ z j false + z j true ≤ 1

/-- The public bundle induced by an outcome for one agent. -/
def publicBundle (Γ : BinaryInstance Agent Issue) (z : Outcome Issue)
    (i : Agent) : Bundle Issue :=
  fun j => z j (Γ.pref i j)

/-- The midpoint outcome putting probability `1/2` on both sides of every issue. -/
noncomputable def half (Issue : Type*) : Outcome Issue :=
  fun _ _ => (1 : ℝ) / 2

theorem half_valid (Issue : Type*) : Valid (half Issue) := by
  intro j
  norm_num [half]

@[simp] theorem publicBundle_apply
    (Γ : BinaryInstance Agent Issue) (z : Outcome Issue) (i : Agent) (j : Issue) :
    publicBundle Γ z i j = z j (Γ.pref i j) := rfl

@[simp] theorem publicBundle_half
    (Γ : BinaryInstance Agent Issue) (i : Agent) :
    publicBundle Γ (half Issue) i = fun _ => (1 : ℝ) / 2 := by
  funext j
  simp [publicBundle, half]

end Outcome

theorem publicBundle_sum_le_of_disagree
    (Γ : BinaryInstance Agent Issue) (z : Outcome Issue) (hz : Outcome.Valid z)
    {i k : Agent} {j : Issue} (h : Γ.pref i j ≠ Γ.pref k j) :
    Outcome.publicBundle Γ z i j + Outcome.publicBundle Γ z k j ≤ 1 := by
  dsimp [Outcome.publicBundle]
  cases hi : Γ.pref i j <;> cases hk : Γ.pref k j <;>
    simp [hi, hk] at h ⊢
  · exact (hz j).2.2
  · linarith [(hz j).2.2]

theorem publicBundle_le_one
    (Γ : BinaryInstance Agent Issue) (z : Outcome Issue) (hz : Outcome.Valid z)
    (i : Agent) (j : Issue) :
    Outcome.publicBundle Γ z i j ≤ 1 := by
  by_cases hi : Γ.pref i j = false
  · simp [Outcome.publicBundle, hi]
    linarith [(hz j).2.1, (hz j).2.2]
  · have htrue : Γ.pref i j = true := by
      cases hpref : Γ.pref i j <;> simp [hpref] at hi ⊢
    simp [Outcome.publicBundle, htrue]
    linarith [(hz j).1, (hz j).2.2]

/-- Feasibility for a private-good allocation with unit supply of every good. -/
def Allocation.Valid [Fintype Agent] (x : Allocation Agent Good) : Prop :=
  (∀ i g, 0 ≤ x i g) ∧ ∀ g, (∑ i, x i g) ≤ 1

/-- Source affordability predicate. -/
def Affordable [Fintype Good] (budget : ℝ) (p : Prices Good)
    (x : Good → ℝ) : Prop :=
  (∀ g, 0 ≤ x g) ∧ (∑ g, x g * p g) ≤ budget

/-- Demand predicate for a utility over bundles indexed by `Good`. -/
def InDemandSet [Fintype Good] (u : (Good → ℝ) → ℝ)
    (budget : ℝ) (p : Prices Good) (x : Good → ℝ) : Prop :=
  Affordable budget p x ∧
    ∀ y, Affordable budget p y → u y ≤ u x

theorem inDemandSet_add_const_iff [Fintype Good]
    (u : (Good → ℝ) → ℝ) (c budget : ℝ) (p : Prices Good)
    (x : Good → ℝ) :
    InDemandSet (fun y => u y + c) budget p x ↔
      InDemandSet u budget p x := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro y hy
    have hle := h.2 y hy
    linarith
  · intro h
    refine ⟨h.1, ?_⟩
    intro y hy
    have hle := h.2 y hy
    linarith

/--
Local nonsatiation in budget form: any affordable bundle that leaves slack in
the budget has a strictly better affordable alternative.
-/
def LocallyNonsatiatedOnBudget [Fintype Good] (u : (Good → ℝ) → ℝ)
    (budget : ℝ) (p : Prices Good) : Prop :=
  ∀ x, Affordable budget p x → Cost x p < budget →
    ∃ y, Affordable budget p y ∧ u x < u y

theorem no_same_utility_lower_cost_of_demand [Fintype Good]
    {u : (Good → ℝ) → ℝ} {budget : ℝ} {p : Prices Good}
    {x y : Good → ℝ}
    (hy : InDemandSet u budget p y)
    (hlns : LocallyNonsatiatedOnBudget u budget p)
    (hx : Affordable budget p x)
    (hcost : Cost x p < Cost y p)
    (hutil : u x = u y) :
    False := by
  have hslack : Cost x p < budget := lt_of_lt_of_le hcost hy.1.2
  rcases hlns x hx hslack with ⟨z, hz, hz_strict⟩
  have hz_le : u z ≤ u y := hy.2 z hz
  linarith

theorem cost_update_zero_lt_of_positive_contribution
    [Fintype Good] [DecidableEq Good]
    (x : Good → ℝ) (p : Prices Good) (g : Good)
    (hpos : 0 < x g * p g) :
    Cost (Function.update x g 0) p < Cost x p := by
  classical
  have hupdate_fun :
      (fun a => Function.update x g 0 a * p a) =
        Function.update (fun a => x a * p a) g 0 := by
    funext a
    by_cases ha : a = g
    · subst ha
      simp
    · simp [Function.update_of_ne ha]
  have hcost_update :
      Cost (Function.update x g 0) p =
        Finset.sum (Finset.univ : Finset Good)
          (Function.update (fun a => x a * p a) g 0) := by
    simp [Cost, hupdate_fun]
  have hsum_update :
      Finset.sum (Finset.univ : Finset Good)
          (Function.update (fun a => x a * p a) g 0) =
        0 + Finset.sum ((Finset.univ : Finset Good) \ {g})
          (fun a => x a * p a) := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ g)]
  have hsum_orig :
      Cost x p =
        x g * p g + Finset.sum ((Finset.univ : Finset Good) \ {g})
          (fun a => x a * p a) := by
    simp only [Cost]
    rw [← Finset.add_sum_erase (Finset.univ : Finset Good)
      (fun a => x a * p a) (Finset.mem_univ g)]
    congr 1
    rw [Finset.sdiff_singleton_eq_erase]
  rw [hcost_update, hsum_update, hsum_orig]
  linarith

theorem cost_update_lt_of_lower_value
    [Fintype Good] [DecidableEq Good]
    (x : Good → ℝ) (p : Prices Good) (g : Good) (v : ℝ)
    (hlt : v < x g) (hp : 0 < p g) :
    Cost (Function.update x g v) p < Cost x p := by
  classical
  have hupdate_fun :
      (fun a => Function.update x g v a * p a) =
        Function.update (fun a => x a * p a) g (v * p g) := by
    funext a
    by_cases ha : a = g
    · subst ha
      simp
    · simp [Function.update_of_ne ha]
  have hcost_update :
      Cost (Function.update x g v) p =
        Finset.sum (Finset.univ : Finset Good)
          (Function.update (fun a => x a * p a) g (v * p g)) := by
    simp [Cost, hupdate_fun]
  have hsum_update :
      Finset.sum (Finset.univ : Finset Good)
          (Function.update (fun a => x a * p a) g (v * p g)) =
        v * p g + Finset.sum ((Finset.univ : Finset Good) \ {g})
          (fun a => x a * p a) := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ g)]
  have hsum_orig :
      Cost x p =
        x g * p g + Finset.sum ((Finset.univ : Finset Good) \ {g})
          (fun a => x a * p a) := by
    simp only [Cost]
    rw [← Finset.add_sum_erase (Finset.univ : Finset Good)
      (fun a => x a * p a) (Finset.mem_univ g)]
    congr 1
    rw [Finset.sdiff_singleton_eq_erase]
  have hmul : v * p g < x g * p g := mul_lt_mul_of_pos_right hlt hp
  rw [hcost_update, hsum_update, hsum_orig]
  linarith

theorem same_utility_of_demanded_same_cost_extension [Fintype Good]
    (u : (Good → ℝ) → ℝ) (budget : ℝ) (p : Prices Good)
    (x x' : Good → ℝ)
    (hx : InDemandSet u budget p x)
    (hmono : ∀ a b : Good → ℝ, (∀ g, a g ≤ b g) → u a ≤ u b)
    (hx'_nonneg : ∀ g, 0 ≤ x' g)
    (hle : ∀ g, x g ≤ x' g)
    (hcost : Cost x' p = Cost x p) :
    u x' = u x := by
  refine le_antisymm ?_ (hmono x x' hle)
  apply hx.2
  refine ⟨hx'_nonneg, ?_⟩
  have hcost' : (∑ g, x' g * p g) = ∑ g, x g * p g := by
    simpa [Cost] using hcost
  exact hcost'.trans_le hx.1.2

theorem inDemandSet_iff_of_affordable_utility_maps
    [Fintype A] [Fintype B]
    {uA : (A → ℝ) → ℝ} {uB : (B → ℝ) → ℝ}
    {pA : Prices A} {pB : Prices B} {budget : ℝ}
    (toB : (A → ℝ) → (B → ℝ))
    (toA : (B → ℝ) → (A → ℝ))
    (x : A → ℝ)
    (h_toB_affordable :
      ∀ x, Affordable budget pA x ↔ Affordable budget pB (toB x))
    (h_toA_affordable :
      ∀ y, Affordable budget pB y → Affordable budget pA (toA y))
    (h_toB_utility : ∀ x, uB (toB x) = uA x)
    (h_toA_utility : ∀ y, uA (toA y) = uB y) :
    InDemandSet uA budget pA x ↔ InDemandSet uB budget pB (toB x) := by
  constructor
  · intro hx
    refine ⟨(h_toB_affordable x).1 hx.1, ?_⟩
    intro y hy
    have hle : uA (toA y) ≤ uA x := hx.2 (toA y) (h_toA_affordable y hy)
    rw [h_toA_utility y] at hle
    rw [h_toB_utility x]
    exact hle
  · intro hx
    have hxA : Affordable budget pA x := (h_toB_affordable x).2 hx.1
    refine ⟨hxA, ?_⟩
    intro y hy
    have hle : uB (toB y) ≤ uB (toB x) :=
      hx.2 (toB y) ((h_toB_affordable y).1 hy)
    rw [h_toB_utility y] at hle
    rw [h_toB_utility x] at hle
    exact hle

/-- Fisher market equilibrium in finite private-good form. -/
def FisherEquilibrium [Fintype Agent] [Fintype Good]
    (u : Agent → (Good → ℝ) → ℝ) (budget : Agent → ℝ)
    (x : Allocation Agent Good) (p : Prices Good) : Prop :=
  (∀ i, InDemandSet (u i) (budget i) p (x i)) ∧
    (∀ g, (∑ i, x i g) ≤ 1 ∧ (0 < p g → (∑ i, x i g) = 1))

/-- Personalized-pricing market equilibrium in finite public-decision form. -/
def PersonalizedPricingEquilibrium [Fintype Agent] [Fintype Issue]
    (Γ : BinaryInstance Agent Issue) (u : Utility Agent Issue)
    (budget : Agent → ℝ)
    (y : Agent → Bundle Issue) (p : PersonalizedPrices Agent Issue) : Prop :=
  (∀ i, InDemandSet (u i) (budget i) (p i) (y i)) ∧
    ∃ z : Outcome Issue,
      (∀ j, z j false + z j true = 1) ∧
      (∀ i j, y i j ≤ z j (Γ.pref i j)) ∧
      (∀ i j, 0 < p i j → y i j = z j (Γ.pref i j))

/-- The personalized-pricing market-clearing condition for a fixed public outcome. -/
def PersonalizedClearing
    (Γ : BinaryInstance Agent Issue)
    (y : Agent → Bundle Issue) (p : PersonalizedPrices Agent Issue)
    (z : Outcome Issue) : Prop :=
  Outcome.Valid z ∧
    (∀ j, z j false + z j true = 1) ∧
    (∀ i j, y i j ≤ z j (Γ.pref i j)) ∧
    (∀ i j, 0 < p i j → y i j = z j (Γ.pref i j))

theorem same_utility_of_personalized_clearing [Fintype Issue]
    (Γ : BinaryInstance Agent Issue)
    (u : Utility Agent Issue) (budget : Agent → ℝ)
    (y : Agent → Bundle Issue) (p : PersonalizedPrices Agent Issue)
    (z : Outcome Issue) (i : Agent)
    (hdemand : InDemandSet (u i) (budget i) (p i) (y i))
    (hmono : ∀ a b : Bundle Issue, (∀ j, a j ≤ b j) → u i a ≤ u i b)
    (hp : ∀ j, 0 ≤ p i j)
    (hclear : PersonalizedClearing Γ y p z) :
    u i (Outcome.publicBundle Γ z i) = u i (y i) := by
  apply same_utility_of_demanded_same_cost_extension
    (u i) (budget i) (p i) (y i) (Outcome.publicBundle Γ z i)
    hdemand hmono
  · intro j
    dsimp [Outcome.publicBundle]
    by_cases hpref : Γ.pref i j
    · simpa [hpref] using (hclear.1 j).2.1
    · simpa [hpref] using (hclear.1 j).1
  · intro j
    exact hclear.2.2.1 i j
  · dsimp [Cost]
    refine Finset.sum_congr rfl ?_
    intro j hj
    by_cases hpos : 0 < p i j
    · rw [← hclear.2.2.2 i j hpos]
    · have hp0 : p i j = 0 := le_antisymm (not_lt.mp hpos) (hp j)
      simp [hp0]

namespace BinaryInstance

/-- Agents `i` and `k` disagree on issue `j`. -/
def Disagree (Γ : BinaryInstance Agent Issue) (i k : Agent) (j : Issue) : Prop :=
  Γ.pref i j ≠ Γ.pref k j

/-- The unordered pair `pair` is a disagreement pair on issue `j`. -/
def DisagreePair (Γ : BinaryInstance Agent Issue) (j : Issue)
    (pair : Sym2 Agent) : Prop :=
  ∃ i k, pair = s(i, k) ∧ Γ.Disagree i k j

/-- The finite set of opponents of agent `i` on issue `j`. -/
noncomputable def opponentSet [Fintype Agent]
    (Γ : BinaryInstance Agent Issue) (i : Agent) (j : Issue) : Finset Agent :=
  by
    classical
    exact (Finset.univ : Finset Agent).filter fun k => Γ.Disagree i k j

/--
Regularity condition for using contraction as a total function: every agent has
at least one disagreeing opponent on every issue. The finite minimum is
otherwise over an empty set.
-/
def HasOpponentOnEveryIssue [Fintype Agent]
    (Γ : BinaryInstance Agent Issue) : Prop :=
  ∀ i j, (Γ.opponentSet i j).Nonempty

/-- Agents whose preferred side on issue `j` is `b`. -/
noncomputable def sideSet [Fintype Agent]
    (Γ : BinaryInstance Agent Issue) (j : Issue) (b : Bool) : Finset Agent :=
  (Finset.univ : Finset Agent).filter fun i => Γ.pref i j = b

theorem opponentSet_eq_sideSet_not [Fintype Agent]
    (Γ : BinaryInstance Agent Issue) {i : Agent} {j : Issue} {b : Bool}
    (hi : Γ.pref i j = b) :
    Γ.opponentSet i j = Γ.sideSet j (!b) := by
  classical
  ext k
  cases b <;> cases hk : Γ.pref k j <;>
    simp [opponentSet, sideSet, Disagree, hi, hk]

theorem sideSet_nonempty [Fintype Agent] [Nonempty Agent]
    (Γ : BinaryInstance Agent Issue) (hopp : Γ.HasOpponentOnEveryIssue)
    (j : Issue) (b : Bool) :
    (Γ.sideSet j b).Nonempty := by
  classical
  let i0 : Agent := Classical.choice inferInstance
  by_cases hi : Γ.pref i0 j = b
  · exact ⟨i0, by simp [sideSet, hi]⟩
  · rcases hopp i0 j with ⟨k, hk_mem⟩
    have hk_disagree : Γ.Disagree i0 k j := (Finset.mem_filter.mp hk_mem).2
    have hk_side : Γ.pref k j = b := by
      cases h0 : Γ.pref i0 j <;> cases hb : b <;>
        cases hk : Γ.pref k j <;> simp [Disagree, h0, hb, hk] at hi hk_disagree ⊢
    exact ⟨k, by simp [sideSet, hk_side]⟩

/-- Maximum public bundle quantity among agents on a fixed side of an issue. -/
noncomputable def sideSup [Fintype Agent] [Nonempty Agent]
    (Γ : BinaryInstance Agent Issue) (hopp : Γ.HasOpponentOnEveryIssue)
    (y : Agent → Bundle Issue) (j : Issue) (b : Bool) : ℝ :=
  (Γ.sideSet j b).sup' (Γ.sideSet_nonempty hopp j b) fun i => y i j

theorem le_sideSup [Fintype Agent] [Nonempty Agent]
    (Γ : BinaryInstance Agent Issue) (hopp : Γ.HasOpponentOnEveryIssue)
    (y : Agent → Bundle Issue) {i : Agent} {j : Issue} {b : Bool}
    (hi : Γ.pref i j = b) :
    y i j ≤ Γ.sideSup hopp y j b := by
  classical
  exact Finset.le_sup'
    (f := fun i => y i j)
    (by simp [sideSet, hi])

theorem sideSup_le [Fintype Agent] [Nonempty Agent]
    (Γ : BinaryInstance Agent Issue) (hopp : Γ.HasOpponentOnEveryIssue)
    (y : Agent → Bundle Issue) {j : Issue} {b : Bool} {a : ℝ}
    (h : ∀ i, Γ.pref i j = b → y i j ≤ a) :
    Γ.sideSup hopp y j b ≤ a := by
  classical
  exact Finset.sup'_le (Γ.sideSet_nonempty hopp j b) (fun i => y i j)
    (by
      intro i hi
      exact h i (by simpa [sideSet] using hi))

/--
Canonical public outcome used in the pairwise-expansion reduction proof:
side `false` is the maximum contracted false-side quantity, and side `true`
is its complement.
-/
noncomputable def outcomeFromSideSup [Fintype Agent] [Nonempty Agent]
    (Γ : BinaryInstance Agent Issue) (hopp : Γ.HasOpponentOnEveryIssue)
    (y : Agent → Bundle Issue) : Outcome Issue :=
  fun j b => if b then 1 - Γ.sideSup hopp y j false else Γ.sideSup hopp y j false

@[simp] theorem outcomeFromSideSup_false [Fintype Agent] [Nonempty Agent]
    (Γ : BinaryInstance Agent Issue) (hopp : Γ.HasOpponentOnEveryIssue)
    (y : Agent → Bundle Issue) (j : Issue) :
    Γ.outcomeFromSideSup hopp y j false = Γ.sideSup hopp y j false := by
  simp [outcomeFromSideSup]

@[simp] theorem outcomeFromSideSup_true [Fintype Agent] [Nonempty Agent]
    (Γ : BinaryInstance Agent Issue) (hopp : Γ.HasOpponentOnEveryIssue)
    (y : Agent → Bundle Issue) (j : Issue) :
    Γ.outcomeFromSideSup hopp y j true = 1 - Γ.sideSup hopp y j false := by
  simp [outcomeFromSideSup]

theorem outcomeFromSideSup_sum_eq_one [Fintype Agent] [Nonempty Agent]
    (Γ : BinaryInstance Agent Issue) (hopp : Γ.HasOpponentOnEveryIssue)
    (y : Agent → Bundle Issue) (j : Issue) :
    Γ.outcomeFromSideSup hopp y j false + Γ.outcomeFromSideSup hopp y j true = 1 := by
  simp

theorem bundle_le_outcomeFromSideSup_of_pair_bounds
    [Fintype Agent] [Nonempty Agent]
    (Γ : BinaryInstance Agent Issue) (hopp : Γ.HasOpponentOnEveryIssue)
    (y : Agent → Bundle Issue)
    (hpair : ∀ i k j, Γ.Disagree i k j → y i j + y k j ≤ 1) :
    ∀ i j, y i j ≤ Γ.outcomeFromSideSup hopp y j (Γ.pref i j) := by
  intro i j
  by_cases hi : Γ.pref i j = false
  · simpa [outcomeFromSideSup, hi] using
      (Γ.le_sideSup hopp y (i := i) (j := j) (b := false) hi)
  · have hi_true : Γ.pref i j = true := by
      cases hpref : Γ.pref i j <;> simp [hpref] at hi ⊢
    have hsup_le : Γ.sideSup hopp y j false ≤ 1 - y i j := by
      apply Γ.sideSup_le hopp y
      intro k hk_false
      have hdis : Γ.Disagree i k j := by
        simp [Disagree, hi_true, hk_false]
      have hle := hpair i k j hdis
      linarith
    have : y i j ≤ 1 - Γ.sideSup hopp y j false := by
      linarith
    simpa [outcomeFromSideSup, hi_true] using this

theorem outcomeFromSideSup_valid_of_pair_bounds
    [Fintype Agent] [Nonempty Agent]
    (Γ : BinaryInstance Agent Issue) (hopp : Γ.HasOpponentOnEveryIssue)
    (y : Agent → Bundle Issue)
    (hy_nonneg : ∀ i j, 0 ≤ y i j)
    (hpair : ∀ i k j, Γ.Disagree i k j → y i j + y k j ≤ 1) :
    Outcome.Valid (Γ.outcomeFromSideSup hopp y) := by
  intro j
  have hfalse_nonneg :
      0 ≤ Γ.outcomeFromSideSup hopp y j false := by
    rcases Γ.sideSet_nonempty hopp j false with ⟨i, hi_mem⟩
    have hi_false : Γ.pref i j = false := by
      simpa [sideSet] using hi_mem
    have hle := Γ.le_sideSup hopp y (i := i) (j := j) (b := false) hi_false
    simpa [outcomeFromSideSup] using (hy_nonneg i j).trans hle
  have hside_le_one : Γ.sideSup hopp y j false ≤ 1 := by
    apply Γ.sideSup_le hopp y
    intro i hi_false
    rcases Γ.sideSet_nonempty hopp j true with ⟨k, hk_mem⟩
    have hk_true : Γ.pref k j = true := by
      simpa [sideSet] using hk_mem
    have hdis : Γ.Disagree i k j := by
      simp [Disagree, hi_false, hk_true]
    have hle := hpair i k j hdis
    have hk_nonneg := hy_nonneg k j
    linarith
  have htrue_nonneg :
      0 ≤ Γ.outcomeFromSideSup hopp y j true := by
    simp [outcomeFromSideSup]
    linarith
  refine ⟨hfalse_nonneg, htrue_nonneg, ?_⟩
  simp [outcomeFromSideSup]

end BinaryInstance

/-- The unordered pairwise goods of the pairwise issue expansion `R(Γ)`. -/
structure DisagreementGood (Γ : BinaryInstance Agent Issue) where
  issue : Issue
  pair : Sym2 Agent
  disagree : Γ.DisagreePair issue pair

namespace DisagreementGood

/-- Pairwise disagreement goods are finite when agents and issues are finite. -/
noncomputable def equivSubtype (Γ : BinaryInstance Agent Issue) :
    DisagreementGood Γ ≃
      {x : Issue × Sym2 Agent // Γ.DisagreePair x.1 x.2} where
  toFun g := ⟨(g.issue, g.pair), g.disagree⟩
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv g := by
    cases g
    rfl
  right_inv x := by
    cases x with
    | mk val h =>
      cases val
      rfl

noncomputable instance instFintype
    [Fintype Agent] [Fintype Issue]
    (Γ : BinaryInstance Agent Issue) : Fintype (DisagreementGood Γ) := by
  classical
  letI : Fintype {x : Issue × Sym2 Agent // Γ.DisagreePair x.1 x.2} :=
    Fintype.ofFinite _
  exact Fintype.ofEquiv {x : Issue × Sym2 Agent // Γ.DisagreePair x.1 x.2}
    (equivSubtype Γ).symm

variable (Γ : BinaryInstance Agent Issue)

/-- The pairwise good `(i,k,j)` for two agents who disagree on issue `j`. -/
def ofAgents (i k : Agent) (j : Issue) (h : Γ.Disagree i k j) :
    DisagreementGood Γ where
  issue := j
  pair := s(i, k)
  disagree := ⟨i, k, rfl, h⟩

@[simp] theorem ofAgents_issue (i k : Agent) (j : Issue) (h : Γ.Disagree i k j) :
    (ofAgents Γ i k j h).issue = j := rfl

@[simp] theorem ofAgents_pair (i k : Agent) (j : Issue) (h : Γ.Disagree i k j) :
    (ofAgents Γ i k j h).pair = s(i, k) := rfl

theorem ofAgents_swap (i k : Agent) (j : Issue) (h : Γ.Disagree i k j) :
    ofAgents Γ i k j h = ofAgents Γ k i j h.symm := by
  apply (equivSubtype Γ).injective
  apply Subtype.ext
  simp [equivSubtype, ofAgents, Sym2.eq_swap]

@[simp] theorem left_mem_ofAgents (i k : Agent) (j : Issue) (h : Γ.Disagree i k j) :
    i ∈ (ofAgents Γ i k j h).pair := by
  simp [ofAgents, Sym2.mem_iff]

@[simp] theorem right_mem_ofAgents (i k : Agent) (j : Issue) (h : Γ.Disagree i k j) :
    k ∈ (ofAgents Γ i k j h).pair := by
  simp [ofAgents, Sym2.mem_iff]

end DisagreementGood

namespace PairwiseExpansion

variable (Γ : BinaryInstance Agent Issue)

/-- Expand one public bundle to pairwise goods. -/
noncomputable def expandBundle (i : Agent) (y : Bundle Issue) :
    DisagreementGood Γ → ℝ :=
  by
    classical
    exact fun g => if i ∈ g.pair then y g.issue else 0

/-- Expand every agent's public bundle. -/
noncomputable def expandAllocation (y : Agent → Bundle Issue) :
    Allocation Agent (DisagreementGood Γ) :=
  fun i => expandBundle Γ i (y i)

/-- Contract one expanded bundle to issue quantities. -/
noncomputable def contractBundle [Fintype Agent]
    (y : DisagreementGood Γ → ℝ) (i : Agent) : Bundle Issue :=
  by
    classical
    exact fun j =>
      if h : (Γ.opponentSet i j).Nonempty then
        (Γ.opponentSet i j).inf' h fun k =>
          if hk : Γ.Disagree i k j then
            y (DisagreementGood.ofAgents Γ i k j hk)
          else 0
      else 1

/-- Contract every agent's expanded bundle. -/
noncomputable def contractAllocation [Fintype Agent]
    (y : Allocation Agent (DisagreementGood Γ)) : Agent → Bundle Issue :=
  fun i => contractBundle Γ (y i) i

@[simp] theorem expandBundle_mk_left
    (i k : Agent) (j : Issue) (h : Γ.Disagree i k j) (y : Bundle Issue) :
    expandBundle Γ i y (DisagreementGood.ofAgents Γ i k j h) = y j := by
  simp [expandBundle]

@[simp] theorem expandBundle_mk_right
    (i k : Agent) (j : Issue) (h : Γ.Disagree i k j) (y : Bundle Issue) :
    expandBundle Γ k y (DisagreementGood.ofAgents Γ i k j h) = y j := by
  simp [expandBundle]

theorem contract_expandBundle_eq [Fintype Agent]
    (hopp : Γ.HasOpponentOnEveryIssue) (i : Agent) (y : Bundle Issue) :
    contractBundle Γ (expandBundle Γ i y) i = y := by
  classical
  funext j
  rw [contractBundle]
  have hne : (Γ.opponentSet i j).Nonempty := hopp i j
  simp only [hne, dite_true]
  refine Finset.inf'_eq_of_forall hne (fun k => if hk : Γ.Disagree i k j then
          expandBundle Γ i y (DisagreementGood.ofAgents Γ i k j hk) else 0) ?_
  intro k hk_mem
  have hk : Γ.Disagree i k j := by
    exact (Finset.mem_filter.mp hk_mem).2
  dsimp
  rw [dif_pos hk]
  exact expandBundle_mk_left Γ i k j hk y

theorem contract_expandAllocation_eq [Fintype Agent]
    (hopp : Γ.HasOpponentOnEveryIssue) (y : Agent → Bundle Issue) :
    contractAllocation Γ (expandAllocation Γ y) = y := by
  funext i
  exact contract_expandBundle_eq Γ hopp i (y i)

/-- Prices induced in the public market by pairwise-good prices. -/
noncomputable def contractPrices [Fintype Agent]
    (p : Prices (DisagreementGood Γ)) : PersonalizedPrices Agent Issue :=
  by
    classical
    exact fun i j =>
      Finset.sum (Γ.opponentSet i j) fun k =>
        if hk : Γ.Disagree i k j then p (DisagreementGood.ofAgents Γ i k j hk) else 0

/-- Pairwise goods on issue `j` incident to agent `i`. -/
noncomputable def incidentGoods [Fintype (DisagreementGood Γ)]
    (i : Agent) (j : Issue) : Finset (DisagreementGood Γ) :=
  by
    classical
    exact (Finset.univ : Finset (DisagreementGood Γ)).filter fun g =>
      g.issue = j ∧ i ∈ g.pair

/-- All pairwise goods incident to agent `i`. -/
noncomputable def agentIncidentGoods [Fintype (DisagreementGood Γ)]
    (i : Agent) : Finset (DisagreementGood Γ) :=
  by
    classical
    exact (Finset.univ : Finset (DisagreementGood Γ)).filter fun g => i ∈ g.pair

/-- Expanded dot-product cost restricted to goods incident to agent `i`. -/
noncomputable def incidentPairwiseCost [Fintype (DisagreementGood Γ)]
    (i : Agent) (y : DisagreementGood Γ → ℝ)
    (p : Prices (DisagreementGood Γ)) : ℝ :=
  Finset.sum (agentIncidentGoods Γ i) fun g => y g * p g

/--
Goods-indexed version of `Rfrom(p)`: the price of an issue is the sum of prices
of all pairwise goods on that issue incident to the agent.
-/
noncomputable def contractPricesByGoods [Fintype (DisagreementGood Γ)]
    (p : Prices (DisagreementGood Γ)) : PersonalizedPrices Agent Issue :=
  fun i j => Finset.sum (incidentGoods Γ i j) fun g => p g

/--
The expanded-market cost of agent `i`'s own pairwise goods.

This is the support-restricted sum over goods incident to `i`.
-/
noncomputable def ownPairwiseCost [Fintype Agent] [Fintype Issue]
    (i : Agent) (y : DisagreementGood Γ → ℝ)
    (p : Prices (DisagreementGood Γ)) : ℝ :=
  by
    classical
    exact
      ∑ j, Finset.sum (Γ.opponentSet i j) fun k =>
        if hk : Γ.Disagree i k j then
          y (DisagreementGood.ofAgents Γ i k j hk) *
            p (DisagreementGood.ofAgents Γ i k j hk)
        else 0

theorem publicCost_contractPrices_eq_ownPairwiseCost
    [Fintype Agent] [Fintype Issue]
    (i : Agent) (y : Bundle Issue) (p : Prices (DisagreementGood Γ)) :
    Cost y (contractPrices Γ p i) =
      ownPairwiseCost Γ i (expandBundle Γ i y) p := by
  classical
  simp only [Cost, contractPrices, ownPairwiseCost]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk_mem
  by_cases hk : Γ.Disagree i k j
  · simp [hk]
  · exact (hk (Finset.mem_filter.mp hk_mem).2).elim

theorem expandedCost_eq_publicCost_contractPricesByGoods
    [Fintype Issue] [Fintype (DisagreementGood Γ)]
    (i : Agent) (y : Bundle Issue) (p : Prices (DisagreementGood Γ)) :
    Cost (expandBundle Γ i y) p = Cost y (contractPricesByGoods Γ p i) := by
  classical
  simp only [Cost, contractPricesByGoods, incidentGoods]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_filter]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro g hg
  by_cases hi : i ∈ g.pair
  · have hcollapse :
        (∑ j, if g.issue = j ∧ i ∈ g.pair then y j * p g else 0) =
          y g.issue * p g := by
      rw [Finset.sum_eq_single (g.issue)]
      · simp [hi]
      · intro j hj hne
        have hne' : g.issue ≠ j := fun h => hne h.symm
        simp [hne', hi]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    simp [expandBundle, hi]
  · have hcollapse :
        (∑ j, if g.issue = j ∧ i ∈ g.pair then y j * p g else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      simp [hi]
    simp [expandBundle, hi]

theorem expandBundle_nonneg
    (i : Agent) {y : Bundle Issue} (hy : ∀ j, 0 ≤ y j) :
    ∀ g : DisagreementGood Γ, 0 ≤ expandBundle Γ i y g := by
  intro g
  by_cases hi : i ∈ g.pair
  · simp [expandBundle, hi, hy g.issue]
  · simp [expandBundle, hi]

theorem nonneg_of_expandBundle_nonneg
    [Fintype Agent]
    (hopp : Γ.HasOpponentOnEveryIssue)
    (i : Agent) {y : Bundle Issue}
    (hy : ∀ g : DisagreementGood Γ, 0 ≤ expandBundle Γ i y g) :
    ∀ j, 0 ≤ y j := by
  classical
  intro j
  rcases hopp i j with ⟨k, hk_mem⟩
  have hk : Γ.Disagree i k j := (Finset.mem_filter.mp hk_mem).2
  simpa using hy (DisagreementGood.ofAgents Γ i k j hk)

theorem contractBundle_nonneg [Fintype Agent]
    (i : Agent) {y : DisagreementGood Γ → ℝ}
    (hy : ∀ g : DisagreementGood Γ, 0 ≤ y g) :
    ∀ j, 0 ≤ contractBundle Γ y i j := by
  classical
  intro j
  rw [contractBundle]
  by_cases hne : (Γ.opponentSet i j).Nonempty
  · simp only [hne, dite_true]
    refine Finset.le_inf'
      (f := fun k =>
        if hk : Γ.Disagree i k j then
          y (DisagreementGood.ofAgents Γ i k j hk)
        else 0) hne ?_
    intro k hk_mem
    by_cases hk : Γ.Disagree i k j
    · simpa [hk] using hy (DisagreementGood.ofAgents Γ i k j hk)
    · simp [hk]
  · simp [hne]

theorem affordable_expandBundle_iff_contractPricesByGoods
    [Fintype Agent] [Fintype Issue] [Fintype (DisagreementGood Γ)]
    (hopp : Γ.HasOpponentOnEveryIssue)
    (budget : ℝ) (i : Agent) (y : Bundle Issue)
    (p : Prices (DisagreementGood Γ)) :
    Affordable budget (contractPricesByGoods Γ p i) y ↔
      Affordable budget p (expandBundle Γ i y) := by
  constructor
  · intro h
    refine ⟨expandBundle_nonneg Γ i h.1, ?_⟩
    change Cost (expandBundle Γ i y) p ≤ budget
    rw [expandedCost_eq_publicCost_contractPricesByGoods Γ i y p]
    exact h.2
  · intro h
    refine ⟨nonneg_of_expandBundle_nonneg Γ hopp i h.1, ?_⟩
    change Cost y (contractPricesByGoods Γ p i) ≤ budget
    rw [← expandedCost_eq_publicCost_contractPricesByGoods Γ i y p]
    exact h.2

theorem incidentPairwiseCost_le_cost_of_nonnegative
    [Fintype (DisagreementGood Γ)]
    (i : Agent) (y : DisagreementGood Γ → ℝ) (p : Prices (DisagreementGood Γ))
    (hy : ∀ g : DisagreementGood Γ, 0 ≤ y g)
    (hp : ∀ g : DisagreementGood Γ, 0 ≤ p g) :
    incidentPairwiseCost Γ i y p ≤ Cost y p := by
  classical
  simp only [Cost, incidentPairwiseCost, agentIncidentGoods]
  have hsplit :
      Finset.sum
          ((Finset.univ : Finset (DisagreementGood Γ)).filter
            (fun g => i ∈ g.pair)) (fun g => y g * p g) +
        Finset.sum
          ((Finset.univ : Finset (DisagreementGood Γ)).filter
            (fun g => ¬ i ∈ g.pair)) (fun g => y g * p g) =
        Finset.sum (Finset.univ : Finset (DisagreementGood Γ))
          (fun g => y g * p g) := by
    rw [Finset.sum_filter_add_sum_filter_not]
  calc
    Finset.sum
        ((Finset.univ : Finset (DisagreementGood Γ)).filter
          (fun g => i ∈ g.pair)) (fun g => y g * p g)
        ≤
        Finset.sum
          ((Finset.univ : Finset (DisagreementGood Γ)).filter
            (fun g => i ∈ g.pair)) (fun g => y g * p g) +
          Finset.sum
            ((Finset.univ : Finset (DisagreementGood Γ)).filter
              (fun g => ¬ i ∈ g.pair)) (fun g => y g * p g) := by
      exact le_add_of_nonneg_right
        (Finset.sum_nonneg fun g hg => mul_nonneg (hy g) (hp g))
    _ = Finset.sum (Finset.univ : Finset (DisagreementGood Γ))
          (fun g => y g * p g) := hsplit

theorem cost_eq_incidentPairwiseCost_of_nonincident_zero
    [Fintype (DisagreementGood Γ)]
    (i : Agent) (y : DisagreementGood Γ → ℝ) (p : Prices (DisagreementGood Γ))
    (hzero : ∀ g : DisagreementGood Γ, i ∉ g.pair → y g * p g = 0) :
    Cost y p = incidentPairwiseCost Γ i y p := by
  classical
  simp only [Cost, incidentPairwiseCost, agentIncidentGoods]
  calc
    Finset.sum (Finset.univ : Finset (DisagreementGood Γ)) (fun g => y g * p g) =
        Finset.sum
            ((Finset.univ : Finset (DisagreementGood Γ)).filter
              (fun g => i ∈ g.pair)) (fun g => y g * p g) +
          Finset.sum
            ((Finset.univ : Finset (DisagreementGood Γ)).filter
              (fun g => ¬ i ∈ g.pair)) (fun g => y g * p g) := by
      rw [Finset.sum_filter_add_sum_filter_not]
    _ = Finset.sum
          ((Finset.univ : Finset (DisagreementGood Γ)).filter
            (fun g => i ∈ g.pair)) (fun g => y g * p g) := by
      rw [add_eq_left]
      exact Finset.sum_eq_zero fun g hg => hzero g (by
        exact (Finset.mem_filter.mp hg).2)

theorem disagree_other_of_mem_pair
    [DecidableEq Agent] (g : DisagreementGood Γ) {i : Agent} (hi : i ∈ g.pair) :
    Γ.Disagree i (Sym2.Mem.other' hi) g.issue := by
  rcases g.disagree with ⟨a, b, hpair, hab⟩
  have hmk : s(i, Sym2.Mem.other' hi) = s(a, b) := by
    rw [Sym2.other_spec' hi, hpair]
  have hpairs : (i, Sym2.Mem.other' hi) = (a, b) ∨
      (i, Sym2.Mem.other' hi) = (a, b).swap := by
    exact Sym2.mk_eq_mk_iff.mp hmk
  rcases hpairs with hpairs | hpairs
  · have hi_a : i = a := congrArg Prod.fst hpairs
    have hother_b : Sym2.Mem.other' hi = b := congrArg Prod.snd hpairs
    intro h
    apply hab
    calc
      Γ.pref a g.issue = Γ.pref i g.issue := by rw [hi_a]
      _ = Γ.pref (Sym2.Mem.other' hi) g.issue := h
      _ = Γ.pref b g.issue := by rw [hother_b]
  · have hi_b : i = b := congrArg Prod.fst hpairs
    have hother_a : Sym2.Mem.other' hi = a := congrArg Prod.snd hpairs
    intro h
    apply hab.symm
    calc
      Γ.pref b g.issue = Γ.pref i g.issue := by rw [hi_b]
      _ = Γ.pref (Sym2.Mem.other' hi) g.issue := h
      _ = Γ.pref a g.issue := by rw [hother_a]

theorem eq_ofAgents_other_of_mem_pair
    [DecidableEq Agent] (g : DisagreementGood Γ) {i : Agent} (hi : i ∈ g.pair) :
    g = DisagreementGood.ofAgents Γ i (Sym2.Mem.other' hi) g.issue
      (disagree_other_of_mem_pair Γ g hi) := by
  apply (DisagreementGood.equivSubtype Γ).injective
  apply Subtype.ext
  simp [DisagreementGood.equivSubtype, DisagreementGood.ofAgents, Sym2.other_spec' hi]

theorem contractBundle_le_of_mem_pair [Fintype Agent] [DecidableEq Agent]
    (i : Agent) (y : DisagreementGood Γ → ℝ)
    (g : DisagreementGood Γ) (hi : i ∈ g.pair) :
    contractBundle Γ y i g.issue ≤ y g := by
  classical
  let k := Sym2.Mem.other' hi
  have hk : Γ.Disagree i k g.issue := disagree_other_of_mem_pair Γ g hi
  have hk_mem : k ∈ Γ.opponentSet i g.issue := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
  have hne : (Γ.opponentSet i g.issue).Nonempty := ⟨k, hk_mem⟩
  have hmin :
      contractBundle Γ y i g.issue ≤
        y (DisagreementGood.ofAgents Γ i k g.issue hk) := by
    rw [contractBundle]
    simp only [hne, dite_true]
    have hle :=
      (Finset.inf'_le
        (fun k =>
          if hk : Γ.Disagree i k g.issue then
            y (DisagreementGood.ofAgents Γ i k g.issue hk)
          else 0)
        hk_mem)
    rw [dif_pos hk] at hle
    exact hle
  have heq :
      DisagreementGood.ofAgents Γ i k g.issue hk = g := by
    exact (eq_ofAgents_other_of_mem_pair Γ g hi).symm
  rw [heq] at hmin
  exact hmin

theorem contractAllocation_pair_sum_le_of_valid
    [Fintype Agent] [DecidableEq Agent] [Fintype (DisagreementGood Γ)]
    (x : Allocation Agent (DisagreementGood Γ)) (hx : Allocation.Valid x)
    {i k : Agent} {j : Issue} (h : Γ.Disagree i k j) :
    contractAllocation Γ x i j + contractAllocation Γ x k j ≤ 1 := by
  classical
  let g : DisagreementGood Γ := DisagreementGood.ofAgents Γ i k j h
  have hi : i ∈ g.pair := by
    dsimp [g]
    exact DisagreementGood.left_mem_ofAgents Γ i k j h
  have hk : k ∈ g.pair := by
    dsimp [g]
    exact DisagreementGood.right_mem_ofAgents Γ i k j h
  have hik : i ≠ k := by
    intro heq
    apply h
    rw [heq]
  have hci : contractAllocation Γ x i j ≤ x i g := by
    dsimp [contractAllocation, g]
    simpa using contractBundle_le_of_mem_pair Γ i (x i) g hi
  have hck : contractAllocation Γ x k j ≤ x k g := by
    dsimp [contractAllocation, g]
    simpa using contractBundle_le_of_mem_pair Γ k (x k) g hk
  have htwo : x i g + x k g ≤ ∑ a, x a g := by
    have hsum_erase_nonneg :
        0 ≤ Finset.sum ((Finset.univ.erase i : Finset Agent).erase k)
          (fun a => x a g) :=
      Finset.sum_nonneg fun a _ => hx.1 a g
    have hsum_univ :
        (∑ a : Agent, x a g) =
          x i g + x k g +
            Finset.sum ((Finset.univ.erase i : Finset Agent).erase k)
              (fun a => x a g) := by
      rw [← Finset.add_sum_erase (Finset.univ : Finset Agent)
        (fun a => x a g) (Finset.mem_univ i)]
      have hk_mem_erase : k ∈ (Finset.univ.erase i : Finset Agent) :=
        Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ k⟩
      rw [← Finset.add_sum_erase (Finset.univ.erase i : Finset Agent)
        (fun a => x a g) hk_mem_erase]
      rw [add_assoc]
    rw [hsum_univ]
    exact le_add_of_nonneg_right hsum_erase_nonneg
  calc
    contractAllocation Γ x i j + contractAllocation Γ x k j
        ≤ x i g + x k g := add_le_add hci hck
    _ ≤ ∑ a, x a g := htwo
    _ ≤ 1 := (hx.2 g)

theorem contractBundle_update_nonincident
    [Fintype Agent] [DecidableEq (DisagreementGood Γ)]
    (i : Agent) (y : DisagreementGood Γ → ℝ)
    (g : DisagreementGood Γ) (v : ℝ)
    (hnot : i ∉ g.pair) :
    contractBundle Γ (Function.update y g v) i = contractBundle Γ y i := by
  classical
  funext j
  rw [contractBundle, contractBundle]
  by_cases hne : (Γ.opponentSet i j).Nonempty
  · simp only [hne, dite_true]
    congr 1
    funext k
    by_cases hk : Γ.Disagree i k j
    · have hneq : DisagreementGood.ofAgents Γ i k j hk ≠ g := by
        intro heq
        apply hnot
        rw [← heq]
        exact DisagreementGood.left_mem_ofAgents Γ i k j hk
      simp [hk, Function.update_of_ne hneq]
    · simp [hk]
  · simp [hne]

theorem nonincident_cost_zero_of_expanded_demand
    [Fintype Agent] [Fintype (DisagreementGood Γ)] [DecidableEq (DisagreementGood Γ)]
    (i : Agent) (u : Bundle Issue → ℝ)
    (budget : ℝ) (p : Prices (DisagreementGood Γ))
    (y : DisagreementGood Γ → ℝ)
    (hy_nonneg : ∀ g : DisagreementGood Γ, 0 ≤ y g)
    (hp_nonneg : ∀ g : DisagreementGood Γ, 0 ≤ p g)
    (hdemand :
      InDemandSet (fun x => u (contractBundle Γ x i)) budget p y)
    (hlns :
      LocallyNonsatiatedOnBudget (fun x => u (contractBundle Γ x i)) budget p) :
    ∀ g : DisagreementGood Γ, i ∉ g.pair → y g * p g = 0 := by
  intro g hnot
  by_contra hnonzero
  have hprod_nonneg : 0 ≤ y g * p g := mul_nonneg (hy_nonneg g) (hp_nonneg g)
  have hpos : 0 < y g * p g := lt_of_le_of_ne hprod_nonneg (Ne.symm hnonzero)
  let y' : DisagreementGood Γ → ℝ := Function.update y g 0
  have hy'_nonneg : ∀ a : DisagreementGood Γ, 0 ≤ y' a := by
    intro a
    by_cases ha : a = g
    · subst ha
      simp [y']
    · simp [y', Function.update_of_ne ha, hy_nonneg a]
  have hcost_lt : Cost y' p < Cost y p :=
    cost_update_zero_lt_of_positive_contribution y p g hpos
  have hy'_affordable : Affordable budget p y' := by
    refine ⟨hy'_nonneg, ?_⟩
    exact (le_of_lt (lt_of_lt_of_le hcost_lt hdemand.1.2))
  have hutil : u (contractBundle Γ y' i) = u (contractBundle Γ y i) := by
    rw [contractBundle_update_nonincident Γ i y g 0 hnot]
  exact no_same_utility_lower_cost_of_demand
    hdemand hlns hy'_affordable hcost_lt hutil

theorem contractBundle_update_incident_to_contract_value
    [Fintype Agent] [DecidableEq Agent] [DecidableEq (DisagreementGood Γ)]
    (i : Agent) (y : DisagreementGood Γ → ℝ)
    (g : DisagreementGood Γ) (hi : i ∈ g.pair) :
    contractBundle Γ
        (Function.update y g (contractBundle Γ y i g.issue)) i =
      contractBundle Γ y i := by
  classical
  funext j
  by_cases hissue : j = g.issue
  · subst hissue
    let k := Sym2.Mem.other' hi
    have hk : Γ.Disagree i k g.issue := disagree_other_of_mem_pair Γ g hi
    have hk_mem : k ∈ Γ.opponentSet i g.issue :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
    have hne : (Γ.opponentSet i g.issue).Nonempty := ⟨k, hk_mem⟩
    let oldf : Agent → ℝ := fun k =>
      if hk : Γ.Disagree i k g.issue then
        y (DisagreementGood.ofAgents Γ i k g.issue hk)
      else 0
    let newf : Agent → ℝ := fun k =>
      if hk : Γ.Disagree i k g.issue then
        Function.update y g (contractBundle Γ y i g.issue)
          (DisagreementGood.ofAgents Γ i k g.issue hk)
      else 0
    have hcontract :
        contractBundle Γ y i g.issue =
          (Γ.opponentSet i g.issue).inf' hne oldf := by
      rw [contractBundle]
      simp [hne, oldf]
    have hcontract_update :
        contractBundle Γ
            (Function.update y g (contractBundle Γ y i g.issue)) i g.issue =
          (Γ.opponentSet i g.issue).inf' hne newf := by
      rw [contractBundle]
      simp [hne, newf]
    rw [hcontract_update, hcontract]
    apply le_antisymm
    · have hle := Finset.inf'_le newf hk_mem
      have heq :
          DisagreementGood.ofAgents Γ i k g.issue hk = g := by
        exact (eq_ofAgents_other_of_mem_pair Γ g hi).symm
      have hnewk :
          newf k = (Γ.opponentSet i g.issue).inf' hne oldf := by
        dsimp [newf]
        rw [dif_pos hk]
        rw [heq]
        rw [Function.update_self]
        exact hcontract
      simpa [hnewk] using hle
    · refine Finset.le_inf' (f := newf) hne ?_
      intro k' hk'_mem
      have hk' : Γ.Disagree i k' g.issue := (Finset.mem_filter.mp hk'_mem).2
      have hle_old := Finset.inf'_le oldf hk'_mem
      by_cases heq :
          DisagreementGood.ofAgents Γ i k' g.issue hk' = g
      · have hnewk' :
            newf k' = (Γ.opponentSet i g.issue).inf' hne oldf := by
          dsimp [newf]
          rw [dif_pos hk']
          rw [heq]
          rw [Function.update_self]
          exact hcontract
        rw [hnewk']
      · have hnewk' : newf k' = oldf k' := by
          simp [newf, oldf, hk', Function.update_of_ne heq]
        simpa [hnewk'] using hle_old
  · rw [contractBundle]
    by_cases hne : (Γ.opponentSet i j).Nonempty
    · simp only [hne, dite_true]
      let oldf : Agent → ℝ := fun k =>
        if hk : Γ.Disagree i k j then
          y (DisagreementGood.ofAgents Γ i k j hk)
        else 0
      let newf : Agent → ℝ := fun k =>
        if hk : Γ.Disagree i k j then
          Function.update y g (contractBundle Γ y i g.issue)
            (DisagreementGood.ofAgents Γ i k j hk)
        else 0
      have hR :
          contractBundle Γ y i j =
            (Γ.opponentSet i j).inf' hne oldf := by
        rw [contractBundle]
        simp [hne, oldf]
      change (Γ.opponentSet i j).inf' hne newf = contractBundle Γ y i j
      rw [hR]
      apply congrArg ((Γ.opponentSet i j).inf' hne)
      funext k
      by_cases hk : Γ.Disagree i k j
      · have hneq :
            DisagreementGood.ofAgents Γ i k j hk ≠ g := by
          intro heq
          apply hissue
          rw [← heq]
          rfl
        simp [newf, oldf, hk, Function.update_of_ne hneq]
      · simp [newf, oldf, hk]
    · have hR : contractBundle Γ y i j = 1 := by
        rw [contractBundle]
        simp [hne]
      rw [hR]
      simp [hne]

theorem incident_priced_min_of_expanded_demand
    [Fintype Agent] [DecidableEq Agent] [Fintype (DisagreementGood Γ)]
    [DecidableEq (DisagreementGood Γ)]
    (i : Agent) (u : Bundle Issue → ℝ)
    (budget : ℝ) (p : Prices (DisagreementGood Γ))
    (y : DisagreementGood Γ → ℝ)
    (hy_nonneg : ∀ g : DisagreementGood Γ, 0 ≤ y g)
    (hp_nonneg : ∀ g : DisagreementGood Γ, 0 ≤ p g)
    (hdemand :
      InDemandSet (fun x => u (contractBundle Γ x i)) budget p y)
    (hlns :
      LocallyNonsatiatedOnBudget (fun x => u (contractBundle Γ x i)) budget p) :
    ∀ g : DisagreementGood Γ,
      i ∈ g.pair → y g ≠ contractBundle Γ y i g.issue → p g = 0 := by
  intro g hi hnot_min
  by_cases hp_pos : 0 < p g
  · have hle_min : contractBundle Γ y i g.issue ≤ y g :=
      contractBundle_le_of_mem_pair Γ i y g hi
    have hlt_min : contractBundle Γ y i g.issue < y g :=
      lt_of_le_of_ne hle_min (Ne.symm hnot_min)
    let y' : DisagreementGood Γ → ℝ :=
      Function.update y g (contractBundle Γ y i g.issue)
    have hy'_nonneg : ∀ a : DisagreementGood Γ, 0 ≤ y' a := by
      intro a
      by_cases ha : a = g
      · subst ha
        simp [y', contractBundle_nonneg Γ i hy_nonneg]
      · simp [y', Function.update_of_ne ha, hy_nonneg a]
    have hcost_lt : Cost y' p < Cost y p :=
      cost_update_lt_of_lower_value y p g
        (contractBundle Γ y i g.issue) hlt_min hp_pos
    have hy'_affordable : Affordable budget p y' := by
      refine ⟨hy'_nonneg, ?_⟩
      exact le_of_lt (lt_of_lt_of_le hcost_lt hdemand.1.2)
    have hutil : u (contractBundle Γ y' i) = u (contractBundle Γ y i) := by
      rw [contractBundle_update_incident_to_contract_value Γ i y g hi]
    exact (no_same_utility_lower_cost_of_demand
      hdemand hlns hy'_affordable hcost_lt hutil).elim
  · exact le_antisymm (not_lt.mp hp_pos) (hp_nonneg g)

theorem publicCost_contractBundle_contractPricesByGoods_le_incidentPairwiseCost
    [Fintype Agent] [DecidableEq Agent] [Fintype Issue] [DecidableEq Issue]
    [Fintype (DisagreementGood Γ)]
    (i : Agent) (y : DisagreementGood Γ → ℝ) (p : Prices (DisagreementGood Γ))
    (hp : ∀ g : DisagreementGood Γ, 0 ≤ p g) :
    Cost (contractBundle Γ y i) (contractPricesByGoods Γ p i) ≤
      incidentPairwiseCost Γ i y p := by
  simp only [Cost, contractPricesByGoods, incidentGoods, incidentPairwiseCost,
    agentIncidentGoods]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_filter]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_le_sum ?_
  intro g hg
  by_cases hi : i ∈ g.pair
  · simpa [hi] using
      mul_le_mul_of_nonneg_right
        (contractBundle_le_of_mem_pair Γ i y g hi) (hp g)
  · simp [hi]

theorem publicCost_contractBundle_contractPricesByGoods_le_of_nonnegative
    [Fintype Agent] [DecidableEq Agent] [Fintype Issue] [DecidableEq Issue]
    [Fintype (DisagreementGood Γ)]
    (i : Agent) (y : DisagreementGood Γ → ℝ) (p : Prices (DisagreementGood Γ))
    (hy : ∀ g : DisagreementGood Γ, 0 ≤ y g)
    (hp : ∀ g : DisagreementGood Γ, 0 ≤ p g) :
    Cost (contractBundle Γ y i) (contractPricesByGoods Γ p i) ≤ Cost y p :=
  (publicCost_contractBundle_contractPricesByGoods_le_incidentPairwiseCost
    Γ i y p hp).trans
    (incidentPairwiseCost_le_cost_of_nonnegative Γ i y p hy hp)

theorem publicCost_contractBundle_contractPricesByGoods_eq_incidentPairwiseCost_of_priced_min
    [Fintype Agent] [DecidableEq Agent] [Fintype Issue] [DecidableEq Issue]
    [Fintype (DisagreementGood Γ)]
    (i : Agent) (y : DisagreementGood Γ → ℝ) (p : Prices (DisagreementGood Γ))
    (hpriced :
      ∀ g : DisagreementGood Γ,
        i ∈ g.pair → y g ≠ contractBundle Γ y i g.issue → p g = 0) :
    Cost (contractBundle Γ y i) (contractPricesByGoods Γ p i) =
      incidentPairwiseCost Γ i y p := by
  simp only [Cost, contractPricesByGoods, incidentGoods, incidentPairwiseCost,
    agentIncidentGoods]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_filter]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro g hg
  by_cases hi : i ∈ g.pair
  · by_cases hy : y g = contractBundle Γ y i g.issue
    · simp [hi, hy]
    · have hp0 : p g = 0 := hpriced g hi hy
      simp [hi, hp0]
  · simp [hi]

theorem publicCost_contractBundle_contractPricesByGoods_eq_of_no_waste
    [Fintype Agent] [DecidableEq Agent] [Fintype Issue] [DecidableEq Issue]
    [Fintype (DisagreementGood Γ)]
    (i : Agent) (y : DisagreementGood Γ → ℝ) (p : Prices (DisagreementGood Γ))
    (hnonincident : ∀ g : DisagreementGood Γ, i ∉ g.pair → y g * p g = 0)
    (hpriced :
      ∀ g : DisagreementGood Γ,
        i ∈ g.pair → y g ≠ contractBundle Γ y i g.issue → p g = 0) :
    Cost (contractBundle Γ y i) (contractPricesByGoods Γ p i) = Cost y p := by
  rw [cost_eq_incidentPairwiseCost_of_nonincident_zero Γ i y p hnonincident]
  exact publicCost_contractBundle_contractPricesByGoods_eq_incidentPairwiseCost_of_priced_min
    Γ i y p hpriced

theorem publicCost_contractBundle_contractPricesByGoods_le_of_nonincident_zero
    [Fintype Agent] [DecidableEq Agent] [Fintype Issue] [DecidableEq Issue]
    [Fintype (DisagreementGood Γ)]
    (i : Agent) (y : DisagreementGood Γ → ℝ) (p : Prices (DisagreementGood Γ))
    (hp : ∀ g : DisagreementGood Γ, 0 ≤ p g)
    (hzero : ∀ g : DisagreementGood Γ, i ∉ g.pair → y g * p g = 0) :
    Cost (contractBundle Γ y i) (contractPricesByGoods Γ p i) ≤ Cost y p := by
  rw [cost_eq_incidentPairwiseCost_of_nonincident_zero Γ i y p hzero]
  exact publicCost_contractBundle_contractPricesByGoods_le_incidentPairwiseCost
    Γ i y p hp

theorem publicCost_contractBundle_contractPrices_le_ownPairwiseCost
    [Fintype Agent] [Fintype Issue]
    (hopp : Γ.HasOpponentOnEveryIssue)
    (i : Agent) (y : DisagreementGood Γ → ℝ) (p : Prices (DisagreementGood Γ))
    (hp : ∀ g : DisagreementGood Γ, 0 ≤ p g) :
    Cost (contractBundle Γ y i) (contractPrices Γ p i) ≤
      ownPairwiseCost Γ i y p := by
  classical
  simp only [Cost, contractPrices, ownPairwiseCost]
  refine Finset.sum_le_sum ?_
  intro j hj
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro k hk_mem
  have hk : Γ.Disagree i k j := (Finset.mem_filter.mp hk_mem).2
  have hmin :
      contractBundle Γ y i j ≤ y (DisagreementGood.ofAgents Γ i k j hk) := by
    rw [contractBundle]
    have hne : (Γ.opponentSet i j).Nonempty := hopp i j
    simp only [hne, dite_true]
    simpa [hk] using
      (Finset.inf'_le
        (fun k =>
          if hk : Γ.Disagree i k j then
            y (DisagreementGood.ofAgents Γ i k j hk)
          else 0)
        hk_mem)
  have hp_nonneg : 0 ≤ p (DisagreementGood.ofAgents Γ i k j hk) :=
    hp (DisagreementGood.ofAgents Γ i k j hk)
  simpa [hk] using mul_le_mul_of_nonneg_right hmin hp_nonneg

theorem publicCost_contractBundle_contractPrices_eq_ownPairwiseCost_of_priced_min
    [Fintype Agent] [Fintype Issue]
    (i : Agent) (y : DisagreementGood Γ → ℝ) (p : Prices (DisagreementGood Γ))
    (hpriced :
      ∀ (j : Issue) (k : Agent) (hk : Γ.Disagree i k j),
        y (DisagreementGood.ofAgents Γ i k j hk) ≠ contractBundle Γ y i j →
          p (DisagreementGood.ofAgents Γ i k j hk) = 0) :
    Cost (contractBundle Γ y i) (contractPrices Γ p i) =
      ownPairwiseCost Γ i y p := by
  classical
  simp only [Cost, contractPrices, ownPairwiseCost]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk_mem
  have hk : Γ.Disagree i k j := (Finset.mem_filter.mp hk_mem).2
  by_cases hEq :
      y (DisagreementGood.ofAgents Γ i k j hk) = contractBundle Γ y i j
  · simp [hk, hEq]
  · have hp0 := hpriced j k hk hEq
    simp [hk, hp0]

theorem expandAllocation_sum_eq_pair
    [Fintype Agent] [DecidableEq Agent]
    (x : Agent → Bundle Issue) (g : DisagreementGood Γ)
    {i : Agent} (hi : i ∈ g.pair) :
    (∑ a : Agent, expandAllocation Γ x a g) =
      x i g.issue + x (Sym2.Mem.other' hi) g.issue := by
  classical
  let k : Agent := Sym2.Mem.other' hi
  have hk : k ∈ g.pair := Sym2.other_mem' hi
  have hik : i ≠ k := by
    have hdis : Γ.Disagree i k g.issue :=
      disagree_other_of_mem_pair Γ g hi
    intro heq
    apply hdis
    rw [heq]
  have htail_zero :
      Finset.sum ((Finset.univ.erase i : Finset Agent).erase k)
          (fun a => expandAllocation Γ x a g) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro a ha
    have hak : a ≠ k := (Finset.mem_erase.mp ha).1
    have ha_erase_i : a ∈ (Finset.univ.erase i : Finset Agent) :=
      (Finset.mem_erase.mp ha).2
    have hai : a ≠ i := (Finset.mem_erase.mp ha_erase_i).1
    have hnot : a ∉ g.pair := by
      intro hag
      have hpair : s(i, k) = g.pair := Sym2.other_spec' hi
      have hag_pair : a ∈ s(i, k) := by
        rwa [hpair]
      have ha_or : a = i ∨ a = k := by
        simpa [Sym2.mem_iff] using hag_pair
      rcases ha_or with rfl | rfl
      · exact hai rfl
      · exact hak rfl
    simp [expandAllocation, expandBundle, hnot]
  rw [← Finset.add_sum_erase (Finset.univ : Finset Agent)
    (fun a => expandAllocation Γ x a g) (Finset.mem_univ i)]
  have hk_mem_erase : k ∈ (Finset.univ.erase i : Finset Agent) :=
    Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ k⟩
  rw [← Finset.add_sum_erase (Finset.univ.erase i : Finset Agent)
    (fun a => expandAllocation Γ x a g) hk_mem_erase]
  rw [htail_zero, add_zero]
  simp [expandAllocation, expandBundle, hi, hk, k]

theorem expand_publicBundle_pair_sum_le
    (z : Outcome Issue) (hz : Outcome.Valid z)
    {i k : Agent} {j : Issue} (h : Γ.Disagree i k j) :
    expandBundle Γ i (Outcome.publicBundle Γ z i) (DisagreementGood.ofAgents Γ i k j h) +
      expandBundle Γ k (Outcome.publicBundle Γ z k) (DisagreementGood.ofAgents Γ i k j h) ≤ 1 := by
  simpa using publicBundle_sum_le_of_disagree Γ z hz h

end PairwiseExpansion

/-- `x` is an `α`-approximation to maximizing `welfare` over `feasible`. -/
def IsAlphaApprox (feasible : A → Prop) (welfare : A → ℝ) (α : ℝ) (x : A) : Prop :=
  feasible x ∧ ∀ y, feasible y → α * welfare y ≤ welfare x

namespace IsAlphaApprox

theorem value_le_of_one_approx {feasible : A → Prop} {welfare : A → ℝ} {x y : A}
    (h : IsAlphaApprox feasible welfare 1 x) (hy : feasible y) :
    welfare y ≤ welfare x := by
  simpa using h.2 y hy

end IsAlphaApprox

/--
Abstract transfer of multiplicative approximation through a pair of
value-preserving feasible maps.
-/
theorem approx_iff_of_value_preserving_maps
    {feasibleA : A → Prop} {feasibleB : B → Prop}
    {welfareA : A → ℝ} {welfareB : B → ℝ}
    (toB : A → B) (toA : B → A) (α : ℝ) (x : A)
    (h_toB_feasible : ∀ a, feasibleA a ↔ feasibleB (toB a))
    (h_toA_feasible : ∀ b, feasibleB b → feasibleA (toA b))
    (h_toB_value : ∀ a, feasibleA a → welfareB (toB a) = welfareA a)
    (h_toA_value : ∀ b, feasibleB b → welfareA (toA b) = welfareB b) :
    IsAlphaApprox feasibleA welfareA α x ↔
      IsAlphaApprox feasibleB welfareB α (toB x) := by
  constructor
  · intro hx
    refine ⟨(h_toB_feasible x).1 hx.1, ?_⟩
    intro b hb
    have hxb : α * welfareA (toA b) ≤ welfareA x := hx.2 (toA b) (h_toA_feasible b hb)
    rw [h_toA_value b hb] at hxb
    rw [h_toB_value x hx.1]
    exact hxb
  · intro hx
    have hxA : feasibleA x := (h_toB_feasible x).2 hx.1
    refine ⟨hxA, ?_⟩
    intro a ha
    have hxa : α * welfareB (toB a) ≤ welfareB (toB x) :=
      hx.2 (toB a) ((h_toB_feasible a).1 ha)
    rw [h_toB_value a ha] at hxa
    rw [h_toB_value x hxA] at hxa
    exact hxa

end PublicDecision
end AppliedModelingLib
