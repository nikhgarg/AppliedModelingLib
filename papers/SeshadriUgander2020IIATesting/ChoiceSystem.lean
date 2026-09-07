import Mathlib
import AppliedModelingLib.Foundations.Graph.EvenPairing

/-!
# Finite choice systems and IIA

Source: Seshadri--Ugander (2020), Section 2.1. A choice observation is an
incidence `(x, C)` of an item and an observed choice set. The paper assumes
every observed set has size at least two and positive sampling probability.

The probability layer is deliberately finite: all probability masses below
are real-valued and their simplex properties are supplied explicitly. This is
the exact finite setting of the paper's lower-bound argument.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators

/-- A finite observed choice-set family over a finite item universe. -/
structure ChoiceFrame where
  Item : Type
  instFintypeItem : Fintype Item
  instDecidableEqItem : DecidableEq Item
  SetId : Type
  instFintypeSetId : Fintype SetId
  instDecidableEqSetId : DecidableEq SetId
  members : SetId → Finset Item
  nonempty_sets : Nonempty SetId
  card_two_le : ∀ C, 2 ≤ (members C).card

attribute [instance] ChoiceFrame.instFintypeItem ChoiceFrame.instDecidableEqItem
  ChoiceFrame.instFintypeSetId ChoiceFrame.instDecidableEqSetId

namespace ChoiceFrame

variable (F : ChoiceFrame)

/-- The finite support of item/choice-set incidences, source Section 2.1. -/
def Observation := Σ C : F.SetId, {x : F.Item // x ∈ F.members C}

instance instFintypeObservation : Fintype F.Observation := by
  classical
  letI : Fintype F.Item := F.instFintypeItem
  letI : Fintype F.SetId := F.instFintypeSetId
  exact Sigma.instFintype

noncomputable instance instDecidableEqObservation : DecidableEq F.Observation := by
  classical
  exact inferInstance

/-- The source's `d = Σ_{C ∈ 𝒞} |C|`. -/
def incidenceCount : ℕ := ∑ C : F.SetId, (F.members C).card

theorem observation_card : Fintype.card F.Observation = F.incidenceCount := by
  simp [Observation, incidenceCount]

theorem incidenceCount_pos : 0 < F.incidenceCount := by
  rw [incidenceCount]
  apply Finset.sum_pos
  · intro C _
    exact lt_of_lt_of_le (by omega) (F.card_two_le C)
  · obtain ⟨C⟩ := F.nonempty_sets
    exact ⟨C, Finset.mem_univ _⟩

/-- The choice sets in which an item occurs, i.e. the item-side neighborhood
of the comparison incidence graph. -/
def occurrences (x : F.Item) : Finset F.SetId :=
  Finset.univ.filter (fun C => x ∈ F.members C)

theorem occurrence_card (x : F.Item) :
    Fintype.card {C : F.SetId // x ∈ F.members C} = (F.occurrences x).card := by
  rw [Fintype.card_subtype]
  rfl

/-- The source's Eulerian restriction (Section 2.4): every choice-set size
and every item occurrence count is even.  This is exactly the even-degree
condition on the two parts of the comparison incidence graph. -/
structure Eulerian : Prop where
  set_even : ∀ C, Even (F.members C).card
  item_even : ∀ x, Even (F.occurrences x).card

/-- Pair the incidences at one choice-set vertex using its even degree. -/
noncomputable def Eulerian.setPairing (h : F.Eulerian) (C : F.SetId) :
    AppliedModelingLib.Foundations.Graph.EvenPairing {x : F.Item // x ∈ F.members C} :=
  AppliedModelingLib.Foundations.Graph.EvenPairing.ofEvenCard (by
    simpa using h.set_even C)

/-- Pair the incidences at one item vertex using its even degree. -/
noncomputable def Eulerian.itemPairing (h : F.Eulerian) (x : F.Item) :
    AppliedModelingLib.Foundations.Graph.EvenPairing {C : F.SetId // x ∈ F.members C} :=
  AppliedModelingLib.Foundations.Graph.EvenPairing.ofEvenCard (by
    rw [F.occurrence_card x]
    exact h.item_even x)

end ChoiceFrame

/-- A mass function on the finite observation support. -/
structure ChoiceSystem (F : ChoiceFrame) where
  mass : F.Observation → ℝ
  nonneg : ∀ o, 0 ≤ mass o
  sum_one : ∑ o, mass o = 1

namespace ChoiceSystem

variable {F : ChoiceFrame}

/-- The sampling weight of an observed choice set. -/
def setMass (q : ChoiceSystem F) (C : F.SetId) : ℝ :=
  ∑ x : {x : F.Item // x ∈ F.members C}, q.mass ⟨C, x⟩

theorem setMass_nonneg (q : ChoiceSystem F) (C : F.SetId) : 0 ≤ q.setMass C := by
  apply Finset.sum_nonneg
  intro x _
  exact q.nonneg ⟨C, x⟩

/-- The total mass of observations in which a particular item appears and is
chosen. This is the item sufficient statistic used in Section 4. -/
def itemMass (q : ChoiceSystem F) (x : F.Item) : ℝ :=
  ∑ C : {C : F.SetId // x ∈ F.members C}, q.mass ⟨C, ⟨x, C.2⟩⟩

/-- Strictly positive sampling of every observed set, source Section 2.1. -/
def PositiveSetMass (q : ChoiceSystem F) : Prop := ∀ C, 0 < q.setMass C

/-- The conditional probability of choosing `x` from `C`. -/
noncomputable def conditional (q : ChoiceSystem F) (C : F.SetId)
    (x : {x : F.Item // x ∈ F.members C}) : ℝ :=
  q.mass ⟨C, x⟩ / q.setMass C

/-- Source Section 2.2's Luce/MNL ratio representation, expressed directly
on the joint observation distribution. Positivity of `γ` is source-faithful.
-/
noncomputable def SatisfiesIIA (q : ChoiceSystem F) : Prop :=
  ∃ γ : F.Item → ℝ, (∀ x, 0 < γ x) ∧
    ∀ C x, q.mass ⟨C, x⟩ =
      q.setMass C * γ x.1 / ∑ z ∈ F.members C, γ z

/-- Total-variation distance for finite choice systems, source Section 2.2. -/
noncomputable def totalVariation (q r : ChoiceSystem F) : ℝ :=
  (1 / 2 : ℝ) * ∑ o, |q.mass o - r.mass o|

/-- The uniform choice system `p₀` of source Section 4. -/
noncomputable def uniform (F : ChoiceFrame) : ChoiceSystem F where
  mass _ := 1 / (F.incidenceCount : ℝ)
  nonneg _ := by positivity
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ChoiceFrame.observation_card F]
    simp only [div_eq_mul_inv, one_mul]
    apply mul_inv_cancel₀
    exact_mod_cast Nat.ne_of_gt (ChoiceFrame.incidenceCount_pos F)

theorem uniform_mass (F : ChoiceFrame) (o : F.Observation) :
    (uniform F).mass o = 1 / (F.incidenceCount : ℝ) := rfl

theorem uniform_mass_pos (F : ChoiceFrame) (o : F.Observation) :
    0 < (uniform F).mass o := by
  rw [uniform_mass]
  exact div_pos zero_lt_one (by exact_mod_cast ChoiceFrame.incidenceCount_pos F)

/-- The uniform null samples a choice set with probability proportional to its
cardinality (source Section 4). -/
theorem uniform_setMass (F : ChoiceFrame) (C : F.SetId) :
    (uniform F).setMass C = (F.members C).card / (F.incidenceCount : ℝ) := by
  simp [setMass, uniform_mass, div_eq_mul_inv]

/-- The uniform null `p₀` is an IIA choice system, with every Luce score equal
to one. This is the null used in the paper's testing relaxation (Section 4). -/
theorem uniform_satisfiesIIA (F : ChoiceFrame) : SatisfiesIIA (uniform F) := by
  refine ⟨fun _ => 1, fun _ => zero_lt_one, ?_⟩
  intro C x
  rw [uniform_mass, uniform_setMass]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hset : ((F.members C).card : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le (by omega) (F.card_two_le C))
  have hincidence : (F.incidenceCount : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (ChoiceFrame.incidenceCount_pos F)
  field_simp


end ChoiceSystem

end SeshadriUgander2020IIATesting
