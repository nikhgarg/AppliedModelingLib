import SeshadriUgander2020IIATesting.AppendixProjection
import SeshadriUgander2020IIATesting.FiniteProbability

/-!
# IIA models near simplex corners

Source: Seshadri--Ugander (2020), Appendix, Fact `cvx_hull_dense`.

This layer constructs the source's joint Luce choice systems from arbitrary
choice-set weights and positive item scores.  The subsequent finite-density
argument uses the construction to approximate every incidence-simplex corner.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators

namespace ChoiceSystem

variable {F : ChoiceFrame}

@[ext] theorem ext {q r : ChoiceSystem F} (hmass : ∀ o, q.mass o = r.mass o) : q = r := by
  cases q
  cases r
  congr
  funext o
  exact hmass o

/-- The Luce normalizing denominator within one observed choice set. -/
noncomputable def luceDenominator (γ : F.Item → ℝ) (C : F.SetId) : ℝ :=
  ∑ z ∈ F.members C, γ z

theorem luceDenominator_pos (γ : F.Item → ℝ) (hγ : ∀ x, 0 < γ x)
    (C : F.SetId) : 0 < luceDenominator γ C := by
  obtain ⟨z, hz⟩ : (F.members C).Nonempty := by
    apply Finset.card_pos.mp
    exact lt_of_lt_of_le (by omega) (F.card_two_le C)
  unfold luceDenominator
  refine Finset.sum_pos' (fun y hy => (hγ y).le) ?_
  exact ⟨z, hz, hγ z⟩

theorem sum_subtype_gamma_eq_luceDenominator (γ : F.Item → ℝ) (C : F.SetId) :
    (∑ x : {x : F.Item // x ∈ F.members C}, γ x.1) = luceDenominator γ C := by
  unfold luceDenominator
  exact (Finset.sum_subtype (s := F.members C)
    (p := fun x => x ∈ F.members C) (h := by intro x; rfl) (f := γ)).symm

/-- One Luce conditional row has unit mass. -/
theorem luce_row_sum (w : FiniteDistribution F.SetId) (γ : F.Item → ℝ)
    (hγ : ∀ x, 0 < γ x) (C : F.SetId) :
    (∑ x : {x : F.Item // x ∈ F.members C},
      w.mass C * γ x.1 / luceDenominator γ C) = w.mass C := by
  have hden : luceDenominator γ C ≠ 0 := (luceDenominator_pos γ hγ C).ne'
  calc
    (∑ x : {x : F.Item // x ∈ F.members C},
        w.mass C * γ x.1 / luceDenominator γ C) =
        ∑ x : {x : F.Item // x ∈ F.members C},
          w.mass C * (γ x.1 / luceDenominator γ C) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ = w.mass C * ∑ x : {x : F.Item // x ∈ F.members C},
          γ x.1 / luceDenominator γ C := by
            rw [Finset.mul_sum]
    _ = w.mass C *
        ((∑ x : {x : F.Item // x ∈ F.members C}, γ x.1) /
          luceDenominator γ C) := by
            rw [Finset.sum_div]
    _ = w.mass C * (luceDenominator γ C / luceDenominator γ C) := by
            rw [sum_subtype_gamma_eq_luceDenominator]
    _ = w.mass C := by field_simp

/-- A joint finite choice system with arbitrary set weights and Luce item
scores.  This is the source's ratio representation in joint-mass form. -/
noncomputable def luceJoint (w : FiniteDistribution F.SetId)
    (γ : F.Item → ℝ) (hγ : ∀ x, 0 < γ x) : ChoiceSystem F where
  mass o := w.mass o.1 * γ o.2.1 / luceDenominator γ o.1
  nonneg o := by
    exact div_nonneg (mul_nonneg (w.nonneg o.1) (hγ o.2.1).le)
      (luceDenominator_pos γ hγ o.1).le
  sum_one := by
    change (∑ o : Sigma fun C : F.SetId => {x : F.Item // x ∈ F.members C},
      w.mass o.1 * γ o.2.1 / luceDenominator γ o.1) = 1
    rw [Fintype.sum_sigma]
    calc
      (∑ C : F.SetId, ∑ x : {x : F.Item // x ∈ F.members C},
        w.mass C * γ x.1 / luceDenominator γ C) = ∑ C : F.SetId, w.mass C := by
          apply Finset.sum_congr rfl
          intro C _
          exact luce_row_sum w γ hγ C
      _ = 1 := w.sum_one

theorem luceJoint_setMass (w : FiniteDistribution F.SetId)
    (γ : F.Item → ℝ) (hγ : ∀ x, 0 < γ x) (C : F.SetId) :
    (luceJoint w γ hγ).setMass C = w.mass C := by
  unfold setMass luceJoint
  change (∑ x : {x : F.Item // x ∈ F.members C},
    w.mass C * γ x.1 / luceDenominator γ C) = w.mass C
  exact luce_row_sum w γ hγ C

/-- Every joint Luce construction satisfies the source's IIA ratio model. -/
theorem luceJoint_satisfiesIIA (w : FiniteDistribution F.SetId)
    (γ : F.Item → ℝ) (hγ : ∀ x, 0 < γ x) :
    (luceJoint w γ hγ).SatisfiesIIA := by
  refine ⟨γ, hγ, ?_⟩
  intro C x
  rw [luceJoint_setMass]
  rfl

/-- The point mass at one observed incidence, viewed as a choice system. -/
noncomputable def pure (o₀ : F.Observation) : ChoiceSystem F where
  mass o := if o = o₀ then 1 else 0
  nonneg o := by split_ifs <;> positivity
  sum_one := by
    classical
    simp

@[simp] theorem pure_mass (o₀ o : F.Observation) :
    (pure o₀).mass o = if o = o₀ then 1 else 0 := rfl

/-- Every coordinate of a finite choice system has mass at most one. -/
theorem mass_le_one (q : ChoiceSystem F) (o : F.Observation) : q.mass o ≤ 1 := by
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset F.Observation)
    q.mass (Finset.mem_univ o)
  rw [q.sum_one] at hsplit
  have hrest_nonneg : 0 ≤ ∑ x ∈ (Finset.univ.erase o), q.mass x := by
    apply Finset.sum_nonneg
    intro x _
    exact q.nonneg x
  linarith

/-- The total-variation distance to an incidence point mass is one minus the
candidate's mass at that incidence. -/
theorem totalVariation_pure_right (q : ChoiceSystem F) (o₀ : F.Observation) :
    totalVariation q (pure o₀) = 1 - q.mass o₀ := by
  have hle : q.mass o₀ ≤ 1 := mass_le_one q o₀
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset F.Observation)
    q.mass (Finset.mem_univ o₀)
  rw [q.sum_one] at hsplit
  have habs_rest :
      (∑ o ∈ Finset.univ.erase o₀, |q.mass o - (pure o₀).mass o|) =
        ∑ o ∈ Finset.univ.erase o₀, q.mass o := by
    apply Finset.sum_congr rfl
    intro o ho
    have hne : o ≠ o₀ := Finset.ne_of_mem_erase ho
    rw [pure_mass, if_neg hne, sub_zero, abs_of_nonneg (q.nonneg o)]
  unfold totalVariation
  rw [← Finset.sum_erase_add (Finset.univ : Finset F.Observation)
    (fun o => |q.mass o - (pure o₀).mass o|) (Finset.mem_univ o₀)]
  rw [pure_mass, if_pos rfl, abs_of_nonpos (sub_nonpos.mpr hle), habs_rest]
  linarith

/-- The deterministic distribution over observed choice sets. -/
noncomputable def pureSetWeight (C₀ : F.SetId) : FiniteDistribution F.SetId where
  mass C := if C = C₀ then 1 else 0
  nonneg C := by split_ifs <;> positivity
  sum_one := by
    classical
    simp

@[simp] theorem pureSetWeight_mass (C₀ C : F.SetId) :
    (pureSetWeight C₀).mass C = if C = C₀ then 1 else 0 := rfl

/-- Scores concentrating on one specified item. -/
noncomputable def cornerScores (x₀ : F.Item) (t : ℝ) : F.Item → ℝ :=
  fun x => if x = x₀ then t else 1

@[simp] theorem cornerScores_self (x₀ : F.Item) (t : ℝ) :
    cornerScores x₀ t x₀ = t := by simp [cornerScores]

@[simp] theorem cornerScores_ne {x x₀ : F.Item} (h : x ≠ x₀) (t : ℝ) :
    cornerScores x₀ t x = 1 := by simp [cornerScores, h]

/-- The normalizer of a corner score: one high-score item and unit scores on
the remaining members. -/
theorem luceDenominator_cornerScores (C : F.SetId)
    (x₀ : {x : F.Item // x ∈ F.members C}) (t : ℝ) :
    luceDenominator (cornerScores x₀.1 t) C =
      t + ((F.members C).erase x₀.1).card := by
  unfold luceDenominator cornerScores
  calc
    (∑ z ∈ F.members C, if z = x₀.1 then t else 1) =
        ∑ z ∈ F.members C, (1 + if z = x₀.1 then t - 1 else 0) := by
          apply Finset.sum_congr rfl
          intro z hz
          by_cases hzx : z = x₀.1 <;> simp [hzx]
    _ = (F.members C).card +
        ∑ z ∈ F.members C, (if z = x₀.1 then t - 1 else 0) := by
          rw [Finset.sum_add_distrib]
          simp
    _ = (F.members C).card + (t - 1) := by
          rw [Finset.sum_ite_eq' (F.members C) x₀.1 (fun _ => t - 1), if_pos x₀.2]
    _ = t + ((F.members C).erase x₀.1).card := by
          rw [Finset.card_erase_of_mem x₀.2]
          have hcard : 1 ≤ (F.members C).card :=
            Finset.card_pos.mpr ⟨x₀.1, x₀.2⟩
          rw [Nat.cast_sub hcard]
          ring

/-- The IIA choice system concentrating its set weight on `C₀` and its Luce
scores on `x₀`. -/
noncomputable def iiaCorner (C₀ : F.SetId)
    (x₀ : {x : F.Item // x ∈ F.members C₀}) (t : ℝ) (ht : 0 < t) :
    ChoiceSystem F :=
  luceJoint (pureSetWeight C₀) (cornerScores x₀.1 t) (by
    intro x
    by_cases hx : x = x₀.1
    · simp [cornerScores, hx, ht]
    · simp [cornerScores, hx])

theorem iiaCorner_satisfiesIIA (C₀ : F.SetId)
    (x₀ : {x : F.Item // x ∈ F.members C₀}) (t : ℝ) (ht : 0 < t) :
    (iiaCorner C₀ x₀ t ht).SatisfiesIIA := by
  apply luceJoint_satisfiesIIA

theorem iiaCorner_mass_focus (C₀ : F.SetId)
    (x₀ : {x : F.Item // x ∈ F.members C₀}) (t : ℝ) (ht : 0 < t) :
    (iiaCorner C₀ x₀ t ht).mass ⟨C₀, x₀⟩ =
      t / (t + ((F.members C₀).erase x₀.1).card) := by
  unfold iiaCorner luceJoint
  change (pureSetWeight C₀).mass C₀ * cornerScores x₀.1 t x₀.1 /
      luceDenominator (cornerScores x₀.1 t) C₀ = _
  rw [pureSetWeight_mass, if_pos rfl, cornerScores_self,
    luceDenominator_cornerScores]
  ring

/-- Exact total-variation distance from an IIA corner construction to its
target incidence point mass. -/
theorem iiaCorner_totalVariation_pure (C₀ : F.SetId)
    (x₀ : {x : F.Item // x ∈ F.members C₀}) (t : ℝ) (ht : 0 < t) :
    totalVariation (iiaCorner C₀ x₀ t ht) (pure ⟨C₀, x₀⟩) =
      ((F.members C₀).erase x₀.1).card /
        (t + ((F.members C₀).erase x₀.1).card) := by
  have hden : t + (((F.members C₀).erase x₀.1).card : ℝ) ≠ 0 := by
    exact (add_pos_of_pos_of_nonneg ht (by positivity)).ne'
  rw [totalVariation_pure_right, iiaCorner_mass_focus]
  field_simp
  ring

/-- Every incidence-simplex corner is arbitrarily close in total variation to
an IIA choice system. This is the constructive ingredient in Appendix Fact
`cvx_hull_dense`. -/
theorem exists_iia_near_pure (C₀ : F.SetId)
    (x₀ : {x : F.Item // x ∈ F.members C₀}) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ChoiceSystem F, q.SatisfiesIIA ∧
      totalVariation q (pure ⟨C₀, x₀⟩) < ε := by
  let m : ℝ := ((F.members C₀).erase x₀.1).card
  let t : ℝ := (m + 1) / ε
  have hm_nonneg : 0 ≤ m := by
    dsimp [m]
    positivity
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos (by linarith) hε
  have hden_pos : 0 < t + m := add_pos_of_pos_of_nonneg ht hm_nonneg
  have hεt : ε * t = m + 1 := by
    dsimp [t]
    field_simp [hε.ne']
  refine ⟨iiaCorner C₀ x₀ t ht, iiaCorner_satisfiesIIA C₀ x₀ t ht, ?_⟩
  rw [iiaCorner_totalVariation_pure]
  change m / (t + m) < ε
  apply (div_lt_iff₀ hden_pos).2
  rw [mul_add, hεt]
  nlinarith [mul_nonneg hε.le hm_nonneg]

/-- A finite convex mixture of choice systems, indexed by the incidence
support. -/
noncomputable def finiteMixture (weight : ChoiceSystem F)
    (component : F.Observation → ChoiceSystem F) : ChoiceSystem F where
  mass o := ∑ i : F.Observation, weight.mass i * (component i).mass o
  nonneg o := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (weight.nonneg i) ((component i).nonneg o)
  sum_one := by
    rw [Finset.sum_comm]
    calc
      (∑ i : F.Observation, ∑ o : F.Observation,
        weight.mass i * (component i).mass o) =
          ∑ i : F.Observation, weight.mass i *
            ∑ o : F.Observation, (component i).mass o := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
      _ = ∑ i : F.Observation, weight.mass i := by
              apply Finset.sum_congr rfl
              intro i _
              rw [(component i).sum_one, mul_one]
      _ = 1 := weight.sum_one

/-- Membership in the finite convex hull of IIA choice systems. -/
noncomputable def InFiniteConvexHullIIA (q : ChoiceSystem F) : Prop :=
  ∃ (weight : ChoiceSystem F) (component : F.Observation → ChoiceSystem F),
    (∀ i, (component i).SatisfiesIIA) ∧ q = finiteMixture weight component

/-- Mixing the point masses with the target's own masses reconstructs the
target choice system exactly. -/
theorem finiteMixture_pure_eq (q : ChoiceSystem F) :
    finiteMixture q pure = q := by
  apply ext
  intro o
  classical
  change (∑ i : F.Observation, q.mass i * (if o = i then 1 else 0)) = q.mass o
  have hterm : ∀ i : F.Observation,
      q.mass i * (if o = i then 1 else 0) = if o = i then q.mass i else 0 := by
    intro i
    by_cases hoi : o = i <;> simp [hoi]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq (Finset.univ : Finset F.Observation) o q.mass,
    if_pos (Finset.mem_univ o)]

/-- Total variation contracts under a common finite mixture of choice
systems. -/
theorem totalVariation_finiteMixture_le (weight : ChoiceSystem F)
    (component₁ component₂ : F.Observation → ChoiceSystem F) :
    totalVariation (finiteMixture weight component₁)
      (finiteMixture weight component₂) ≤
      ∑ i : F.Observation, weight.mass i *
        totalVariation (component₁ i) (component₂ i) := by
  have hdiff : ∀ o : F.Observation,
      (finiteMixture weight component₁).mass o -
        (finiteMixture weight component₂).mass o =
        ∑ i : F.Observation, weight.mass i *
          ((component₁ i).mass o - (component₂ i).mass o) := by
    intro o
    change (∑ i : F.Observation, weight.mass i * (component₁ i).mass o) -
        ∑ i : F.Observation, weight.mass i * (component₂ i).mass o = _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold totalVariation
  simp_rw [hdiff]
  calc
    (1 / 2 : ℝ) * ∑ o : F.Observation,
        |∑ i : F.Observation, weight.mass i *
          ((component₁ i).mass o - (component₂ i).mass o)| ≤
        (1 / 2 : ℝ) * ∑ o : F.Observation, ∑ i : F.Observation,
          |weight.mass i * ((component₁ i).mass o - (component₂ i).mass o)| := by
            apply mul_le_mul_of_nonneg_left
            · exact Finset.sum_le_sum fun o _ => Finset.abs_sum_le_sum_abs _ _
            · norm_num
    _ = (1 / 2 : ℝ) * ∑ o : F.Observation, ∑ i : F.Observation,
          weight.mass i * |(component₁ i).mass o - (component₂ i).mass o| := by
            apply congrArg (fun value : ℝ => (1 / 2 : ℝ) * value)
            apply Finset.sum_congr rfl
            intro o _
            apply Finset.sum_congr rfl
            intro i _
            rw [abs_mul, abs_of_nonneg (weight.nonneg i)]
    _ = ∑ i : F.Observation, weight.mass i *
        ((1 / 2 : ℝ) * ∑ o : F.Observation,
          |(component₁ i).mass o - (component₂ i).mass o|) := by
            rw [Finset.sum_comm]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [← Finset.mul_sum]
            ring

/-- Total variation is symmetric. -/
theorem totalVariation_comm (q r : ChoiceSystem F) :
    totalVariation q r = totalVariation r q := by
  unfold totalVariation
  apply congrArg (fun value : ℝ => (1 / 2 : ℝ) * value)
  apply Finset.sum_congr rfl
  intro o _
  rw [abs_sub_comm]

/-- Appendix Fact `cvx_hull_dense`: every finite choice system is a total-
variation limit of finite convex mixtures of IIA choice systems.

For every incidence atom, `exists_iia_near_pure` supplies an IIA system close
to its point mass.  Averaging those systems with the target's own atom masses
then contracts total variation, giving the stated density result. -/
theorem finiteConvexHullIIA_dense_totalVariation (q : ChoiceSystem F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ChoiceSystem F,
      InFiniteConvexHullIIA r ∧ totalVariation q r < ε := by
  classical
  let component : F.Observation → ChoiceSystem F := fun i =>
    Classical.choose (exists_iia_near_pure i.1 i.2 ε hε)
  have hcomponent_iia : ∀ i, (component i).SatisfiesIIA := by
    intro i
    exact (Classical.choose_spec (exists_iia_near_pure i.1 i.2 ε hε)).1
  have hcomponent_near : ∀ i,
      totalVariation (component i) (pure i) < ε := by
    intro i
    simpa [component] using
      (Classical.choose_spec (exists_iia_near_pure i.1 i.2 ε hε)).2
  let r := finiteMixture q component
  refine ⟨r, ⟨q, component, hcomponent_iia, rfl⟩, ?_⟩
  have hpositive_weight : ∃ i : F.Observation, 0 < q.mass i := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ i : F.Observation, q.mass i = 0 := by
      intro i
      exact le_antisymm (hnone i) (q.nonneg i)
    have hsum := q.sum_one
    simp_rw [hzero] at hsum
    norm_num at hsum
  calc
    totalVariation q r = totalVariation (finiteMixture q pure) r := by
      rw [finiteMixture_pure_eq]
    _ ≤ ∑ i : F.Observation, q.mass i *
        totalVariation (pure i) (component i) :=
      totalVariation_finiteMixture_le q pure component
    _ < ∑ i : F.Observation, q.mass i * ε := by
      refine Finset.sum_lt_sum (fun i _ => ?_) ?_
      · rw [totalVariation_comm]
        exact mul_le_mul_of_nonneg_left (hcomponent_near i).le (q.nonneg i)
      · obtain ⟨i, hi⟩ := hpositive_weight
        refine ⟨i, Finset.mem_univ i, ?_⟩
        rw [totalVariation_comm]
        exact mul_lt_mul_of_pos_left (hcomponent_near i) hi
    _ = ε := by
      rw [← Finset.sum_mul, q.sum_one, one_mul]


end ChoiceSystem

end SeshadriUgander2020IIATesting
