import GN21DriverSurgePricing.Lemma5Variational

/-!
# Null-interval bridge for GN21 endpoint variations

The source treats policies modulo the trip-length measure.  These lemmas make
that convention available when an endpoint crosses an entire interval of zero
trip mass.  They deliberately do not assume density positivity.
-/

open MeasureTheory

namespace GN21DriverSurgePricing

/-- A null open interval remains null after adding its left endpoint. -/
theorem measure_Ico_eq_zero_of_measure_Ioo_eq_zero
    (mu : Measure TripLength) [NoAtoms mu]
    {left right : TripLength}
    (hnull : mu (Set.Ioo left right) = 0) :
    mu (Set.Ico left right) = 0 := by
  apply measure_mono_null ?_ (measure_union_null (measure_singleton left) hnull)
  intro x hx
  rcases lt_or_eq_of_le hx.1 with hleft_x | rfl
  · exact Or.inr ⟨hleft_x, hx.2⟩
  · exact Or.inl rfl

/--
Moving the upper endpoint of an open interval across a null interval changes
the policy only on a null set, even in the presence of a fixed policy context.
-/
theorem policyAlmostEverywhereEq_union_interval_expand_of_null
    (mu : Measure TripLength) [NoAtoms mu]
    (context : TripPolicy) {lower left right : TripLength}
    (hleft_right : left ≤ right)
    (hnull : mu (Set.Ioo left right) = 0) :
    policyAlmostEverywhereEq mu
      (context ∪ Set.Ioo lower left)
      (context ∪ Set.Ioo lower right) := by
  apply policyAlmostEverywhereEq_of_diff_null mu
  · have hsub :
        (context ∪ Set.Ioo lower left) \
          (context ∪ Set.Ioo lower right) ⊆ (∅ : Set TripLength) := by
      intro x hx
      exact False.elim (hx.2 (by
        rcases hx.1 with hcontext | hinterval
        · exact Or.inl hcontext
        · exact Or.inr ⟨hinterval.1, hinterval.2.trans_le hleft_right⟩))
    exact measure_mono_null hsub (by simp)
  · have hsub :
        (context ∪ Set.Ioo lower right) \
          (context ∪ Set.Ioo lower left) ⊆ Set.Ico left right := by
      intro x hx
      rcases hx.1 with hcontext | hinterval
      · exact False.elim (hx.2 (Or.inl hcontext))
      · by_cases hx_left : x < left
        · exact False.elim (hx.2 (Or.inr ⟨hinterval.1, hx_left⟩))
        · exact ⟨le_of_not_gt hx_left, hinterval.2⟩
    exact measure_mono_null hsub
      (measure_Ico_eq_zero_of_measure_Ioo_eq_zero mu hnull)

/--
Symmetric-difference continuity turns a null endpoint traversal into exact
reward equality.  This is the source paper's equality-up-to-measure-zero
convention in the form needed by endpoint paths.
-/
theorem reward_eq_of_union_interval_expand_of_null
    (mu : Measure TripLength) [NoAtoms mu]
    (Rhat : SingleStateReward) (context : TripPolicy)
    {lower left right : TripLength}
    (hleft_right : left ≤ right)
    (hnull : mu (Set.Ioo left right) = 0)
    (hcontinuous :
      GN21SymmDiffContinuousAt mu Rhat (context ∪ Set.Ioo lower left)) :
    Rhat (context ∪ Set.Ioo lower left) =
      Rhat (context ∪ Set.Ioo lower right) :=
  reward_eq_of_symmDiffContinuousAt_of_policyAlmostEverywhereEq
    mu Rhat hcontinuous
    (policyAlmostEverywhereEq_union_interval_expand_of_null
      mu context hleft_right hnull)

/-- A `withDensity` measure gives zero mass to the zero set of its density. -/
theorem measure_densityNN_zero_set_eq_zero
    (mu : Measure TripLength) (densityNN : TripLength → NNReal)
    (hmu : mu = volume.withDensity (fun tau => (densityNN tau : ENNReal)))
    (hdensity_meas : Measurable densityNN) :
    mu {tau : TripLength | densityNN tau = 0} = 0 := by
  have hdensity_meas' : Measurable (fun tau => (densityNN tau : ENNReal)) := by
    simpa only [Function.comp_apply] using
      (measurable_coe_nnreal_ennreal.comp hdensity_meas)
  rw [hmu]
  apply (withDensity_apply_eq_zero hdensity_meas').2
  have hempty :
      {tau : TripLength | (densityNN tau : ENNReal) ≠ 0} ∩
        {tau : TripLength | densityNN tau = 0} = ∅ := by
    ext tau
    simp
  rw [hempty]
  exact measure_empty

/-- An interval on which a density vanishes pointwise is null for its measure. -/
theorem measure_Ioo_eq_zero_of_densityNN_eq_zero_on
    (mu : Measure TripLength) (densityNN : TripLength → NNReal)
    (hmu : mu = volume.withDensity (fun tau => (densityNN tau : ENNReal)))
    (hdensity_meas : Measurable densityNN)
    {left right : TripLength}
    (hzero : ∀ tau, tau ∈ Set.Ioo left right → densityNN tau = 0) :
    mu (Set.Ioo left right) = 0 := by
  apply measure_mono_null ?_
    (measure_densityNN_zero_set_eq_zero mu densityNN hmu hdensity_meas)
  intro tau htau
  exact hzero tau htau

/-- Positive mass contains a point at which a density is positive. -/
theorem exists_densityNN_pos_of_measure_pos
    (mu : Measure TripLength) (densityNN : TripLength → NNReal)
    (hmu : mu = volume.withDensity (fun tau => (densityNN tau : ENNReal)))
    (hdensity_meas : Measurable densityNN)
    {s : Set TripLength} (hmass : 0 < mu s) :
    ∃ tau, tau ∈ s ∧ 0 < densityNN tau := by
  by_contra h
  push Not at h
  have hsubset : s ⊆ {tau : TripLength | densityNN tau = 0} := by
    intro tau htau
    exact le_antisymm (h tau htau) (zero_le _)
  have hnull : mu s = 0 :=
    measure_mono_null hsubset
      (measure_densityNN_zero_set_eq_zero mu densityNN hmu hdensity_meas)
  exact (ne_of_gt hmass) hnull

/--
A continuous endpoint path with a weakly nonnegative derivative is strictly
increasing when its derivative is positive at one interior point.  This is the
calculus step needed after density-zero endpoints have been reduced to zero
derivative contributions.
-/
theorem endpoint_path_lt_of_hasDerivAt_nonneg_on_Icc_of_exists_pos
    {path derivative : Real -> Real} {left right : Real}
    (hpath_continuous : ContinuousOn path (Set.Icc left right))
    (hpath_derivative :
      ∀ x ∈ Set.Ioo left right, HasDerivAt path (derivative x) x)
    (hderivative_nonneg :
      ∀ x ∈ Set.Ioo left right, 0 ≤ derivative x)
    (hderivative_pos :
      ∃ x ∈ Set.Ioo left right, 0 < derivative x) :
    path left < path right := by
  obtain ⟨x, hx, hx_pos⟩ := hderivative_pos
  obtain ⟨epsilon, hepsilon_pos, hepsilon_lt, himprove⟩ :=
    AppliedModelingLib.Optimization.exists_pos_right_improvement_of_hasDerivAt_pos_lt
      (hpath_derivative x hx) hx_pos (sub_pos.mpr hx.2)
  have hx_epsilon_right : x + epsilon < right := by
    linarith
  have hleft_le_x : path left <= path x := by
    apply AppliedModelingLib.Optimization.endpoint_path_le_of_hasDerivAt_nonneg_on_Icc
      (le_of_lt hx.1)
    · exact hpath_continuous.mono (Set.Icc_subset_Icc_right (le_of_lt hx.2))
    · intro y hy
      exact hpath_derivative y ⟨hy.1, hy.2.trans hx.2⟩
    · intro y hy
      exact hderivative_nonneg y ⟨hy.1, hy.2.trans hx.2⟩
  have hx_epsilon_le_right : path (x + epsilon) <= path right := by
    apply AppliedModelingLib.Optimization.endpoint_path_le_of_hasDerivAt_nonneg_on_Icc
      (le_of_lt hx_epsilon_right)
    · apply hpath_continuous.mono
      intro y hy
      constructor
      · linarith [hx.1, hepsilon_pos, hy.1]
      · exact hy.2
    · intro y hy
      exact hpath_derivative y ⟨by linarith [hx.1, hepsilon_pos, hy.1], hy.2⟩
    · intro y hy
      exact hderivative_nonneg y ⟨by linarith [hx.1, hepsilon_pos, hy.1], hy.2⟩
  exact hleft_le_x.trans_lt (himprove.trans_le hx_epsilon_le_right)

/--
The density-aware replacement for a pointwise strict-sign endpoint premise.
It supports arbitrary zero sets: at zero-density points the derivative is
zero, and on a positive-mass move there is a density-positive point where the
strict sign gives a strict local gain.
-/
theorem endpoint_path_lt_of_densityNN_sign_on_Icc
    (mu : Measure TripLength) (densityNN : TripLength -> NNReal)
    (hmu : mu = volume.withDensity (fun tau => (densityNN tau : ENNReal)))
    (hdensity_meas : Measurable densityNN)
    {path derivative response : Real -> Real} {left right : Real}
    (hpath_continuous : ContinuousOn path (Set.Icc left right))
    (hpath_derivative :
      ∀ x ∈ Set.Ioo left right, HasDerivAt path (derivative x) x)
    (hzero_derivative :
      ∀ x ∈ Set.Ioo left right, densityNN x = 0 → derivative x = 0)
    (hpositive_density_sign :
      ∀ x ∈ Set.Ioo left right, 0 < densityNN x →
        sameStrictSign (derivative x) (response x))
    (hresponse_nonneg :
      ∀ x ∈ Set.Ioo left right, 0 ≤ response x)
    (hresponse_pos :
      ∀ x ∈ Set.Ioo left right, 0 < response x)
    (hmass : 0 < mu (Set.Ioo left right)) :
    path left < path right := by
  apply endpoint_path_lt_of_hasDerivAt_nonneg_on_Icc_of_exists_pos
    hpath_continuous hpath_derivative
  · intro x hx
    by_cases hdensity_zero : densityNN x = 0
    · rw [hzero_derivative x hx hdensity_zero]
    · have hdensity_pos : 0 < densityNN x :=
        lt_of_le_of_ne (zero_le _) (Ne.symm hdensity_zero)
      exact sameStrictSign_nonneg_right
        (sameStrictSign_symm (hpositive_density_sign x hx hdensity_pos))
        (hresponse_nonneg x hx)
  · obtain ⟨x, hx, hdensity_pos⟩ :=
      exists_densityNN_pos_of_measure_pos mu densityNN hmu hdensity_meas hmass
    exact ⟨x, hx,
      sameStrictSign_pos_left
        (hpositive_density_sign x hx hdensity_pos) (hresponse_pos x hx)⟩

end GN21DriverSurgePricing
