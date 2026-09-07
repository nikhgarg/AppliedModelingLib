import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Finite-dimensional Euclidean nets

Reusable quantitative entropy lemmas for finite-dimensional normed spaces.
The initial result is the volumetric packing estimate at the scale used by
fixed-support random-matrix arguments.  It is intentionally stated without
any paper, matrix, or probability terminology.
-/

open Metric MeasureTheory Module
open scoped Function
open scoped ENNReal

namespace AppliedModelingLib
namespace Math
namespace EuclideanNets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The Gram deviation of a linear map from an isometry. -/
noncomputable def gramDeviation
    {E' F : Type*} [NormedAddCommGroup E'] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E'] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E'] [FiniteDimensional ℝ F]
    (L : E' →L[ℝ] F) : E' →L[ℝ] E' :=
  L.adjoint.comp L - ContinuousLinearMap.id ℝ E'

/-- The Gram deviation is symmetric. -/
theorem gramDeviation_isSymmetric
    {E' F : Type*} [NormedAddCommGroup E'] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E'] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E'] [FiniteDimensional ℝ F]
    (L : E' →L[ℝ] F) : (gramDeviation L).IsSymmetric := by
  intro x y
  change inner ℝ (L.adjoint (L x) - x) y =
    inner ℝ x (L.adjoint (L y) - y)
  rw [inner_sub_left, inner_sub_right, L.adjoint_inner_left,
    L.adjoint_inner_right]

/-- The Gram quadratic form is the difference of squared output and input norms. -/
theorem inner_gramDeviation_self_eq_norm_sq_sub
    {E' F : Type*} [NormedAddCommGroup E'] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E'] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E'] [FiniteDimensional ℝ F]
    (L : E' →L[ℝ] F) (x : E') :
    inner ℝ (gramDeviation L x) x = ‖L x‖ ^ 2 - ‖x‖ ^ 2 := by
  change inner ℝ (L.adjoint (L x) - x) x = _
  rw [inner_sub_left, L.adjoint_inner_left,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/--
A finite subset of the unit ball whose distinct points are at least `1 / 4`
apart has cardinality at most `9 ^ dim`.  This is the elementary volume-packing
bound obtained from disjoint balls of radius `1 / 8` inside the ball of radius
`9 / 8`.
-/
theorem card_le_nine_pow_finrank_of_unit_ball_quarter_separated
    (s : Finset E) (hs : ∀ c ∈ s, ‖c‖ ≤ 1)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → (1 : ℝ) / 4 ≤ ‖c - d‖) :
    s.card ≤ 9 ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := (1 : ℝ) / 8
  let ρ : ℝ := (9 : ℝ) / 8
  have hρ_pos : 0 < ρ := by norm_num [ρ]
  set A := ⋃ c ∈ s, Metric.ball (c : E) δ with hA
  have hdisjoint : Set.Pairwise (s : Set E)
      (Disjoint on fun c => Metric.ball (c : E) δ) := by
    rintro c hc d hd hcd
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    convert hsep c hc d hd hcd using 1
    norm_num [δ]
  have hsubset : A ⊆ Metric.ball (0 : E) ρ := by
    refine Set.iUnion₂_subset fun x hx => ?_
    apply Metric.ball_subset_ball'
    calc
      δ + dist x 0 ≤ δ + 1 := by
        rw [dist_zero_right]
        exact add_le_add le_rfl (hs x hx)
      _ = 9 / 8 := by norm_num [δ, ρ]
  have hvolume :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) *
          μ (Metric.ball 0 1) ≤
        ENNReal.ofReal (ρ ^ finrank ℝ E) *
          μ (Metric.ball 0 1) :=
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) *
          μ (Metric.ball 0 1) = μ A := by
            rw [hA, measure_biUnion_finset hdisjoint fun c _ => measurableSet_ball]
            have hδ_pos : 0 < δ := by norm_num [δ]
            simp only [μ.addHaar_ball_of_pos _ hδ_pos]
            simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (Metric.ball (0 : E) ρ) := measure_mono hsubset
      _ = ENNReal.ofReal (ρ ^ finrank ℝ E) *
          μ (Metric.ball 0 1) := by
            simp only [μ.addHaar_ball_of_pos _ hρ_pos]
  have hratio :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) ≤
        ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left
      (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 hvolume
  have hreal : (s.card : ℝ) ≤ (9 : ℝ) ^ finrank ℝ E := by
    have h := ENNReal.toReal_le_of_le_ofReal
      (pow_nonneg hρ_pos.le _) hratio
    simpa [ρ, δ, div_eq_mul_inv, mul_pow] using h
  exact mod_cast hreal

/--
There is a finite `5/16`-net of the unit sphere with at most `9 ^ dim`
points.  The construction first takes a finite compactness cover and then a
maximal `1/4`-separated subfamily; the preceding volumetric lemma supplies the
cardinality bound.
-/
theorem exists_finset_unit_sphere_five_sixteenths_net
    [Nontrivial E] :
    ∃ N : Finset E,
      N.card ≤ 9 ^ finrank ℝ E ∧
      (∀ y ∈ N, ‖y‖ = 1) ∧
      ∀ x, ‖x‖ = 1 → ∃ y ∈ N, ‖x - y‖ < (5 : ℝ) / 16 := by
  classical
  let ε : ℝ := (1 : ℝ) / 16
  have hε : 0 < ε := by norm_num [ε]
  obtain ⟨q, hqsphere, hqfin, hqcover⟩ :
      ∃ q : Set E, q ⊆ sphere (0 : E) 1 ∧ q.Finite ∧
        sphere (0 : E) 1 ⊆ ⋃ y ∈ q, ball y ε := by
    have hcover : sphere (0 : E) 1 ⊆ ⋃ y ∈ sphere (0 : E) 1, ball y ε := by
      intro x hx
      exact Set.mem_iUnion₂.mpr ⟨x, hx, Metric.mem_ball_self hε⟩
    exact (isCompact_sphere (0 : E) 1).elim_finite_subcover_image
      (fun _ _ => isOpen_ball) hcover
  let F : Finset E := hqfin.toFinset
  have hF_iff {y : E} : y ∈ F ↔ y ∈ q := by simp [F]
  let candidates : Finset (Finset E) :=
    F.powerset.filter fun S =>
      ∀ c ∈ S, ∀ d ∈ S, c ≠ d → (1 : ℝ) / 4 ≤ ‖c - d‖
  obtain ⟨N, hN⟩ := candidates.exists_maximal (by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, ?_⟩⟩
    simp)
  simp only [candidates, Finset.mem_filter, Finset.mem_powerset] at hN
  have hN_subset : N ⊆ F := hN.1.1
  have hN_sep : ∀ c ∈ N, ∀ d ∈ N, c ≠ d → (1 : ℝ) / 4 ≤ ‖c - d‖ := hN.1.2
  have hF_net : ∀ z ∈ F, ∃ y ∈ N, ‖z - y‖ < (1 : ℝ) / 4 := by
    intro z hz
    by_contra hnot
    push Not at hnot
    have hz_not_mem : z ∉ N := by
      intro hzN
      have hzero := hnot z hzN
      have hquarter_pos : (0 : ℝ) < 1 / 4 := by norm_num
      have : (1 : ℝ) / 4 ≤ 0 := by simpa using hzero
      exact (not_le_of_gt hquarter_pos this).elim
    have hinsert_subset : insert z N ⊆ F := by
      exact Finset.insert_subset hz hN_subset
    have hinsert_sep :
        ∀ c ∈ insert z N, ∀ d ∈ insert z N, c ≠ d →
          (1 : ℝ) / 4 ≤ ‖c - d‖ := by
      intro c hc d hd hcd
      rcases Finset.mem_insert.mp hc with hcz | hcN
      · subst c
        rcases Finset.mem_insert.mp hd with hdz | hdN
        · subst d
          exact (hcd rfl).elim
        · exact hnot d hdN
      · rcases Finset.mem_insert.mp hd with hdz | hdN
        · subst d
          rw [norm_sub_rev]
          exact hnot c hcN
        · exact hN_sep c hcN d hdN hcd
    have hstrict : N < insert z N := Finset.ssubset_insert hz_not_mem
    exact (hN.not_gt ⟨hinsert_subset, hinsert_sep⟩ hstrict).elim
  have hcard : N.card ≤ 9 ^ finrank ℝ E := by
    apply card_le_nine_pow_finrank_of_unit_ball_quarter_separated N
    · intro y hy
      have hyq : y ∈ q := hF_iff.mp (hN_subset hy)
      have hysphere := hqsphere hyq
      simpa [mem_sphere_iff_norm] using hysphere.le
    · exact hN_sep
  refine ⟨N, hcard, ?_, ?_⟩
  · intro y hy
    have hyq : y ∈ q := hF_iff.mp (hN_subset hy)
    simpa [mem_sphere_iff_norm] using hqsphere hyq
  · intro x hx
    have hxsphere : x ∈ sphere (0 : E) 1 := by
      simpa [mem_sphere_iff_norm] using hx
    obtain ⟨z, hzq, hxz⟩ := Set.mem_iUnion₂.mp (hqcover hxsphere)
    obtain ⟨y, hyN, hzy⟩ := hF_net z (hF_iff.mpr hzq)
    refine ⟨y, hyN, ?_⟩
    calc
      ‖x - y‖ = ‖(x - z) + (z - y)‖ := by congr; abel
      _ ≤ ‖x - z‖ + ‖z - y‖ := norm_add_le _ _
      _ < (1 : ℝ) / 16 + (1 : ℝ) / 4 := add_lt_add_of_lt_of_le
        (by simpa [ε, dist_eq_norm] using hxz) hzy.le
      _ = (5 : ℝ) / 16 := by norm_num

/-- A scale-sensitive packing bound for points in the unit ball.  At
separation `1 / (2 * (n + 1))`, the usual disjoint-ball argument gives the
integer entropy bound `(4 * n + 5)^d`. -/
theorem card_le_four_mul_add_five_pow_finrank_of_unit_ball_inv_succ_separated
    [Nontrivial E] (n : ℕ) (s : Finset E)
    (hs : ∀ c ∈ s, ‖c‖ ≤ 1)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d →
      (1 : ℝ) / (2 * (n + 1 : ℝ)) ≤ ‖c - d‖) :
    s.card ≤ (4 * n + 5) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := (1 : ℝ) / (4 * (n + 1 : ℝ))
  let ρ : ℝ := 1 + δ
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρ_factor : ρ = (4 * n + 5 : ℝ) * δ := by
    dsimp [ρ, δ]
    field_simp
    ring
  set A := ⋃ c ∈ s, Metric.ball (c : E) δ with hA
  have hdisjoint : Set.Pairwise (s : Set E)
      (Disjoint on fun c => Metric.ball (c : E) δ) := by
    rintro c hc d hd hcd
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    convert hsep c hc d hd hcd using 1
    dsimp [δ]
    field_simp
    ring
  have hsubset : A ⊆ Metric.ball (0 : E) ρ := by
    refine Set.iUnion₂_subset fun x hx => ?_
    apply Metric.ball_subset_ball'
    calc
      δ + dist x 0 ≤ δ + 1 := by
        rw [dist_zero_right]
        exact add_le_add le_rfl (hs x hx)
      _ = ρ := by dsimp [ρ]; ring
  have hvolume :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) *
          μ (Metric.ball 0 1) ≤
        ENNReal.ofReal (ρ ^ finrank ℝ E) *
          μ (Metric.ball 0 1) :=
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) *
          μ (Metric.ball 0 1) = μ A := by
            rw [hA, measure_biUnion_finset hdisjoint fun c _ => measurableSet_ball]
            simp only [μ.addHaar_ball_of_pos _ hδ_pos]
            simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (Metric.ball (0 : E) ρ) := measure_mono hsubset
      _ = ENNReal.ofReal (ρ ^ finrank ℝ E) *
          μ (Metric.ball 0 1) := by
            simp only [μ.addHaar_ball_of_pos _ hρ_pos]
  have hratio :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) ≤
        ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left
      (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 hvolume
  have hraw : (s.card : ℝ) * δ ^ finrank ℝ E ≤ ρ ^ finrank ℝ E := by
    have h := ENNReal.toReal_le_of_le_ofReal
      (pow_nonneg hρ_pos.le _) hratio
    simpa [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hδ_pos.le _)] using h
  have hscaled : (s.card : ℝ) * δ ^ finrank ℝ E ≤
      (4 * n + 5 : ℝ) ^ finrank ℝ E * δ ^ finrank ℝ E := by
    calc
      (s.card : ℝ) * δ ^ finrank ℝ E ≤ ρ ^ finrank ℝ E := hraw
      _ = (4 * n + 5 : ℝ) ^ finrank ℝ E * δ ^ finrank ℝ E := by
        rw [hρ_factor, mul_pow]
  have hreal : (s.card : ℝ) ≤ (4 * n + 5 : ℝ) ^ finrank ℝ E := by
    have hδpow : 0 < δ ^ finrank ℝ E := pow_pos hδ_pos _
    nlinarith
  exact_mod_cast hreal

/-- A finite unit-sphere net at radius `1 / (n + 1)`, together with the
volumetric cardinality bound used for horizon-indexed finite-net arguments. -/
theorem exists_finset_unit_sphere_inv_succ_net
    [Nontrivial E] (n : ℕ) :
    ∃ N : Finset E,
      N.card ≤ (4 * n + 5) ^ finrank ℝ E ∧
      (∀ y ∈ N, ‖y‖ = 1) ∧
      ∀ x, ‖x‖ = 1 → ∃ y ∈ N, ‖x - y‖ < 1 / (n + 1 : ℝ) := by
  classical
  let ε : ℝ := (1 : ℝ) / (n + 1 : ℝ)
  let δ : ℝ := ε / 2
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨q, hqsphere, hqfin, hqcover⟩ :
      ∃ q : Set E, q ⊆ sphere (0 : E) 1 ∧ q.Finite ∧
        sphere (0 : E) 1 ⊆ ⋃ y ∈ q, ball y δ := by
    have hcover : sphere (0 : E) 1 ⊆ ⋃ y ∈ sphere (0 : E) 1, ball y δ := by
      intro x hx
      exact Set.mem_iUnion₂.mpr ⟨x, hx, Metric.mem_ball_self hδ⟩
    exact (isCompact_sphere (0 : E) 1).elim_finite_subcover_image
      (fun _ _ => isOpen_ball) hcover
  let F : Finset E := hqfin.toFinset
  have hF_iff {y : E} : y ∈ F ↔ y ∈ q := by simp [F]
  let candidates : Finset (Finset E) :=
    F.powerset.filter fun S =>
      ∀ c ∈ S, ∀ d ∈ S, c ≠ d → ε / 2 ≤ ‖c - d‖
  obtain ⟨N, hN⟩ := candidates.exists_maximal (by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, ?_⟩⟩
    simp)
  simp only [candidates, Finset.mem_filter, Finset.mem_powerset] at hN
  have hN_subset : N ⊆ F := hN.1.1
  have hN_sep : ∀ c ∈ N, ∀ d ∈ N, c ≠ d → ε / 2 ≤ ‖c - d‖ := hN.1.2
  have hF_net : ∀ z ∈ F, ∃ y ∈ N, ‖z - y‖ < ε / 2 := by
    intro z hz
    by_contra hnot
    push Not at hnot
    have hz_not_mem : z ∉ N := by
      intro hzN
      have hzero := hnot z hzN
      have : ε / 2 ≤ 0 := by simpa using hzero
      exact (not_le_of_gt (by positivity : 0 < ε / 2) this).elim
    have hinsert_subset : insert z N ⊆ F := Finset.insert_subset hz hN_subset
    have hinsert_sep :
        ∀ c ∈ insert z N, ∀ d ∈ insert z N, c ≠ d → ε / 2 ≤ ‖c - d‖ := by
      intro c hc d hd hcd
      rcases Finset.mem_insert.mp hc with hcz | hcN
      · subst c
        rcases Finset.mem_insert.mp hd with hdz | hdN
        · subst d
          exact (hcd rfl).elim
        · exact hnot d hdN
      · rcases Finset.mem_insert.mp hd with hdz | hdN
        · subst d
          rw [norm_sub_rev]
          exact hnot c hcN
        · exact hN_sep c hcN d hdN hcd
    have hstrict : N < insert z N := Finset.ssubset_insert hz_not_mem
    exact (hN.not_gt ⟨hinsert_subset, hinsert_sep⟩ hstrict).elim
  have hcard : N.card ≤ (4 * n + 5) ^ finrank ℝ E := by
    apply card_le_four_mul_add_five_pow_finrank_of_unit_ball_inv_succ_separated n N
    · intro y hy
      have hyq : y ∈ q := hF_iff.mp (hN_subset hy)
      have hysphere := hqsphere hyq
      simpa [mem_sphere_iff_norm] using hysphere.le
    · intro c hc d hd hcd
      simpa [ε, div_eq_mul_inv] using hN_sep c hc d hd hcd
  refine ⟨N, hcard, ?_, ?_⟩
  · intro y hy
    have hyq : y ∈ q := hF_iff.mp (hN_subset hy)
    simpa [mem_sphere_iff_norm] using hqsphere hyq
  · intro x hx
    have hxsphere : x ∈ sphere (0 : E) 1 := by
      simpa [mem_sphere_iff_norm] using hx
    obtain ⟨z, hzq, hxz⟩ := Set.mem_iUnion₂.mp (hqcover hxsphere)
    obtain ⟨y, hyN, hzy⟩ := hF_net z (hF_iff.mpr hzq)
    refine ⟨y, hyN, ?_⟩
    calc
      ‖x - y‖ = ‖(x - z) + (z - y)‖ := by congr; abel
      _ ≤ ‖x - z‖ + ‖z - y‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add (by simpa [δ, dist_eq_norm] using hxz) hzy
      _ = 1 / (n + 1 : ℝ) := by dsimp [ε]; ring

/-- A finite unit-ball net at radius `1 / (n + 1)`.  Unlike a coordinate-grid
argument, the volumetric construction keeps the entropy exponent equal to the
ambient real dimension.  This is the form needed for simultaneous vector and
matrix parameter covers in least-squares value classes. -/
theorem exists_finset_unit_closedBall_inv_succ_net
    [Nontrivial E] (n : ℕ) :
    ∃ N : Finset E,
      N.card ≤ (4 * n + 5) ^ finrank ℝ E ∧
      (∀ y ∈ N, ‖y‖ ≤ 1) ∧
      ∀ x, ‖x‖ ≤ 1 → ∃ y ∈ N, ‖x - y‖ < 1 / (n + 1 : ℝ) := by
  classical
  let ε : ℝ := (1 : ℝ) / (n + 1 : ℝ)
  let δ : ℝ := ε / 2
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨q, hqball, hqfin, hqcover⟩ :
      ∃ q : Set E, q ⊆ closedBall (0 : E) 1 ∧ q.Finite ∧
        closedBall (0 : E) 1 ⊆ ⋃ y ∈ q, ball y δ := by
    have hcover : closedBall (0 : E) 1 ⊆
        ⋃ y ∈ closedBall (0 : E) 1, ball y δ := by
      intro x hx
      exact Set.mem_iUnion₂.mpr ⟨x, hx, Metric.mem_ball_self hδ⟩
    exact (isCompact_closedBall (0 : E) 1).elim_finite_subcover_image
      (fun _ _ => isOpen_ball) hcover
  let F : Finset E := hqfin.toFinset
  have hF_iff {y : E} : y ∈ F ↔ y ∈ q := by simp [F]
  let candidates : Finset (Finset E) :=
    F.powerset.filter fun S =>
      ∀ c ∈ S, ∀ d ∈ S, c ≠ d → ε / 2 ≤ ‖c - d‖
  obtain ⟨N, hN⟩ := candidates.exists_maximal (by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, ?_⟩⟩
    simp)
  simp only [candidates, Finset.mem_filter, Finset.mem_powerset] at hN
  have hN_subset : N ⊆ F := hN.1.1
  have hN_sep : ∀ c ∈ N, ∀ d ∈ N, c ≠ d → ε / 2 ≤ ‖c - d‖ := hN.1.2
  have hF_net : ∀ z ∈ F, ∃ y ∈ N, ‖z - y‖ < ε / 2 := by
    intro z hz
    by_contra hnot
    push Not at hnot
    have hz_not_mem : z ∉ N := by
      intro hzN
      have hzero := hnot z hzN
      have : ε / 2 ≤ 0 := by simpa using hzero
      exact (not_le_of_gt (by positivity : 0 < ε / 2) this).elim
    have hinsert_subset : insert z N ⊆ F := Finset.insert_subset hz hN_subset
    have hinsert_sep :
        ∀ c ∈ insert z N, ∀ d ∈ insert z N, c ≠ d → ε / 2 ≤ ‖c - d‖ := by
      intro c hc d hd hcd
      rcases Finset.mem_insert.mp hc with hcz | hcN
      · subst c
        rcases Finset.mem_insert.mp hd with hdz | hdN
        · subst d
          exact (hcd rfl).elim
        · exact hnot d hdN
      · rcases Finset.mem_insert.mp hd with hdz | hdN
        · subst d
          rw [norm_sub_rev]
          exact hnot c hcN
        · exact hN_sep c hcN d hdN hcd
    have hstrict : N < insert z N := Finset.ssubset_insert hz_not_mem
    exact (hN.not_gt ⟨hinsert_subset, hinsert_sep⟩ hstrict).elim
  have hcard : N.card ≤ (4 * n + 5) ^ finrank ℝ E := by
    apply card_le_four_mul_add_five_pow_finrank_of_unit_ball_inv_succ_separated n N
    · intro y hy
      have hyq : y ∈ q := hF_iff.mp (hN_subset hy)
      have hyball := hqball hyq
      simpa [mem_closedBall, dist_zero_right] using hyball
    · intro c hc d hd hcd
      simpa [ε, div_eq_mul_inv] using hN_sep c hc d hd hcd
  refine ⟨N, hcard, ?_, ?_⟩
  · intro y hy
    have hyq : y ∈ q := hF_iff.mp (hN_subset hy)
    simpa [mem_closedBall, dist_zero_right] using hqball hyq
  · intro x hx
    have hxball : x ∈ closedBall (0 : E) 1 := by
      simpa [mem_closedBall, dist_zero_right] using hx
    obtain ⟨z, hzq, hxz⟩ := Set.mem_iUnion₂.mp (hqcover hxball)
    obtain ⟨y, hyN, hzy⟩ := hF_net z (hF_iff.mpr hzq)
    refine ⟨y, hyN, ?_⟩
    calc
      ‖x - y‖ = ‖(x - z) + (z - y)‖ := by congr; abel
      _ ≤ ‖x - z‖ + ‖z - y‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add (by simpa [δ, dist_eq_norm] using hxz) hzy
      _ = 1 / (n + 1 : ℝ) := by dsimp [ε]; ring

/--
Controlling a continuous linear map on an `ε`-net of the unit sphere controls
its operator norm.  This is the deterministic lifting step used after a
finite-net probability estimate; it is stated for arbitrary normed spaces so
that the finite-dimensional net construction above is only one possible
source of `hnet`.
-/
theorem opNorm_le_div_of_unit_sphere_net
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (N : Finset E) (epsilon M : ℝ)
    (hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_lt_one : epsilon < 1)
    (hM_nonneg : 0 ≤ M)
    (hnet : ∀ x, ‖x‖ = 1 → ∃ y ∈ N, ‖x - y‖ < epsilon)
    (hN : ∀ y ∈ N, ‖A y‖ ≤ M) :
    ‖A‖ ≤ M / (1 - epsilon) := by
  have hone_sub_pos : 0 < 1 - epsilon := by linarith
  apply (le_div_iff₀ hone_sub_pos).2
  by_contra h
  push Not at h
  have hstrict : M + epsilon * ‖A‖ < ‖A‖ := by
    nlinarith [ContinuousLinearMap.opNorm_nonneg A]
  let r : ℝ := (M + epsilon * ‖A‖ + ‖A‖) / 2
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr_lt : r < ‖A‖ := by
    dsimp [r]
    linarith
  obtain ⟨x, hx⟩ := A.exists_mul_lt_of_lt_opNorm hr_nonneg hr_lt
  have hx_norm_pos : 0 < ‖x‖ := by
    by_contra hzero
    have hzero' : ‖x‖ = 0 := le_antisymm (not_lt.mp hzero) (norm_nonneg _)
    have : x = 0 := norm_eq_zero.mp hzero'
    simp [this] at hx
  let u : E := ‖x‖⁻¹ • x
  have hu_norm : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hx_norm_pos.le),
      inv_mul_cancel₀ hx_norm_pos.ne']
  have hr_lt_Au : r < ‖A u‖ := by
    apply lt_of_mul_lt_mul_right _ hx_norm_pos.le
    calc
      r * ‖x‖ < ‖A x‖ := hx
      _ = ‖A u‖ * ‖x‖ := by
        dsimp [u]
        rw [A.map_smul, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr hx_norm_pos.le)]
        field_simp
  obtain ⟨y, hyN, huy⟩ := hnet u hu_norm
  have hA_pos : 0 < ‖A‖ := by
    have : 0 ≤ M + epsilon * ‖A‖ := by positivity
    linarith
  have hAu_bound : ‖A u‖ < M + epsilon * ‖A‖ := by
    calc
      ‖A u‖ = ‖A y + A (u - y)‖ := by
        congr
        rw [A.map_sub]
        abel
      _ ≤ ‖A y‖ + ‖A (u - y)‖ := norm_add_le _ _
      _ ≤ M + ‖A‖ * ‖u - y‖ := by
        exact add_le_add (hN y hyN) (A.le_opNorm _)
      _ < M + ‖A‖ * epsilon := by
        exact add_lt_add_of_le_of_lt le_rfl
          (mul_lt_mul_of_pos_left huy hA_pos)
      _ = M + epsilon * ‖A‖ := by ring
  have hr_gt : M + epsilon * ‖A‖ < r := by
    dsimp [r]
    linarith
  linarith

/--
For a symmetric linear map, a bound on its quadratic form over a unit-sphere
net controls its operator norm.  This is the standard deterministic lifting
step from fixed-vector norm preservation to a uniform finite-dimensional
estimate.
-/
theorem opNorm_le_div_of_quadratic_form_unit_sphere_net
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (hT : T.IsSymmetric) (N : Finset E) (epsilon M : ℝ)
    (hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_lt_half : epsilon < 1 / 2)
    (hM_nonneg : 0 ≤ M)
    (hnet : ∀ x, ‖x‖ = 1 → ∃ y ∈ N, ‖x - y‖ < epsilon)
    (hN_unit : ∀ y ∈ N, ‖y‖ = 1)
    (hN : ∀ y ∈ N, |inner ℝ (T y) y| ≤ M) :
    ‖T‖ ≤ M / (1 - 2 * epsilon) := by
  have hdenom : 0 < 1 - 2 * epsilon := by linarith
  have hglobal_rayleigh :
      (⨆ x, |T.rayleighQuotient x|) ≤ M + 2 * epsilon * ‖T‖ := by
    apply ciSup_le
    intro x
    by_cases hx : x = 0
    · simp [hx]
      positivity
    let u : E := (‖x‖⁻¹ : ℝ) • x
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hunit : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hxnorm.le),
        inv_mul_cancel₀ hxnorm.ne']
    obtain ⟨y, hyN, huy⟩ := hnet u hunit
    have hyunit := hN_unit y hyN
    have hquad :
        |inner ℝ (T u) u| ≤ M + 2 * epsilon * ‖T‖ := by
      have hdiff :
          inner ℝ (T u) u - inner ℝ (T y) y =
            inner ℝ (T (u - y)) u + inner ℝ (T y) (u - y) := by
        rw [T.map_sub, inner_sub_left, inner_sub_right]
        ring
      calc
        |inner ℝ (T u) u| = |inner ℝ (T y) y +
            (inner ℝ (T u) u - inner ℝ (T y) y)| := by
              congr 1
              ring
        _ ≤ |inner ℝ (T y) y| +
            |inner ℝ (T u) u - inner ℝ (T y) y| := by
              exact abs_add_le _ _
        _ = |inner ℝ (T y) y| +
            |inner ℝ (T (u - y)) u + inner ℝ (T y) (u - y)| := by rw [hdiff]
        _ ≤ M + (|inner ℝ (T (u - y)) u| + |inner ℝ (T y) (u - y)|) := by
          gcongr
          · exact hN y hyN
          · exact abs_add_le _ _
        _ ≤ M + (‖T‖ * ‖u - y‖ * ‖u‖ + ‖T‖ * ‖y‖ * ‖u - y‖) := by
          gcongr
          · calc
              |inner ℝ (T (u - y)) u| ≤ ‖T (u - y)‖ * ‖u‖ :=
                abs_real_inner_le_norm _ _
              _ ≤ (‖T‖ * ‖u - y‖) * ‖u‖ :=
                mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _)
              _ = ‖T‖ * ‖u - y‖ * ‖u‖ := by ring
          · calc
              |inner ℝ (T y) (u - y)| ≤ ‖T y‖ * ‖u - y‖ :=
                abs_real_inner_le_norm _ _
              _ ≤ (‖T‖ * ‖y‖) * ‖u - y‖ :=
                mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _)
              _ = ‖T‖ * ‖y‖ * ‖u - y‖ := by ring
        _ ≤ M + (‖T‖ * epsilon * 1 + ‖T‖ * 1 * epsilon) := by
          have hT_nonneg : 0 ≤ ‖T‖ := T.opNorm_nonneg
          have hfirst : ‖T‖ * ‖u - y‖ * ‖u‖ ≤ ‖T‖ * epsilon * 1 := by
            rw [hunit]
            simpa using mul_le_mul_of_nonneg_left huy.le hT_nonneg
          have hsecond : ‖T‖ * ‖y‖ * ‖u - y‖ ≤ ‖T‖ * 1 * epsilon := by
            rw [hyunit]
            simpa using mul_le_mul_of_nonneg_left huy.le hT_nonneg
          linarith
        _ = M + 2 * epsilon * ‖T‖ := by ring
    have hrayleigh :
        |T.rayleighQuotient x| ≤ M + 2 * epsilon * ‖T‖ := by
      have hc : (‖x‖⁻¹ : ℝ) ≠ 0 := inv_ne_zero hxnorm.ne'
      rw [← T.rayleigh_smul x hc]
      change |inner ℝ (T u) u / ‖u‖ ^ 2| ≤ M + 2 * epsilon * ‖T‖
      simpa [hunit] using hquad
    exact hrayleigh
  have hglobal : ‖T‖ ≤ M + 2 * epsilon * ‖T‖ := by
    calc
      ‖T‖ = ⨆ x, |T.rayleighQuotient x| := T.norm_eq_iSup_rayleighQuotient hT
      _ ≤ M + 2 * epsilon * ‖T‖ := hglobal_rayleigh
  apply (le_div_iff₀ hdenom).mpr
  nlinarith

/--
A finite unit-sphere net on which a linear map nearly preserves squared norm
controls its squared-norm distortion on the whole space.  This packages the
Gram-operator lifting used in finite-dimensional random embedding arguments.
-/
theorem abs_norm_sq_sub_norm_sq_le_of_unit_sphere_net
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] F) (N : Finset E) (epsilon M : ℝ)
    (hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_lt_half : epsilon < 1 / 2)
    (hM_nonneg : 0 ≤ M)
    (hnet : ∀ x, ‖x‖ = 1 → ∃ y ∈ N, ‖x - y‖ < epsilon)
    (hN_unit : ∀ y ∈ N, ‖y‖ = 1)
    (hN : ∀ y ∈ N, |‖L y‖ ^ 2 - 1| ≤ M) :
    ∀ x : E, |‖L x‖ ^ 2 - ‖x‖ ^ 2| ≤
      (M / (1 - 2 * epsilon)) * ‖x‖ ^ 2 := by
  let T : E →L[ℝ] E := gramDeviation L
  have hT : T.IsSymmetric := by
    exact gramDeviation_isSymmetric L
  have hquad : ∀ y ∈ N, |inner ℝ (T y) y| ≤ M := by
    intro y hy
    change |inner ℝ (gramDeviation L y) y| ≤ M
    rw [inner_gramDeviation_self_eq_norm_sq_sub]
    simpa [hN_unit y hy] using hN y hy
  have hop : ‖T‖ ≤ M / (1 - 2 * epsilon) := by
    exact opNorm_le_div_of_quadratic_form_unit_sphere_net T hT N epsilon M
      hepsilon_nonneg hepsilon_lt_half hM_nonneg hnet hN_unit hquad
  intro x
  rw [← inner_gramDeviation_self_eq_norm_sq_sub L x]
  change |inner ℝ (T x) x| ≤ _
  calc
    |inner ℝ (T x) x| ≤ ‖T x‖ * ‖x‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖T‖ * ‖x‖) * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg _)
    _ = ‖T‖ * ‖x‖ ^ 2 := by ring
    _ ≤ (M / (1 - 2 * epsilon)) * ‖x‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right hop (sq_nonneg _)

/--
A bounded subset of a finite-dimensional real normed space has a finite net
whose centers remain in the subset.  Starting from the volumetric unit-ball
net, each cell meeting the subset contributes one selected subset point; this
doubles the covering radius without increasing cardinality.
-/
theorem exists_finset_subset_scaled_closedBall_net
    (subset : Set E) (anchor : E) (hanchor : anchor ∈ subset)
    (radius : ℝ) (hradius : 0 ≤ radius) (resolution : ℕ)
    (hbounded : ∀ point ∈ subset, ‖point - anchor‖ ≤ radius) :
    ∃ net : Finset E,
      net.card ≤ (4 * resolution + 5) ^ finrank ℝ E ∧
      (∀ center ∈ net, center ∈ subset) ∧
      ∀ point ∈ subset, ∃ center ∈ net,
        ‖point - center‖ ≤ 2 * radius / (resolution + 1 : ℝ) := by
  classical
  by_cases hradiusZero : radius = 0
  · refine ⟨{anchor}, ?_, ?_, ?_⟩
    · have hbase : 0 < 4 * resolution + 5 := by omega
      have hpower : 0 < (4 * resolution + 5) ^ finrank ℝ E :=
        pow_pos hbase _
      simp only [Finset.card_singleton]
      omega
    · intro center hcenter
      have hcenterEq : center = anchor := Finset.mem_singleton.mp hcenter
      simpa [hcenterEq] using hanchor
    · intro point hpoint
      have hnorm : ‖point - anchor‖ = 0 :=
        le_antisymm (by simpa [hradiusZero] using hbounded point hpoint) (norm_nonneg _)
      have hpointEq : point = anchor := sub_eq_zero.mp (norm_eq_zero.mp hnorm)
      refine ⟨anchor, Finset.mem_singleton_self anchor, ?_⟩
      simp [hpointEq, hradiusZero]
  have hradiusPos : 0 < radius := lt_of_le_of_ne hradius (Ne.symm hradiusZero)
  rcases subsingleton_or_nontrivial E with hsubsingleton | hnontrivial
  · letI : Subsingleton E := hsubsingleton
    refine ⟨{anchor}, ?_, ?_, ?_⟩
    · have hbase : 0 < 4 * resolution + 5 := by omega
      have hpower : 0 < (4 * resolution + 5) ^ finrank ℝ E :=
        pow_pos hbase _
      simp only [Finset.card_singleton]
      omega
    · intro center hcenter
      have hcenterEq : center = anchor := Subsingleton.elim _ _
      simpa [hcenterEq] using hanchor
    · intro point hpoint
      refine ⟨anchor, Finset.mem_singleton_self anchor, ?_⟩
      have hpointEq : point = anchor := Subsingleton.elim _ _
      rw [hpointEq, sub_self, norm_zero]
      positivity
  · letI : Nontrivial E := hnontrivial
    let epsilon : ℝ := 1 / (resolution + 1 : ℝ)
    let normalized : E → E :=
      fun point => radius⁻¹ • (point - anchor)
    obtain ⟨unitNet, hcard, _hunit, hcover⟩ :=
      exists_finset_unit_closedBall_inv_succ_net (E := E) resolution
    let CellMeets (candidate : E) : Prop :=
      ∃ point ∈ subset, ‖normalized point - candidate‖ < epsilon
    let pick (candidate : E) : E :=
      if hcell : CellMeets candidate then hcell.choose else anchor
    have hpick (candidate : E) (hcell : CellMeets candidate) :
        pick candidate ∈ subset ∧
          ‖normalized (pick candidate) - candidate‖ < epsilon := by
      simp only [pick, dif_pos hcell]
      exact hcell.choose_spec
    let eligible : Finset E := unitNet.filter CellMeets
    let net : Finset E := eligible.image pick
    refine ⟨net, ?_, ?_, ?_⟩
    · calc
        net.card ≤ eligible.card := Finset.card_image_le
        _ ≤ unitNet.card := Finset.card_filter_le _ _
        _ ≤ (4 * resolution + 5) ^ finrank ℝ E := hcard
    · intro center hcenter
      obtain ⟨candidate, hcandidate, rfl⟩ := Finset.mem_image.mp hcenter
      have hcell : CellMeets candidate := (Finset.mem_filter.mp hcandidate).2
      exact (hpick candidate hcell).1
    · intro point hpoint
      have hnormalized : ‖normalized point‖ ≤ 1 := by
        simp only [normalized, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_pos hradiusPos]
        calc
          radius⁻¹ * ‖point - anchor‖ ≤ radius⁻¹ * radius :=
            mul_le_mul_of_nonneg_left (hbounded point hpoint) (inv_nonneg.mpr hradius)
          _ = 1 := inv_mul_cancel₀ hradiusPos.ne'
      obtain ⟨candidate, hcandidate, hpointCandidate⟩ :=
        hcover (normalized point) hnormalized
      have hcell : CellMeets candidate :=
        ⟨point, hpoint, by simpa [epsilon] using hpointCandidate⟩
      have hcandidateEligible : candidate ∈ eligible :=
        Finset.mem_filter.mpr ⟨hcandidate, hcell⟩
      refine ⟨pick candidate, Finset.mem_image.mpr
        ⟨candidate, hcandidateEligible, rfl⟩, ?_⟩
      have hpicked := (hpick candidate hcell).2
      have hnormalizedDifference :
          ‖normalized point - normalized (pick candidate)‖ < 2 * epsilon := by
        calc
          ‖normalized point - normalized (pick candidate)‖ =
              ‖(normalized point - candidate) +
                (candidate - normalized (pick candidate))‖ := by
                congr 1
                abel
          _ ≤ ‖normalized point - candidate‖ +
                ‖candidate - normalized (pick candidate)‖ := norm_add_le _ _
          _ < epsilon + epsilon := by
            apply add_lt_add hpointCandidate
            simpa [norm_sub_rev] using hpicked
          _ = 2 * epsilon := by ring
      have hscale :
          point - pick candidate =
            radius • (normalized point - normalized (pick candidate)) := by
        simp only [normalized, smul_sub, smul_smul]
        rw [mul_inv_cancel₀ hradiusPos.ne']
        simp
      rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_pos hradiusPos]
      calc
        radius * ‖normalized point - normalized (pick candidate)‖ ≤
            radius * (2 * epsilon) :=
          (mul_lt_mul_of_pos_left hnormalizedDifference hradiusPos).le
        _ = 2 * radius / (resolution + 1 : ℝ) := by
          simp [epsilon]
          ring

end EuclideanNets
end Math
end AppliedModelingLib
