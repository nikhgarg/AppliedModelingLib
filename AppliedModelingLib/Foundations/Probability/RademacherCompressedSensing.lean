import AppliedModelingLib.Foundations.Probability.RademacherMatrix
import AppliedModelingLib.Foundations.Math.MatrixRankInequalities

/-!
# Rademacher Basis-Pursuit Recovery

A fully finite random-matrix construction for exact sparse recovery at the
standard logarithmic row scale.
-/

namespace AppliedModelingLib
namespace Probability
namespace RademacherMatrix

open AppliedModelingLib.Math.LinearCompressedSensing

abbrev FiniteFeatureMatrix (m d : ℕ) : Type :=
  Fin m → Fin d → ℝ

abbrev rademacher_compressed_sensing_boundary : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ m k : ℕ, 1 ≤ k → 2 * k ≤ m →
      ∃ d : ℕ, ∃ A : FiniteFeatureMatrix m d,
        (d : ℝ) ≤ C * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) ∧
          BasisPursuitExactRecovery A k


abbrev rademacher_nullspace_property_boundary : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ m k : ℕ, 1 ≤ k → 2 * k ≤ m →
      ∃ d : ℕ, ∃ A : FiniteFeatureMatrix m d,
        (d : ℝ) ≤ C * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) ∧
          NullspaceProperty A k


abbrev rademacher_supportwise_rip_uniform_failure_boundary :
    Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ m k : ℕ, 1 ≤ k → 2 * k ≤ m →
      ∃ d : ℕ, ∃ δ η : ℝ,
        0 ≤ δ ∧ δ < 2 / 5 ∧
          (d : ℝ) ≤ C * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) ∧
            0 ≤ η ∧
              ((supportFinsetsCardLe (Feature := Fin m) (3 * k)).card : ℝ) *
                  η < 1 ∧
                ∀ S ∈ supportFinsetsCardLe (Feature := Fin m) (3 * k),
                  AppliedModelingLib.measureProb
                    (AppliedModelingLib.Probability.RademacherMatrix.rowsMeasure
                      (Fin m) (Fin d))
                    (fun ω =>
                      ¬ RestrictedIsometryOnSupport
                        (AppliedModelingLib.Probability.RademacherMatrix.scaledMatrix
                          (Feature := Fin m) (Coord := Fin d) ω) S δ) ≤ η


abbrev rademacher_supportwise_rip_binomial_failure_boundary :
    Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ m k : ℕ, 1 ≤ k → 2 * k ≤ m →
      ∃ d : ℕ, ∃ δ η : ℝ,
        0 ≤ δ ∧ δ < 2 / 5 ∧
          (d : ℝ) ≤ C * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) ∧
            0 ≤ η ∧
              ((∑ r ∈ Finset.range (3 * k + 1), Nat.choose m r : ℕ) : ℝ) *
                  η < 1 ∧
                ∀ S ∈ supportFinsetsCardLe (Feature := Fin m) (3 * k),
                  AppliedModelingLib.measureProb
                    (AppliedModelingLib.Probability.RademacherMatrix.rowsMeasure
                      (Fin m) (Fin d))
                    (fun ω =>
                      ¬ RestrictedIsometryOnSupport
                        (AppliedModelingLib.Probability.RademacherMatrix.scaledMatrix
                          (Feature := Fin m) (Coord := Fin d) ω) S δ) ≤ η


abbrev rademacher_supportwise_rip_large_choose_failure_boundary :
    Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ m k : ℕ, 1 ≤ k → 6 * k ≤ m →
      ∃ d : ℕ, ∃ δ η : ℝ,
        0 ≤ δ ∧ δ < 2 / 5 ∧
          (d : ℝ) ≤ C * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) ∧
            0 ≤ η ∧
              (((3 * k + 1) * Nat.choose m (3 * k) : ℕ) : ℝ) *
                  η < 1 ∧
                ∀ S ∈ supportFinsetsCardLe (Feature := Fin m) (3 * k),
                  AppliedModelingLib.measureProb
                    (AppliedModelingLib.Probability.RademacherMatrix.rowsMeasure
                      (Fin m) (Fin d))
                    (fun ω =>
                      ¬ RestrictedIsometryOnSupport
                        (AppliedModelingLib.Probability.RademacherMatrix.scaledMatrix
                          (Feature := Fin m) (Coord := Fin d) ω) S δ) ≤ η


abbrev rademacher_supportwise_rip_large_exp_failure_boundary :
    Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ m k : ℕ, 1 ≤ k → 6 * k ≤ m →
      ∃ d : ℕ, ∃ δ rate : ℝ,
        0 ≤ δ ∧ δ < 2 / 5 ∧
          (d : ℝ) ≤ C * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) ∧
            Real.log ((((3 * k + 1) * Nat.choose m (3 * k) : ℕ) : ℝ)) <
              rate ∧
                ∀ S ∈ supportFinsetsCardLe (Feature := Fin m) (3 * k),
                  AppliedModelingLib.measureProb
                    (AppliedModelingLib.Probability.RademacherMatrix.rowsMeasure
                      (Fin m) (Fin d))
                    (fun ω =>
                      ¬ RestrictedIsometryOnSupport
                        (AppliedModelingLib.Probability.RademacherMatrix.scaledMatrix
                          (Feature := Fin m) (Coord := Fin d) ω) S δ) ≤
                    Real.exp (-rate)


abbrev rademacher_supportwise_rip_large_count_envelope_failure_boundary :
    Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ m k : ℕ, 1 ≤ k → 6 * k ≤ m →
      ∃ d : ℕ, ∃ δ rate : ℝ,
        0 ≤ δ ∧ δ < 2 / 5 ∧
          (d : ℝ) ≤ C * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) ∧
            Real.log (((3 * k + 1 : ℕ) : ℝ)) +
                ((3 * k : ℕ) : ℝ) *
                  Real.log (Real.exp 1 * (m : ℝ) / ((3 * k : ℕ) : ℝ)) <
              rate ∧
                ∀ S ∈ supportFinsetsCardLe (Feature := Fin m) (3 * k),
                  AppliedModelingLib.measureProb
                    (AppliedModelingLib.Probability.RademacherMatrix.rowsMeasure
                      (Fin m) (Fin d))
                    (fun ω =>
                      ¬ RestrictedIsometryOnSupport
                        (AppliedModelingLib.Probability.RademacherMatrix.scaledMatrix
                          (Feature := Fin m) (Coord := Fin d) ω) S δ) ≤
                    Real.exp (-rate)

private theorem log_exp_mul_nat_div_three_mul_le_one_add_log_div
    {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    Real.log (Real.exp 1 * (m : ℝ) / ((3 * k : ℕ) : ℝ)) ≤
      1 + Real.log ((m : ℝ) / (k : ℝ)) := by
  have hm_real : 0 < (m : ℝ) := by exact_mod_cast hm
  have hk_real : 0 < (k : ℝ) := by exact_mod_cast hk
  have hratio_pos : 0 < (m : ℝ) / (k : ℝ) := div_pos hm_real hk_real
  have hdiv_three_pos : 0 < ((m : ℝ) / (k : ℝ)) / 3 := by positivity
  have hrewrite :
      Real.exp 1 * (m : ℝ) / ((3 * k : ℕ) : ℝ) =
        Real.exp 1 * (((m : ℝ) / (k : ℝ)) / 3) := by
    norm_num [Nat.cast_mul]
    field_simp [hk_real.ne']
  rw [hrewrite, Real.log_mul (Real.exp_pos 1).ne' hdiv_three_pos.ne',
    Real.log_exp]
  have hdiv_three_le : ((m : ℝ) / (k : ℝ)) / 3 ≤ (m : ℝ) / (k : ℝ) := by
    nlinarith [hratio_pos]
  have hlog_div_three_le :
      Real.log (((m : ℝ) / (k : ℝ)) / 3) ≤
        Real.log ((m : ℝ) / (k : ℝ)) :=
    Real.log_le_log hdiv_three_pos hdiv_three_le
  linarith


theorem supportwise_rip_large_count_envelope_le_logarithmic_scale
    {m k : ℕ} (hk : 1 ≤ k) (hlarge : 6 * k ≤ m) :
    Real.log (((3 * k + 1 : ℕ) : ℝ)) +
        ((3 * k : ℕ) : ℝ) *
          Real.log (Real.exp 1 * (m : ℝ) / ((3 * k : ℕ) : ℝ)) ≤
      (6 / Real.log 2 + 3) * (k : ℝ) *
        Real.log ((m : ℝ) / (k : ℝ)) := by
  have hk_pos : 0 < k := lt_of_lt_of_le (by omega) hk
  have hm_pos : 0 < m := by omega
  have hk_real : 0 < (k : ℝ) := by exact_mod_cast hk_pos
  have hratio_ge_two : (2 : ℝ) ≤ (m : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ hk_real]
    have htwo_le_sixk : 2 * k ≤ 6 * k := by nlinarith [hk_pos]
    exact_mod_cast htwo_le_sixk.trans hlarge
  have hlog_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog_two_le :
      Real.log (2 : ℝ) ≤ Real.log ((m : ℝ) / (k : ℝ)) :=
    Real.log_le_log (by norm_num) hratio_ge_two
  have hlog_ratio_nonneg :
      0 ≤ Real.log ((m : ℝ) / (k : ℝ)) :=
    hlog_two_pos.le.trans hlog_two_le
  have hlog_succ_le :
      Real.log (((3 * k + 1 : ℕ) : ℝ)) ≤ ((3 * k : ℕ) : ℝ) := by
    have hpos : 0 < (((3 * k + 1 : ℕ) : ℝ)) := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    have hcast : (((3 * k + 1 : ℕ) : ℝ)) = ((3 * k : ℕ) : ℝ) + 1 := by
      norm_num [Nat.cast_add, Nat.cast_one]
    linarith
  have hlog_base_le :
      Real.log (Real.exp 1 * (m : ℝ) / ((3 * k : ℕ) : ℝ)) ≤
        1 + Real.log ((m : ℝ) / (k : ℝ)) :=
    log_exp_mul_nat_div_three_mul_le_one_add_log_div hm_pos hk_pos
  have hthree_k_nonneg : 0 ≤ (((3 * k : ℕ) : ℝ)) := by positivity
  have hmul_log_base_le :
      ((3 * k : ℕ) : ℝ) *
          Real.log (Real.exp 1 * (m : ℝ) / ((3 * k : ℕ) : ℝ)) ≤
        ((3 * k : ℕ) : ℝ) *
          (1 + Real.log ((m : ℝ) / (k : ℝ))) :=
    mul_le_mul_of_nonneg_left hlog_base_le hthree_k_nonneg
  have hcoarse :
      Real.log (((3 * k + 1 : ℕ) : ℝ)) +
          ((3 * k : ℕ) : ℝ) *
            Real.log (Real.exp 1 * (m : ℝ) / ((3 * k : ℕ) : ℝ)) ≤
        6 * (k : ℝ) + 3 * (k : ℝ) *
          Real.log ((m : ℝ) / (k : ℝ)) := by
    have hthree_cast : (((3 * k : ℕ) : ℝ)) = 3 * (k : ℝ) := by
      norm_num [Nat.cast_mul]
    nlinarith
  have hsix_le :
      6 * (k : ℝ) ≤
        (6 / Real.log 2) * (k : ℝ) *
          Real.log ((m : ℝ) / (k : ℝ)) := by
    calc
      6 * (k : ℝ) =
          (6 / Real.log 2) * (k : ℝ) * Real.log (2 : ℝ) := by
            field_simp [hlog_two_pos.ne']
      _ ≤ (6 / Real.log 2) * (k : ℝ) *
          Real.log ((m : ℝ) / (k : ℝ)) := by
            have hcoeff_nonneg : 0 ≤ (6 / Real.log 2) * (k : ℝ) := by
              positivity
            exact mul_le_mul_of_nonneg_left hlog_two_le hcoeff_nonneg
  nlinarith [hcoarse, hsix_le]


abbrev rademacher_supportwise_rip_large_logarithmic_scale_failure_boundary :
    Prop :=
  ∃ C R : ℝ, 0 < C ∧ (6 / Real.log 2 + 3) < R ∧
    ∀ m k : ℕ, 1 ≤ k → 6 * k ≤ m →
      ∃ d : ℕ, ∃ δ : ℝ,
        0 ≤ δ ∧ δ < 2 / 5 ∧
          (d : ℝ) ≤ C * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) ∧
            ∀ S ∈ supportFinsetsCardLe (Feature := Fin m) (3 * k),
              AppliedModelingLib.measureProb
                (AppliedModelingLib.Probability.RademacherMatrix.rowsMeasure
                  (Fin m) (Fin d))
                (fun ω =>
                  ¬ RestrictedIsometryOnSupport
                    (AppliedModelingLib.Probability.RademacherMatrix.scaledMatrix
                      (Feature := Fin m) (Coord := Fin d) ω) S δ) ≤
                Real.exp
                  (-(R * (k : ℝ) *
                    Real.log ((m : ℝ) / (k : ℝ))))


abbrev rademacher_supportwise_rip_fixed_support_rows_failure_boundary :
    Prop :=
  ∃ A B δ : ℝ,
    0 < A ∧ 0 < B ∧ 0 ≤ δ ∧ δ < 2 / 5 ∧
      (6 / Real.log 2 + 3) < B * A ∧
        ∀ m k d : ℕ, 1 ≤ k → 6 * k ≤ m →
          A * ((k : ℝ) * Real.log ((m : ℝ) / (k : ℝ))) ≤ (d : ℝ) →
            ∀ S ∈ supportFinsetsCardLe (Feature := Fin m) (3 * k),
              AppliedModelingLib.measureProb
                (AppliedModelingLib.Probability.RademacherMatrix.rowsMeasure
                  (Fin m) (Fin d))
                (fun ω =>
                  ¬ RestrictedIsometryOnSupport
                    (AppliedModelingLib.Probability.RademacherMatrix.scaledMatrix
                      (Feature := Fin m) (Coord := Fin d) ω) S δ) ≤
                Real.exp (-(B * (d : ℝ)))


abbrev rademacher_supportwise_rip_failure_sum_boundary :
    Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ m k : ℕ, 1 ≤ k → 2 * k ≤ m →
      ∃ d : ℕ, ∃ δ : ℝ,
        0 ≤ δ ∧ δ < 2 / 5 ∧
          (d : ℝ) ≤ C * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) ∧
            ∑ S ∈ supportFinsetsCardLe (Feature := Fin m) (3 * k),
              AppliedModelingLib.measureProb
                (AppliedModelingLib.Probability.RademacherMatrix.rowsMeasure
                  (Fin m) (Fin d))
                (fun ω =>
                  ¬ RestrictedIsometryOnSupport
                    (AppliedModelingLib.Probability.RademacherMatrix.scaledMatrix
                      (Feature := Fin m) (Coord := Fin d) ω) S δ) < 1


abbrev rademacher_supportwise_rip_boundary : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ m k : ℕ, 1 ≤ k → 2 * k ≤ m →
      ∃ d : ℕ, ∃ A : FiniteFeatureMatrix m d, ∃ δ : ℝ,
        0 ≤ δ ∧ δ < 2 / 5 ∧
          (d : ℝ) ≤ C * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) ∧
            ∀ S ∈ supportFinsetsCardLe (Feature := Fin m) (3 * k),
              RestrictedIsometryOnSupport A S δ


abbrev rademacher_rip_boundary : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ m k : ℕ, 1 ≤ k → 2 * k ≤ m →
      ∃ d : ℕ, ∃ A : FiniteFeatureMatrix m d, ∃ δ : ℝ,
        0 ≤ δ ∧ δ < 2 / 5 ∧
          (d : ℝ) ≤ C * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) ∧
            RestrictedIsometryProperty A (3 * k) δ

theorem rademacher_rip_boundary_of_uniform_failure
    (H : rademacher_supportwise_rip_uniform_failure_boundary) :
    rademacher_rip_boundary := by
  rcases H with ⟨C, hC, hmain⟩
  refine ⟨C, hC, ?_⟩
  intro m k hk hm
  rcases hmain m k hk hm with
    ⟨d, δ, η, hδ_nonneg, hδ, hd, _hη_nonneg, hcard_mul, hfail⟩
  rcases
    AppliedModelingLib.Probability.RademacherMatrix.exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_lt_one
      (Feature := Fin m) (Coord := Fin d) (s := 3 * k) (δ := δ) (η := η)
      (by simpa [supportFinsetsCardLe] using hcard_mul)
      (by
        intro S hS
        simpa [supportFinsetsCardLe,
          RestrictedIsometryOnSupport] using hfail S hS) with
    ⟨A, hrip⟩
  exact ⟨d, A, δ, hδ_nonneg, hδ, hd, hrip⟩

theorem rademacher_rip_boundary_of_binomial_failure
    (H : rademacher_supportwise_rip_binomial_failure_boundary) :
    rademacher_rip_boundary := by
  rcases H with ⟨C, hC, hmain⟩
  refine ⟨C, hC, ?_⟩
  intro m k hk hm
  rcases hmain m k hk hm with
    ⟨d, δ, η, hδ_nonneg, hδ, hd, hη_nonneg, hcount_mul, hfail⟩
  rcases
    AppliedModelingLib.Probability.RademacherMatrix.exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_sum_choose_lt_one
      (Feature := Fin m) (Coord := Fin d) (s := 3 * k) (δ := δ) (η := η)
      hη_nonneg
      (by simpa [Fintype.card_fin] using hcount_mul)
      (by
        intro S hS
        simpa [supportFinsetsCardLe,
          RestrictedIsometryOnSupport] using hfail S hS) with
    ⟨A, hrip⟩
  exact ⟨d, A, δ, hδ_nonneg, hδ, hd, hrip⟩

theorem rademacher_supportwise_rip_large_choose_failure_boundary_of_large_exp_failure
    (H : rademacher_supportwise_rip_large_exp_failure_boundary) :
    rademacher_supportwise_rip_large_choose_failure_boundary := by
  rcases H with ⟨C, hC, hmain⟩
  refine ⟨C, hC, ?_⟩
  intro m k hk hlarge
  rcases hmain m k hk hlarge with
    ⟨d, δ, rate, hδ_nonneg, hδ, hd, hlog_count_lt, hfail⟩
  have hcount_pos :
      0 < ((((3 * k + 1) * Nat.choose m (3 * k) : ℕ) : ℝ)) := by
    have hchoose_pos : 0 < Nat.choose m (3 * k) :=
      Nat.choose_pos (by omega)
    have hfactor_pos : 0 < 3 * k + 1 := Nat.succ_pos _
    exact_mod_cast Nat.mul_pos hfactor_pos hchoose_pos
  have hcount_mul :
      ((((3 * k + 1) * Nat.choose m (3 * k) : ℕ) : ℝ)) *
          Real.exp (-rate) < 1 :=
    AppliedModelingLib.Math.mul_exp_neg_lt_one_of_log_lt hcount_pos hlog_count_lt
  exact ⟨d, δ, Real.exp (-rate), hδ_nonneg, hδ, hd,
    (Real.exp_pos _).le, hcount_mul, hfail⟩

theorem rademacher_supportwise_rip_large_exp_failure_boundary_of_count_envelope
    (H : rademacher_supportwise_rip_large_count_envelope_failure_boundary) :
    rademacher_supportwise_rip_large_exp_failure_boundary := by
  rcases H with ⟨C, hC, hmain⟩
  refine ⟨C, hC, ?_⟩
  intro m k hk hlarge
  rcases hmain m k hk hlarge with
    ⟨d, δ, rate, hδ_nonneg, hδ, hd, hcount_envelope_lt, hfail⟩
  have hk_pos : 0 < k := lt_of_lt_of_le (by omega) hk
  have hthree_k_pos : 0 < 3 * k := by omega
  have hthree_k_le_m : 3 * k ≤ m := by omega
  have hlog_count_le :
      Real.log ((((3 * k + 1) * Nat.choose m (3 * k) : ℕ) : ℝ)) ≤
        Real.log (((3 * k + 1 : ℕ) : ℝ)) +
          ((3 * k : ℕ) : ℝ) *
            Real.log (Real.exp 1 * (m : ℝ) / ((3 * k : ℕ) : ℝ)) :=
    AppliedModelingLib.Math.MatrixRankInequalities.log_succ_mul_choose_le_log_succ_add_mul_log_exp_mul_div
      (N := m) (p := 3 * k) hthree_k_pos hthree_k_le_m
  exact ⟨d, δ, rate, hδ_nonneg, hδ, hd,
    lt_of_le_of_lt hlog_count_le hcount_envelope_lt, hfail⟩

theorem rademacher_supportwise_rip_large_count_envelope_failure_boundary_of_logarithmic_scale
    (H : rademacher_supportwise_rip_large_logarithmic_scale_failure_boundary) :
    rademacher_supportwise_rip_large_count_envelope_failure_boundary := by
  rcases H with ⟨C, R, hC, hR, hmain⟩
  refine ⟨C, hC, ?_⟩
  intro m k hk hlarge
  rcases hmain m k hk hlarge with
    ⟨d, δ, hδ_nonneg, hδ, hd, hfail⟩
  have hk_pos : 0 < k := lt_of_lt_of_le (by omega) hk
  have hk_real : 0 < (k : ℝ) := by exact_mod_cast hk_pos
  have hratio_ge_two : (2 : ℝ) ≤ (m : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ hk_real]
    have htwo_le_sixk : 2 * k ≤ 6 * k := by nlinarith [hk_pos]
    exact_mod_cast htwo_le_sixk.trans hlarge
  have hlog_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog_two_le :
      Real.log (2 : ℝ) ≤ Real.log ((m : ℝ) / (k : ℝ)) :=
    Real.log_le_log (by norm_num) hratio_ge_two
  have hlog_ratio_pos :
      0 < Real.log ((m : ℝ) / (k : ℝ)) :=
    hlog_two_pos.trans_le hlog_two_le
  have hscale_pos :
      0 < (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) :=
    mul_pos hk_real hlog_ratio_pos
  have hcount_envelope_le :=
    supportwise_rip_large_count_envelope_le_logarithmic_scale
      (m := m) (k := k) hk hlarge
  have hscale_lt :
      (6 / Real.log 2 + 3) * (k : ℝ) *
          Real.log ((m : ℝ) / (k : ℝ)) <
        R * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) := by
    have hmul := mul_lt_mul_of_pos_right hR hscale_pos
    simpa [mul_assoc] using hmul
  exact ⟨d, δ,
    R * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)),
    hδ_nonneg, hδ, hd,
    lt_of_le_of_lt hcount_envelope_le hscale_lt, hfail⟩

theorem rademacher_supportwise_rip_large_logarithmic_scale_failure_boundary_of_fixed_support_rows
    (H : rademacher_supportwise_rip_fixed_support_rows_failure_boundary) :
    rademacher_supportwise_rip_large_logarithmic_scale_failure_boundary := by
  rcases H with ⟨A, B, δ, hA, hB, hδ_nonneg, hδ, hBA, htail⟩
  refine ⟨A + 1 / Real.log 2, B * A, ?_, hBA, ?_⟩
  · have hlog_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  · intro m k hk hlarge
    let scale : ℝ := (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ))
    let d : ℕ := Nat.ceil (A * scale)
    have hk_pos : 0 < k := lt_of_lt_of_le (by omega) hk
    have hk_real : 0 < (k : ℝ) := by exact_mod_cast hk_pos
    have hk_real_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hratio_ge_two : (2 : ℝ) ≤ (m : ℝ) / (k : ℝ) := by
      rw [le_div_iff₀ hk_real]
      have htwo_le_sixk : 2 * k ≤ 6 * k := by nlinarith [hk_pos]
      exact_mod_cast htwo_le_sixk.trans hlarge
    have hlog_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlog_two_le :
        Real.log (2 : ℝ) ≤ Real.log ((m : ℝ) / (k : ℝ)) :=
      Real.log_le_log (by norm_num) hratio_ge_two
    have hlog_ratio_nonneg :
        0 ≤ Real.log ((m : ℝ) / (k : ℝ)) :=
      hlog_two_pos.le.trans hlog_two_le
    have hscale_nonneg : 0 ≤ scale := by
      dsimp [scale]
      exact mul_nonneg hk_real.le hlog_ratio_nonneg
    have hscale_ge_log_two : Real.log (2 : ℝ) ≤ scale := by
      dsimp [scale]
      nlinarith [hk_real_one, hlog_two_le, hlog_two_pos]
    have hone_le_inv_log_two_mul_scale :
        1 ≤ (1 / Real.log 2) * scale := by
      calc
        1 = (1 / Real.log 2) * Real.log (2 : ℝ) := by
          field_simp [hlog_two_pos.ne']
        _ ≤ (1 / Real.log 2) * scale := by
          have hcoeff_nonneg : 0 ≤ (1 / Real.log 2) := by positivity
          exact mul_le_mul_of_nonneg_left hscale_ge_log_two hcoeff_nonneg
    have hx_nonneg : 0 ≤ A * scale := mul_nonneg hA.le hscale_nonneg
    have hd_lower : A * scale ≤ (d : ℝ) := by
      simpa [d] using Nat.le_ceil (A * scale)
    have hd_lt : (d : ℝ) < A * scale + 1 := by
      simpa [d] using Nat.ceil_lt_add_one hx_nonneg
    have hd_upper :
        (d : ℝ) ≤ (A + 1 / Real.log 2) * (k : ℝ) *
          Real.log ((m : ℝ) / (k : ℝ)) := by
      dsimp [scale] at hd_lt hone_le_inv_log_two_mul_scale ⊢
      nlinarith
    refine ⟨d, δ, hδ_nonneg, hδ, hd_upper, ?_⟩
    intro S hS
    have htail_S :=
      htail m k d hk hlarge (by simpa [scale] using hd_lower) S hS
    have hexp_mono :
        Real.exp (-(B * (d : ℝ))) ≤
          Real.exp
            (-(B * A * (k : ℝ) *
              Real.log ((m : ℝ) / (k : ℝ)))) := by
      apply Real.exp_le_exp.mpr
      dsimp [scale] at hd_lower
      nlinarith [hd_lower, hB]
    exact htail_S.trans (by simpa [mul_assoc] using hexp_mono)

theorem rademacher_compressed_sensing_boundary_of_large_choose_failure
    (H : rademacher_supportwise_rip_large_choose_failure_boundary) :
    rademacher_compressed_sensing_boundary := by
  rcases H with ⟨C, hC, hmain⟩
  let Csmall : ℝ := 6 / Real.log 2
  refine ⟨C + Csmall, ?_, ?_⟩
  · have hlog_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hsmall_pos : 0 < Csmall := by
      dsimp [Csmall]
      positivity
    positivity
  · intro m k hk hm
    have hk_pos_nat : 0 < k := lt_of_lt_of_le (by omega) hk
    have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos_nat
    have hratio_ge_two : (2 : ℝ) ≤ (m : ℝ) / (k : ℝ) := by
      rw [le_div_iff₀ hk_pos]
      exact_mod_cast hm
    have hratio_ge_one : (1 : ℝ) ≤ (m : ℝ) / (k : ℝ) :=
      (by norm_num : (1 : ℝ) ≤ 2).trans hratio_ge_two
    have hlog_nonneg :
        0 ≤ Real.log ((m : ℝ) / (k : ℝ)) :=
      Real.log_nonneg hratio_ge_one
    have hscale_nonneg :
        0 ≤ (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) :=
      mul_nonneg hk_pos.le hlog_nonneg
    by_cases hlarge : 6 * k ≤ m
    · rcases hmain m k hk hlarge with
        ⟨d, δ, η, hδ_nonneg, hδ, hd, hη_nonneg, hcount_mul, hfail⟩
      have hs_half : 3 * k ≤ Fintype.card (Fin m) / 2 := by
        simp [Fintype.card_fin]
        omega
      rcases
        AppliedModelingLib.Probability.RademacherMatrix.exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_succ_mul_choose_lt_one
          (Feature := Fin m) (Coord := Fin d) (s := 3 * k) (δ := δ) (η := η)
          hs_half hη_nonneg
          (by simpa [Fintype.card_fin] using hcount_mul)
          (by
            intro S hS
            simpa [supportFinsetsCardLe,
              RestrictedIsometryOnSupport] using hfail S hS) with
        ⟨A, hrip⟩
      have hC_le : C ≤ C + Csmall := by
        have hlog_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
        have hsmall_nonneg : 0 ≤ Csmall := by
          dsimp [Csmall]
          positivity
        linarith
      have hd' :
          (d : ℝ) ≤
            (C + Csmall) * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) := by
        have hmul :
            C * ((k : ℝ) * Real.log ((m : ℝ) / (k : ℝ))) ≤
              (C + Csmall) *
                ((k : ℝ) * Real.log ((m : ℝ) / (k : ℝ))) :=
          mul_le_mul_of_nonneg_right hC_le hscale_nonneg
        nlinarith [hd, hmul]
      exact ⟨d, A, hd',
        basisPursuitExactRecovery_of_nullspaceProperty
          (nullspaceProperty_of_restrictedIsometry_three_mul
            (A := A) (k := k) (δ := δ)
            hk_pos_nat hδ_nonneg hδ hrip)⟩
    · have hm_le_sixk_nat : m ≤ 6 * k := by omega
      have hm_le_sixk : (m : ℝ) ≤ 6 * (k : ℝ) := by
        exact_mod_cast hm_le_sixk_nat
      have hlog_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      have hlog_two_le :
          Real.log (2 : ℝ) ≤ Real.log ((m : ℝ) / (k : ℝ)) :=
        Real.log_le_log (by norm_num) hratio_ge_two
      have hsmall_scale :
          6 * (k : ℝ) ≤
            Csmall * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) := by
        calc
          6 * (k : ℝ) =
              Csmall * (k : ℝ) * Real.log (2 : ℝ) := by
                dsimp [Csmall]
                field_simp [hlog_two_pos.ne']
          _ ≤ Csmall * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) := by
                have hcoeff_nonneg : 0 ≤ Csmall * (k : ℝ) := by
                  dsimp [Csmall]
                  positivity
                exact mul_le_mul_of_nonneg_left hlog_two_le hcoeff_nonneg
      have hC_scale_nonneg :
          0 ≤ C * ((k : ℝ) * Real.log ((m : ℝ) / (k : ℝ))) :=
        mul_nonneg hC.le hscale_nonneg
      have hd_small :
          (m : ℝ) ≤
            (C + Csmall) * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) := by
        have htarget :
            Csmall * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) ≤
              (C + Csmall) * (k : ℝ) *
                Real.log ((m : ℝ) / (k : ℝ)) := by
          nlinarith [hC_scale_nonneg]
        linarith
      exact ⟨m, featureIdentityMatrix, hd_small,
        basisPursuitExactRecovery_featureIdentityMatrix (Feature := Fin m) k⟩

theorem rademacher_rip_boundary_of_supportwise_failure_sum
    (H : rademacher_supportwise_rip_failure_sum_boundary) :
    rademacher_rip_boundary := by
  rcases H with ⟨C, hC, hmain⟩
  refine ⟨C, hC, ?_⟩
  intro m k hk hm
  rcases hmain m k hk hm with ⟨d, δ, hδ_nonneg, hδ, hd, hsum⟩
  rcases
    AppliedModelingLib.Probability.RademacherMatrix.exists_scaledMatrix_restrictedIsometryProperty_of_supportwise_failure_sum_lt_one
      (Feature := Fin m) (Coord := Fin d) (s := 3 * k) (δ := δ)
      (by
        simpa [supportFinsetsCardLe,
          RestrictedIsometryOnSupport] using hsum) with
    ⟨A, hrip⟩
  exact ⟨d, A, δ, hδ_nonneg, hδ, hd, hrip⟩

theorem rademacher_rip_boundary_of_supportwise
    (H : rademacher_supportwise_rip_boundary) :
    rademacher_rip_boundary := by
  rcases H with ⟨C, hC, hmain⟩
  refine ⟨C, hC, ?_⟩
  intro m k hk hm
  rcases hmain m k hk hm with ⟨d, A, δ, hδ_nonneg, hδ, hd, hsupport⟩
  exact ⟨d, A, δ, hδ_nonneg, hδ, hd,
    restrictedIsometryProperty_of_forall_supportFinsetsCardLe
      (A := A) (s := 3 * k) (δ := δ) hsupport⟩

theorem rademacher_nullspace_property_boundary_of_rip
    (H : rademacher_rip_boundary) :
    rademacher_nullspace_property_boundary := by
  rcases H with ⟨C, hC, hmain⟩
  refine ⟨C, hC, ?_⟩
  intro m k hk hm
  rcases hmain m k hk hm with ⟨d, A, δ, hδ_nonneg, hδ, hd, hrip⟩
  exact ⟨d, A, hd,
    nullspaceProperty_of_restrictedIsometry_three_mul
      (A := A) (k := k) (δ := δ) hk hδ_nonneg hδ hrip⟩

theorem rademacher_compressed_sensing_boundary_of_nullspace_property
    (H : rademacher_nullspace_property_boundary) :
    rademacher_compressed_sensing_boundary := by
  rcases H with ⟨C, hC, hmain⟩
  refine ⟨C, hC, ?_⟩
  intro m k hk hm
  rcases hmain m k hk hm with ⟨d, A, hd, hnsp⟩
  exact ⟨d, A, hd,
    basisPursuitExactRecovery_of_nullspaceProperty hnsp⟩

theorem rademacher_compressed_sensing_boundary_of_rip
    (H : rademacher_rip_boundary) :
    rademacher_compressed_sensing_boundary :=
  rademacher_compressed_sensing_boundary_of_nullspace_property
    (rademacher_nullspace_property_boundary_of_rip H)

theorem rademacher_compressed_sensing_boundary_of_supportwise_rip
    (H : rademacher_supportwise_rip_boundary) :
    rademacher_compressed_sensing_boundary :=
  rademacher_compressed_sensing_boundary_of_rip
    (rademacher_rip_boundary_of_supportwise H)

theorem rademacher_compressed_sensing_boundary_of_supportwise_failure_sum
    (H : rademacher_supportwise_rip_failure_sum_boundary) :
    rademacher_compressed_sensing_boundary :=
  rademacher_compressed_sensing_boundary_of_rip
    (rademacher_rip_boundary_of_supportwise_failure_sum H)

theorem rademacher_compressed_sensing_boundary_of_uniform_failure
    (H : rademacher_supportwise_rip_uniform_failure_boundary) :
    rademacher_compressed_sensing_boundary :=
  rademacher_compressed_sensing_boundary_of_rip
    (rademacher_rip_boundary_of_uniform_failure H)

theorem rademacher_compressed_sensing_boundary_of_binomial_failure
    (H : rademacher_supportwise_rip_binomial_failure_boundary) :
    rademacher_compressed_sensing_boundary :=
  rademacher_compressed_sensing_boundary_of_rip
    (rademacher_rip_boundary_of_binomial_failure H)

theorem rademacher_compressed_sensing_boundary_of_large_exp_failure
    (H : rademacher_supportwise_rip_large_exp_failure_boundary) :
    rademacher_compressed_sensing_boundary :=
  rademacher_compressed_sensing_boundary_of_large_choose_failure
    (rademacher_supportwise_rip_large_choose_failure_boundary_of_large_exp_failure H)

theorem rademacher_compressed_sensing_boundary_of_large_count_envelope_failure
    (H : rademacher_supportwise_rip_large_count_envelope_failure_boundary) :
    rademacher_compressed_sensing_boundary :=
  rademacher_compressed_sensing_boundary_of_large_exp_failure
    (rademacher_supportwise_rip_large_exp_failure_boundary_of_count_envelope H)

theorem rademacher_compressed_sensing_boundary_of_large_logarithmic_scale_failure
    (H : rademacher_supportwise_rip_large_logarithmic_scale_failure_boundary) :
    rademacher_compressed_sensing_boundary :=
  rademacher_compressed_sensing_boundary_of_large_count_envelope_failure
    (rademacher_supportwise_rip_large_count_envelope_failure_boundary_of_logarithmic_scale H)

theorem rademacher_compressed_sensing_boundary_of_fixed_support_rows_failure
    (H : rademacher_supportwise_rip_fixed_support_rows_failure_boundary) :
    rademacher_compressed_sensing_boundary :=
  rademacher_compressed_sensing_boundary_of_large_logarithmic_scale_failure
    (rademacher_supportwise_rip_large_logarithmic_scale_failure_boundary_of_fixed_support_rows H)

private theorem rademacher_fixed_support_rows :
    rademacher_supportwise_rip_fixed_support_rows_failure_boundary := by
  let c : ℝ := 524288
  let A : ℝ := 2 * c * (6 / Real.log 2 + 11)
  let B : ℝ := 1 / (2 * c)
  refine ⟨A, B, 3 / 8, ?_, ?_, by norm_num, by norm_num, ?_, ?_⟩
  · dsimp [A, c]
    have hlog_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  · dsimp [B, c]
    positivity
  · dsimp [A, B, c]
    have hlog_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    field_simp [hlog_two_pos.ne']
    nlinarith
  · intro m k d hk hlarge hd_lower S hS
    have hk_pos : 0 < k := lt_of_lt_of_le (by omega) hk
    have hk_real : 0 < (k : ℝ) := by exact_mod_cast hk_pos
    have hratio_ge_six : (6 : ℝ) ≤ (m : ℝ) / (k : ℝ) := by
      rw [le_div_iff₀ hk_real]
      exact_mod_cast hlarge
    have hlog_six_pos : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
    have hlog_six_le : Real.log (6 : ℝ) ≤ Real.log ((m : ℝ) / (k : ℝ)) :=
      Real.log_le_log (by norm_num) hratio_ge_six
    have hscale_ge : (k : ℝ) * Real.log (6 : ℝ) ≤
        (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_six_le hk_real.le
    have hC_ge_seven : (7 : ℝ) ≤ 6 / Real.log 2 + 11 := by
      have hlog_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      have hdiv_pos : 0 < 6 / Real.log 2 := div_pos (by norm_num) hlog_two_pos
      linarith
    have hrow_ge : 2 * c * (7 * (k : ℝ) * Real.log (6 : ℝ)) ≤ (d : ℝ) := by
      have hscale_nonneg : 0 ≤ (k : ℝ) * Real.log (6 : ℝ) :=
        mul_nonneg hk_real.le hlog_six_pos.le
      have hCscale :
          7 * ((k : ℝ) * Real.log (6 : ℝ)) ≤
            (6 / Real.log 2 + 11) *
              ((k : ℝ) * Real.log ((m : ℝ) / (k : ℝ))) := by
        calc
          7 * ((k : ℝ) * Real.log (6 : ℝ)) ≤
              (6 / Real.log 2 + 11) * ((k : ℝ) * Real.log (6 : ℝ)) :=
            mul_le_mul_of_nonneg_right hC_ge_seven hscale_nonneg
          _ ≤ (6 / Real.log 2 + 11) *
              ((k : ℝ) * Real.log ((m : ℝ) / (k : ℝ))) := by
            have hC_nonneg : 0 ≤ 6 / Real.log 2 + 11 := by positivity
            exact mul_le_mul_of_nonneg_left hscale_ge hC_nonneg
      have hA_nonneg : 0 ≤ 2 * c := by dsimp [c]; norm_num
      calc
        2 * c * (7 * (k : ℝ) * Real.log (6 : ℝ)) =
            (2 * c) * (7 * ((k : ℝ) * Real.log (6 : ℝ))) := by ring
        _ ≤ (2 * c) * ((6 / Real.log 2 + 11) *
            ((k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)))) :=
          mul_le_mul_of_nonneg_left hCscale hA_nonneg
        _ = A * ((k : ℝ) * Real.log ((m : ℝ) / (k : ℝ))) := by
          dsimp [A]
          ring
        _ ≤ (d : ℝ) := hd_lower
    have hd_pos : 0 < d := by
      have hleft_pos : 0 < 2 * c * (7 * (k : ℝ) * Real.log (6 : ℝ)) := by
        dsimp [c]
        positivity
      exact_mod_cast lt_of_lt_of_le hleft_pos hrow_ge
    have hlog_two_le : Real.log (2 : ℝ) ≤ Real.log (6 : ℝ) :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hlog_nine_le : Real.log (9 : ℝ) ≤ 2 * Real.log (6 : ℝ) := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 9) (by norm_num : (9 : ℝ) ≤ 6 ^ 2)
      rw [Real.log_pow] at h
      norm_num at h ⊢
      exact h
    have hlog_prefactor :
        Real.log (2 * ((9 ^ (3 * k) : ℕ) : ℝ)) ≤ (d : ℝ) / (2 * c) := by
      have hpow_cast : ((9 ^ (3 * k) : ℕ) : ℝ) = (9 : ℝ) ^ (3 * k) := by
        norm_num [Nat.cast_pow]
      rw [hpow_cast, Real.log_mul (by norm_num) (pow_ne_zero _ (by norm_num)),
        Real.log_pow]
      have hk_real_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hthree_cast : ((3 * k : ℕ) : ℝ) = 3 * (k : ℝ) := by
        norm_num [Nat.cast_mul]
      have hsmall :
          Real.log (2 : ℝ) + ((3 * k : ℕ) : ℝ) * Real.log (9 : ℝ) ≤
            7 * (k : ℝ) * Real.log (6 : ℝ) := by
        rw [hthree_cast]
        nlinarith
      have hden_pos : 0 < 2 * c := by dsimp [c]; norm_num
      calc
        Real.log (2 : ℝ) + ((3 * k : ℕ) : ℝ) * Real.log (9 : ℝ) ≤
            7 * (k : ℝ) * Real.log (6 : ℝ) := hsmall
        _ = (2 * c * (7 * (k : ℝ) * Real.log (6 : ℝ))) / (2 * c) := by
          field_simp [hden_pos.ne']
          ring
        _ ≤ (d : ℝ) / (2 * c) := by
          exact (div_le_div_iff_of_pos_right hden_pos).mpr hrow_ge
    have htail :=
      AppliedModelingLib.Probability.RademacherMatrix.measure_not_restrictedIsometryOnSupport_scaledMatrix_three_eighths_le
        (Feature := Fin m) (Coord := Fin d) (by simpa using hd_pos) S
    have habsorb := AppliedModelingLib.Math.mul_exp_neg_le_exp_neg_of_log_le
      (count := 2 * ((9 ^ (3 * k) : ℕ) : ℝ))
      (rate := (d : ℝ) / c) (penalty := (d : ℝ) / (2 * c))
      (by positivity) hlog_prefactor
    have hScard : S.card ≤ 3 * k :=
      AppliedModelingLib.Math.LinearCompressedSensing.mem_supportFinsetsCardLe.mp hS
    have hpow_nat : 9 ^ S.card ≤ 9 ^ (3 * k) :=
      Nat.pow_le_pow_right (by norm_num) hScard
    have hpow : ((9 ^ S.card : ℕ) : ℝ) ≤ ((9 ^ (3 * k) : ℕ) : ℝ) := by
      exact_mod_cast hpow_nat
    calc
      AppliedModelingLib.measureProb
          (AppliedModelingLib.Probability.RademacherMatrix.rowsMeasure (Fin m) (Fin d))
          (fun omega =>
            ¬ RestrictedIsometryOnSupport
              (AppliedModelingLib.Probability.RademacherMatrix.scaledMatrix
                (Feature := Fin m) (Coord := Fin d) omega) S (3 / 8 : ℝ)) ≤
          2 * ((9 ^ S.card : ℕ) : ℝ) * Real.exp (-(d : ℝ) / 524288) := by
            simpa [Fintype.card_fin,
              RestrictedIsometryOnSupport] using htail
      _ ≤ 2 * ((9 ^ (3 * k) : ℕ) : ℝ) * Real.exp (-(d : ℝ) / 524288) := by
            gcongr
      _ = 2 * ((9 ^ (3 * k) : ℕ) : ℝ) * Real.exp (-(d : ℝ) / c) := by
            dsimp [c]
      _ ≤ Real.exp (-((d : ℝ) / c - (d : ℝ) / (2 * c))) := by
            simpa only [neg_div] using habsorb
      _ = Real.exp (-(B * (d : ℝ))) := by
            dsimp [B]
            congr 1
            field_simp
            ring


theorem exists_basisPursuitExactRecovery_dimension_bigO :
    rademacher_compressed_sensing_boundary :=
  rademacher_compressed_sensing_boundary_of_fixed_support_rows_failure
    rademacher_fixed_support_rows
end RademacherMatrix
end Probability
end AppliedModelingLib
