import AppliedModelingLib.Alignment.Welfare.Borda
import AppliedModelingLib.Foundations.Optimization.UniformArgmaxStability
import AppliedModelingLib.Foundations.Probability.FiniteKLOptimization
import AppliedModelingLib.Foundations.Probability.FiniteIidUniformLaw
import AppliedModelingLib.Foundations.Probability.FiniteIidStrongLaw
import AppliedModelingLib.Foundations.Probability.Weighted
import AppliedModelingLib.Learning.HumanFeedback.BradleyTerryFit
import AppliedModelingLib.Learning.HumanFeedback.BradleyTerryFitExistence
import AppliedModelingLib.Learning.HumanFeedback.PairwiseReportCounts
import AppliedModelingLib.Learning.HumanFeedback.PairwiseReportFiniteConsistency
import GolzHaghtalabYang2025Distortion.Theorem5FiniteSample
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Theorem 6: RLHF distortion lower-bound construction

Appendix F.2 uses two utility types and `m - 2` identical type-`c`
alternatives.  This module begins with the literal finite construction before
the Borda/MLE and KL-policy arguments are composed.  The candidate sampling
law remains uniform, as in the source; it is not conflated with the reference
policy used later in the proof.
-/

namespace GolzHaghtalabYang2025Distortion

open scoped Topology

open AppliedModelingLib
open AppliedModelingLib.Alignment.Welfare
open AppliedModelingLib.Learning.HumanFeedback
open AppliedModelingLib.Learning.HumanFeedback.PairwiseCountDataset

/-- The type-I population mass `δ = 10 / (10 + exp β)` from Appendix F.2. -/
noncomputable def theorem6MinorityMass (beta : ℝ) : ℝ :=
  10 / (10 + Real.exp beta)

/-- The source alternatives `a`, `b`, and the `copies` type-`c` alternatives. -/
abbrev theorem6Alternative (copies : ℕ) : Type := Fin 2 ⊕ Fin copies

/-- Source alternative `a`. -/
abbrev theorem6A {copies : ℕ} : theorem6Alternative copies := Sum.inl 0

/-- Source alternative `b`. -/
abbrev theorem6B {copies : ℕ} : theorem6Alternative copies := Sum.inl 1

/-- The `index`th type-`c` alternative. -/
abbrev theorem6C {copies : ℕ} (index : Fin copies) : theorem6Alternative copies :=
  Sum.inr index

/-- The two distinguished alternatives as a finite index type for iid Borda analysis. -/
def theorem6ABCandidate {copies : ℕ} : Fin 2 → theorem6Alternative copies
  | 0 => theorem6A
  | 1 => theorem6B

/-- The two source population weights, in type-I/type-II order. -/
noncomputable def theorem6TypeWeight (beta : ℝ) : Fin 2 → ℝ
  | 0 => theorem6MinorityMass beta
  | 1 => 1 - theorem6MinorityMass beta

/-- The two utility vectors printed in Appendix F.2. -/
noncomputable def theorem6Utility (beta : ℝ) {copies : ℕ} :
    FiniteUtilityProfile (Fin 2) (theorem6Alternative copies)
  | 0, Sum.inl 0 => 0
  | 0, Sum.inl 1 => 1
  | 0, Sum.inr _ => 0
  | 1, Sum.inl 0 => 1 / beta
  | 1, Sum.inl 1 => 0
  | 1, Sum.inr _ => 1

/-- Appendix F.2's reference-policy weight vector: `a` and `b` split the
non-clone mass and the type-`c` alternatives split the clone mass. -/
noncomputable def theorem6ReferenceWeight (epsilon : ℝ) {copies : ℕ} :
    theorem6Alternative copies → ℝ
  | Sum.inl _ => (1 - epsilon) / 2
  | Sum.inr _ => epsilon / (copies : ℝ)

/-- The displayed reference weights sum to one when the clone class is nonempty. -/
theorem theorem6ReferenceWeight_sum_one
    {epsilon : ℝ} {copies : ℕ} (hcopies_pos : 0 < copies) :
    (∑ alternative : theorem6Alternative copies,
      theorem6ReferenceWeight epsilon alternative) = 1 := by
  have hcopies_ne : (copies : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hcopies_pos
  rw [Fintype.sum_sum_type]
  simp only [theorem6ReferenceWeight, Fin.sum_univ_two]
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  field_simp [hcopies_ne]
  ring

/-- The literal reference policy used in the KL-ball portion of Appendix F.2. -/
noncomputable def theorem6Reference
    (epsilon : ℝ) {copies : ℕ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (hcopies_pos : 0 < copies) : PMF (theorem6Alternative copies) :=
  finiteWeightedPMF (theorem6ReferenceWeight epsilon)
    (by
      intro alternative
      rcases alternative with alternative | copy
      · exact div_nonneg (sub_nonneg.mpr hepsilon_lt_one.le) (by norm_num)
      · exact div_nonneg hepsilon_pos.le (by positivity))
    (by
      rw [theorem6ReferenceWeight_sum_one hcopies_pos]
      norm_num)

/-- The source reference PMF has full support. -/
theorem theorem6Reference_fullSupport
    {epsilon : ℝ} {copies : ℕ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (hcopies_pos : 0 < copies) :
    PMFFullSupport (theorem6Reference epsilon hepsilon_pos hepsilon_lt_one hcopies_pos) := by
  intro alternative
  unfold theorem6Reference
  rw [finiteWeightedPMF_apply_toReal]
  rw [theorem6ReferenceWeight_sum_one hcopies_pos, div_one]
  rcases alternative with alternative | copy
  · exact div_pos (sub_pos.mpr hepsilon_lt_one) (by norm_num)
  · exact div_pos hepsilon_pos (by positivity)

/-- Each type-`c` alternative receives exactly its stated reference mass. -/
theorem theorem6Reference_c_toReal
    {epsilon : ℝ} {copies : ℕ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (hcopies_pos : 0 < copies) (copy : Fin copies) :
    (theorem6Reference epsilon hepsilon_pos hepsilon_lt_one hcopies_pos
      (theorem6C copy)).toReal = epsilon / (copies : ℝ) := by
  unfold theorem6Reference
  rw [finiteWeightedPMF_apply_toReal]
  rw [theorem6ReferenceWeight_sum_one hcopies_pos, div_one]
  rfl

/-- Each distinguished alternative has the displayed non-clone reference mass. -/
theorem theorem6Reference_ab_toReal
    {epsilon : ℝ} {copies : ℕ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (hcopies_pos : 0 < copies) (alternative : Fin 2) :
    (theorem6Reference epsilon hepsilon_pos hepsilon_lt_one hcopies_pos
      (Sum.inl alternative)).toReal = (1 - epsilon) / 2 := by
  unfold theorem6Reference
  rw [finiteWeightedPMF_apply_toReal]
  rw [theorem6ReferenceWeight_sum_one hcopies_pos, div_one]
  rfl

/-- The KL divergence of pure `b` against the literal reference policy. -/
theorem theorem6_pureB_KL
    {epsilon : ℝ} {copies : ℕ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (hcopies_pos : 0 < copies) :
    finiteKLDivergence (PMF.pure (theorem6B : theorem6Alternative copies))
      (theorem6Reference epsilon hepsilon_pos hepsilon_lt_one hcopies_pos) =
      Real.log (2 / (1 - epsilon)) := by
  rw [finiteKLDivergence_pure,
    theorem6Reference_ab_toReal hepsilon_pos hepsilon_lt_one hcopies_pos (1 : Fin 2)]
  have hnonzero : (1 - epsilon) / 2 ≠ 0 := by
    exact div_ne_zero (ne_of_gt (sub_pos.mpr hepsilon_lt_one)) (by norm_num)
  rw [← Real.log_inv]
  congr 1
  field_simp [hnonzero]

/-- A transparent numerical condition under which pure `b` is in the source
unit KL ball. -/
theorem theorem6_pureB_KL_feasible_of_log_bound
    {epsilon : ℝ} {copies : ℕ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (hcopies_pos : 0 < copies)
    (hlog : Real.log (2 / (1 - epsilon)) ≤ 1) :
    finiteKLDivergence (PMF.pure (theorem6B : theorem6Alternative copies))
      (theorem6Reference epsilon hepsilon_pos hepsilon_lt_one hcopies_pos) ≤ 1 := by
  rw [theorem6_pureB_KL hepsilon_pos hepsilon_lt_one hcopies_pos]
  exact hlog

/-- Pure `a` has the same KL divergence as pure `b` under the symmetric
reference policy. -/
theorem theorem6_pureA_KL
    {epsilon : ℝ} {copies : ℕ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (hcopies_pos : 0 < copies) :
    finiteKLDivergence (PMF.pure (theorem6A : theorem6Alternative copies))
      (theorem6Reference epsilon hepsilon_pos hepsilon_lt_one hcopies_pos) =
      Real.log (2 / (1 - epsilon)) := by
  rw [finiteKLDivergence_pure,
    theorem6Reference_ab_toReal hepsilon_pos hepsilon_lt_one hcopies_pos (0 : Fin 2)]
  have hnonzero : (1 - epsilon) / 2 ≠ 0 := by
    exact div_ne_zero (ne_of_gt (sub_pos.mpr hepsilon_lt_one)) (by norm_num)
  rw [← Real.log_inv]
  congr 1
  field_simp [hnonzero]

/-- The same explicit numerical condition places pure `a` in the unit KL ball. -/
theorem theorem6_pureA_KL_feasible_of_log_bound
    {epsilon : ℝ} {copies : ℕ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (hcopies_pos : 0 < copies)
    (hlog : Real.log (2 / (1 - epsilon)) ≤ 1) :
    finiteKLDivergence (PMF.pure (theorem6A : theorem6Alternative copies))
      (theorem6Reference epsilon hepsilon_pos hepsilon_lt_one hcopies_pos) ≤ 1 := by
  rw [theorem6_pureA_KL hepsilon_pos hepsilon_lt_one hcopies_pos]
  exact hlog

/--
The reusable clone-class KL estimate specialized to the Appendix F.2
reference policy.  Thus every policy in a unit KL ball has clone mass at most
`2 / log (1 / epsilon)` whenever that logarithm is positive; the elementary
rearrangement is left explicit for the policy-specific step below.
-/
theorem theorem6_KL_cloneMass_lower
    {epsilon : ℝ} {copies : ℕ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (hcopies_pos : 0 < copies)
    (policy : PMF (theorem6Alternative copies)) :
    (∑ copy : Fin copies, (policy (theorem6C copy)).toReal) * Real.log epsilon⁻¹ - 1 ≤
      finiteKLDivergence policy
        (theorem6Reference epsilon hepsilon_pos hepsilon_lt_one hcopies_pos) := by
  letI : Nonempty (Fin copies) := ⟨⟨0, hcopies_pos⟩⟩
  simpa only [theorem6C] using
    (finiteKLDivergence_right_uniform_mass_lower
      (Left := Fin 2) (Right := Fin copies)
      policy (theorem6Reference epsilon hepsilon_pos hepsilon_lt_one hcopies_pos) epsilon
      hepsilon_pos
      (theorem6Reference_fullSupport hepsilon_pos hepsilon_lt_one hcopies_pos)
      (by
        intro copy
        simpa only [Fintype.card_fin] using
          (theorem6Reference_c_toReal hepsilon_pos hepsilon_lt_one hcopies_pos copy)))

/-- A unit KL-ball policy places at most `2 / log (1 / epsilon)` mass on the
clone class, exactly as required by the source's small-reference-mass step. -/
theorem theorem6_KL_cloneMass_le_two_div_log
    {epsilon : ℝ} {copies : ℕ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (hlog_pos : 0 < Real.log epsilon⁻¹) (hcopies_pos : 0 < copies)
    (policy : PMF (theorem6Alternative copies))
    (hfeasible : finiteKLDivergence policy
      (theorem6Reference epsilon hepsilon_pos hepsilon_lt_one hcopies_pos) ≤ 1) :
    (∑ copy : Fin copies, (policy (theorem6C copy)).toReal) ≤
      2 / Real.log epsilon⁻¹ := by
  have hlower := theorem6_KL_cloneMass_lower
    hepsilon_pos hepsilon_lt_one hcopies_pos policy
  apply (le_div_iff₀ hlog_pos).mpr
  linarith

/-- Total policy mass assigned to the type-`c` clone class. -/
noncomputable def theorem6CloneMass {copies : ℕ}
    (policy : PMF (theorem6Alternative copies)) : ℝ :=
  ∑ copy : Fin copies, (policy (theorem6C copy)).toReal

/-- The two named alternatives and the clone class exhaust policy mass. -/
theorem theorem6_policyMass_decomposition {copies : ℕ}
    (policy : PMF (theorem6Alternative copies)) :
    (policy (theorem6A : theorem6Alternative copies)).toReal +
      (policy (theorem6B : theorem6Alternative copies)).toReal +
      theorem6CloneMass policy = 1 := by
  unfold theorem6CloneMass
  have hsum := pmfToRealSum policy
  rw [Fintype.sum_sum_type, Fin.sum_univ_two] at hsum
  simpa only [theorem6A, theorem6B, theorem6C] using hsum

/-- Exact decomposition of any policy's finite expected score. -/
theorem theorem6_policyScore_decomposition {copies : ℕ}
    (policy : PMF (theorem6Alternative copies))
    (score : theorem6Alternative copies → ℝ) :
    pmfExp policy score =
      (policy (theorem6A : theorem6Alternative copies)).toReal * score theorem6A +
        (policy (theorem6B : theorem6Alternative copies)).toReal * score theorem6B +
          ∑ copy : Fin copies, (policy (theorem6C copy)).toReal * score (theorem6C copy) := by
  unfold pmfExp
  rw [Fintype.sum_sum_type, Fin.sum_univ_two]

/-- A reward normalized to zero on every clone has policy score supported only
on `a` and `b`. -/
theorem theorem6_policyScore_eq_of_clone_zero {copies : ℕ}
    (policy : PMF (theorem6Alternative copies))
    (reward : theorem6Alternative copies → ℝ)
    (hclone_zero : ∀ copy : Fin copies, reward (theorem6C copy) = 0) :
    pmfExp policy reward =
      (policy (theorem6A : theorem6Alternative copies)).toReal * reward theorem6A +
        (policy (theorem6B : theorem6Alternative copies)).toReal * reward theorem6B := by
  rw [theorem6_policyScore_decomposition]
  have hclone_sum :
      (∑ copy : Fin copies, (policy (theorem6C copy)).toReal * reward (theorem6C copy)) = 0 := by
    refine Finset.sum_eq_zero fun copy _ => ?_
    rw [hclone_zero copy]
    ring
  rw [hclone_sum]
  dsimp only [theorem6A, theorem6B]
  ring

/--
The welfare-maximizer calculation in the second bullet of Appendix F.2.  A
feasible score maximizer for a bounded welfare score cannot put much mass on
`b` once clone mass is controlled and pure `a` is feasible.
-/
theorem theorem6_scoreMax_bMass_le_of_cloneMass
    {copies : ℕ} (reference policy : PMF (theorem6Alternative copies))
    (welfare : theorem6Alternative copies → ℝ) (eta : ℝ)
    (hwelfare_a_nonneg : 0 ≤ welfare theorem6A)
    (hwelfare_b_lt_a : welfare theorem6B < welfare theorem6A)
    (hclone_welfare_le_one : ∀ copy : Fin copies, welfare (theorem6C copy) ≤ 1)
    (hclone_mass : theorem6CloneMass policy ≤ eta)
    (hmax : ∀ other : PMF (theorem6Alternative copies),
      finiteKLDivergence other reference ≤ 1 → pmfExp other welfare ≤ pmfExp policy welfare)
    (hpure_a_feasible : finiteKLDivergence
      (PMF.pure (theorem6A : theorem6Alternative copies)) reference ≤ 1) :
    (policy (theorem6B : theorem6Alternative copies)).toReal ≤
      eta / (welfare theorem6A - welfare theorem6B) := by
  have hscore_lower : welfare theorem6A ≤ pmfExp policy welfare := by
    have h := hmax (PMF.pure theorem6A) hpure_a_feasible
    simpa using h
  have hscore_eq := theorem6_policyScore_decomposition policy welfare
  have hmass := theorem6_policyMass_decomposition policy
  have hclone_nonneg : 0 ≤ theorem6CloneMass policy := by
    unfold theorem6CloneMass
    exact Finset.sum_nonneg fun copy _ => ENNReal.toReal_nonneg
  have hpolicy_a_le : (policy theorem6A).toReal ≤ 1 - (policy theorem6B).toReal := by
    linarith
  have hclone_score_le :
      (∑ copy : Fin copies, (policy (theorem6C copy)).toReal * welfare (theorem6C copy)) ≤
        theorem6CloneMass policy := by
    unfold theorem6CloneMass
    refine Finset.sum_le_sum fun copy _ => ?_
    calc
      (policy (theorem6C copy)).toReal * welfare (theorem6C copy) ≤
          (policy (theorem6C copy)).toReal * 1 :=
            mul_le_mul_of_nonneg_left (hclone_welfare_le_one copy) ENNReal.toReal_nonneg
      _ = (policy (theorem6C copy)).toReal := by ring
  have hscore_upper : pmfExp policy welfare ≤
      welfare theorem6A +
        (policy theorem6B).toReal * (welfare theorem6B - welfare theorem6A) + eta := by
    rw [hscore_eq]
    have hfirst := mul_le_mul_of_nonneg_right hpolicy_a_le hwelfare_a_nonneg
    linarith
  have hgap_pos : 0 < welfare theorem6A - welfare theorem6B := by linarith
  apply (le_div_iff₀ hgap_pos).mpr
  linarith

/-- The second policy conclusion in Appendix F.2, with the welfare-maximizer
and pure-`a` feasibility conditions made explicit. -/
theorem theorem6_constrainedWelfareMax_bMass_bound
    {epsilon : ℝ} {copies : ℕ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (hlog_clone_pos : 0 < Real.log epsilon⁻¹) (hcopies_pos : 0 < copies)
    (hlog_pure_a : Real.log (2 / (1 - epsilon)) ≤ 1)
    (welfare : theorem6Alternative copies → ℝ)
    (hwelfare_a_nonneg : 0 ≤ welfare theorem6A)
    (hwelfare_b_lt_a : welfare theorem6B < welfare theorem6A)
    (hclone_welfare_le_one : ∀ copy : Fin copies, welfare (theorem6C copy) ≤ 1)
    (policy : PMF (theorem6Alternative copies))
    (hpolicy_feasible : finiteKLDivergence policy
      (theorem6Reference epsilon hepsilon_pos hepsilon_lt_one hcopies_pos) ≤ 1)
    (hmax : ∀ other : PMF (theorem6Alternative copies),
      finiteKLDivergence other
        (theorem6Reference epsilon hepsilon_pos hepsilon_lt_one hcopies_pos) ≤ 1 →
      pmfExp other welfare ≤ pmfExp policy welfare) :
    (policy (theorem6B : theorem6Alternative copies)).toReal ≤
      (2 / Real.log epsilon⁻¹) / (welfare theorem6A - welfare theorem6B) := by
  have hclone_mass := theorem6_KL_cloneMass_le_two_div_log
    hepsilon_pos hepsilon_lt_one hlog_clone_pos hcopies_pos policy hpolicy_feasible
  have hpure_a := theorem6_pureA_KL_feasible_of_log_bound
    hepsilon_pos hepsilon_lt_one hcopies_pos hlog_pure_a
  exact theorem6_scoreMax_bMass_le_of_cloneMass
    (theorem6Reference epsilon hepsilon_pos hepsilon_lt_one hcopies_pos)
    policy welfare (2 / Real.log epsilon⁻¹)
    hwelfare_a_nonneg hwelfare_b_lt_a hclone_welfare_le_one hclone_mass hmax hpure_a

/--
The elementary constrained-score calculation in Appendix F.2.  If a policy
maximizes an estimated reward over a KL-feasible set containing pure `b`, and
clone mass is at most `eta`, then its mass on the lower-reward alternative `a`
is bounded by the displayed reward-gap ratio.  The maximizer and pure-`b`
feasibility hypotheses remain explicit rather than being encoded as a
certificate.
-/
theorem theorem6_scoreMax_aMass_le_of_cloneMass
    {copies : ℕ} (reference policy : PMF (theorem6Alternative copies))
    (reward : theorem6Alternative copies → ℝ) (eta : ℝ)
    (hreward_ab : reward theorem6A < reward theorem6B)
    (hreward_b_neg : reward theorem6B < 0)
    (hclone_zero : ∀ copy : Fin copies, reward (theorem6C copy) = 0)
    (hclone_mass : theorem6CloneMass policy ≤ eta)
    (hmax : ∀ other : PMF (theorem6Alternative copies),
      finiteKLDivergence other reference ≤ 1 → pmfExp other reward ≤ pmfExp policy reward)
    (hpure_b_feasible : finiteKLDivergence
      (PMF.pure (theorem6B : theorem6Alternative copies)) reference ≤ 1) :
    (policy (theorem6A : theorem6Alternative copies)).toReal ≤
      eta * (-reward theorem6B) / (reward theorem6B - reward theorem6A) := by
  have hscore_lower : reward theorem6B ≤ pmfExp policy reward := by
    have h := hmax (PMF.pure theorem6B) hpure_b_feasible
    simpa using h
  have hscore_eq := theorem6_policyScore_eq_of_clone_zero policy reward hclone_zero
  have hmass := theorem6_policyMass_decomposition policy
  have hpolicy_b_lower : 1 - (policy theorem6A).toReal - eta ≤
      (policy theorem6B).toReal := by
    linarith
  have hscore_upper : pmfExp policy reward ≤
      (policy theorem6A).toReal * reward theorem6A +
        (1 - (policy theorem6A).toReal - eta) * reward theorem6B := by
    rw [hscore_eq]
    have hmul := mul_le_mul_of_nonpos_right hpolicy_b_lower hreward_b_neg.le
    linarith
  have hgap_pos : 0 < reward theorem6B - reward theorem6A := by linarith
  apply (le_div_iff₀ hgap_pos).mpr
  linarith

/-- A finite-MLE version of the first Appendix-F.2 policy calculation.  Exact
clone-score equality is not needed: after the fixed-reference normalization
sets the `a` score to zero, a common upper bound on clone scores and a positive
`b` margin control the mass that a reward-maximizing policy can retain on
`a`.  This is the stability form needed for literal finite report samples. -/
theorem theorem6_scoreMax_aMass_le_of_zero_a_bGap_cloneUpper
    {copies : ℕ} (reference policy : PMF (theorem6Alternative copies))
    (reward : theorem6Alternative copies → ℝ) (eta cloneUpper gap : ℝ)
    (hreward_a_zero : reward theorem6A = 0)
    (hgap_pos : 0 < gap) (hgap : gap ≤ reward theorem6B)
    (hclone_upper_nonneg : 0 ≤ cloneUpper)
    (hclone_upper : ∀ copy : Fin copies, reward (theorem6C copy) ≤ cloneUpper)
    (hclone_mass : theorem6CloneMass policy ≤ eta)
    (hmax : ∀ other : PMF (theorem6Alternative copies),
      finiteKLDivergence other reference ≤ 1 → pmfExp other reward ≤ pmfExp policy reward)
    (hpure_b_feasible : finiteKLDivergence
      (PMF.pure (theorem6B : theorem6Alternative copies)) reference ≤ 1) :
    (policy (theorem6A : theorem6Alternative copies)).toReal ≤ eta * cloneUpper / gap := by
  have hscore_lower : reward theorem6B ≤ pmfExp policy reward := by
    have h := hmax (PMF.pure theorem6B) hpure_b_feasible
    simpa using h
  have hmass := theorem6_policyMass_decomposition policy
  have hclone_nonneg : 0 ≤ theorem6CloneMass policy := by
    unfold theorem6CloneMass
    exact Finset.sum_nonneg fun copy _ => ENNReal.toReal_nonneg
  have hclone_score_le :
      (∑ copy : Fin copies, (policy (theorem6C copy)).toReal *
        reward (theorem6C copy)) ≤ theorem6CloneMass policy * cloneUpper := by
    calc
      (∑ copy : Fin copies, (policy (theorem6C copy)).toReal *
          reward (theorem6C copy)) ≤
        ∑ copy : Fin copies, (policy (theorem6C copy)).toReal * cloneUpper :=
          Finset.sum_le_sum fun copy _ =>
            mul_le_mul_of_nonneg_left (hclone_upper copy) ENNReal.toReal_nonneg
      _ = theorem6CloneMass policy * cloneUpper := by
        unfold theorem6CloneMass
        rw [Finset.sum_mul]
  have hclone_score_le_eta :
      (∑ copy : Fin copies, (policy (theorem6C copy)).toReal *
        reward (theorem6C copy)) ≤ eta * cloneUpper := by
    calc
      (∑ copy : Fin copies, (policy (theorem6C copy)).toReal *
          reward (theorem6C copy)) ≤ theorem6CloneMass policy * cloneUpper := hclone_score_le
      _ ≤ eta * cloneUpper :=
        mul_le_mul_of_nonneg_right hclone_mass hclone_upper_nonneg
  have hscore_upper : pmfExp policy reward ≤
      (1 - (policy theorem6A).toReal - theorem6CloneMass policy) * reward theorem6B +
        eta * cloneUpper := by
    rw [theorem6_policyScore_decomposition]
    rw [hreward_a_zero]
    have hpolicy_b : (policy theorem6B).toReal =
        1 - (policy theorem6A).toReal - theorem6CloneMass policy := by
      linarith
    rw [hpolicy_b]
    linarith
  have hreward_b_pos : 0 < reward theorem6B := hgap_pos.trans_le hgap
  have ha_nonneg : 0 ≤ (policy theorem6A).toReal := ENNReal.toReal_nonneg
  have hgap_mul : (policy theorem6A).toReal * gap ≤
      (policy theorem6A).toReal * reward theorem6B :=
    mul_le_mul_of_nonneg_left hgap ha_nonneg
  have hmain : (policy theorem6A).toReal * reward theorem6B ≤ eta * cloneUpper := by
    nlinarith
  apply (le_div_iff₀ hgap_pos).mpr
  exact hgap_mul.trans hmain

/--
The first policy conclusion in Appendix F.2, with every optimization premise
spelled out: a unit-KL feasible score maximizer with the shifted MLE order
puts little mass on `a`.  The source's choice of a sufficiently small
reference clone mass can be supplied through the two explicit logarithmic
premises.
-/
theorem theorem6_constrainedScoreMax_aMass_bound
    {epsilon : ℝ} {copies : ℕ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (hlog_clone_pos : 0 < Real.log epsilon⁻¹) (hcopies_pos : 0 < copies)
    (hlog_pure_b : Real.log (2 / (1 - epsilon)) ≤ 1)
    (reward : theorem6Alternative copies → ℝ)
    (hreward_ab : reward theorem6A < reward theorem6B)
    (hreward_b_neg : reward theorem6B < 0)
    (hclone_zero : ∀ copy : Fin copies, reward (theorem6C copy) = 0)
    (policy : PMF (theorem6Alternative copies))
    (hpolicy_feasible : finiteKLDivergence policy
      (theorem6Reference epsilon hepsilon_pos hepsilon_lt_one hcopies_pos) ≤ 1)
    (hmax : ∀ other : PMF (theorem6Alternative copies),
      finiteKLDivergence other
        (theorem6Reference epsilon hepsilon_pos hepsilon_lt_one hcopies_pos) ≤ 1 →
      pmfExp other reward ≤ pmfExp policy reward) :
    (policy (theorem6A : theorem6Alternative copies)).toReal ≤
      (2 / Real.log epsilon⁻¹) * (-reward theorem6B) /
        (reward theorem6B - reward theorem6A) := by
  have hclone_mass := theorem6_KL_cloneMass_le_two_div_log
    hepsilon_pos hepsilon_lt_one hlog_clone_pos hcopies_pos policy hpolicy_feasible
  have hpure_b := theorem6_pureB_KL_feasible_of_log_bound
    hepsilon_pos hepsilon_lt_one hcopies_pos hlog_pure_b
  exact theorem6_scoreMax_aMass_le_of_cloneMass
    (theorem6Reference epsilon hepsilon_pos hepsilon_lt_one hcopies_pos)
    policy reward (2 / Real.log epsilon⁻¹) hreward_ab hreward_b_neg hclone_zero
    hclone_mass hmax hpure_b

/-- The source mass is strictly positive. -/
theorem theorem6MinorityMass_pos (beta : ℝ) : 0 < theorem6MinorityMass beta := by
  unfold theorem6MinorityMass
  exact div_pos (by norm_num) (by positivity)

/-- The source mass is at most one. -/
theorem theorem6MinorityMass_le_one (beta : ℝ) : theorem6MinorityMass beta ≤ 1 := by
  have hden : 0 < 10 + Real.exp beta := by positivity
  have hlt : theorem6MinorityMass beta < 1 := by
    unfold theorem6MinorityMass
    rw [div_lt_one hden]
    linarith [Real.exp_pos beta]
  exact hlt.le

/-- The two displayed source masses sum to one. -/
theorem theorem6TypeWeight_sum_one (beta : ℝ) :
    (∑ user : Fin 2, theorem6TypeWeight beta user) = 1 := by
  simp [Fin.sum_univ_succ, theorem6TypeWeight]

/-- The literal two-type population from Appendix F.2. -/
noncomputable def theorem6Population (beta : ℝ) : PMF (Fin 2) :=
  finiteWeightedPMF (theorem6TypeWeight beta)
    (by
      intro user
      fin_cases user
      · exact (theorem6MinorityMass_pos beta).le
      · exact sub_nonneg.mpr (theorem6MinorityMass_le_one beta))
    (by
      rw [theorem6TypeWeight_sum_one]
      norm_num)

/-- The source population comparison model, with its one-point context universe fixed. -/
noncomputable def theorem6Preference (beta : ℝ) {copies : ℕ} :
    PairwisePreference PUnit.{1} (theorem6Alternative copies) :=
  populationBradleyTerryPreference (theorem6Population beta)
    (theorem6Utility beta (copies := copies)) beta

/-- The literal population Bradley--Terry comparison model has strictly
positive probability on every ordered pair, including the diagonal. -/
theorem theorem6Preference_prob_pos
    (beta : ℝ) {copies : ℕ} (first second : theorem6Alternative copies) :
    0 < (theorem6Preference beta).prob PUnit.unit.{1} first second := by
  change 0 < (populationBradleyTerryPreference (theorem6Population beta)
    (theorem6Utility beta) beta).prob PUnit.unit.{1} first second
  exact populationBradleyTerryPreference_prob_pos (theorem6Population beta)
    (theorem6Utility beta) beta first second

/-- The uniformly sampled literal construction has an attained population
Bradley--Terry MLE.  This discharges the compactness/existence premise that is
implicit in the source's population argument. -/
theorem theorem6_exists_populationMLE
    (beta : ℝ) {copies : ℕ} :
    ∃ reward : theorem6Alternative copies → ℝ, ∀ candidate,
      bradleyTerryFitObjective (theorem6Preference beta)
        (uniformPMF (theorem6Alternative copies)) candidate ≤
      bradleyTerryFitObjective (theorem6Preference beta)
        (uniformPMF (theorem6Alternative copies)) reward := by
  apply exists_bradleyTerryFit_globalMax
  · intro alternative
    exact uniformPMF_apply_toReal_pos alternative
  · intro first second _
    exact theorem6Preference_prob_pos beta first second

/-- The type mass stored in the finite PMF is its literal real weight. -/
@[simp] theorem theorem6Population_toReal
    (beta : ℝ) (user : Fin 2) :
    (theorem6Population beta user).toReal = theorem6TypeWeight beta user := by
  unfold theorem6Population
  rw [finiteWeightedPMF_apply_toReal]
  rw [theorem6TypeWeight_sum_one]
  ring

/-- Expectation under the source population is the displayed two-type mixture. -/
theorem theorem6Population_pmfExp (beta : ℝ) (f : Fin 2 → ℝ) :
    pmfExp (theorem6Population beta) f =
      theorem6MinorityMass beta * f 0 +
        (1 - theorem6MinorityMass beta) * f 1 := by
  unfold pmfExp
  rw [show
    (∑ user : Fin 2, (theorem6Population beta user).toReal * f user) =
      (theorem6Population beta (0 : Fin 2)).toReal * f 0 +
        (theorem6Population beta (1 : Fin 2)).toReal * f 1 by
      simp [Fin.sum_univ_succ]]
  simp [theorem6TypeWeight]

/-- For the source range `β ≥ 1`, both printed utility vectors lie in `[0,1]`. -/
theorem theorem6Utility_unitInterval
    {beta : ℝ} {copies : ℕ} (hbeta : 1 ≤ beta) :
    UnitIntervalUtilityProfile (theorem6Utility beta (copies := copies)) := by
  have hbeta_pos : 0 < beta := lt_of_lt_of_le zero_lt_one hbeta
  intro user alternative
  fin_cases user
  · rcases alternative with alternative | copy
    · fin_cases alternative <;> norm_num [theorem6Utility]
    · norm_num [theorem6Utility]
  · rcases alternative with alternative | copy
    · fin_cases alternative
      · change 0 ≤ 1 / beta ∧ 1 / beta ≤ 1
        constructor
        · exact div_nonneg zero_le_one hbeta_pos.le
        · simpa using one_div_le_one_div_of_le zero_lt_one hbeta
      · norm_num [theorem6Utility]
    · norm_num [theorem6Utility]

/-- Population-average utility, the welfare objective used in Appendix F.2's
second constrained-policy calculation. -/
noncomputable def theorem6Welfare (beta : ℝ) {copies : ℕ} :
    theorem6Alternative copies → ℝ :=
  populationAverageUtility (theorem6Population beta) (theorem6Utility beta)

/-- Exact source average welfare of alternative `a`. -/
theorem theorem6_populationAverageUtility_a
    {beta : ℝ} {copies : ℕ} :
    populationAverageUtility (theorem6Population beta)
      (theorem6Utility beta) (theorem6A : theorem6Alternative copies) =
      (1 - theorem6MinorityMass beta) / beta := by
  unfold populationAverageUtility
  rw [theorem6Population_pmfExp]
  simp only [theorem6Utility]
  ring

/-- Exact source average welfare of alternative `b`. -/
theorem theorem6_populationAverageUtility_b
    {beta : ℝ} {copies : ℕ} :
    populationAverageUtility (theorem6Population beta)
      (theorem6Utility beta) (theorem6B : theorem6Alternative copies) =
      theorem6MinorityMass beta := by
  unfold populationAverageUtility
  rw [theorem6Population_pmfExp]
  simp only [theorem6Utility]
  ring

/-- At `beta ≥ 10`, the elementary exponential growth estimate needed for the
literal welfare comparison is explicit. -/
theorem theorem6_ten_mul_beta_lt_exp {beta : ℝ} (hbeta : 10 ≤ beta) :
    10 * beta < Real.exp beta := by
  have hfactor : 0 < beta - 9 := by linarith
  have hshift : beta - 9 ≤ Real.exp (beta - 10) := by
    nlinarith [Real.add_one_le_exp (beta - 10)]
  have hexp_ten : (100 : ℝ) < Real.exp 10 := by
    calc
      (100 : ℝ) < 2 ^ (10 : ℕ) := by norm_num
      _ < Real.exp 1 ^ (10 : ℕ) :=
        pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num) (by norm_num)
      _ = Real.exp 10 := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hlinear : 10 * beta ≤ 100 * (beta - 9) := by linarith
  have hfirst : 100 * (beta - 9) < Real.exp 10 * (beta - 9) := by
    exact mul_lt_mul_of_pos_right hexp_ten hfactor
  have hsecond : Real.exp 10 * (beta - 9) ≤
      Real.exp 10 * Real.exp (beta - 10) := by
    exact mul_le_mul_of_nonneg_left hshift (Real.exp_pos _).le
  calc
    10 * beta ≤ 100 * (beta - 9) := hlinear
    _ < Real.exp 10 * (beta - 9) := hfirst
    _ ≤ Real.exp 10 * Real.exp (beta - 10) := hsecond
    _ = Real.exp beta := by
      rw [← Real.exp_add]
      congr 1 <;> ring

/-- The explicit asymptotic cutoff `β ≥ 10` already entails the auxiliary
`exp β ≥ 100` regime used by the finite construction.  It is therefore an
internal proof fact, not an additional source-facing premise. -/
theorem theorem6_log_hundred_le_ten : Real.log 100 ≤ (10 : ℝ) := by
  have hten : (100 : ℝ) < Real.exp (10 : ℝ) := by
    convert theorem6_ten_mul_beta_lt_exp (beta := (10 : ℝ)) (by norm_num) using 1 <;>
      norm_num
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 100)] at hten
  exact (Real.exp_le_exp.mp hten.le)

/-- For the literal source construction in the explicit large-`beta` regime,
alternative `a` has strictly greater population welfare than `b`. -/
theorem theorem6_populationAverageUtility_b_lt_a
    {beta : ℝ} {copies : ℕ} (hbeta : 10 ≤ beta) :
    populationAverageUtility (theorem6Population beta)
      (theorem6Utility beta) (theorem6B : theorem6Alternative copies) <
    populationAverageUtility (theorem6Population beta)
      (theorem6Utility beta) (theorem6A : theorem6Alternative copies) := by
  rw [theorem6_populationAverageUtility_b, theorem6_populationAverageUtility_a]
  have hbeta_pos : 0 < beta := by linarith
  apply (lt_div_iff₀ hbeta_pos).mpr
  unfold theorem6MinorityMass
  have hden : 0 < 10 + Real.exp beta := by positivity
  calc
    10 / (10 + Real.exp beta) * beta =
        (10 * beta) / (10 + Real.exp beta) := by ring
    _ < Real.exp beta / (10 + Real.exp beta) :=
      div_lt_div_of_pos_right (theorem6_ten_mul_beta_lt_exp hbeta) hden
    _ = 1 - 10 / (10 + Real.exp beta) := by
      field_simp
      ring

/-- Alternative `a` has nonnegative literal population welfare throughout the
unit-interval source regime. -/
theorem theorem6_populationAverageUtility_a_nonneg
    {beta : ℝ} {copies : ℕ} (hbeta : 1 ≤ beta) :
    0 ≤ populationAverageUtility (theorem6Population beta)
      (theorem6Utility beta) (theorem6A : theorem6Alternative copies) := by
  rw [theorem6_populationAverageUtility_a]
  exact div_nonneg (sub_nonneg.mpr (theorem6MinorityMass_le_one beta))
    (by linarith)

/-- Exact source average welfare of every clone alternative. -/
theorem theorem6_populationAverageUtility_c
    {beta : ℝ} {copies : ℕ} (copy : Fin copies) :
    populationAverageUtility (theorem6Population beta)
      (theorem6Utility beta) (theorem6C copy) =
      1 - theorem6MinorityMass beta := by
  unfold populationAverageUtility
  rw [theorem6Population_pmfExp]
  simp only [theorem6Utility]
  ring

/-- Every clone has literal population welfare at most one. -/
theorem theorem6_populationAverageUtility_c_le_one
    {beta : ℝ} {copies : ℕ} (copy : Fin copies) :
    populationAverageUtility (theorem6Population beta)
      (theorem6Utility beta) (theorem6C copy) ≤ 1 := by
  rw [theorem6_populationAverageUtility_c]
  linarith [theorem6MinorityMass_pos beta]

/-- The generic KL-ball welfare calculation specializes to the literal
population welfare of Appendix F.2.  Thus, whenever the displayed policy is
an attained feasible welfare maximizer, its mass on `b` obeys the source's
clone-mass-controlled bound. -/
theorem theorem6_constrainedLiteralWelfareMax_bMass_bound
    {epsilon beta : ℝ} {copies : ℕ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (hlog_clone_pos : 0 < Real.log epsilon⁻¹) (hcopies_pos : 0 < copies)
    (hlog_pure_a : Real.log (2 / (1 - epsilon)) ≤ 1)
    (hbeta : 10 ≤ beta)
    (policy : PMF (theorem6Alternative copies))
    (hpolicy_feasible : finiteKLDivergence policy
      (theorem6Reference epsilon hepsilon_pos hepsilon_lt_one hcopies_pos) ≤ 1)
    (hmax : ∀ other : PMF (theorem6Alternative copies),
      finiteKLDivergence other
        (theorem6Reference epsilon hepsilon_pos hepsilon_lt_one hcopies_pos) ≤ 1 →
      pmfExp other (theorem6Welfare beta) ≤ pmfExp policy (theorem6Welfare beta)) :
    (policy (theorem6B : theorem6Alternative copies)).toReal ≤
      (2 / Real.log epsilon⁻¹) /
        ((1 - theorem6MinorityMass beta) / beta - theorem6MinorityMass beta) := by
  have hbound := theorem6_constrainedWelfareMax_bMass_bound
    hepsilon_pos hepsilon_lt_one hlog_clone_pos hcopies_pos hlog_pure_a
    (theorem6Welfare beta)
    (by
      change 0 ≤ populationAverageUtility (theorem6Population beta)
        (theorem6Utility beta) (theorem6A : theorem6Alternative copies)
      exact theorem6_populationAverageUtility_a_nonneg (by linarith))
    (by
      change populationAverageUtility (theorem6Population beta)
          (theorem6Utility beta) (theorem6B : theorem6Alternative copies) <
        populationAverageUtility (theorem6Population beta)
          (theorem6Utility beta) (theorem6A : theorem6Alternative copies)
      exact theorem6_populationAverageUtility_b_lt_a hbeta)
    (by
      intro copy
      change populationAverageUtility (theorem6Population beta)
        (theorem6Utility beta) (theorem6C copy) ≤ 1
      exact theorem6_populationAverageUtility_c_le_one copy)
    policy hpolicy_feasible hmax
  change (policy (theorem6B : theorem6Alternative copies)).toReal ≤
    (2 / Real.log epsilon⁻¹) /
      (populationAverageUtility (theorem6Population beta)
        (theorem6Utility beta) (theorem6A : theorem6Alternative copies) -
        populationAverageUtility (theorem6Population beta)
          (theorem6Utility beta) (theorem6B : theorem6Alternative copies)) at hbound
  rw [theorem6_populationAverageUtility_a, theorem6_populationAverageUtility_b] at hbound
  exact hbound

/-- A concrete small reference mass.  For `0 < eta ≤ 1`, it makes the
KL clone-mass upper bound exactly `eta`, while preserving feasibility of the
two pure comparators used in Appendix F.2. -/
noncomputable def theorem6Epsilon (eta : ℝ) : ℝ := Real.exp (-2 / eta)

theorem theorem6Epsilon_pos (eta : ℝ) : 0 < theorem6Epsilon eta := by
  exact Real.exp_pos _

theorem theorem6Epsilon_lt_one {eta : ℝ} (heta : 0 < eta) :
    theorem6Epsilon eta < 1 := by
  unfold theorem6Epsilon
  rw [Real.exp_lt_one_iff]
  exact div_neg_of_neg_of_pos (by norm_num) heta

/-- The logarithm that controls clone mass has the exact chosen value. -/
theorem theorem6_log_invEpsilon {eta : ℝ} :
    Real.log (theorem6Epsilon eta)⁻¹ = 2 / eta := by
  unfold theorem6Epsilon
  rw [show -2 / eta = -(2 / eta) by ring, Real.exp_neg, inv_inv, Real.log_exp]

theorem theorem6_log_invEpsilon_pos {eta : ℝ} (heta : 0 < eta) :
    0 < Real.log (theorem6Epsilon eta)⁻¹ := by
  rw [theorem6_log_invEpsilon]
  positivity

/-- The selected reference mass makes the generic clone bound exactly `eta`. -/
theorem theorem6_two_div_log_invEpsilon {eta : ℝ} (heta : 0 < eta) :
    2 / Real.log (theorem6Epsilon eta)⁻¹ = eta := by
  rw [theorem6_log_invEpsilon]
  field_simp [ne_of_gt heta]

/-- A numerical estimate ensuring that the reference's two non-clone atoms
are sufficiently large for pure `a` and pure `b` to lie in the unit KL ball. -/
theorem theorem6_exp_neg_two_le_pureSlack :
    Real.exp (-2) ≤ 1 - 2 / Real.exp 1 := by
  have hlarge : 1 < Real.exp 1 * (Real.exp 1 - 2) := by
    nlinarith [Real.exp_one_gt_d9, sq_nonneg (Real.exp 1 - 3)]
  have hexp_pos : 0 < Real.exp 1 := Real.exp_pos _
  have hpow_pos : 0 < Real.exp 1 ^ (2 : ℕ) := by positivity
  have hcross : Real.exp 1 ≤ (Real.exp 1 - 2) * Real.exp 1 ^ (2 : ℕ) := by
    calc
      Real.exp 1 = 1 * Real.exp 1 := by ring
      _ ≤ (Real.exp 1 * (Real.exp 1 - 2)) * Real.exp 1 :=
        (mul_lt_mul_of_pos_right hlarge hexp_pos).le
      _ = (Real.exp 1 - 2) * Real.exp 1 ^ (2 : ℕ) := by ring
  have hfrac : 1 / Real.exp 1 ^ (2 : ℕ) ≤
      (Real.exp 1 - 2) / Real.exp 1 := by
    apply (div_le_div_iff₀ hpow_pos hexp_pos).mpr
    convert hcross using 1 <;> ring
  calc
    Real.exp (-2) = 1 / Real.exp 1 ^ (2 : ℕ) := by
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.exp_neg]
      rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      ring
    _ ≤ (Real.exp 1 - 2) / Real.exp 1 := hfrac
    _ = 1 - 2 / Real.exp 1 := by
      field_simp [Real.exp_ne_zero]

/-- For `eta ≤ 1`, the concrete reference mass is no larger than the slack
needed for the pure-policy KL feasibility calculation. -/
theorem theorem6Epsilon_le_pureSlack {eta : ℝ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1) :
    theorem6Epsilon eta ≤ 1 - 2 / Real.exp 1 := by
  have hratio : 2 ≤ 2 / eta := by
    apply (le_div_iff₀ heta_pos).mpr
    nlinarith
  have hargument : -2 / eta ≤ -2 := by
    calc
      -2 / eta = -(2 / eta) := by ring
      _ ≤ -2 := neg_le_neg hratio
  calc
    theorem6Epsilon eta = Real.exp (-2 / eta) := rfl
    _ ≤ Real.exp (-2) := Real.exp_le_exp.mpr hargument
    _ ≤ 1 - 2 / Real.exp 1 := theorem6_exp_neg_two_le_pureSlack

/-- The concrete epsilon satisfies the pure-`a`/pure-`b` KL logarithmic
feasibility condition whenever `0 < eta ≤ 1`. -/
theorem theorem6Epsilon_pureLog_le_one {eta : ℝ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1) :
    Real.log (2 / (1 - theorem6Epsilon eta)) ≤ 1 := by
  have hepsilon_le := theorem6Epsilon_le_pureSlack heta_pos heta_le_one
  have hden : 0 < 1 - theorem6Epsilon eta := by
    linarith [theorem6Epsilon_lt_one heta_pos]
  apply (Real.log_le_iff_le_exp (div_pos (by norm_num) hden)).mpr
  apply (div_le_iff₀ hden).mpr
  have hright : 2 / Real.exp 1 ≤ 1 - theorem6Epsilon eta := by
    linarith
  calc
    (2 : ℝ) = Real.exp 1 * (2 / Real.exp 1) := by
      field_simp [Real.exp_ne_zero]
    _ ≤ Real.exp 1 * (1 - theorem6Epsilon eta) :=
      mul_le_mul_of_nonneg_left hright (Real.exp_pos _).le

/-- At the concrete epsilon choice, every unit-KL-feasible policy puts at
most `eta` total mass on the clone class. -/
theorem theorem6_cloneMass_le_eta_of_Epsilon
    {eta : ℝ} {copies : ℕ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1) (hcopies_pos : 0 < copies)
    (policy : PMF (theorem6Alternative copies))
    (hpolicy_feasible : finiteKLDivergence policy
      (theorem6Reference (theorem6Epsilon eta)
        (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos) hcopies_pos) ≤ 1) :
    theorem6CloneMass policy ≤ eta := by
  have hmass := theorem6_KL_cloneMass_le_two_div_log
    (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
    (theorem6_log_invEpsilon_pos heta_pos) hcopies_pos policy hpolicy_feasible
  change theorem6CloneMass policy ≤
    2 / Real.log (theorem6Epsilon eta)⁻¹ at hmass
  rw [theorem6_two_div_log_invEpsilon heta_pos] at hmass
  exact hmass

/-- The source's RLHF mass conclusion with the explicit small-reference-mass
choice substituted.  Its reward ordering, clone normalization, and attained
KL-feasible maximizer hypotheses stay visible. -/
theorem theorem6_constrainedScoreMax_aMass_bound_of_eta
    {eta : ℝ} {copies : ℕ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1) (hcopies_pos : 0 < copies)
    (reward : theorem6Alternative copies → ℝ)
    (hreward_ab : reward theorem6A < reward theorem6B)
    (hreward_b_neg : reward theorem6B < 0)
    (hclone_zero : ∀ copy : Fin copies, reward (theorem6C copy) = 0)
    (policy : PMF (theorem6Alternative copies))
    (hpolicy_feasible : finiteKLDivergence policy
      (theorem6Reference (theorem6Epsilon eta)
        (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos) hcopies_pos) ≤ 1)
    (hmax : ∀ other : PMF (theorem6Alternative copies),
      finiteKLDivergence other
        (theorem6Reference (theorem6Epsilon eta)
          (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos) hcopies_pos) ≤ 1 →
      pmfExp other reward ≤ pmfExp policy reward) :
    (policy (theorem6A : theorem6Alternative copies)).toReal ≤
      eta * (-reward theorem6B) / (reward theorem6B - reward theorem6A) := by
  have hbound := theorem6_constrainedScoreMax_aMass_bound
    (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
    (theorem6_log_invEpsilon_pos heta_pos) hcopies_pos
    (theorem6Epsilon_pureLog_le_one heta_pos heta_le_one)
    reward hreward_ab hreward_b_neg hclone_zero policy hpolicy_feasible hmax
  rw [theorem6_two_div_log_invEpsilon heta_pos] at hbound
  exact hbound

/-- The source's welfare-optimal-policy mass conclusion with the same
explicit small-reference-mass choice substituted. -/
theorem theorem6_constrainedLiteralWelfareMax_bMass_bound_of_eta
    {eta beta : ℝ} {copies : ℕ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1) (hcopies_pos : 0 < copies)
    (hbeta : 10 ≤ beta)
    (policy : PMF (theorem6Alternative copies))
    (hpolicy_feasible : finiteKLDivergence policy
      (theorem6Reference (theorem6Epsilon eta)
        (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos) hcopies_pos) ≤ 1)
    (hmax : ∀ other : PMF (theorem6Alternative copies),
      finiteKLDivergence other
        (theorem6Reference (theorem6Epsilon eta)
          (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos) hcopies_pos) ≤ 1 →
      pmfExp other (theorem6Welfare beta) ≤ pmfExp policy (theorem6Welfare beta)) :
    (policy (theorem6B : theorem6Alternative copies)).toReal ≤
      eta / ((1 - theorem6MinorityMass beta) / beta - theorem6MinorityMass beta) := by
  have hbound := theorem6_constrainedLiteralWelfareMax_bMass_bound
    (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
    (theorem6_log_invEpsilon_pos heta_pos) hcopies_pos
    (theorem6Epsilon_pureLog_le_one heta_pos heta_le_one)
    hbeta policy hpolicy_feasible hmax
  rw [theorem6_two_div_log_invEpsilon heta_pos] at hbound
  exact hbound

/-- A single elementary endpoint calculation shared by the source's two
policy bullets: a coordinate bounded by `eta * q` plus clone mass at most
`eta` is at most `exp (-beta)` under the displayed smallness condition. -/
theorem theorem6_coordinate_add_cloneMass_le_exp_neg
    {beta eta q : ℝ} {copies : ℕ} (policy : PMF (theorem6Alternative copies))
    (coordinate : theorem6Alternative copies)
    (hcoordinate : (policy coordinate).toReal ≤ eta * q)
    (hclone : theorem6CloneMass policy ≤ eta)
    (hq_nonneg : 0 ≤ q)
    (heta_small : eta ≤ Real.exp (-beta) / (1 + q)) :
    (policy coordinate).toReal + theorem6CloneMass policy ≤ Real.exp (-beta) := by
  have hden_pos : 0 < 1 + q := by linarith
  have hproduct : eta * (1 + q) ≤ Real.exp (-beta) :=
    (le_div_iff₀ hden_pos).mp heta_small
  calc
    (policy coordinate).toReal + theorem6CloneMass policy ≤ eta * q + eta :=
      add_le_add hcoordinate hclone
    _ = eta * (1 + q) := by ring
    _ ≤ Real.exp (-beta) := hproduct

/-- The preceding finite-MLE score bound, composed with the literal KL clone
mass estimate and the same elementary exceptional-mass algebra as Appendix
F.2. -/
theorem theorem6_constrainedScorePolicy_badMass_le_exp_neg_of_zero_a_bGap_cloneUpper
    {eta beta : ℝ} {copies : ℕ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1) (hcopies_pos : 0 < copies)
    (reward : theorem6Alternative copies → ℝ) (cloneUpper gap : ℝ)
    (hreward_a_zero : reward theorem6A = 0)
    (hgap_pos : 0 < gap) (hgap : gap ≤ reward theorem6B)
    (hclone_upper_nonneg : 0 ≤ cloneUpper)
    (hclone_upper : ∀ copy : Fin copies, reward (theorem6C copy) ≤ cloneUpper)
    (policy : PMF (theorem6Alternative copies))
    (hpolicy_feasible : finiteKLDivergence policy
      (theorem6Reference (theorem6Epsilon eta)
        (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos) hcopies_pos) ≤ 1)
    (hmax : ∀ other : PMF (theorem6Alternative copies),
      finiteKLDivergence other
        (theorem6Reference (theorem6Epsilon eta)
          (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos) hcopies_pos) ≤ 1 →
        pmfExp other reward ≤ pmfExp policy reward)
    (heta_small : eta ≤ Real.exp (-beta) / (1 + cloneUpper / gap)) :
    (policy (theorem6A : theorem6Alternative copies)).toReal + theorem6CloneMass policy ≤
      Real.exp (-beta) := by
  have hclone_mass := theorem6_cloneMass_le_eta_of_Epsilon
    heta_pos heta_le_one hcopies_pos policy hpolicy_feasible
  have hpure_b := theorem6_pureB_KL_feasible_of_log_bound
    (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos) hcopies_pos
    (theorem6Epsilon_pureLog_le_one heta_pos heta_le_one)
  have ha := theorem6_scoreMax_aMass_le_of_zero_a_bGap_cloneUpper
    (theorem6Reference (theorem6Epsilon eta)
      (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos) hcopies_pos)
    policy reward eta cloneUpper gap hreward_a_zero hgap_pos hgap hclone_upper_nonneg
    hclone_upper hclone_mass hmax hpure_b
  have ha' : (policy (theorem6A : theorem6Alternative copies)).toReal ≤
      eta * (cloneUpper / gap) := by
    convert ha using 1 <;> ring
  exact theorem6_coordinate_add_cloneMass_le_exp_neg
    (q := cloneUpper / gap) policy theorem6A ha' hclone_mass
    (div_nonneg hclone_upper_nonneg hgap_pos.le) heta_small

/-- If a policy puts little mass outside `b`, its literal population welfare
is at most `AvgUtil(b)` plus that exceptional mass. -/
theorem theorem6_policyWelfare_le_minority_add_badMass
    {beta badMass : ℝ} {copies : ℕ}
    (hbeta : 1 ≤ beta) (policy : PMF (theorem6Alternative copies))
    (hbad : (policy (theorem6A : theorem6Alternative copies)).toReal +
      theorem6CloneMass policy ≤ badMass) :
    pmfExp policy (theorem6Welfare beta) ≤ theorem6MinorityMass beta + badMass := by
  have hunit : UnitIntervalUtilityProfile (theorem6Utility beta (copies := copies)) :=
    theorem6Utility_unitInterval hbeta
  have ha_le : theorem6Welfare beta (theorem6A : theorem6Alternative copies) ≤ 1 := by
    unfold theorem6Welfare
    exact populationAverageUtility_le_one (theorem6Population beta) (theorem6Utility beta)
      hunit (theorem6A : theorem6Alternative copies)
  have ha_term : (policy (theorem6A : theorem6Alternative copies)).toReal *
      theorem6Welfare beta (theorem6A : theorem6Alternative copies) ≤
      (policy (theorem6A : theorem6Alternative copies)).toReal := by
    calc
      (policy (theorem6A : theorem6Alternative copies)).toReal *
          theorem6Welfare beta (theorem6A : theorem6Alternative copies) ≤
          (policy (theorem6A : theorem6Alternative copies)).toReal * 1 :=
        mul_le_mul_of_nonneg_left ha_le ENNReal.toReal_nonneg
      _ = (policy (theorem6A : theorem6Alternative copies)).toReal := by ring
  have hb_term : (policy (theorem6B : theorem6Alternative copies)).toReal *
      theorem6Welfare beta (theorem6B : theorem6Alternative copies) ≤ theorem6MinorityMass beta := by
    change (policy (theorem6B : theorem6Alternative copies)).toReal *
      populationAverageUtility (theorem6Population beta) (theorem6Utility beta)
        (theorem6B : theorem6Alternative copies) ≤
        theorem6MinorityMass beta
    rw [theorem6_populationAverageUtility_b]
    calc
      (policy (theorem6B : theorem6Alternative copies)).toReal * theorem6MinorityMass beta ≤
          1 * theorem6MinorityMass beta :=
        mul_le_mul_of_nonneg_right
          (pmf_apply_toReal_le_one policy (theorem6B : theorem6Alternative copies))
          (theorem6MinorityMass_pos beta).le
      _ = theorem6MinorityMass beta := by ring
  have hclone_term :
      (∑ copy : Fin copies, (policy (theorem6C copy)).toReal *
        theorem6Welfare beta (theorem6C copy)) ≤ theorem6CloneMass policy := by
    unfold theorem6CloneMass
    refine Finset.sum_le_sum fun copy _ => ?_
    have hc_le : theorem6Welfare beta (theorem6C copy) ≤ 1 := by
      unfold theorem6Welfare
      exact populationAverageUtility_le_one (theorem6Population beta) (theorem6Utility beta)
        hunit (theorem6C copy)
    calc
      (policy (theorem6C copy)).toReal * theorem6Welfare beta (theorem6C copy) ≤
          (policy (theorem6C copy)).toReal * 1 :=
        mul_le_mul_of_nonneg_left hc_le ENNReal.toReal_nonneg
      _ = (policy (theorem6C copy)).toReal := by ring
  rw [theorem6_policyScore_decomposition]
  calc
    (policy (theorem6A : theorem6Alternative copies)).toReal *
        theorem6Welfare beta (theorem6A : theorem6Alternative copies) +
        (policy (theorem6B : theorem6Alternative copies)).toReal *
          theorem6Welfare beta (theorem6B : theorem6Alternative copies) +
          ∑ copy : Fin copies, (policy (theorem6C copy)).toReal *
            theorem6Welfare beta (theorem6C copy) ≤
        (policy (theorem6A : theorem6Alternative copies)).toReal +
          theorem6MinorityMass beta + theorem6CloneMass policy := by
            linarith
    _ = theorem6MinorityMass beta +
        ((policy (theorem6A : theorem6Alternative copies)).toReal + theorem6CloneMass policy) := by
          ring
    _ ≤ theorem6MinorityMass beta + badMass := by linarith

/-- If a policy puts little mass outside `a`, its literal population welfare
is at least the welfare of `a` times the remaining mass. -/
theorem theorem6_policyWelfare_ge_a_times_goodMass
    {beta badMass : ℝ} {copies : ℕ}
    (hbeta : 1 ≤ beta) (policy : PMF (theorem6Alternative copies))
    (hbad : (policy (theorem6B : theorem6Alternative copies)).toReal +
      theorem6CloneMass policy ≤ badMass) :
    (1 - badMass) * theorem6Welfare beta (theorem6A : theorem6Alternative copies) ≤
      pmfExp policy (theorem6Welfare beta) := by
  have hunit : UnitIntervalUtilityProfile (theorem6Utility beta (copies := copies)) :=
    theorem6Utility_unitInterval hbeta
  have ha_nonneg : 0 ≤ theorem6Welfare beta (theorem6A : theorem6Alternative copies) := by
    unfold theorem6Welfare
    exact populationAverageUtility_nonneg (theorem6Population beta) (theorem6Utility beta)
      hunit (theorem6A : theorem6Alternative copies)
  have hb_nonneg : 0 ≤ theorem6Welfare beta (theorem6B : theorem6Alternative copies) := by
    unfold theorem6Welfare
    exact populationAverageUtility_nonneg (theorem6Population beta) (theorem6Utility beta)
      hunit (theorem6B : theorem6Alternative copies)
  have hclone_nonneg : 0 ≤
      ∑ copy : Fin copies, (policy (theorem6C copy)).toReal *
        theorem6Welfare beta (theorem6C copy) := by
    exact Finset.sum_nonneg fun copy _ =>
      mul_nonneg ENNReal.toReal_nonneg
        (by
          unfold theorem6Welfare
          exact populationAverageUtility_nonneg (theorem6Population beta)
            (theorem6Utility beta) hunit (theorem6C copy))
  have hmass := theorem6_policyMass_decomposition policy
  have ha_mass : 1 - badMass ≤ (policy (theorem6A : theorem6Alternative copies)).toReal := by
    linarith
  have ha_term : (1 - badMass) *
      theorem6Welfare beta (theorem6A : theorem6Alternative copies) ≤
      (policy (theorem6A : theorem6Alternative copies)).toReal *
        theorem6Welfare beta (theorem6A : theorem6Alternative copies) :=
    mul_le_mul_of_nonneg_right ha_mass ha_nonneg
  have hb_term_nonneg : 0 ≤
      (policy (theorem6B : theorem6Alternative copies)).toReal *
        theorem6Welfare beta (theorem6B : theorem6Alternative copies) :=
    mul_nonneg ENNReal.toReal_nonneg hb_nonneg
  rw [theorem6_policyScore_decomposition]
  linarith [ha_term, hb_term_nonneg, hclone_nonneg]

/-- The literal welfare-separation endpoint once the two source policies have
their respective exceptional-mass bounds.  The first inequality is for the
welfare-maximizing policy (mostly `a`); the second is for the reward-maximizing
policy (mostly `b`). -/
theorem theorem6_policyWelfare_separation_of_badMass
    {beta : ℝ} {copies : ℕ} (hbeta : 10 ≤ beta)
    (rewardPolicy welfarePolicy : PMF (theorem6Alternative copies))
    (hreward_bad : (rewardPolicy (theorem6A : theorem6Alternative copies)).toReal +
      theorem6CloneMass rewardPolicy ≤ Real.exp (-beta))
    (hwelfare_bad : (welfarePolicy (theorem6B : theorem6Alternative copies)).toReal +
      theorem6CloneMass welfarePolicy ≤ Real.exp (-beta)) :
    (1 - Real.exp (-beta)) *
        ((1 - theorem6MinorityMass beta) / beta) ≤
      pmfExp welfarePolicy (theorem6Welfare beta) ∧
    pmfExp rewardPolicy (theorem6Welfare beta) ≤
      theorem6MinorityMass beta + Real.exp (-beta) := by
  constructor
  · have hbound := theorem6_policyWelfare_ge_a_times_goodMass
      (beta := beta) (copies := copies) (by linarith) welfarePolicy hwelfare_bad
    change (1 - Real.exp (-beta)) *
        populationAverageUtility (theorem6Population beta) (theorem6Utility beta)
          (theorem6A : theorem6Alternative copies) ≤
      pmfExp welfarePolicy (theorem6Welfare beta) at hbound
    rw [theorem6_populationAverageUtility_a] at hbound
    exact hbound
  · exact theorem6_policyWelfare_le_minority_add_badMass
      (beta := beta) (copies := copies) (by linarith) rewardPolicy hreward_bad

/-- A reward policy with exceptional mass strictly below one has strictly
positive literal welfare: its remaining positive mass lies on `b`, whose
population utility is `delta > 0`. -/
theorem theorem6_rewardPolicyWelfare_pos_of_badMass
    {beta : ℝ} {copies : ℕ} (hbeta : 1 ≤ beta)
    (policy : PMF (theorem6Alternative copies))
    (hbad : (policy (theorem6A : theorem6Alternative copies)).toReal +
      theorem6CloneMass policy ≤ Real.exp (-beta)) :
    0 < pmfExp policy (theorem6Welfare beta) := by
  have hexp_lt_one : Real.exp (-beta) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hmass := theorem6_policyMass_decomposition policy
  have hb_mass : 0 < (policy (theorem6B : theorem6Alternative copies)).toReal := by
    linarith
  have ha_nonneg : 0 ≤ theorem6Welfare beta (theorem6A : theorem6Alternative copies) := by
    unfold theorem6Welfare
    exact populationAverageUtility_nonneg (theorem6Population beta) (theorem6Utility beta)
      (theorem6Utility_unitInterval (by linarith))
      (theorem6A : theorem6Alternative copies)
  have hclone_nonneg : 0 ≤
      ∑ copy : Fin copies, (policy (theorem6C copy)).toReal *
        theorem6Welfare beta (theorem6C copy) := by
    exact Finset.sum_nonneg fun copy _ =>
      mul_nonneg ENNReal.toReal_nonneg
        (by
          unfold theorem6Welfare
          exact populationAverageUtility_nonneg (theorem6Population beta)
            (theorem6Utility beta) (theorem6Utility_unitInterval (by linarith))
            (theorem6C copy))
  have hb_term : 0 < (policy (theorem6B : theorem6Alternative copies)).toReal *
      theorem6Welfare beta (theorem6B : theorem6Alternative copies) := by
    change 0 < (policy (theorem6B : theorem6Alternative copies)).toReal *
      populationAverageUtility (theorem6Population beta) (theorem6Utility beta)
        (theorem6B : theorem6Alternative copies)
    rw [theorem6_populationAverageUtility_b]
    exact mul_pos hb_mass (theorem6MinorityMass_pos beta)
  rw [theorem6_policyScore_decomposition]
  have ha_term_nonneg : 0 ≤
      (policy (theorem6A : theorem6Alternative copies)).toReal *
        theorem6Welfare beta (theorem6A : theorem6Alternative copies) :=
    mul_nonneg ENNReal.toReal_nonneg ha_nonneg
  linarith

/-- The exact distortion-ratio inequality obtained from the checked Appendix
F.2 mass calculations.  It is conditional only on the two exceptional-mass
conclusions, which are supplied above by the explicit KL-policy lemmas once
their optimizer and reward-normalization hypotheses have been discharged. -/
theorem theorem6_policyWelfare_ratio_lower_of_badMass
    {beta : ℝ} {copies : ℕ} (hbeta : 10 ≤ beta)
    (rewardPolicy welfarePolicy : PMF (theorem6Alternative copies))
    (hreward_bad : (rewardPolicy (theorem6A : theorem6Alternative copies)).toReal +
      theorem6CloneMass rewardPolicy ≤ Real.exp (-beta))
    (hwelfare_bad : (welfarePolicy (theorem6B : theorem6Alternative copies)).toReal +
      theorem6CloneMass welfarePolicy ≤ Real.exp (-beta)) :
    ((1 - Real.exp (-beta)) * ((1 - theorem6MinorityMass beta) / beta)) /
        (theorem6MinorityMass beta + Real.exp (-beta)) ≤
      pmfExp welfarePolicy (theorem6Welfare beta) /
        pmfExp rewardPolicy (theorem6Welfare beta) := by
  obtain ⟨hwelfare_lower, hreward_upper⟩ :=
    theorem6_policyWelfare_separation_of_badMass hbeta rewardPolicy welfarePolicy
      hreward_bad hwelfare_bad
  have hreward_pos := theorem6_rewardPolicyWelfare_pos_of_badMass
    (copies := copies) (by linarith) rewardPolicy hreward_bad
  have hden_pos : 0 < theorem6MinorityMass beta + Real.exp (-beta) :=
    add_pos (theorem6MinorityMass_pos beta) (Real.exp_pos _)
  have hleft_nonneg : 0 ≤
      (1 - Real.exp (-beta)) * ((1 - theorem6MinorityMass beta) / beta) := by
    have hexp_le_one : Real.exp (-beta) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have hbeta_pos : 0 < beta := by linarith
    exact mul_nonneg (sub_nonneg.mpr hexp_le_one)
      (div_nonneg (sub_nonneg.mpr (theorem6MinorityMass_le_one beta)) hbeta_pos.le)
  apply (div_le_div_iff₀ hden_pos hreward_pos).mpr
  calc
    (1 - Real.exp (-beta)) * ((1 - theorem6MinorityMass beta) / beta) *
        pmfExp rewardPolicy (theorem6Welfare beta) ≤
      (1 - Real.exp (-beta)) * ((1 - theorem6MinorityMass beta) / beta) *
        (theorem6MinorityMass beta + Real.exp (-beta)) :=
      mul_le_mul_of_nonneg_left hreward_upper hleft_nonneg
    _ ≤ pmfExp welfarePolicy (theorem6Welfare beta) *
        (theorem6MinorityMass beta + Real.exp (-beta)) :=
      mul_le_mul_of_nonneg_right hwelfare_lower hden_pos.le

/-- The first Appendix-F.2 policy bullet, fully composed with the concrete
epsilon choice: a KL-feasible attained reward maximizer has at most
`exp(-beta)` mass outside `b` under its explicit score-gap threshold. -/
theorem theorem6_constrainedScorePolicy_badMass_le_exp_neg
    {eta beta : ℝ} {copies : ℕ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1) (hcopies_pos : 0 < copies)
    (reward : theorem6Alternative copies → ℝ)
    (hreward_ab : reward theorem6A < reward theorem6B)
    (hreward_b_neg : reward theorem6B < 0)
    (hclone_zero : ∀ copy : Fin copies, reward (theorem6C copy) = 0)
    (policy : PMF (theorem6Alternative copies))
    (hpolicy_feasible : finiteKLDivergence policy
      (theorem6Reference (theorem6Epsilon eta)
        (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos) hcopies_pos) ≤ 1)
    (hmax : ∀ other : PMF (theorem6Alternative copies),
      finiteKLDivergence other
        (theorem6Reference (theorem6Epsilon eta)
          (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos) hcopies_pos) ≤ 1 →
      pmfExp other reward ≤ pmfExp policy reward)
    (heta_small : eta ≤ Real.exp (-beta) /
      (1 + (-reward theorem6B) / (reward theorem6B - reward theorem6A))) :
    (policy (theorem6A : theorem6Alternative copies)).toReal + theorem6CloneMass policy ≤
      Real.exp (-beta) := by
  have ha := theorem6_constrainedScoreMax_aMass_bound_of_eta
    heta_pos heta_le_one hcopies_pos reward hreward_ab hreward_b_neg hclone_zero
    policy hpolicy_feasible hmax
  have hc := theorem6_cloneMass_le_eta_of_Epsilon
    heta_pos heta_le_one hcopies_pos policy hpolicy_feasible
  have hgap_pos : 0 < reward theorem6B - reward theorem6A := by linarith
  have hq_nonneg : 0 ≤ (-reward theorem6B) / (reward theorem6B - reward theorem6A) :=
    div_nonneg (by linarith) hgap_pos.le
  have ha' : (policy (theorem6A : theorem6Alternative copies)).toReal ≤
      eta * ((-reward theorem6B) / (reward theorem6B - reward theorem6A)) := by
    calc
      (policy (theorem6A : theorem6Alternative copies)).toReal ≤
          eta * (-reward theorem6B) / (reward theorem6B - reward theorem6A) := ha
      _ = eta * ((-reward theorem6B) / (reward theorem6B - reward theorem6A)) := by
        ring
  exact theorem6_coordinate_add_cloneMass_le_exp_neg policy theorem6A ha' hc hq_nonneg heta_small

/-- The second Appendix-F.2 policy bullet, fully composed with the concrete
epsilon choice and the corrected welfare-gap threshold: a KL-feasible
attained welfare maximizer has at most `exp(-beta)` mass outside `a`. -/
theorem theorem6_constrainedWelfarePolicy_badMass_le_exp_neg
    {eta beta : ℝ} {copies : ℕ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1) (hcopies_pos : 0 < copies)
    (hbeta : 10 ≤ beta)
    (policy : PMF (theorem6Alternative copies))
    (hpolicy_feasible : finiteKLDivergence policy
      (theorem6Reference (theorem6Epsilon eta)
        (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos) hcopies_pos) ≤ 1)
    (hmax : ∀ other : PMF (theorem6Alternative copies),
      finiteKLDivergence other
        (theorem6Reference (theorem6Epsilon eta)
          (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos) hcopies_pos) ≤ 1 →
      pmfExp other (theorem6Welfare beta) ≤ pmfExp policy (theorem6Welfare beta))
    (heta_small : eta ≤ Real.exp (-beta) /
      (1 + (((1 - theorem6MinorityMass beta) / beta - theorem6MinorityMass beta)⁻¹))) :
    (policy (theorem6B : theorem6Alternative copies)).toReal + theorem6CloneMass policy ≤
      Real.exp (-beta) := by
  have hb := theorem6_constrainedLiteralWelfareMax_bMass_bound_of_eta
    heta_pos heta_le_one hcopies_pos hbeta policy hpolicy_feasible hmax
  have hc := theorem6_cloneMass_le_eta_of_Epsilon
    heta_pos heta_le_one hcopies_pos policy hpolicy_feasible
  have horder := theorem6_populationAverageUtility_b_lt_a (copies := copies) hbeta
  rw [theorem6_populationAverageUtility_a, theorem6_populationAverageUtility_b] at horder
  have hgap_pos : 0 < (1 - theorem6MinorityMass beta) / beta - theorem6MinorityMass beta := by
    linarith
  have hb' : (policy (theorem6B : theorem6Alternative copies)).toReal ≤
      eta * (((1 - theorem6MinorityMass beta) / beta - theorem6MinorityMass beta)⁻¹) := by
    simpa only [div_eq_mul_inv] using hb
  exact theorem6_coordinate_add_cloneMass_le_exp_neg policy theorem6B hb' hc
    (inv_pos.mpr hgap_pos).le heta_small

/-- Exact two-type expansion of every population Bradley--Terry probability. -/
theorem theorem6_populationBradleyTerry_prob
    (beta : ℝ) {copies : ℕ}
    (first second : theorem6Alternative copies) :
    (populationBradleyTerryPreference (theorem6Population beta)
      (theorem6Utility beta) beta).prob PUnit.unit.{1} first second =
      theorem6MinorityMass beta *
          Real.sigmoid (beta *
            (theorem6Utility beta (0 : Fin 2) first -
              theorem6Utility beta (0 : Fin 2) second)) +
        (1 - theorem6MinorityMass beta) *
          Real.sigmoid (beta *
            (theorem6Utility beta (1 : Fin 2) first -
              theorem6Utility beta (1 : Fin 2) second)) := by
  change pmfExp (theorem6Population beta) (fun user =>
    Real.sigmoid (beta *
      (theorem6Utility beta user first - theorem6Utility beta user second))) = _
  rw [theorem6Population_pmfExp]

/--
The literal per-copy Borda advantage in Appendix F.2.  This is the expression
that the source subsequently lower-bounds; no numerical relaxation has yet
been taken here.
-/
theorem theorem6_bordaCopyGap_formula
    {beta : ℝ} {copies : ℕ} (hbeta_ne : beta ≠ 0) (copy : Fin copies) :
    (populationBradleyTerryPreference (theorem6Population beta)
        (theorem6Utility beta) beta).prob PUnit.unit.{1}
        (theorem6B : theorem6Alternative copies) (theorem6C copy) -
      (populationBradleyTerryPreference (theorem6Population beta)
        (theorem6Utility beta) beta).prob PUnit.unit.{1}
        (theorem6A : theorem6Alternative copies) (theorem6C copy) =
      theorem6MinorityMass beta * (Real.sigmoid beta - Real.sigmoid 0) +
        (1 - theorem6MinorityMass beta) *
          (Real.sigmoid (-beta) - Real.sigmoid (1 - beta)) := by
  have hreciprocal : beta * (1 / beta - 1) = 1 - beta := by
    field_simp [hbeta_ne]
  rw [theorem6_populationBradleyTerry_prob beta
    (theorem6B : theorem6Alternative copies) (theorem6C copy),
    theorem6_populationBradleyTerry_prob beta
      (theorem6A : theorem6Alternative copies) (theorem6C copy)]
  simp only [theorem6Utility]
  rw [hreciprocal]
  ring_nf

/--
The type-`c` versus `b` population preference gap has a closed form.  It is
positive once `exp(beta) > 10`; this additional large-`beta` condition is
needed for the later reward-shift sentence in the source proof.
-/
theorem theorem6_cloneBeatsB_formula
    {beta : ℝ} {copies : ℕ} (copy : Fin copies) :
    (populationBradleyTerryPreference (theorem6Population beta)
        (theorem6Utility beta) beta).prob PUnit.unit.{1}
        (theorem6C copy) (theorem6B : theorem6Alternative copies) - (1 : ℝ) / 2 =
      ((Real.exp beta - 1) * (Real.exp beta - 10)) /
        (2 * (10 + Real.exp beta) * (1 + Real.exp beta)) := by
  have hsigmoid_pos : Real.sigmoid beta = Real.exp beta / (1 + Real.exp beta) := by
    rw [Real.sigmoid_def, Real.exp_neg]
    field_simp [Real.exp_ne_zero beta]
    ring
  have hsigmoid_neg : Real.sigmoid (-beta) = 1 / (1 + Real.exp beta) := by
    rw [Real.sigmoid_def]
    ring_nf
  rw [theorem6_populationBradleyTerry_prob beta
    (theorem6C copy) (theorem6B : theorem6Alternative copies)]
  simp only [theorem6Utility]
  ring_nf
  rw [hsigmoid_pos, hsigmoid_neg]
  unfold theorem6MinorityMass
  field_simp [Real.exp_ne_zero beta]
  ring

/-- For `exp(beta) > 10`, every type-`c` alternative beats `b` in the source
population comparison probability. -/
theorem theorem6_cloneBeatsB_pos
    {beta : ℝ} {copies : ℕ} (hexp : 10 < Real.exp beta) (copy : Fin copies) :
    0 <
      (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta).prob PUnit.unit.{1}
          (theorem6C copy) (theorem6B : theorem6Alternative copies) - (1 : ℝ) / 2 := by
  rw [theorem6_cloneBeatsB_formula copy]
  have hnumerator : 0 < (Real.exp beta - 1) * (Real.exp beta - 10) :=
    mul_pos (by linarith [Real.exp_pos beta]) (by linarith)
  have hdenominator : 0 < 2 * (10 + Real.exp beta) * (1 + Real.exp beta) := by
    positivity
  exact div_pos hnumerator hdenominator

/--
Before taking any analytic bounds, the uniform population Borda-score
difference is exactly the direct `a`--`b` comparison plus one identical term
for each type-`c` alternative.  The two self-comparisons cancel at one half.
-/
theorem theorem6_uniformBordaGap_formula
    (beta : ℝ) {copies : ℕ} :
    pairwiseBordaScore (uniformPMF (theorem6Alternative copies))
        (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta)
        (theorem6B : theorem6Alternative copies) -
      pairwiseBordaScore (uniformPMF (theorem6Alternative copies))
        (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta)
        (theorem6A : theorem6Alternative copies) =
      (Fintype.card (theorem6Alternative copies) : ℝ)⁻¹ *
        ((populationBradleyTerryPreference (theorem6Population beta)
            (theorem6Utility beta) beta).prob PUnit.unit.{1}
            (theorem6B : theorem6Alternative copies)
            (theorem6A : theorem6Alternative copies) -
          (populationBradleyTerryPreference (theorem6Population beta)
            (theorem6Utility beta) beta).prob PUnit.unit.{1}
            (theorem6A : theorem6Alternative copies)
            (theorem6B : theorem6Alternative copies) +
          ∑ copy : Fin copies,
            ((populationBradleyTerryPreference (theorem6Population beta)
                (theorem6Utility beta) beta).prob PUnit.unit.{1}
                (theorem6B : theorem6Alternative copies) (theorem6C copy) -
              (populationBradleyTerryPreference (theorem6Population beta)
                (theorem6Utility beta) beta).prob PUnit.unit.{1}
                (theorem6A : theorem6Alternative copies) (theorem6C copy))) := by
  classical
  let preference := populationBradleyTerryPreference (theorem6Population beta)
    (theorem6Utility beta (copies := copies)) beta
  change pairwiseBordaScore (uniformPMF (theorem6Alternative copies)) preference
        (theorem6B : theorem6Alternative copies) -
      pairwiseBordaScore (uniformPMF (theorem6Alternative copies)) preference
        (theorem6A : theorem6Alternative copies) =
      (Fintype.card (theorem6Alternative copies) : ℝ)⁻¹ *
        (preference.prob PUnit.unit.{1}
            (theorem6B : theorem6Alternative copies)
            (theorem6A : theorem6Alternative copies) -
          preference.prob PUnit.unit.{1}
            (theorem6A : theorem6Alternative copies)
            (theorem6B : theorem6Alternative copies) +
          ∑ copy : Fin copies,
            (preference.prob PUnit.unit.{1}
                (theorem6B : theorem6Alternative copies) (theorem6C copy) -
              preference.prob PUnit.unit.{1}
                (theorem6A : theorem6Alternative copies) (theorem6C copy)))
  unfold pairwiseBordaScore pmfExp
  rw [← Finset.sum_sub_distrib]
  simp_rw [uniformPMF_apply_toReal]
  simp_rw [← mul_sub]
  rw [← Finset.mul_sum, Fintype.sum_sum_type, Fin.sum_univ_two]
  have hselfA : preference.prob PUnit.unit.{1}
      (Sum.inl (0 : Fin 2)) (Sum.inl (0 : Fin 2)) = (1 : ℝ) / 2 :=
    by
      have h := preference.complementary PUnit.unit.{1}
        (Sum.inl (0 : Fin 2)) (Sum.inl (0 : Fin 2))
      linarith
  have hselfB : preference.prob PUnit.unit.{1}
      (Sum.inl (1 : Fin 2)) (Sum.inl (1 : Fin 2)) = (1 : ℝ) / 2 :=
    by
      have h := preference.complementary PUnit.unit.{1}
        (Sum.inl (1 : Fin 2)) (Sum.inl (1 : Fin 2))
      linarith
  dsimp only [theorem6A, theorem6B, theorem6C]
  rw [hselfA, hselfB]
  ring

/--
The uniform Borda gap between a fixed type-`c` alternative and `b`, before any
analytic lower bound.  Keeping the direct `a` term and the clone-class terms
separate makes the additional source reward-order requirement auditable.
-/
theorem theorem6_uniformCloneBordaGap_formula
    (beta : ℝ) {copies : ℕ} (copy : Fin copies) :
    pairwiseBordaScore (uniformPMF (theorem6Alternative copies))
        (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta)
        (theorem6C copy) -
      pairwiseBordaScore (uniformPMF (theorem6Alternative copies))
        (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta)
        (theorem6B : theorem6Alternative copies) =
      (Fintype.card (theorem6Alternative copies) : ℝ)⁻¹ *
        ((populationBradleyTerryPreference (theorem6Population beta)
            (theorem6Utility beta) beta).prob PUnit.unit.{1}
            (theorem6C copy) (theorem6A : theorem6Alternative copies) -
          (populationBradleyTerryPreference (theorem6Population beta)
            (theorem6Utility beta) beta).prob PUnit.unit.{1}
            (theorem6B : theorem6Alternative copies) (theorem6A : theorem6Alternative copies) +
          ((populationBradleyTerryPreference (theorem6Population beta)
            (theorem6Utility beta) beta).prob PUnit.unit.{1}
            (theorem6C copy) (theorem6B : theorem6Alternative copies) - (1 : ℝ) / 2) +
          ∑ other : Fin copies,
            ((populationBradleyTerryPreference (theorem6Population beta)
                (theorem6Utility beta) beta).prob PUnit.unit.{1}
                (theorem6C copy) (theorem6C other) -
              (populationBradleyTerryPreference (theorem6Population beta)
                (theorem6Utility beta) beta).prob PUnit.unit.{1}
                (theorem6B : theorem6Alternative copies) (theorem6C other))) := by
  classical
  let preference := populationBradleyTerryPreference (theorem6Population beta)
    (theorem6Utility beta (copies := copies)) beta
  change pairwiseBordaScore (uniformPMF (theorem6Alternative copies)) preference
        (theorem6C copy) -
      pairwiseBordaScore (uniformPMF (theorem6Alternative copies)) preference
        (theorem6B : theorem6Alternative copies) =
      (Fintype.card (theorem6Alternative copies) : ℝ)⁻¹ *
        (preference.prob PUnit.unit.{1} (theorem6C copy) theorem6A -
          preference.prob PUnit.unit.{1} theorem6B theorem6A +
          (preference.prob PUnit.unit.{1} (theorem6C copy) theorem6B - (1 : ℝ) / 2) +
          ∑ other : Fin copies,
            (preference.prob PUnit.unit.{1} (theorem6C copy) (theorem6C other) -
              preference.prob PUnit.unit.{1} theorem6B (theorem6C other)))
  unfold pairwiseBordaScore pmfExp
  rw [← Finset.sum_sub_distrib]
  simp_rw [uniformPMF_apply_toReal]
  simp_rw [← mul_sub]
  rw [← Finset.mul_sum, Fintype.sum_sum_type, Fin.sum_univ_two]
  have hselfB : preference.prob PUnit.unit.{1}
      (Sum.inl (1 : Fin 2)) (Sum.inl (1 : Fin 2)) = (1 : ℝ) / 2 := by
    have h := preference.complementary PUnit.unit.{1}
      (Sum.inl (1 : Fin 2)) (Sum.inl (1 : Fin 2))
    linarith
  dsimp only [theorem6A, theorem6B, theorem6C]
  rw [hselfB]

/-- All type-`c` alternatives are tied against one another in the literal
population Bradley--Terry model. -/
theorem theorem6_clone_vs_clone_prob
    (beta : ℝ) {copies : ℕ} (first second : Fin copies) :
    (populationBradleyTerryPreference (theorem6Population beta)
        (theorem6Utility beta) beta).prob PUnit.unit.{1}
        (theorem6C first) (theorem6C second) = (1 : ℝ) / 2 := by
  rw [theorem6_populationBradleyTerry_prob beta
    (theorem6C first) (theorem6C second)]
  simp [theorem6Utility, Real.sigmoid_zero]
  ring

/-- Each clone-class Borda summand equals the same clone-versus-`b` gap. -/
theorem theorem6_cloneBordaSummand_eq_cloneBeatsBGap
    (beta : ℝ) {copies : ℕ} (copy other : Fin copies) :
    (populationBradleyTerryPreference (theorem6Population beta)
        (theorem6Utility beta) beta).prob PUnit.unit.{1}
        (theorem6C copy) (theorem6C other) -
      (populationBradleyTerryPreference (theorem6Population beta)
        (theorem6Utility beta) beta).prob PUnit.unit.{1}
        (theorem6B : theorem6Alternative copies) (theorem6C other) =
      (populationBradleyTerryPreference (theorem6Population beta)
        (theorem6Utility beta) beta).prob PUnit.unit.{1}
        (theorem6C copy) (theorem6B : theorem6Alternative copies) - (1 : ℝ) / 2 := by
  let preference := populationBradleyTerryPreference (theorem6Population beta)
    (theorem6Utility beta (copies := copies)) beta
  have hclone : preference.prob PUnit.unit.{1}
      (theorem6C copy) (theorem6C other) = (1 : ℝ) / 2 :=
    theorem6_clone_vs_clone_prob beta copy other
  have hcomplement := preference.complementary PUnit.unit.{1}
    theorem6B (theorem6C other)
  have hsame : preference.prob PUnit.unit.{1}
      (theorem6C other) theorem6B =
      preference.prob PUnit.unit.{1} (theorem6C copy) theorem6B := by
    have hother := theorem6_cloneBeatsB_formula (beta := beta) other
    have hcopy := theorem6_cloneBeatsB_formula (beta := beta) copy
    linarith
  change preference.prob PUnit.unit.{1}
      (theorem6C copy) (theorem6C other) -
      preference.prob PUnit.unit.{1} theorem6B (theorem6C other) =
    preference.prob PUnit.unit.{1} (theorem6C copy) theorem6B - (1 : ℝ) / 2
  rw [hclone]
  linarith [hcomplement, hsame]

/--
If the clone class supplies enough copies of its positive pairwise advantage,
then a fixed clone has strictly larger uniform Borda score than `b`.
-/
theorem theorem6_uniformCloneBordaGap_pos_of_copyBound
    {beta : ℝ} {copies : ℕ} (copy : Fin copies)
    (hclone_pos : 0 <
      (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta).prob PUnit.unit.{1}
          (theorem6C copy) (theorem6B : theorem6Alternative copies) - (1 : ℝ) / 2)
    (hcopies : 1 < ((copies : ℝ) + 1) *
      ((populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta).prob PUnit.unit.{1}
          (theorem6C copy) (theorem6B : theorem6Alternative copies) - (1 : ℝ) / 2)) :
    0 <
      pairwiseBordaScore (uniformPMF (theorem6Alternative copies))
        (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta)
        (theorem6C copy) -
      pairwiseBordaScore (uniformPMF (theorem6Alternative copies))
        (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta)
        (theorem6B : theorem6Alternative copies) := by
  let preference := populationBradleyTerryPreference (theorem6Population beta)
    (theorem6Utility beta (copies := copies)) beta
  let cloneGap : ℝ := preference.prob PUnit.unit.{1}
    (theorem6C copy) theorem6B - (1 : ℝ) / 2
  change 0 < cloneGap at hclone_pos
  change 1 < ((copies : ℝ) + 1) * cloneGap at hcopies
  have hdirect : -1 ≤ preference.prob PUnit.unit.{1}
      (theorem6C copy) theorem6A - preference.prob PUnit.unit.{1} theorem6B theorem6A := by
    have hnonneg := preference.nonneg PUnit.unit.{1} (theorem6C copy) theorem6A
    have hleone := preference.le_one PUnit.unit.{1} theorem6B theorem6A
    linarith
  have hsum :
      ∑ other : Fin copies,
        (preference.prob PUnit.unit.{1} (theorem6C copy) (theorem6C other) -
          preference.prob PUnit.unit.{1} theorem6B (theorem6C other)) =
        (copies : ℝ) * cloneGap := by
    calc
      (∑ other : Fin copies,
        (preference.prob PUnit.unit.{1} (theorem6C copy) (theorem6C other) -
          preference.prob PUnit.unit.{1} theorem6B (theorem6C other))) =
          ∑ _ : Fin copies, cloneGap := by
            refine Finset.sum_congr rfl fun other _ => ?_
            exact theorem6_cloneBordaSummand_eq_cloneBeatsBGap beta copy other
      _ = (copies : ℝ) * cloneGap := by
            simp [Finset.sum_const, nsmul_eq_mul]
  have htotal : 0 < preference.prob PUnit.unit.{1}
      (theorem6C copy) theorem6A - preference.prob PUnit.unit.{1} theorem6B theorem6A +
      cloneGap +
      ∑ other : Fin copies,
        (preference.prob PUnit.unit.{1} (theorem6C copy) (theorem6C other) -
          preference.prob PUnit.unit.{1} theorem6B (theorem6C other)) := by
    rw [hsum]
    linarith
  have hcard_pos : 0 < (Fintype.card (theorem6Alternative copies) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      (show Nonempty (theorem6Alternative copies) from ⟨theorem6A⟩)
  change 0 < pairwiseBordaScore (uniformPMF (theorem6Alternative copies)) preference
      (theorem6C copy) -
    pairwiseBordaScore (uniformPMF (theorem6Alternative copies)) preference theorem6B
  rw [theorem6_uniformCloneBordaGap_formula]
  exact mul_pos (inv_pos.mpr hcard_pos) htotal

/-- The source range `β ≥ 2` implies the elementary bound `exp β > 5`. -/
theorem theorem6_exp_beta_gt_five {beta : ℝ} (hbeta : 2 ≤ beta) :
    5 < Real.exp beta := by
  have hexpTwo : (5 : ℝ) < Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_d9]
  exact hexpTwo.trans_le (Real.exp_le_exp.mpr hbeta)

/-- A source-independent elementary upper bound for the real sigmoid. -/
theorem theorem6_sigmoid_le_exp (z : ℝ) : Real.sigmoid z ≤ Real.exp z := by
  rw [Real.sigmoid_def]
  calc
    (1 + Real.exp (-z))⁻¹ ≤ (Real.exp (-z))⁻¹ := by
      have hle : Real.exp (-z) ≤ 1 + Real.exp (-z) := by linarith
      convert one_div_le_one_div_of_le (Real.exp_pos (-z)) hle using 1 <;> ring
    _ = Real.exp z := by
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero z]

/-- The positive component of the source per-copy gap is at least one third. -/
theorem theorem6_sigmoid_beta_centered_lower
    {beta : ℝ} (hbeta : 2 ≤ beta) :
    (1 : ℝ) / 3 ≤ Real.sigmoid beta - Real.sigmoid 0 := by
  have hexp : (5 : ℝ) < Real.exp beta := theorem6_exp_beta_gt_five hbeta
  have hden : 0 < 1 + Real.exp beta := by positivity
  have hsigmoid : Real.sigmoid beta = Real.exp beta / (1 + Real.exp beta) := by
    rw [Real.sigmoid_def, Real.exp_neg]
    field_simp [Real.exp_ne_zero beta]
    ring
  rw [hsigmoid, Real.sigmoid_zero]
  apply (le_sub_iff_add_le).mpr
  calc
    (1 : ℝ) / 3 + (2 : ℝ)⁻¹ = 5 / 6 := by norm_num
    _ ≤ Real.exp beta / (1 + Real.exp beta) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith [hexp.le]

/-- The two source mixture weights convert the negative sigmoid tail to `δ e / 10`. -/
theorem theorem6_majorityMass_mul_exp_one_sub
    (beta : ℝ) :
    (1 - theorem6MinorityMass beta) * Real.exp (1 - beta) =
      (Real.exp 1 / 10) * theorem6MinorityMass beta := by
  unfold theorem6MinorityMass
  rw [show 1 - beta = 1 + (-beta) by ring, Real.exp_add, Real.exp_neg]
  field_simp [Real.exp_ne_zero beta]
  ring

/-- The negative type-II contribution is bounded exactly as in Appendix F.2. -/
theorem theorem6_negative_component_lower (beta : ℝ) :
    -(Real.exp 1 / 10) * theorem6MinorityMass beta ≤
      (1 - theorem6MinorityMass beta) *
        (Real.sigmoid (-beta) - Real.sigmoid (1 - beta)) := by
  have hsigmoid : Real.sigmoid (1 - beta) ≤ Real.exp (1 - beta) :=
    theorem6_sigmoid_le_exp (1 - beta)
  have hnonneg : 0 ≤ Real.sigmoid (-beta) := Real.sigmoid_nonneg _
  have hgap : -Real.exp (1 - beta) ≤
      Real.sigmoid (-beta) - Real.sigmoid (1 - beta) := by
    linarith
  have hweight : 0 ≤ 1 - theorem6MinorityMass beta :=
    sub_nonneg.mpr (theorem6MinorityMass_le_one beta)
  have hmass := theorem6_majorityMass_mul_exp_one_sub beta
  calc
    -(Real.exp 1 / 10) * theorem6MinorityMass beta =
        -((Real.exp 1 / 10) * theorem6MinorityMass beta) := by ring
    _ = -((1 - theorem6MinorityMass beta) * Real.exp (1 - beta)) := by
      rw [hmass]
    _ = -(1 - theorem6MinorityMass beta) * Real.exp (1 - beta) := by ring
    _ ≤ (1 - theorem6MinorityMass beta) *
        (Real.sigmoid (-beta) - Real.sigmoid (1 - beta)) :=
      by
        convert mul_le_mul_of_nonneg_left hgap hweight using 1 <;> ring

/--
Every type-`c` alternative supplies a strictly positive Borda increment once
`β ≥ 2`.  This repairs the source proof by deriving the literal bound rather
than relying on its printed final constant comparison.
-/
theorem theorem6_bordaCopyGap_lower
    {beta : ℝ} {copies : ℕ} (hbeta : 2 ≤ beta) (copy : Fin copies) :
    theorem6MinorityMass beta * ((1 : ℝ) / 3 - Real.exp 1 / 10) ≤
      (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta).prob PUnit.unit.{1}
          (theorem6B : theorem6Alternative copies) (theorem6C copy) -
        (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta).prob PUnit.unit.{1}
          (theorem6A : theorem6Alternative copies) (theorem6C copy) := by
  have hbeta_ne : beta ≠ 0 := by linarith
  have hfirst := mul_le_mul_of_nonneg_left
    (theorem6_sigmoid_beta_centered_lower hbeta)
    (theorem6MinorityMass_pos beta).le
  have hsecond := theorem6_negative_component_lower beta
  calc
    theorem6MinorityMass beta * ((1 : ℝ) / 3 - Real.exp 1 / 10) ≤
        theorem6MinorityMass beta *
            (Real.sigmoid beta - Real.sigmoid 0) +
          (1 - theorem6MinorityMass beta) *
            (Real.sigmoid (-beta) - Real.sigmoid (1 - beta)) := by
              linarith
    _ = (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta).prob PUnit.unit.{1}
          (theorem6B : theorem6Alternative copies) (theorem6C copy) -
        (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta).prob PUnit.unit.{1}
          (theorem6A : theorem6Alternative copies) (theorem6C copy) :=
      (theorem6_bordaCopyGap_formula (copies := copies) hbeta_ne copy).symm

/-- The lower-bound coefficient in the repaired per-copy estimate is positive. -/
theorem theorem6_bordaCopyGap_coefficient_pos (beta : ℝ) :
    0 < theorem6MinorityMass beta * ((1 : ℝ) / 3 - Real.exp 1 / 10) := by
  apply mul_pos (theorem6MinorityMass_pos beta)
  nlinarith [Real.exp_one_lt_three]

/-- Each copied alternative strictly favors `b` over `a` in population Borda count. -/
theorem theorem6_bordaCopyGap_pos
    {beta : ℝ} {copies : ℕ} (hbeta : 2 ≤ beta) (copy : Fin copies) :
    0 <
      (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta).prob PUnit.unit.{1}
          (theorem6B : theorem6Alternative copies) (theorem6C copy) -
        (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta).prob PUnit.unit.{1}
          (theorem6A : theorem6Alternative copies) (theorem6C copy) :=
  lt_of_lt_of_le (theorem6_bordaCopyGap_coefficient_pos beta)
    (theorem6_bordaCopyGap_lower (beta := beta) (copies := copies) hbeta copy)

/--
The repaired construction uses this explicit finite number of copied
alternatives.  It is deliberately stronger than the source's printed
`m - 2 ≥ 4 exp β` condition, whose final displayed comparison is not valid as
written.
-/
noncomputable def theorem6CopyCount (beta : ℝ) : ℕ :=
  Nat.ceil (2 / (theorem6MinorityMass beta * ((1 : ℝ) / 3 - Real.exp 1 / 10)))

/-- The repaired number of copies overwhelms a worst-case direct comparison. -/
theorem theorem6_copyCount_dominates (beta : ℝ) :
    1 < (theorem6CopyCount beta : ℝ) *
      (theorem6MinorityMass beta * ((1 : ℝ) / 3 - Real.exp 1 / 10)) := by
  let gapCoefficient : ℝ :=
    theorem6MinorityMass beta * ((1 : ℝ) / 3 - Real.exp 1 / 10)
  have hpositive : 0 < gapCoefficient := theorem6_bordaCopyGap_coefficient_pos beta
  have hceil : 2 / gapCoefficient ≤ (Nat.ceil (2 / gapCoefficient) : ℝ) :=
    Nat.le_ceil _
  have htwo : 2 ≤ (Nat.ceil (2 / gapCoefficient) : ℝ) * gapCoefficient :=
    (div_le_iff₀ hpositive).mp hceil
  change 1 < (Nat.ceil (2 / gapCoefficient) : ℝ) * gapCoefficient
  linarith

/-- The repaired copy count has a nonempty clone class. -/
theorem theorem6CopyCount_pos (beta : ℝ) : 0 < theorem6CopyCount beta := by
  by_contra hnot
  have hzero : theorem6CopyCount beta = 0 := Nat.eq_zero_of_not_pos hnot
  have hdominates := theorem6_copyCount_dominates beta
  rw [hzero] at hdominates
  norm_num at hdominates

/-- The repaired per-copy Borda coefficient is at most one third. -/
theorem theorem6_bordaCopyGap_coefficient_le_one_third (beta : ℝ) :
    theorem6MinorityMass beta * ((1 : ℝ) / 3 - Real.exp 1 / 10) ≤ (1 : ℝ) / 3 := by
  have hfactor_nonneg : 0 ≤ (1 : ℝ) / 3 - Real.exp 1 / 10 := by
    nlinarith [Real.exp_one_lt_three]
  have hfactor_le : (1 : ℝ) / 3 - Real.exp 1 / 10 ≤ (1 : ℝ) / 3 := by
    nlinarith [Real.exp_pos 1]
  calc
    theorem6MinorityMass beta * ((1 : ℝ) / 3 - Real.exp 1 / 10) ≤
        (1 : ℝ) * ((1 : ℝ) / 3 - Real.exp 1 / 10) := by
          exact mul_le_mul_of_nonneg_right (theorem6MinorityMass_le_one beta) hfactor_nonneg
    _ ≤ (1 : ℝ) / 3 := by simpa using hfactor_le

/-- The repaired Borda copy count is at least two. -/
theorem theorem6CopyCount_two_le (beta : ℝ) : 2 ≤ theorem6CopyCount beta := by
  by_contra hnot
  have hcount_le : theorem6CopyCount beta ≤ 1 := by omega
  have hcount_cast : (theorem6CopyCount beta : ℝ) ≤ 1 := by exact_mod_cast hcount_le
  have hdominates := theorem6_copyCount_dominates beta
  have hcoefficient := theorem6_bordaCopyGap_coefficient_le_one_third beta
  nlinarith

/-- A logarithmic lower bound on `beta` gives the convenient explicit
`exp(beta) ≥ 100` regime used to certify the clone reward order. -/
theorem theorem6_exp_beta_ge_hundred {beta : ℝ}
    (hbeta : Real.log 100 ≤ beta) : 100 ≤ Real.exp beta := by
  calc
    (100 : ℝ) = Real.exp (Real.log 100) := by
      rw [Real.exp_log]
      norm_num
    _ ≤ Real.exp beta := Real.exp_le_exp.mpr hbeta

/-- In the `exp(beta) ≥ 100` regime, a clone beats `b` by at least `2 / 5`
in its pairwise Borda summand. -/
theorem theorem6_cloneBeatsB_atLeast_two_fifths
    {beta : ℝ} {copies : ℕ} (hexp : 100 ≤ Real.exp beta) (copy : Fin copies) :
    (2 : ℝ) / 5 ≤
      (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta).prob PUnit.unit.{1}
          (theorem6C copy) (theorem6B : theorem6Alternative copies) - (1 : ℝ) / 2 := by
  rw [theorem6_cloneBeatsB_formula copy]
  have hden : 0 < 2 * (10 + Real.exp beta) * (1 + Real.exp beta) := by positivity
  apply (le_div_iff₀ hden).mpr
  have htail_nonneg : 0 ≤ (Real.exp beta - 100) * Real.exp beta := by
    exact mul_nonneg (by linarith) (Real.exp_pos beta).le
  nlinarith

/-- The repaired copy count also overwhelms the explicit clone-versus-`b`
gap in the large-`beta` regime. -/
theorem theorem6_copyCount_cloneDominates
    {beta : ℝ} (hbeta : Real.log 100 ≤ beta) (copy : Fin (theorem6CopyCount beta)) :
    1 < ((theorem6CopyCount beta : ℝ) + 1) *
      ((populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta).prob PUnit.unit.{1}
          (theorem6C copy) (theorem6B : theorem6Alternative (theorem6CopyCount beta)) -
        (1 : ℝ) / 2) := by
  have hexp := theorem6_exp_beta_ge_hundred hbeta
  have hgap := theorem6_cloneBeatsB_atLeast_two_fifths
    (copies := theorem6CopyCount beta) hexp copy
  have hcount : (2 : ℝ) ≤ theorem6CopyCount beta := by
    exact_mod_cast theorem6CopyCount_two_le beta
  have hthree : (3 : ℝ) ≤ (theorem6CopyCount beta : ℝ) + 1 := by linarith
  have hfirst : 1 < (3 : ℝ) * ((2 : ℝ) / 5) := by norm_num
  have hsecond : (3 : ℝ) * ((2 : ℝ) / 5) ≤
      3 *
        ((populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta).prob PUnit.unit.{1}
          (theorem6C copy) (theorem6B : theorem6Alternative (theorem6CopyCount beta)) -
          (1 : ℝ) / 2) := by
    exact mul_le_mul_of_nonneg_left hgap (by norm_num)
  have hthird : 3 *
      ((populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta).prob PUnit.unit.{1}
          (theorem6C copy) (theorem6B : theorem6Alternative (theorem6CopyCount beta)) -
          (1 : ℝ) / 2) ≤
      ((theorem6CopyCount beta : ℝ) + 1) *
        ((populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta).prob PUnit.unit.{1}
          (theorem6C copy) (theorem6B : theorem6Alternative (theorem6CopyCount beta)) -
          (1 : ℝ) / 2) := by
    exact mul_le_mul_of_nonneg_right hthree (le_trans (by norm_num) hgap)
  exact hfirst.trans_le (hsecond.trans hthird)

/-- In the explicit large-`beta` construction, every clone has larger uniform
population Borda score than `b`. -/
theorem theorem6_uniformCloneBordaGap_pos
    {beta : ℝ} (hbeta : Real.log 100 ≤ beta) (copy : Fin (theorem6CopyCount beta)) :
    0 <
      pairwiseBordaScore (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
        (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta)
        (theorem6C copy) -
      pairwiseBordaScore (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
        (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta)
        (theorem6B : theorem6Alternative (theorem6CopyCount beta)) := by
  apply theorem6_uniformCloneBordaGap_pos_of_copyBound copy
  · have hgap := theorem6_cloneBeatsB_atLeast_two_fifths
      (copies := theorem6CopyCount beta) (theorem6_exp_beta_ge_hundred hbeta) copy
    linarith
  · exact theorem6_copyCount_cloneDominates hbeta copy

/--
Whenever the number of copies beats the displayed positive per-copy lower
bound, `b` has a strictly larger uniform population Borda score than `a`.
-/
theorem theorem6_uniformBordaGap_pos_of_copyBound
    {beta : ℝ} {copies : ℕ} (hbeta : 2 ≤ beta)
    (hcopies : 1 < (copies : ℝ) *
      (theorem6MinorityMass beta * ((1 : ℝ) / 3 - Real.exp 1 / 10)) ) :
    0 <
      pairwiseBordaScore (uniformPMF (theorem6Alternative copies))
        (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta)
        (theorem6B : theorem6Alternative copies) -
      pairwiseBordaScore (uniformPMF (theorem6Alternative copies))
        (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta)
        (theorem6A : theorem6Alternative copies) := by
  let preference := populationBradleyTerryPreference (theorem6Population beta)
    (theorem6Utility beta (copies := copies)) beta
  let gapCoefficient : ℝ :=
    theorem6MinorityMass beta * ((1 : ℝ) / 3 - Real.exp 1 / 10)
  have hdirect : -1 ≤ preference.prob PUnit.unit.{1}
      (theorem6B : theorem6Alternative copies) theorem6A -
      preference.prob PUnit.unit.{1}
        (theorem6A : theorem6Alternative copies) theorem6B := by
    have hnonneg := preference.nonneg PUnit.unit.{1}
      (theorem6B : theorem6Alternative copies) theorem6A
    have hleone := preference.le_one PUnit.unit.{1}
      (theorem6A : theorem6Alternative copies) theorem6B
    linarith
  have hsum : (copies : ℝ) * gapCoefficient ≤
      ∑ copy : Fin copies,
        (preference.prob PUnit.unit.{1}
            (theorem6B : theorem6Alternative copies) (theorem6C copy) -
          preference.prob PUnit.unit.{1}
            (theorem6A : theorem6Alternative copies) (theorem6C copy)) := by
    calc
      (copies : ℝ) * gapCoefficient = ∑ _ : Fin copies, gapCoefficient := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ copy : Fin copies,
          (preference.prob PUnit.unit.{1}
              (theorem6B : theorem6Alternative copies) (theorem6C copy) -
            preference.prob PUnit.unit.{1}
              (theorem6A : theorem6Alternative copies) (theorem6C copy)) := by
        apply Finset.sum_le_sum
        intro copy _
        change gapCoefficient ≤
          (populationBradleyTerryPreference (theorem6Population beta)
            (theorem6Utility beta) beta).prob PUnit.unit.{1}
            (theorem6B : theorem6Alternative copies) (theorem6C copy) -
          (populationBradleyTerryPreference (theorem6Population beta)
            (theorem6Utility beta) beta).prob PUnit.unit.{1}
            (theorem6A : theorem6Alternative copies) (theorem6C copy)
        exact theorem6_bordaCopyGap_lower (beta := beta) (copies := copies) hbeta copy
  have htotal : 0 < preference.prob PUnit.unit.{1}
      (theorem6B : theorem6Alternative copies) theorem6A -
      preference.prob PUnit.unit.{1}
        (theorem6A : theorem6Alternative copies) theorem6B +
      ∑ copy : Fin copies,
        (preference.prob PUnit.unit.{1}
            (theorem6B : theorem6Alternative copies) (theorem6C copy) -
          preference.prob PUnit.unit.{1}
            (theorem6A : theorem6Alternative copies) (theorem6C copy)) := by
    change 0 < preference.prob PUnit.unit.{1}
        (theorem6B : theorem6Alternative copies) theorem6A -
        preference.prob PUnit.unit.{1}
          (theorem6A : theorem6Alternative copies) theorem6B +
        ∑ copy : Fin copies,
          (preference.prob PUnit.unit.{1}
              (theorem6B : theorem6Alternative copies) (theorem6C copy) -
            preference.prob PUnit.unit.{1}
              (theorem6A : theorem6Alternative copies) (theorem6C copy))
    change 1 < (copies : ℝ) * gapCoefficient at hcopies
    linarith
  have hcardpos : 0 < (Fintype.card (theorem6Alternative copies) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      (show Nonempty (theorem6Alternative copies) from ⟨theorem6A⟩)
  change 0 < pairwiseBordaScore (uniformPMF (theorem6Alternative copies)) preference
      (theorem6B : theorem6Alternative copies) -
    pairwiseBordaScore (uniformPMF (theorem6Alternative copies)) preference
      (theorem6A : theorem6Alternative copies)
  rw [theorem6_uniformBordaGap_formula]
  exact mul_pos (inv_pos.mpr hcardpos) htotal

/-- The repaired finite construction has `b` strictly above `a` in Borda score. -/
theorem theorem6_uniformBordaGap_pos {beta : ℝ} (hbeta : 2 ≤ beta) :
    0 <
      pairwiseBordaScore (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
        (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta)
        (theorem6B : theorem6Alternative (theorem6CopyCount beta)) -
      pairwiseBordaScore (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
        (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta)
        (theorem6A : theorem6Alternative (theorem6CopyCount beta)) :=
  theorem6_uniformBordaGap_pos_of_copyBound hbeta (theorem6_copyCount_dominates beta)

/--
Under the literal iid one-comparison report experiment, the probability that
the normalized empirical Borda score fails to rank `b` above `a` tends to
zero. This is the finite-report Borda part of Appendix F.2; converting this
random score order to a finite-sample MLE order remains a separate boundary.
-/
theorem theorem6_iidEmpiricalBordaBAFailure_tendsto_zero
    {beta : ℝ} (hbeta : 2 ≤ beta) :
    Filter.Tendsto
      (fun horizon =>
        pmfProb
          (theorem12IidBordaReportBatchLaw
            (theorem12OneComparisonReportLaw
              (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
              (theorem6Preference beta)) horizon)
          (fun sample => theorem12IidEmpiricalBordaFailure
            (fun index report => theorem12OneComparisonWins
              (theorem6ABCandidate index) report)
            (fun index report => theorem12OneComparisonIncidences
              (theorem6ABCandidate index) report)
            (1 : Fin 2) sample))
      Filter.atTop (𝓝 0) := by
  let sampling := uniformPMF (theorem6Alternative (theorem6CopyCount beta))
  let preference := theorem6Preference beta (copies := theorem6CopyCount beta)
  let wins : Fin 2 → ((theorem6Alternative (theorem6CopyCount beta) ×
      theorem6Alternative (theorem6CopyCount beta)) × Bool) → ℝ :=
    fun index report => theorem12OneComparisonWins (theorem6ABCandidate index) report
  let incidences : Fin 2 → ((theorem6Alternative (theorem6CopyCount beta) ×
      theorem6Alternative (theorem6CopyCount beta)) × Bool) → ℝ :=
    fun index report => theorem12OneComparisonIncidences (theorem6ABCandidate index) report
  let score : Fin 2 → ℝ :=
    fun index => pairwiseBordaScore sampling preference (theorem6ABCandidate index)
  change Filter.Tendsto
    (fun horizon =>
      pmfProb
        (theorem12IidBordaReportBatchLaw
          (theorem12OneComparisonReportLaw sampling preference) horizon)
        (fun sample => theorem12IidEmpiricalBordaFailure wins incidences (1 : Fin 2) sample))
    Filter.atTop (𝓝 0)
  apply theorem12_iidEmpiricalBordaFailure_tendsto_zero_of_calibrated_strict_winner
    (theorem12OneComparisonReportLaw sampling preference) wins incidences score (1 : Fin 2)
  · intro index report
    exact theorem12OneComparisonWins_nonneg (theorem6ABCandidate index) report
  · intro index report
    exact theorem12OneComparisonWins_le_incidences (theorem6ABCandidate index) report
  · intro index
    dsimp [score]
    apply pmfExp_nonneg_of_forall_nonneg sampling _
    intro opponent
    exact preference.nonneg PUnit.unit.{1} (theorem6ABCandidate index) opponent
  · intro index
    dsimp [wins, incidences, score]
    rw [theorem12OneComparisonWins_pmfExp,
      theorem12OneComparisonIncidences_pmfExp]
    ring
  · intro index
    dsimp [incidences]
    rw [theorem12OneComparisonIncidences_pmfExp]
    exact mul_pos (by norm_num) (uniformPMF_apply_toReal_pos (theorem6ABCandidate index))
  · intro ordinary hordinary
    fin_cases ordinary
    · dsimp [score]
      change pairwiseBordaScore sampling preference theorem6A <
        pairwiseBordaScore sampling preference theorem6B
      dsimp [sampling, preference, theorem6Preference]
      linarith [theorem6_uniformBordaGap_pos hbeta]
    · exact (hordinary rfl).elim

/-- In the literal iid one-comparison source experiment, the probability that
some distinct ordered alternative pair has no observed directed win tends to
zero.  These are the same reports used for the finite Borda statement above;
no balanced replacement design is introduced. -/
theorem theorem6_iidDirectedWinFailure_tendsto_zero
    {beta : ℝ} :
    Filter.Tendsto
      (fun horizon =>
        directedWinFailureProbability
          (theorem12OneComparisonReportLaw
            (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
            (theorem6Preference beta)) horizon)
      Filter.atTop (𝓝 0) := by
  apply directedWinFailureProbability_tendsto_zero
  intro winner loser _hneq
  exact theorem12OneComparisonReportLaw_directTrue_pos
    (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
    (theorem6Preference beta) winner loser
    (fun alternative => uniformPMF_apply_toReal_pos alternative)
    (fun first second => theorem6Preference_prob_pos beta first second)

/-- In the literal iid report model, the probability that the aggregated
finite logistic likelihood has no attained fixed-reference MLE tends to zero.
This closes the existence part of the finite-report bridge; it does not turn
empirical count fluctuations into the population MLE order. -/
theorem theorem6_iidNoFiniteMLEProbability_tendsto_zero
    {beta : ℝ} :
    Filter.Tendsto
      (noPairwiseMLEProbability
        (theorem12OneComparisonReportLaw
          (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
          (theorem6Preference beta))
        sigmoidCDFLikePairwiseLink
        (theorem6A : theorem6Alternative (theorem6CopyCount beta)))
      Filter.atTop (𝓝 0) := by
  apply noPairwiseMLEProbability_tendsto_zero
    (theorem12OneComparisonReportLaw
      (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
      (theorem6Preference beta))
    sigmoidCDFLikePairwiseLink
    (theorem6A : theorem6Alternative (theorem6CopyCount beta))
  · exact continuous_sigmoidCDFLikePairwiseLink
  · exact strictMono_sigmoidCDFLikePairwiseLink
  · intro winner loser hneq
    exact theorem12OneComparisonReportLaw_directTrue_pos
      (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
      (theorem6Preference beta) winner loser
      (fun alternative => uniformPMF_apply_toReal_pos alternative)
      (fun first second => theorem6Preference_prob_pos beta first second)

/-- The finite collection of direct-true report atoms in Theorem 6 has one
common strictly positive interior frequency threshold.  This is the
source-law input for the deterministic common score-cube bound below. -/
theorem theorem6_exists_directTrueFrequencyThreshold
    (beta : ℝ) :
    ∃ threshold : ℝ, 0 < threshold ∧ threshold < 1 ∧
      ∀ winner loser : theorem6Alternative (theorem6CopyCount beta), winner ≠ loser →
        threshold <
          (theorem12OneComparisonReportLaw
            (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
            (theorem6Preference beta)
            (directTrueBinaryReport winner loser)).toReal := by
  let alternatives : Type := theorem6Alternative (theorem6CopyCount beta)
  let reportLaw : PMF (BinaryPairwiseReport alternatives) :=
    theorem12OneComparisonReportLaw (uniformPMF alternatives) (theorem6Preference beta)
  let atoms : Finset (BinaryPairwiseReport alternatives) :=
    directedTrueBinaryReports alternatives
  have hAneB : (theorem6A : alternatives) ≠ theorem6B := by
    intro h
    have hfin : (0 : Fin 2) = 1 := Sum.inl.inj h
    exact Fin.zero_ne_one hfin
  have hatoms : atoms.Nonempty := by
    refine ⟨directTrueBinaryReport (theorem6A : alternatives) (theorem6B : alternatives), ?_⟩
    apply directTrueBinaryReport_mem_directedTrueBinaryReports
    exact hAneB
  have hmass : ∀ atom ∈ atoms, 0 < (reportLaw atom).toReal := by
    intro atom hatom
    rcases Finset.mem_image.mp hatom with ⟨pair, hpair, rfl⟩
    exact theorem12OneComparisonReportLaw_directTrue_pos
      (uniformPMF alternatives) (theorem6Preference beta) pair.1 pair.2
      (fun alternative => uniformPMF_apply_toReal_pos alternative)
      (fun first second => theorem6Preference_prob_pos beta first second)
  obtain ⟨threshold, hthreshold_pos, hthreshold⟩ :=
    Probability.exists_pos_lt_atomMass_of_finite reportLaw atoms hatoms hmass
  refine ⟨threshold, hthreshold_pos, ?_, ?_⟩
  · have hmember : directTrueBinaryReport (theorem6A : alternatives) (theorem6B : alternatives) ∈
      atoms := by
      apply directTrueBinaryReport_mem_directedTrueBinaryReports
      exact hAneB
    exact lt_of_lt_of_le (hthreshold _ hmember)
      (pmf_apply_toReal_le_one reportLaw _)
  · intro winner loser hneq
    exact hthreshold _ (directTrueBinaryReport_mem_directedTrueBinaryReports winner loser hneq)

/-- The literal iid report event that one directed true atom falls below its
common linear frequency threshold. -/
def theorem6DirectTrueFrequencyEvent
    (beta threshold : ℝ) {horizon : ℕ}
    (sample : Fin horizon → BinaryPairwiseReport (theorem6Alternative (theorem6CopyCount beta))) :
    Prop :=
  ∃ atom, atom ∈ directedTrueBinaryReports (theorem6Alternative (theorem6CopyCount beta)) ∧
    (Probability.empiricalCount sample atom : ℝ) ≤ (horizon : ℝ) * threshold

/-- Decidability of the paper's literal direct-true frequency event. -/
noncomputable instance theorem6_instDecidablePredDirectTrueFrequencyEvent
    (beta threshold : ℝ) {horizon : ℕ} :
    DecidablePred (theorem6DirectTrueFrequencyEvent beta threshold (horizon := horizon)) :=
  Classical.decPred _

/-- The literal iid probability that a direct-true report atom falls below a
specified common linear frequency threshold. -/
noncomputable def theorem6DirectTrueFrequencyFailure
    (beta threshold : ℝ) (horizon : ℕ) : ℝ :=
  pmfProb (pmfProduct (Fin horizon)
    (BinaryPairwiseReport (theorem6Alternative (theorem6CopyCount beta)))
    (theorem12OneComparisonReportLaw
      (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
      (theorem6Preference beta)))
    (theorem6DirectTrueFrequencyEvent beta threshold)

/-- Unfolding form of the direct-true frequency failure event. -/
theorem theorem6DirectTrueFrequencyFailure_eq
    (beta threshold : ℝ) (horizon : ℕ) :
    theorem6DirectTrueFrequencyFailure beta threshold horizon = by
      classical
      exact pmfProb
        (pmfProduct (Fin horizon)
          (BinaryPairwiseReport (theorem6Alternative (theorem6CopyCount beta)))
          (theorem12OneComparisonReportLaw
            (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
            (theorem6Preference beta)))
        (theorem6DirectTrueFrequencyEvent beta threshold) := by
  rfl

set_option maxHeartbeats 1200000 in
-- Relating the paper's named direct-report event to the generic finite iid
-- lower-tail event requires one controlled expansion of its finite alphabet.
/-- Any threshold strictly below every direct-true report mass is met by all
directed report atoms with probability tending to one in the literal iid
source experiment. -/
theorem theorem6_iidDirectTrueFrequencyFailure_tendsto_zero
    (beta threshold : ℝ)
    (hthreshold : ∀ winner loser : theorem6Alternative (theorem6CopyCount beta), winner ≠ loser →
      threshold <
        (theorem12OneComparisonReportLaw
          (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
          (theorem6Preference beta)
          (directTrueBinaryReport winner loser)).toReal) :
    Filter.Tendsto (theorem6DirectTrueFrequencyFailure beta threshold) Filter.atTop (𝓝 0) := by
  let reportLaw : PMF (BinaryPairwiseReport (theorem6Alternative (theorem6CopyCount beta))) :=
    theorem12OneComparisonReportLaw
      (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
      (theorem6Preference beta)
  have hgeneric : Filter.Tendsto
      (Probability.finiteIidFiniteSetLowerFrequencyFailure reportLaw
        (directedTrueBinaryReports (theorem6Alternative (theorem6CopyCount beta))) threshold)
      Filter.atTop (𝓝 0) := by
    apply Probability.finiteIidFiniteSetLowerFrequencyFailure_tendsto_zero
    intro atom hatom
    rcases Finset.mem_image.mp hatom with ⟨pair, hpair, rfl⟩
    exact hthreshold pair.1 pair.2 (Finset.mem_filter.mp hpair).2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 0))
    hgeneric ?_ ?_
  · intro horizon
    exact pmfProb_nonneg _ _
  · intro horizon
    unfold theorem6DirectTrueFrequencyFailure
    unfold Probability.finiteIidFiniteSetLowerFrequencyFailure
    apply le_of_eq
    apply pmfProb_congr
    intro sample
    rfl

/-- Outside the direct-true frequency failure event, every attained finite
logistic MLE lies in one deterministic score cube.  This keeps the compact
domain used for the later uniform likelihood argument faithful to the source's
literal iid reports. -/
theorem theorem6_scoreSupNorm_bound_of_not_directTrueFrequencyFailure
    {beta threshold : ℝ} {horizon : ℕ}
    (horizon_pos : 0 < horizon) (hthreshold_pos : 0 < threshold)
    (hthreshold_lt_one : threshold < 1)
    (sample : Fin horizon → BinaryPairwiseReport (theorem6Alternative (theorem6CopyCount beta)))
    (hgood : ¬ ∃ atom,
      atom ∈ directedTrueBinaryReports (theorem6Alternative (theorem6CopyCount beta)) ∧
      (Probability.empiricalCount sample atom : ℝ) ≤ (horizon : ℝ) * threshold)
    (reference : theorem6Alternative (theorem6CopyCount beta))
    (score : ScoreVector (theorem6Alternative (theorem6CopyCount beta)))
    (hmle : isPairwiseMLE (ofBinaryReports sample) sigmoidCDFLikePairwiseLink reference score) :
    ∃ bound : ℝ, 0 < bound ∧ scoreSupNorm reference score ≤
      (Fintype.card (theorem6Alternative (theorem6CopyCount beta)) : ℝ) * bound := by
  obtain ⟨bound, hbound_pos, hlow, hhigh⟩ :=
    CDFLikePairwiseLink.exists_pos_tailBand sigmoidCDFLikePairwiseLink threshold
      hthreshold_pos hthreshold_lt_one
  refine ⟨bound, hbound_pos, ?_⟩
  apply scoreSupNorm_le_card_mul_bound_of_directTrueLowerFrequency
    sample sigmoidCDFLikePairwiseLink continuous_sigmoidCDFLikePairwiseLink
    strictMono_sigmoidCDFLikePairwiseLink reference score hmle threshold bound horizon_pos hthreshold_pos
  · intro winner loser hneq
    apply le_of_not_gt
    intro hlt
    apply hgood
    exact ⟨directTrueBinaryReport winner loser,
      directTrueBinaryReport_mem_directedTrueBinaryReports winner loser hneq, hlt.le⟩
  · exact hbound_pos
  · exact hlow
  · exact hhigh

/-- The preceding score-cube conclusion with a supplied tail-band radius.
Keeping the radius explicit lets the finite-MLE consistency proof use the
same compact cube for its deterministic MLE bound and its uniform likelihood
law. -/
theorem theorem6_scoreSupNorm_le_of_not_directTrueFrequencyFailure
    {beta threshold bound : ℝ} {horizon : ℕ}
    (horizon_pos : 0 < horizon) (hthreshold_pos : 0 < threshold)
    (sample : Fin horizon → BinaryPairwiseReport (theorem6Alternative (theorem6CopyCount beta)))
    (hgood : ¬ ∃ atom,
      atom ∈ directedTrueBinaryReports (theorem6Alternative (theorem6CopyCount beta)) ∧
      (Probability.empiricalCount sample atom : ℝ) ≤ (horizon : ℝ) * threshold)
    (reference : theorem6Alternative (theorem6CopyCount beta))
    (score : ScoreVector (theorem6Alternative (theorem6CopyCount beta)))
    (hmle : isPairwiseMLE (ofBinaryReports sample) sigmoidCDFLikePairwiseLink reference score)
    (hbound_pos : 0 < bound)
    (hlow : Real.sigmoid (-bound) < threshold)
    (hhigh : 1 - threshold < Real.sigmoid bound) :
    scoreSupNorm reference score ≤
      (Fintype.card (theorem6Alternative (theorem6CopyCount beta)) : ℝ) * bound := by
  apply scoreSupNorm_le_card_mul_bound_of_directTrueLowerFrequency
    sample sigmoidCDFLikePairwiseLink continuous_sigmoidCDFLikePairwiseLink
    strictMono_sigmoidCDFLikePairwiseLink reference score hmle threshold bound horizon_pos hthreshold_pos
  · intro winner loser hneq
    apply le_of_not_gt
    intro hlt
    apply hgood
    exact ⟨directTrueBinaryReport winner loser,
      directTrueBinaryReport_mem_directedTrueBinaryReports winner loser hneq, hlt.le⟩
  · exact hbound_pos
  · exact hlow
  · exact hhigh

/-- The literal one-report population log likelihood for the Appendix F.2
construction.  Unlike the full Bradley--Terry fit objective, this is exactly
the expectation of the finite raw count likelihood. -/
noncomputable def theorem6RawPopulationLogLikelihood (beta : ℝ)
    (score : ScoreVector (theorem6Alternative (theorem6CopyCount beta))) : ℝ :=
  theorem12OneComparisonExpectedRawLogLikelihood
    (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
    (theorem6Preference beta) score

/-- The literal raw population likelihood is continuous in every finite score
coordinate. -/
theorem continuous_theorem6RawPopulationLogLikelihood (beta : ℝ) :
    Continuous (theorem6RawPopulationLogLikelihood beta) := by
  unfold theorem6RawPopulationLogLikelihood theorem12OneComparisonExpectedRawLogLikelihood pmfExp
  apply continuous_finset_sum
  intro report _
  apply Continuous.const_mul
  exact PairwiseCountDataset.continuous_binaryReportLogLikelihoodTerm_sigmoid report

/-- The raw literal population likelihood and the source's full population
Bradley--Terry objective have the same global maximizers.  The equality uses
the exact ordered-report factor two and the score-independent diagonal term,
not an asymptotic surrogate. -/
theorem theorem6_rawPopulation_globalMax_iff_bradleyTerryFit_globalMax
    (beta : ℝ) (score : ScoreVector (theorem6Alternative (theorem6CopyCount beta))) :
    (∀ candidate, theorem6RawPopulationLogLikelihood beta candidate ≤
        theorem6RawPopulationLogLikelihood beta score) ↔
      (∀ candidate,
        bradleyTerryFitObjective (theorem6Preference beta)
          (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) candidate ≤
        bradleyTerryFitObjective (theorem6Preference beta)
          (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) score) := by
  constructor
  · intro h
    apply (theorem12_offDiagonalFit_globalMax_iff_bradleyTerryFit_globalMax
      (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
      (theorem6Preference beta) score).mp
    intro candidate
    have hraw := h candidate
    unfold theorem6RawPopulationLogLikelihood at hraw
    rw [theorem12OneComparisonExpectedRawLogLikelihood_eq_two_offDiagonalFitObjective,
      theorem12OneComparisonExpectedRawLogLikelihood_eq_two_offDiagonalFitObjective] at hraw
    nlinarith
  · intro h
    have hoff : ∀ candidate,
        theorem12OneComparisonOffDiagonalFitObjective
          (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
          (theorem6Preference beta) candidate ≤
        theorem12OneComparisonOffDiagonalFitObjective
          (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
          (theorem6Preference beta) score :=
      (theorem12_offDiagonalFit_globalMax_iff_bradleyTerryFit_globalMax
        (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
        (theorem6Preference beta) score).mpr h
    intro candidate
    unfold theorem6RawPopulationLogLikelihood
    rw [theorem12OneComparisonExpectedRawLogLikelihood_eq_two_offDiagonalFitObjective,
      theorem12OneComparisonExpectedRawLogLikelihood_eq_two_offDiagonalFitObjective]
    nlinarith [hoff candidate]

/- The literal wrong-order event for an attained finite logistic MLE. -/
def theorem6FiniteMLEBadOrderEvent
    (beta : ℝ) {horizon : ℕ}
    (sample : Fin horizon → BinaryPairwiseReport (theorem6Alternative (theorem6CopyCount beta))) :
    Prop :=
  ∃ score : ScoreVector (theorem6Alternative (theorem6CopyCount beta)),
    isPairwiseMLE (ofBinaryReports sample) sigmoidCDFLikePairwiseLink
      (theorem6A : theorem6Alternative (theorem6CopyCount beta)) score ∧
      score (theorem6B : theorem6Alternative (theorem6CopyCount beta)) ≤
        score (theorem6A : theorem6Alternative (theorem6CopyCount beta))

/-- The literal iid probability that some attained finite logistic MLE has the
wrong weak order between the two distinguished alternatives. -/
noncomputable def theorem6FiniteMLEBadOrderProbability
    (beta : ℝ) (horizon : ℕ) : ℝ := by
  classical
  let alternatives : Type := theorem6Alternative (theorem6CopyCount beta)
  let reportLaw : PMF (BinaryPairwiseReport alternatives) :=
    theorem12OneComparisonReportLaw (uniformPMF alternatives) (theorem6Preference beta)
  letI : DecidablePred (theorem6FiniteMLEBadOrderEvent beta (horizon := horizon)) :=
    Classical.decPred _
  exact pmfProb (pmfProduct (Fin horizon) (BinaryPairwiseReport alternatives) reportLaw)
    (theorem6FiniteMLEBadOrderEvent beta)

/-- Unfolding form of the finite wrong-order event, used to compare it with
the two literal iid concentration failures. -/
theorem theorem6FiniteMLEBadOrderProbability_eq
    (beta : ℝ) (horizon : ℕ) :
    theorem6FiniteMLEBadOrderProbability beta horizon = by
      classical
      exact pmfProb
        (pmfProduct (Fin horizon)
          (BinaryPairwiseReport (theorem6Alternative (theorem6CopyCount beta)))
          (theorem12OneComparisonReportLaw
            (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
            (theorem6Preference beta)))
        (theorem6FiniteMLEBadOrderEvent beta) := by
  rfl

/--
For the repaired finite construction, every attained global unregularized
Bradley--Terry MLE ranks `a` below `b`.  The maximum hypothesis is explicit:
this is the source's MLE/Borda implication, not an assumed reward ordering.
-/
theorem theorem6_globalMLE_rewardA_lt_rewardB
    {beta : ℝ} (hbeta : 2 ≤ beta)
    (reward : theorem6Alternative (theorem6CopyCount beta) → ℝ)
    (hmax : ∀ candidate,
      bradleyTerryFitObjective
        (theorem6Preference beta)
        (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) candidate ≤
      bradleyTerryFitObjective
        (theorem6Preference beta)
        (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) reward) :
    reward (theorem6A : theorem6Alternative (theorem6CopyCount beta)) <
      reward (theorem6B : theorem6Alternative (theorem6CopyCount beta)) := by
  have hborda :
      preferenceAgainstSampling
        (theorem6Preference beta)
        (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
        (theorem6A : theorem6Alternative (theorem6CopyCount beta)) <
      preferenceAgainstSampling
        (theorem6Preference beta)
        (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
        (theorem6B : theorem6Alternative (theorem6CopyCount beta)) := by
    change
      pairwiseBordaScore (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
        (theorem6Preference beta)
        (theorem6A : theorem6Alternative (theorem6CopyCount beta)) <
      pairwiseBordaScore (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
        (theorem6Preference beta)
        (theorem6B : theorem6Alternative (theorem6CopyCount beta))
    change
      pairwiseBordaScore (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
        (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta)
        (theorem6A : theorem6Alternative (theorem6CopyCount beta)) <
      pairwiseBordaScore (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
        (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta)
        (theorem6B : theorem6Alternative (theorem6CopyCount beta))
    linarith [theorem6_uniformBordaGap_pos hbeta]
  exact
    (bradleyTerryFit_reward_lt_iff_preferenceAgainstSampling_lt_of_globalMax
      (theorem6Preference beta)
      (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) reward hmax
      theorem6A theorem6B
      (uniformPMF_apply_toReal_pos theorem6A)
      (uniformPMF_apply_toReal_pos theorem6B)).mpr hborda

/--
For the same attained unregularized MLE, the explicit large-`beta` construction
also places `b` strictly below every type-`c` alternative.  This supplies the
otherwise implicit precondition for the source proof's normalization
`reward(c) = 0 > reward(b) > reward(a)`.
-/
theorem theorem6_globalMLE_rewardB_lt_rewardC
    {beta : ℝ} (hbeta : Real.log 100 ≤ beta)
    (reward : theorem6Alternative (theorem6CopyCount beta) → ℝ)
    (hmax : ∀ candidate,
      bradleyTerryFitObjective
        (theorem6Preference beta)
        (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) candidate ≤
      bradleyTerryFitObjective
        (theorem6Preference beta)
        (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) reward)
    (copy : Fin (theorem6CopyCount beta)) :
    reward (theorem6B : theorem6Alternative (theorem6CopyCount beta)) <
      reward (theorem6C copy) := by
  have hborda :
      preferenceAgainstSampling
        (theorem6Preference beta)
        (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
        (theorem6B : theorem6Alternative (theorem6CopyCount beta)) <
      preferenceAgainstSampling
        (theorem6Preference beta)
        (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
        (theorem6C copy) := by
    change
      pairwiseBordaScore (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
        (theorem6Preference beta)
        (theorem6B : theorem6Alternative (theorem6CopyCount beta)) <
      pairwiseBordaScore (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
        (theorem6Preference beta)
        (theorem6C copy)
    change
      pairwiseBordaScore (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
        (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta)
        (theorem6B : theorem6Alternative (theorem6CopyCount beta)) <
      pairwiseBordaScore (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
        (populationBradleyTerryPreference (theorem6Population beta)
          (theorem6Utility beta) beta)
        (theorem6C copy)
    linarith [theorem6_uniformCloneBordaGap_pos hbeta copy]
  exact
    (bradleyTerryFit_reward_lt_iff_preferenceAgainstSampling_lt_of_globalMax
      (theorem6Preference beta)
      (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) reward hmax
      theorem6B (theorem6C copy)
      (uniformPMF_apply_toReal_pos theorem6B)
      (uniformPMF_apply_toReal_pos (theorem6C copy))).mpr hborda

/-- Any two type-`c` alternatives have identical population comparison
probabilities against every alternative in the literal construction. -/
theorem theorem6_populationPreference_clone_eq
    (beta : ℝ) {copies : ℕ} (first second : Fin copies)
    (opponent : theorem6Alternative copies) :
    (theorem6Preference beta).prob PUnit.unit.{1} (theorem6C first) opponent =
      (theorem6Preference beta).prob PUnit.unit.{1} (theorem6C second) opponent := by
  rcases opponent with ordinary | copy
  · fin_cases ordinary <;>
      simp [theorem6Preference, theorem6_populationBradleyTerry_prob, theorem6Utility]
  · simp [theorem6Preference, theorem6_populationBradleyTerry_prob, theorem6Utility]

/-- Consequently, every two type-`c` alternatives have the same uniform
population Borda score. -/
theorem theorem6_clone_preferenceAgainstUniform_eq
    (beta : ℝ) {copies : ℕ} (first second : Fin copies) :
    preferenceAgainstSampling (theorem6Preference beta)
      (uniformPMF (theorem6Alternative copies)) (theorem6C first) =
      preferenceAgainstSampling (theorem6Preference beta)
        (uniformPMF (theorem6Alternative copies)) (theorem6C second) := by
  unfold preferenceAgainstSampling
  refine pmfExp_congr (uniformPMF (theorem6Alternative copies)) ?_
  intro opponent
  exact theorem6_populationPreference_clone_eq beta first second opponent

/--
At an attained global MLE of the literal population likelihood, all type-`c`
alternatives receive the same reward.  This is the formal source bridge behind
the Appendix-F.2 normalization `r(c)=0`; it follows from MLE calibration and
the clone symmetry, rather than being added as a premise.
-/
theorem theorem6_globalMLE_clone_reward_eq
    {beta : ℝ} {copies : ℕ}
    (reward : theorem6Alternative copies → ℝ)
    (hmax : ∀ candidate,
      bradleyTerryFitObjective (theorem6Preference beta)
        (uniformPMF (theorem6Alternative copies)) candidate ≤
      bradleyTerryFitObjective (theorem6Preference beta)
        (uniformPMF (theorem6Alternative copies)) reward)
    (first second : Fin copies) :
    reward (theorem6C first) = reward (theorem6C second) := by
  have hfirstCalibration := bradleyTerryFit_averageCalibration_of_globalMax
    (theorem6Preference beta) (uniformPMF (theorem6Alternative copies)) reward hmax
    (theorem6C first) (uniformPMF_apply_toReal_pos (theorem6C first))
  have hsecondCalibration := bradleyTerryFit_averageCalibration_of_globalMax
    (theorem6Preference beta) (uniformPMF (theorem6Alternative copies)) reward hmax
    (theorem6C second) (uniformPMF_apply_toReal_pos (theorem6C second))
  have hscore := theorem6_clone_preferenceAgainstUniform_eq beta first second
  by_contra hne
  rcases lt_or_gt_of_ne hne with hfirst_lt | hsecond_lt
  · have hfitted := bradleyTerryAgainstSampling_strictMono_reward reward
      (uniformPMF (theorem6Alternative copies)) (theorem6C first) (theorem6C second)
      hfirst_lt
    rw [← hfirstCalibration, ← hsecondCalibration] at hfitted
    linarith
  · have hfitted := bradleyTerryAgainstSampling_strictMono_reward reward
      (uniformPMF (theorem6Alternative copies)) (theorem6C second) (theorem6C first)
      hsecond_lt
    rw [← hsecondCalibration, ← hfirstCalibration] at hfitted
    linarith

/--
The first policy conclusion of Appendix F.2 with its MLE normalization bridge
closed.  A population MLE is shifted by the (now proved common) clone reward;
this does not change a policy maximizer because every policy expectation is
shifted by the same constant.  The statement keeps the finite KL feasibility,
attained policy maximizer, and explicit small-reference-mass condition visible.
-/
theorem theorem6_populationMLE_constrainedScorePolicy_badMass_le_exp_neg
    {eta beta : ℝ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1)
    (hbeta_two : 2 ≤ beta) (hbeta_hundred : Real.log 100 ≤ beta)
    (reward : theorem6Alternative (theorem6CopyCount beta) → ℝ)
    (hmle : ∀ candidate,
      bradleyTerryFitObjective (theorem6Preference beta)
        (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) candidate ≤
      bradleyTerryFitObjective (theorem6Preference beta)
        (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) reward)
    (policy : PMF (theorem6Alternative (theorem6CopyCount beta)))
    (hpolicy_feasible : finiteKLDivergence policy
      (theorem6Reference (theorem6Epsilon eta)
        (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
        (theorem6CopyCount_pos beta)) ≤ 1)
    (hpolicy_max : ∀ other : PMF (theorem6Alternative (theorem6CopyCount beta)),
      finiteKLDivergence other
        (theorem6Reference (theorem6Epsilon eta)
          (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
          (theorem6CopyCount_pos beta)) ≤ 1 →
      pmfExp other reward ≤ pmfExp policy reward)
    (heta_small :
      let clone : Fin (theorem6CopyCount beta) := ⟨0, theorem6CopyCount_pos beta⟩
      let shifted : theorem6Alternative (theorem6CopyCount beta) → ℝ :=
        fun alternative => reward alternative - reward (theorem6C clone)
      eta ≤ Real.exp (-beta) /
        (1 + (-shifted theorem6B) / (shifted theorem6B - shifted theorem6A))) :
    (policy (theorem6A : theorem6Alternative (theorem6CopyCount beta))).toReal +
        theorem6CloneMass policy ≤ Real.exp (-beta) := by
  let clone : Fin (theorem6CopyCount beta) := ⟨0, theorem6CopyCount_pos beta⟩
  let shifted : theorem6Alternative (theorem6CopyCount beta) → ℝ :=
    fun alternative => reward alternative - reward (theorem6C clone)
  have hab : reward theorem6A < reward theorem6B :=
    theorem6_globalMLE_rewardA_lt_rewardB hbeta_two reward hmle
  have hbc : reward theorem6B < reward (theorem6C clone) :=
    theorem6_globalMLE_rewardB_lt_rewardC hbeta_hundred reward hmle clone
  have hshifted_ab : shifted theorem6A < shifted theorem6B := by
    dsimp [shifted]
    linarith
  have hshifted_b_neg : shifted theorem6B < 0 := by
    dsimp [shifted]
    linarith
  have hclone_zero : ∀ copy : Fin (theorem6CopyCount beta),
      shifted (theorem6C copy) = 0 := by
    intro copy
    dsimp [shifted]
    have hclone := theorem6_globalMLE_clone_reward_eq reward hmle copy clone
    linarith
  have hshifted_max : ∀ other : PMF (theorem6Alternative (theorem6CopyCount beta)),
      finiteKLDivergence other
        (theorem6Reference (theorem6Epsilon eta)
          (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
          (theorem6CopyCount_pos beta)) ≤ 1 →
      pmfExp other shifted ≤ pmfExp policy shifted := by
    intro other hother_feasible
    dsimp [shifted]
    rw [pmfExp_sub, pmfExp_const, pmfExp_sub, pmfExp_const]
    linarith [hpolicy_max other hother_feasible]
  exact theorem6_constrainedScorePolicy_badMass_le_exp_neg
    heta_pos heta_le_one (theorem6CopyCount_pos beta) shifted hshifted_ab hshifted_b_neg
    hclone_zero policy hpolicy_feasible hshifted_max heta_small

/--
The fully composed population endpoint of Appendix F.2.  The literal MLE
construction, clone normalization, concrete KL reference mass, both attained
policy maxima, and the corrected welfare smallness threshold yield the stated
finite distortion-ratio lower bound.  Only existence/selection of the two
constrained maximizers and the separate finite-report MLE limit lie outside
this population theorem.
-/
theorem theorem6_populationMLE_distortion_ratio_lower
    {eta beta : ℝ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1)
    (hbeta_ten : 10 ≤ beta) (hbeta_hundred : Real.log 100 ≤ beta)
    (reward : theorem6Alternative (theorem6CopyCount beta) → ℝ)
    (hmle : ∀ candidate,
      bradleyTerryFitObjective (theorem6Preference beta)
        (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) candidate ≤
      bradleyTerryFitObjective (theorem6Preference beta)
        (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) reward)
    (rewardPolicy welfarePolicy : PMF (theorem6Alternative (theorem6CopyCount beta)))
    (hreward_feasible : finiteKLDivergence rewardPolicy
      (theorem6Reference (theorem6Epsilon eta)
        (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
        (theorem6CopyCount_pos beta)) ≤ 1)
    (hreward_max : ∀ other : PMF (theorem6Alternative (theorem6CopyCount beta)),
      finiteKLDivergence other
        (theorem6Reference (theorem6Epsilon eta)
          (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
          (theorem6CopyCount_pos beta)) ≤ 1 →
      pmfExp other reward ≤ pmfExp rewardPolicy reward)
    (hwelfare_feasible : finiteKLDivergence welfarePolicy
      (theorem6Reference (theorem6Epsilon eta)
        (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
        (theorem6CopyCount_pos beta)) ≤ 1)
    (hwelfare_max : ∀ other : PMF (theorem6Alternative (theorem6CopyCount beta)),
      finiteKLDivergence other
        (theorem6Reference (theorem6Epsilon eta)
          (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
          (theorem6CopyCount_pos beta)) ≤ 1 →
      pmfExp other (theorem6Welfare beta) ≤ pmfExp welfarePolicy (theorem6Welfare beta))
    (hscore_small :
      let clone : Fin (theorem6CopyCount beta) := ⟨0, theorem6CopyCount_pos beta⟩
      let shifted : theorem6Alternative (theorem6CopyCount beta) → ℝ :=
        fun alternative => reward alternative - reward (theorem6C clone)
      eta ≤ Real.exp (-beta) /
        (1 + (-shifted theorem6B) / (shifted theorem6B - shifted theorem6A)))
    (hwelfare_small : eta ≤ Real.exp (-beta) /
      (1 + (((1 - theorem6MinorityMass beta) / beta - theorem6MinorityMass beta)⁻¹))) :
    ((1 - Real.exp (-beta)) * ((1 - theorem6MinorityMass beta) / beta)) /
        (theorem6MinorityMass beta + Real.exp (-beta)) ≤
      pmfExp welfarePolicy (theorem6Welfare beta) /
        pmfExp rewardPolicy (theorem6Welfare beta) := by
  have hreward_bad := theorem6_populationMLE_constrainedScorePolicy_badMass_le_exp_neg
    heta_pos heta_le_one (by linarith) hbeta_hundred reward hmle rewardPolicy
    hreward_feasible hreward_max hscore_small
  have hwelfare_bad := theorem6_constrainedWelfarePolicy_badMass_le_exp_neg
    heta_pos heta_le_one (theorem6CopyCount_pos beta) hbeta_ten welfarePolicy
    hwelfare_feasible hwelfare_max hwelfare_small
  exact theorem6_policyWelfare_ratio_lower_of_badMass hbeta_ten rewardPolicy welfarePolicy
    hreward_bad hwelfare_bad

/--
The population Appendix-F.2 distortion endpoint with constrained policy
attainment discharged.  Finite-simplex compactness and continuity construct
both unit-KL maximizers; the source's remaining population hypothesis is only
the attained population Bradley--Terry MLE.
-/
theorem theorem6_populationMLE_exists_constrainedPolicies_distortion_ratio_lower
    {eta beta : ℝ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1)
    (hbeta_ten : 10 ≤ beta) (hbeta_hundred : Real.log 100 ≤ beta)
    (reward : theorem6Alternative (theorem6CopyCount beta) → ℝ)
    (hmle : ∀ candidate,
      bradleyTerryFitObjective (theorem6Preference beta)
        (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) candidate ≤
      bradleyTerryFitObjective (theorem6Preference beta)
        (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) reward)
    (hscore_small :
      let clone : Fin (theorem6CopyCount beta) := ⟨0, theorem6CopyCount_pos beta⟩
      let shifted : theorem6Alternative (theorem6CopyCount beta) → ℝ :=
        fun alternative => reward alternative - reward (theorem6C clone)
      eta ≤ Real.exp (-beta) /
        (1 + (-shifted theorem6B) / (shifted theorem6B - shifted theorem6A)))
    (hwelfare_small : eta ≤ Real.exp (-beta) /
      (1 + (((1 - theorem6MinorityMass beta) / beta - theorem6MinorityMass beta)⁻¹))) :
    ∃ rewardPolicy welfarePolicy : PMF (theorem6Alternative (theorem6CopyCount beta)),
      finiteKLDivergence rewardPolicy
          (theorem6Reference (theorem6Epsilon eta)
            (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
            (theorem6CopyCount_pos beta)) ≤ 1 ∧
      (∀ other : PMF (theorem6Alternative (theorem6CopyCount beta)),
        finiteKLDivergence other
            (theorem6Reference (theorem6Epsilon eta)
              (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
              (theorem6CopyCount_pos beta)) ≤ 1 →
          pmfExp other reward ≤ pmfExp rewardPolicy reward) ∧
      finiteKLDivergence welfarePolicy
          (theorem6Reference (theorem6Epsilon eta)
            (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
            (theorem6CopyCount_pos beta)) ≤ 1 ∧
      (∀ other : PMF (theorem6Alternative (theorem6CopyCount beta)),
        finiteKLDivergence other
            (theorem6Reference (theorem6Epsilon eta)
              (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
              (theorem6CopyCount_pos beta)) ≤ 1 →
          pmfExp other (theorem6Welfare beta) ≤
            pmfExp welfarePolicy (theorem6Welfare beta)) ∧
      ((1 - Real.exp (-beta)) * ((1 - theorem6MinorityMass beta) / beta)) /
          (theorem6MinorityMass beta + Real.exp (-beta)) ≤
        pmfExp welfarePolicy (theorem6Welfare beta) /
          pmfExp rewardPolicy (theorem6Welfare beta) := by
  let reference : PMF (theorem6Alternative (theorem6CopyCount beta)) :=
    theorem6Reference (theorem6Epsilon eta)
      (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
      (theorem6CopyCount_pos beta)
  obtain ⟨rewardPolicy, hreward_feasible, hreward_max⟩ :=
    exists_finiteKL_maximizer reference 1 (by norm_num) reward
  obtain ⟨welfarePolicy, hwelfare_feasible, hwelfare_max⟩ :=
    exists_finiteKL_maximizer reference 1 (by norm_num) (theorem6Welfare beta)
  have hreward_feasible' : finiteKLDivergence rewardPolicy reference ≤ 1 := by
    exact hreward_feasible
  have hreward_max' : ∀ other : PMF (theorem6Alternative (theorem6CopyCount beta)),
      finiteKLDivergence other reference ≤ 1 →
        pmfExp other reward ≤ pmfExp rewardPolicy reward := by
    intro other hother
    apply hreward_max other
    exact hother
  have hwelfare_feasible' : finiteKLDivergence welfarePolicy reference ≤ 1 := by
    exact hwelfare_feasible
  have hwelfare_max' : ∀ other : PMF (theorem6Alternative (theorem6CopyCount beta)),
      finiteKLDivergence other reference ≤ 1 →
        pmfExp other (theorem6Welfare beta) ≤
          pmfExp welfarePolicy (theorem6Welfare beta) := by
    intro other hother
    apply hwelfare_max other
    exact hother
  refine ⟨rewardPolicy, welfarePolicy, hreward_feasible', hreward_max',
    hwelfare_feasible', hwelfare_max', ?_⟩
  exact theorem6_populationMLE_distortion_ratio_lower
    heta_pos heta_le_one hbeta_ten hbeta_hundred reward hmle rewardPolicy welfarePolicy
    hreward_feasible' hreward_max' hwelfare_feasible' hwelfare_max' hscore_small hwelfare_small

/--
For every attained population MLE in the literal large-scale construction,
one can choose a positive reference clone mass that makes both policy
smallness conditions hold.  Thus the finite distortion endpoint needs no
independent policy- or reference-mass attainment assumption.
-/
theorem theorem6_populationMLE_exists_policies_distortion_ratio_lower
    {beta : ℝ} (hbeta_ten : 10 ≤ beta) (hbeta_hundred : Real.log 100 ≤ beta)
    (reward : theorem6Alternative (theorem6CopyCount beta) → ℝ)
    (hmle : ∀ candidate,
      bradleyTerryFitObjective (theorem6Preference beta)
        (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) candidate ≤
      bradleyTerryFitObjective (theorem6Preference beta)
        (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) reward) :
    ∃ rewardPolicy welfarePolicy : PMF (theorem6Alternative (theorem6CopyCount beta)),
      ((1 - Real.exp (-beta)) * ((1 - theorem6MinorityMass beta) / beta)) /
          (theorem6MinorityMass beta + Real.exp (-beta)) ≤
        pmfExp welfarePolicy (theorem6Welfare beta) /
          pmfExp rewardPolicy (theorem6Welfare beta) := by
  let clone : Fin (theorem6CopyCount beta) := ⟨0, theorem6CopyCount_pos beta⟩
  let shifted : theorem6Alternative (theorem6CopyCount beta) → ℝ :=
    fun alternative => reward alternative - reward (theorem6C clone)
  have hab : reward theorem6A < reward theorem6B :=
    theorem6_globalMLE_rewardA_lt_rewardB (by linarith) reward hmle
  have hbc : reward theorem6B < reward (theorem6C clone) :=
    theorem6_globalMLE_rewardB_lt_rewardC hbeta_hundred reward hmle clone
  have hshifted_b_neg : shifted theorem6B < 0 := by
    dsimp [shifted]
    linarith
  have hshifted_gap_pos : 0 < shifted theorem6B - shifted theorem6A := by
    dsimp [shifted]
    linarith
  let scoreThreshold : ℝ := Real.exp (-beta) /
    (1 + (-shifted theorem6B) / (shifted theorem6B - shifted theorem6A))
  have hscore_den_pos : 0 <
      1 + (-shifted theorem6B) / (shifted theorem6B - shifted theorem6A) := by
    have hquot_nonneg : 0 ≤
        (-shifted theorem6B) / (shifted theorem6B - shifted theorem6A) :=
      div_nonneg (by linarith) hshifted_gap_pos.le
    linarith
  have hscoreThreshold_pos : 0 < scoreThreshold := by
    dsimp [scoreThreshold]
    exact div_pos (Real.exp_pos _) hscore_den_pos
  have hwelfare_gap_pos :
      0 < (1 - theorem6MinorityMass beta) / beta - theorem6MinorityMass beta := by
    have horder := theorem6_populationAverageUtility_b_lt_a
      (copies := theorem6CopyCount beta) hbeta_ten
    rw [theorem6_populationAverageUtility_a,
      theorem6_populationAverageUtility_b] at horder
    linarith
  let welfareThreshold : ℝ := Real.exp (-beta) /
    (1 + (((1 - theorem6MinorityMass beta) / beta - theorem6MinorityMass beta)⁻¹))
  have hwelfare_den_pos : 0 <
      1 + (((1 - theorem6MinorityMass beta) / beta - theorem6MinorityMass beta)⁻¹) := by
    exact add_pos_of_pos_of_nonneg zero_lt_one (inv_nonneg.mpr hwelfare_gap_pos.le)
  have hwelfareThreshold_pos : 0 < welfareThreshold := by
    dsimp [welfareThreshold]
    exact div_pos (Real.exp_pos _) hwelfare_den_pos
  let eta : ℝ := min 1 (min scoreThreshold welfareThreshold) / 2
  have hmin_pos : 0 < min 1 (min scoreThreshold welfareThreshold) := by
    exact lt_min zero_lt_one (lt_min hscoreThreshold_pos hwelfareThreshold_pos)
  have heta_pos : 0 < eta := by
    dsimp [eta]
    positivity
  have heta_nonneg : 0 ≤ eta := heta_pos.le
  have heta_le_min : eta ≤ min 1 (min scoreThreshold welfareThreshold) := by
    dsimp [eta]
    nlinarith
  have heta_le_one : eta ≤ 1 := heta_le_min.trans (min_le_left _ _)
  have heta_score : eta ≤ scoreThreshold :=
    heta_le_min.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heta_welfare : eta ≤ welfareThreshold :=
    heta_le_min.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨rewardPolicy, welfarePolicy, -, -, -, -, hratio⟩ :=
    theorem6_populationMLE_exists_constrainedPolicies_distortion_ratio_lower
      heta_pos heta_le_one hbeta_ten hbeta_hundred reward hmle (by
        dsimp [scoreThreshold] at heta_score
        simpa [clone, shifted] using heta_score) (by
        dsimp [welfareThreshold] at heta_welfare
        exact heta_welfare)
  exact ⟨rewardPolicy, welfarePolicy, hratio⟩

/--
The explicit population ratio from Appendix F.2 grows at least as
`exp(beta) / (44 * beta)` in the large-scale regime.  This is the concrete
finite inequality underlying the source notation `exp(Ω(beta))`.
-/
theorem theorem6_populationRatio_lower_exp_div
    {beta : ℝ} (hbeta_ten : 10 ≤ beta) (hbeta_hundred : Real.log 100 ≤ beta) :
    Real.exp beta / (44 * beta) ≤
      ((1 - Real.exp (-beta)) * ((1 - theorem6MinorityMass beta) / beta)) /
        (theorem6MinorityMass beta + Real.exp (-beta)) := by
  have hbeta_pos : 0 < beta := by linarith
  have hexp_hundred : 100 ≤ Real.exp beta := theorem6_exp_beta_ge_hundred hbeta_hundred
  have hdelta_half : theorem6MinorityMass beta ≤ (1 : ℝ) / 2 := by
    unfold theorem6MinorityMass
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [hexp_hundred]
  have htail_half : Real.exp (-beta) ≤ (1 : ℝ) / 2 := by
    have hinv : (1 : ℝ) / Real.exp beta ≤ 1 / 2 := by
      apply (div_le_div_iff₀ (Real.exp_pos beta) (by norm_num)).mpr
      nlinarith [hexp_hundred]
    calc
      Real.exp (-beta) = 1 / Real.exp beta := by
        rw [Real.exp_neg]
        ring
      _ ≤ 1 / 2 := hinv
  have hone_tail : (1 : ℝ) / 2 ≤ 1 - Real.exp (-beta) := by linarith
  have hone_delta : (1 : ℝ) / 2 ≤ 1 - theorem6MinorityMass beta := by linarith
  have hfactor_lower : (1 : ℝ) / (2 * beta) ≤
      (1 - theorem6MinorityMass beta) / beta := by
    calc
      (1 : ℝ) / (2 * beta) = ((1 : ℝ) / 2) / beta := by ring
      _ ≤ (1 - theorem6MinorityMass beta) / beta :=
        (div_le_div_iff_of_pos_right hbeta_pos).mpr hone_delta
  have hfactor_pos : 0 ≤ (1 : ℝ) / (2 * beta) := by positivity
  have hnumerator_lower : (1 : ℝ) / (4 * beta) ≤
      (1 - Real.exp (-beta)) * ((1 - theorem6MinorityMass beta) / beta) := by
    calc
      (1 : ℝ) / (4 * beta) = ((1 : ℝ) / 2) * ((1 : ℝ) / (2 * beta)) := by
        field_simp [hbeta_pos.ne']
        ring
      _ ≤ (1 - Real.exp (-beta)) * ((1 - theorem6MinorityMass beta) / beta) :=
        mul_le_mul hone_tail hfactor_lower hfactor_pos (by linarith [hone_tail])
  have hdelta_tail : theorem6MinorityMass beta ≤ 10 * Real.exp (-beta) := by
    have hinv' : (1 : ℝ) / (10 + Real.exp beta) ≤ 1 / Real.exp beta :=
      one_div_le_one_div_of_le (Real.exp_pos beta) (by linarith)
    have hinv : (10 + Real.exp beta)⁻¹ ≤ (Real.exp beta)⁻¹ := by
      simpa [one_div] using hinv'
    calc
      theorem6MinorityMass beta = 10 * (10 + Real.exp beta)⁻¹ := by
        unfold theorem6MinorityMass
        ring
      _ ≤ 10 * (Real.exp beta)⁻¹ := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 10 * Real.exp (-beta) := by rw [Real.exp_neg]
  have hdenominator_bound : theorem6MinorityMass beta + Real.exp (-beta) ≤
      11 * Real.exp (-beta) := by linarith
  have hdenominator_pos : 0 < theorem6MinorityMass beta + Real.exp (-beta) :=
    add_pos (theorem6MinorityMass_pos beta) (Real.exp_pos _)
  have hcoefficient_nonneg : 0 ≤ Real.exp beta / (44 * beta) := by positivity
  apply (le_div_iff₀ hdenominator_pos).mpr
  calc
    Real.exp beta / (44 * beta) *
        (theorem6MinorityMass beta + Real.exp (-beta)) ≤
      Real.exp beta / (44 * beta) * (11 * Real.exp (-beta)) :=
      mul_le_mul_of_nonneg_left hdenominator_bound hcoefficient_nonneg
    _ = (1 : ℝ) / (4 * beta) := by
      have hexp_product : Real.exp beta * Real.exp (-beta) = 1 := by
        rw [← Real.exp_add]
        norm_num
      field_simp [hbeta_pos.ne']
      nlinarith [hexp_product]
    _ ≤ (1 - Real.exp (-beta)) * ((1 - theorem6MinorityMass beta) / beta) :=
      hnumerator_lower

/--
Conditional on an attained population Bradley--Terry MLE, the literal
Appendix-F.2 family has an explicit exponential distortion lower bound.  The
remaining MLE boundary is its population/finite-report existence and
consistency, not constrained-policy optimization or the asymptotic scaling.
-/
theorem theorem6_populationMLE_exists_policies_exp_distortion_lower
    {beta : ℝ} (hbeta_ten : 10 ≤ beta) (hbeta_hundred : Real.log 100 ≤ beta)
    (reward : theorem6Alternative (theorem6CopyCount beta) → ℝ)
    (hmle : ∀ candidate,
      bradleyTerryFitObjective (theorem6Preference beta)
        (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) candidate ≤
      bradleyTerryFitObjective (theorem6Preference beta)
        (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) reward) :
    ∃ rewardPolicy welfarePolicy : PMF (theorem6Alternative (theorem6CopyCount beta)),
      Real.exp beta / (44 * beta) ≤
        pmfExp welfarePolicy (theorem6Welfare beta) /
          pmfExp rewardPolicy (theorem6Welfare beta) := by
  obtain ⟨rewardPolicy, welfarePolicy, hratio⟩ :=
    theorem6_populationMLE_exists_policies_distortion_ratio_lower
      hbeta_ten hbeta_hundred reward hmle
  exact ⟨rewardPolicy, welfarePolicy,
    (theorem6_populationRatio_lower_exp_div hbeta_ten hbeta_hundred).trans hratio⟩

/-- The explicit Appendix-F.2 population construction jointly supplies an
attained logistic MLE and the two policy witnesses giving its exponential
welfare-distortion lower bound. -/
theorem theorem6_exists_populationMLE_policies_exp_distortion_lower
    {beta : ℝ} (hbeta_ten : 10 ≤ beta) (hbeta_hundred : Real.log 100 ≤ beta) :
    ∃ reward : theorem6Alternative (theorem6CopyCount beta) → ℝ,
      (∀ candidate,
        bradleyTerryFitObjective (theorem6Preference beta)
          (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) candidate ≤
        bradleyTerryFitObjective (theorem6Preference beta)
          (uniformPMF (theorem6Alternative (theorem6CopyCount beta))) reward) ∧
      ∃ rewardPolicy welfarePolicy : PMF (theorem6Alternative (theorem6CopyCount beta)),
        Real.exp beta / (44 * beta) ≤
          pmfExp welfarePolicy (theorem6Welfare beta) /
            pmfExp rewardPolicy (theorem6Welfare beta) := by
  obtain ⟨reward, hmle⟩ :=
    theorem6_exists_populationMLE beta (copies := theorem6CopyCount beta)
  obtain ⟨rewardPolicy, welfarePolicy, hratio⟩ :=
    theorem6_populationMLE_exists_policies_exp_distortion_lower
      hbeta_ten hbeta_hundred reward hmle
  exact ⟨reward, hmle, rewardPolicy, welfarePolicy, hratio⟩

/--
The literal Appendix-F.2 construction has an attained population MLE and
therefore admits the explicit exponential distortion lower bound without an
extra optimizer premise.  The separate finite-report consistency question is
not part of this population theorem.
-/
theorem theorem6_exists_policies_exp_distortion_lower
    {beta : ℝ} (hbeta_ten : 10 ≤ beta) (hbeta_hundred : Real.log 100 ≤ beta) :
    ∃ reward : theorem6Alternative (theorem6CopyCount beta) → ℝ,
      ∃ rewardPolicy welfarePolicy : PMF (theorem6Alternative (theorem6CopyCount beta)),
        Real.exp beta / (44 * beta) ≤
          pmfExp welfarePolicy (theorem6Welfare beta) /
            pmfExp rewardPolicy (theorem6Welfare beta) := by
  obtain ⟨reward, hmle⟩ :=
    theorem6_exists_populationMLE beta (copies := theorem6CopyCount beta)
  obtain ⟨rewardPolicy, welfarePolicy, hratio⟩ :=
    theorem6_populationMLE_exists_policies_exp_distortion_lower
      hbeta_ten hbeta_hundred reward hmle
  exact ⟨reward, rewardPolicy, welfarePolicy, hratio⟩

set_option maxHeartbeats 800000 in
-- The literal finite-MLE consistency proof combines three nested finite event
-- comparisons and needs a larger elaboration budget than the local lemmas.
/-- Under the literal iid report experiment of Appendix F.2, the probability
that an attained finite logistic MLE fails to rank `b` above `a` converges to
zero.  The proof combines: (i) direct report frequencies that keep all finite
MLEs in one compact score cube, (ii) finite-alphabet uniform concentration of
the *raw* likelihood on that cube, and (iii) the strict population MLE order.
No balanced-design replacement or finite-MLE consistency axiom is used. -/
theorem theorem6_iidFiniteMLEBadOrderProbability_tendsto_zero
    {beta : ℝ} (hbeta : 2 ≤ beta) :
    Filter.Tendsto (theorem6FiniteMLEBadOrderProbability beta) Filter.atTop (𝓝 0) := by
  classical
  let alternatives : Type := theorem6Alternative (theorem6CopyCount beta)
  let reportLaw : PMF (BinaryPairwiseReport alternatives) :=
    theorem12OneComparisonReportLaw (uniformPMF alternatives) (theorem6Preference beta)
  let raw : ScoreVector alternatives → ℝ := theorem6RawPopulationLogLikelihood beta
  letI : Nonempty alternatives := ⟨theorem6A⟩
  letI : Nonempty (BinaryPairwiseReport alternatives) :=
    ⟨((theorem6A, theorem6A), true)⟩
  obtain ⟨threshold, hthreshold_pos, hthreshold_lt_one, hthreshold_mass⟩ :=
    theorem6_exists_directTrueFrequencyThreshold beta
  obtain ⟨bound, hbound_pos, htail_low, htail_high⟩ :=
    CDFLikePairwiseLink.exists_pos_tailBand sigmoidCDFLikePairwiseLink threshold
      hthreshold_pos hthreshold_lt_one
  obtain ⟨base, hbase_btl⟩ := theorem6_exists_populationMLE beta
  let cubeBound : ℝ :=
    max ((Fintype.card alternatives : ℝ) * bound)
      (scoreSupNorm (theorem6A : alternatives) base)
  let cube : Set (ScoreVector alternatives) :=
    Set.univ.pi (fun _ : alternatives => Set.Icc (-cubeBound) cubeBound)
  have hcube_compact : IsCompact cube := by
    dsimp [cube]
    exact isCompact_univ_pi fun _ : alternatives => isCompact_Icc
  have hbase_raw : ∀ candidate : ScoreVector alternatives,
      raw candidate ≤ raw base := by
    dsimp [raw, alternatives]
    exact (theorem6_rawPopulation_globalMax_iff_bradleyTerryFit_globalMax beta base).mpr hbase_btl
  have hbase_cube : base ∈ cube := by
    change ∀ alternative : alternatives, alternative ∈ Set.univ →
      -cubeBound ≤ base alternative ∧ base alternative ≤ cubeBound
    intro alternative _
    apply abs_le.mp
    exact (abs_score_le_scoreSupNorm (theorem6A : alternatives) alternative base).trans
      (le_max_right _ _)
  have hscore_cube : ∀ {horizon : ℕ}
      (horizon_pos : 0 < horizon)
      (sample : Fin horizon → BinaryPairwiseReport alternatives)
      (hgood : ¬ ∃ atom,
        atom ∈ directedTrueBinaryReports alternatives ∧
        (Probability.empiricalCount sample atom : ℝ) ≤ (horizon : ℝ) * threshold)
      (score : ScoreVector alternatives),
      isPairwiseMLE (ofBinaryReports sample) sigmoidCDFLikePairwiseLink
        (theorem6A : alternatives) score → score ∈ cube := by
    intro horizon horizon_pos sample hgood score hmle
    have hscore_bound : scoreSupNorm (theorem6A : alternatives) score ≤
        (Fintype.card alternatives : ℝ) * bound := by
      dsimp [alternatives] at hgood ⊢
      exact theorem6_scoreSupNorm_le_of_not_directTrueFrequencyFailure
        horizon_pos hthreshold_pos sample hgood theorem6A score hmle hbound_pos htail_low htail_high
    change ∀ alternative : alternatives, alternative ∈ Set.univ →
      -cubeBound ≤ score alternative ∧ score alternative ≤ cubeBound
    intro alternative _
    apply abs_le.mp
    exact (abs_score_le_scoreSupNorm (theorem6A : alternatives) alternative score).trans
      (hscore_bound.trans (le_max_left _ _))
  let bad : Set (ScoreVector alternatives) := cube ∩
    {score | score (theorem6B : alternatives) ≤ score (theorem6A : alternatives)}
  have hbad_compact : IsCompact bad := by
    dsimp [bad]
    exact hcube_compact.inter_right
      (isClosed_le (continuous_apply (theorem6B : alternatives))
        (continuous_apply (theorem6A : alternatives)))
  have hbad_subset : bad ⊆ cube := by
    intro score hscore
    exact hscore.1
  have hraw_continuous : Continuous raw := by
    dsimp [raw, alternatives]
    exact continuous_theorem6RawPopulationLogLikelihood beta
  have hbad_strict : ∀ score, score ∈ bad → raw score < raw base := by
    intro score hscore
    by_contra hnot
    have hbase_le : raw base ≤ raw score := le_of_not_gt hnot
    have hscore_raw_max : ∀ candidate : ScoreVector alternatives,
        raw candidate ≤ raw score := by
      intro candidate
      exact (hbase_raw candidate).trans hbase_le
    have hscore_btl_max : ∀ candidate,
        bradleyTerryFitObjective (theorem6Preference beta)
          (uniformPMF alternatives) candidate ≤
        bradleyTerryFitObjective (theorem6Preference beta)
          (uniformPMF alternatives) score := by
      apply (theorem6_rawPopulation_globalMax_iff_bradleyTerryFit_globalMax beta score).mp
      simpa only [raw, alternatives] using hscore_raw_max
    have horder := theorem6_globalMLE_rewardA_lt_rewardB hbeta score (by
      simpa only [alternatives] using hscore_btl_max)
    exact (not_lt_of_ge hscore.2) horder
  obtain ⟨tolerance, htolerance_pos, hstable⟩ :=
    AppliedModelingLib.Optimization.exists_pos_uniformArgmaxTolerance_not_mem_of_compact_of_strictSeparation
      hbad_compact hbad_subset hraw_continuous.continuousOn
      ⟨hbase_cube, fun candidate _ => hbase_raw candidate⟩ hbad_strict
  let reportScore : ScoreVector alternatives → BinaryPairwiseReport alternatives → ℝ :=
    fun score report =>
      PairwiseCountDataset.binaryReportLogLikelihoodTerm Real.sigmoid score report
  have hreportScore_continuous : ∀ report,
      Continuous (fun score : ScoreVector alternatives => reportScore score report) := by
    intro report
    exact PairwiseCountDataset.continuous_binaryReportLogLikelihoodTerm_sigmoid report
  have huniform : Filter.Tendsto
      (Probability.finiteIidUniformScoreDeviationFailure reportLaw reportScore cube tolerance)
      Filter.atTop (𝓝 0) := by
    apply Probability.finiteIidUniformScoreDeviationFailure_tendsto_zero
      reportLaw reportScore cube hcube_compact hreportScore_continuous tolerance htolerance_pos
  have hdirect : Filter.Tendsto (theorem6DirectTrueFrequencyFailure beta threshold)
      Filter.atTop (𝓝 0) :=
    theorem6_iidDirectTrueFrequencyFailure_tendsto_zero beta threshold hthreshold_mass
  have hprob : ∀ horizon,
      theorem6FiniteMLEBadOrderProbability beta horizon ≤
        theorem6DirectTrueFrequencyFailure beta threshold horizon +
          Probability.finiteIidUniformScoreDeviationFailure reportLaw reportScore cube tolerance horizon := by
    intro horizon
    let product : PMF (Fin horizon → BinaryPairwiseReport alternatives) :=
      pmfProduct (Fin horizon) (BinaryPairwiseReport alternatives) reportLaw
    let directBad : (Fin horizon → BinaryPairwiseReport alternatives) → Prop :=
      theorem6DirectTrueFrequencyEvent beta threshold
    let uniformBad : (Fin horizon → BinaryPairwiseReport alternatives) → Prop :=
      Probability.finiteIidUniformScoreDeviationEvent reportLaw reportScore cube tolerance
    let mleBad : (Fin horizon → BinaryPairwiseReport alternatives) → Prop :=
      theorem6FiniteMLEBadOrderEvent beta
    letI : DecidablePred directBad := Classical.decPred _
    letI : DecidablePred uniformBad := Classical.decPred _
    letI : DecidablePred mleBad := Classical.decPred _
    have hsubset : ∀ sample, mleBad sample → directBad sample ∨ uniformBad sample := by
      intro sample hmleBad
      unfold mleBad theorem6FiniteMLEBadOrderEvent at hmleBad
      rcases hmleBad with ⟨score, hmle, horder⟩
      by_cases horizon_zero : horizon = 0
      · left
        subst horizon
        unfold directBad theorem6DirectTrueFrequencyEvent
        refine ⟨directTrueBinaryReport (theorem6A : alternatives) (theorem6B : alternatives),
          directTrueBinaryReport_mem_directedTrueBinaryReports theorem6A theorem6B ?_, ?_⟩
        · intro hab
          have hfin : (0 : Fin 2) = 1 := Sum.inl.inj hab
          exact Fin.zero_ne_one hfin
        · simp [Probability.empiricalCount]
      by_cases hdirectBad : directBad sample
      · exact Or.inl hdirectBad
      · right
        by_contra huniformBad
        unfold uniformBad Probability.finiteIidUniformScoreDeviationEvent at huniformBad
        have horizon_pos : 0 < horizon := Nat.pos_of_ne_zero horizon_zero
        have horizon_real_pos : (0 : ℝ) < horizon := by exact_mod_cast horizon_pos
        have hscore_mem : score ∈ cube := by
          have hgood : ¬ ∃ atom,
              atom ∈ directedTrueBinaryReports alternatives ∧
            (Probability.empiricalCount sample atom : ℝ) ≤ (horizon : ℝ) * threshold := by
            unfold directBad theorem6DirectTrueFrequencyEvent at hdirectBad
            exact hdirectBad
          exact hscore_cube horizon_pos sample hgood score hmle
        let empirical : ScoreVector alternatives → ℝ := fun candidate =>
          pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid candidate / (horizon : ℝ)
        have hemprical_uniform : ∀ candidate, candidate ∈ cube →
            |empirical candidate - raw candidate| ≤ tolerance := by
          intro candidate hcandidate
          have hraw_bound :
              |Probability.finiteIidScoreSum (reportScore candidate) sample -
                  (horizon : ℝ) * pmfExp reportLaw (reportScore candidate)| ≤
                (horizon : ℝ) * tolerance := by
              apply le_of_not_gt
              intro hgt
              apply huniformBad
              exact ⟨candidate, hcandidate, hgt⟩
          have hraw_bound' :
              |pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid candidate -
                  (horizon : ℝ) * raw candidate| ≤ (horizon : ℝ) * tolerance := by
            dsimp [reportScore, raw, alternatives] at hraw_bound ⊢
            unfold Probability.finiteIidScoreSum at hraw_bound
            rw [← PairwiseCountDataset.pairwiseLogLikelihood_ofBinaryReports_eq_sum
              sample Real.sigmoid candidate] at hraw_bound
            exact hraw_bound
          have hemprical_eq : empirical candidate - raw candidate =
              (pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid candidate -
                (horizon : ℝ) * raw candidate) / (horizon : ℝ) := by
            dsimp [empirical]
            field_simp
          rw [hemprical_eq, abs_div, abs_of_pos horizon_real_pos]
          exact (div_le_iff₀ horizon_real_pos).mpr (by simpa [mul_comm] using hraw_bound')
        have hemprical_max : IsMaxOn empirical cube score := by
          intro candidate _
          dsimp [empirical]
          apply (div_le_div_iff₀ horizon_real_pos horizon_real_pos).mpr
          exact mul_le_mul_of_nonneg_right
            (isPairwiseMLE_global_max (ofBinaryReports sample)
              sigmoidCDFLikePairwiseLink (theorem6A : alternatives) score hmle candidate)
            horizon_real_pos.le
        have hnot_bad := hstable empirical score hemprical_uniform hscore_mem hemprical_max
        exact hnot_bad ⟨hscore_mem, horder⟩
    have hprob_or : pmfProb product mleBad ≤ pmfProb product directBad + pmfProb product uniformBad := by
      calc
        pmfProb product mleBad ≤ pmfProb product (fun sample => directBad sample ∨ uniformBad sample) :=
          pmfProb_le_of_imp product mleBad (fun sample => directBad sample ∨ uniformBad sample) hsubset
        _ ≤ pmfProb product directBad + pmfProb product uniformBad := by
          rw [pmfProb_or_eq_add_sub_inter]
          exact sub_le_self _ (pmfProb_nonneg product (fun sample => directBad sample ∧ uniformBad sample))
    have hmle_eq : theorem6FiniteMLEBadOrderProbability beta horizon = pmfProb product mleBad := by
      simpa only [product, mleBad, reportLaw, alternatives] using
        (theorem6FiniteMLEBadOrderProbability_eq beta horizon)
    have hdirect_eq : theorem6DirectTrueFrequencyFailure beta threshold horizon =
        pmfProb product directBad := by
      simpa only [product, directBad, reportLaw, alternatives] using
        (theorem6DirectTrueFrequencyFailure_eq beta threshold horizon)
    have huniform_eq : Probability.finiteIidUniformScoreDeviationFailure
        reportLaw reportScore cube tolerance horizon = pmfProb product uniformBad := by
      simpa only [product, uniformBad, alternatives] using
        (Probability.finiteIidUniformScoreDeviationFailure_eq
          reportLaw reportScore cube tolerance horizon)
    calc
      theorem6FiniteMLEBadOrderProbability beta horizon = pmfProb product mleBad := hmle_eq
      _ ≤ pmfProb product directBad + pmfProb product uniformBad := hprob_or
      _ = theorem6DirectTrueFrequencyFailure beta threshold horizon +
          Probability.finiteIidUniformScoreDeviationFailure
            reportLaw reportScore cube tolerance horizon := by
          rw [← hdirect_eq, ← huniform_eq]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 0))
    (by simpa using hdirect.add huniform) ?_ hprob
  intro horizon
  unfold theorem6FiniteMLEBadOrderProbability
  exact pmfProb_nonneg _ _

set_option maxHeartbeats 800000 in
-- The pathwise extension combines the same compact likelihood argument with
-- canonical finite-iid strong-law events for the literal report process.
/-- The Appendix-F.2 finite-MLE ordering bridge in its source-style
almost-sure form.  On almost every literal iid report path, every sufficiently
long prefix has no attained logistic MLE with `b ≤ a`. -/
theorem theorem6_ae_eventually_noFiniteMLEBadOrder
    {beta : ℝ} (hbeta : 2 ≤ beta) :
    letI : MeasurableSpace
      (BinaryPairwiseReport (theorem6Alternative (theorem6CopyCount beta))) := ⊤
    ∀ᵐ path ∂AppliedModelingLib.finitePMFIidPathMeasure
        (theorem12OneComparisonReportLaw
          (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
          (theorem6Preference beta)),
      ∀ᶠ horizon : ℕ in Filter.atTop,
        ¬ theorem6FiniteMLEBadOrderEvent beta
          (AppliedModelingLib.finitePMFIidPathPrefix path horizon) := by
  classical
  let alternatives : Type := theorem6Alternative (theorem6CopyCount beta)
  letI : MeasurableSpace (BinaryPairwiseReport alternatives) := ⊤
  let reportLaw : PMF (BinaryPairwiseReport alternatives) :=
    theorem12OneComparisonReportLaw (uniformPMF alternatives) (theorem6Preference beta)
  let raw : ScoreVector alternatives → ℝ := theorem6RawPopulationLogLikelihood beta
  let reference : alternatives := theorem6A
  letI : Nonempty alternatives := ⟨theorem6A⟩
  letI : Nonempty (BinaryPairwiseReport alternatives) :=
    ⟨((theorem6A, theorem6A), true)⟩
  obtain ⟨threshold, hthreshold_pos, hthreshold_lt_one, hthreshold_mass⟩ :=
    theorem6_exists_directTrueFrequencyThreshold beta
  obtain ⟨bound, hbound_pos, htail_low, htail_high⟩ :=
    CDFLikePairwiseLink.exists_pos_tailBand sigmoidCDFLikePairwiseLink threshold
      hthreshold_pos hthreshold_lt_one
  obtain ⟨base, hbase_btl⟩ := theorem6_exists_populationMLE beta
  let cubeBound : ℝ :=
    max ((Fintype.card alternatives : ℝ) * bound) (scoreSupNorm reference base)
  let cube : Set (ScoreVector alternatives) :=
    Set.univ.pi (fun _ : alternatives => Set.Icc (-cubeBound) cubeBound)
  have hcube_compact : IsCompact cube := by
    dsimp [cube]
    exact isCompact_univ_pi fun _ : alternatives => isCompact_Icc
  have hbase_raw : ∀ candidate : ScoreVector alternatives, raw candidate ≤ raw base := by
    dsimp [raw, alternatives]
    exact
      (theorem6_rawPopulation_globalMax_iff_bradleyTerryFit_globalMax beta base).mpr hbase_btl
  have hbase_cube : base ∈ cube := by
    change ∀ alternative : alternatives, alternative ∈ Set.univ →
      -cubeBound ≤ base alternative ∧ base alternative ≤ cubeBound
    intro alternative _
    apply abs_le.mp
    exact (abs_score_le_scoreSupNorm reference alternative base).trans (le_max_right _ _)
  have hscore_cube : ∀ {horizon : ℕ}
      (horizon_pos : 0 < horizon)
      (sample : Fin horizon → BinaryPairwiseReport alternatives)
      (hgood : ¬ ∃ atom,
        atom ∈ directedTrueBinaryReports alternatives ∧
        (Probability.empiricalCount sample atom : ℝ) ≤ (horizon : ℝ) * threshold)
      (score : ScoreVector alternatives),
      isPairwiseMLE (ofBinaryReports sample) sigmoidCDFLikePairwiseLink reference score →
        score ∈ cube := by
    intro horizon horizon_pos sample hgood score hmle
    have hscore_bound : scoreSupNorm reference score ≤
        (Fintype.card alternatives : ℝ) * bound := by
      dsimp [alternatives] at hgood ⊢
      exact theorem6_scoreSupNorm_le_of_not_directTrueFrequencyFailure
        horizon_pos hthreshold_pos sample hgood theorem6A score hmle hbound_pos htail_low htail_high
    change ∀ alternative : alternatives, alternative ∈ Set.univ →
      -cubeBound ≤ score alternative ∧ score alternative ≤ cubeBound
    intro alternative _
    apply abs_le.mp
    exact (abs_score_le_scoreSupNorm reference alternative score).trans
      (hscore_bound.trans (le_max_left _ _))
  let bad : Set (ScoreVector alternatives) := cube ∩
    {score | score (theorem6B : alternatives) ≤ score (theorem6A : alternatives)}
  have hbad_compact : IsCompact bad := by
    dsimp [bad]
    exact hcube_compact.inter_right
      (isClosed_le (continuous_apply (theorem6B : alternatives))
        (continuous_apply (theorem6A : alternatives)))
  have hbad_subset : bad ⊆ cube := by
    intro score hscore
    exact hscore.1
  have hraw_continuous : Continuous raw := by
    dsimp [raw, alternatives]
    exact continuous_theorem6RawPopulationLogLikelihood beta
  have hbad_strict : ∀ score, score ∈ bad → raw score < raw base := by
    intro score hscore
    by_contra hnot
    have hbase_le : raw base ≤ raw score := le_of_not_gt hnot
    have hscore_raw_max : ∀ candidate : ScoreVector alternatives, raw candidate ≤ raw score := by
      intro candidate
      exact (hbase_raw candidate).trans hbase_le
    have hscore_btl_max : ∀ candidate,
        bradleyTerryFitObjective (theorem6Preference beta)
          (uniformPMF alternatives) candidate ≤
        bradleyTerryFitObjective (theorem6Preference beta)
          (uniformPMF alternatives) score := by
      apply (theorem6_rawPopulation_globalMax_iff_bradleyTerryFit_globalMax beta score).mp
      simpa only [raw, alternatives] using hscore_raw_max
    have horder := theorem6_globalMLE_rewardA_lt_rewardB hbeta score (by
      simpa only [alternatives] using hscore_btl_max)
    exact (not_lt_of_ge hscore.2) horder
  obtain ⟨tolerance, htolerance_pos, hstable⟩ :=
    AppliedModelingLib.Optimization.exists_pos_uniformArgmaxTolerance_not_mem_of_compact_of_strictSeparation
      hbad_compact hbad_subset hraw_continuous.continuousOn
      ⟨hbase_cube, fun candidate _ => hbase_raw candidate⟩ hbad_strict
  let reportScore : ScoreVector alternatives → BinaryPairwiseReport alternatives → ℝ :=
    fun score report =>
      PairwiseCountDataset.binaryReportLogLikelihoodTerm Real.sigmoid score report
  have hreportScore_continuous : ∀ report,
      Continuous (fun score : ScoreVector alternatives => reportScore score report) := by
    intro report
    exact PairwiseCountDataset.continuous_binaryReportLogLikelihoodTerm_sigmoid report
  have hdirect :=
    AppliedModelingLib.ae_eventually_finitePMFIidPath_not_finiteIidFiniteSetLowerFrequencyEvent
      reportLaw (directedTrueBinaryReports alternatives) threshold (by
        intro atom hatom
        rcases Finset.mem_image.mp hatom with ⟨pair, hpair, rfl⟩
        exact hthreshold_mass pair.1 pair.2 (Finset.mem_filter.mp hpair).2)
  have huniform := AppliedModelingLib.ae_eventually_finitePMFIidPath_uniformScoreDeviation
    reportLaw reportScore cube hcube_compact hreportScore_continuous tolerance htolerance_pos
  filter_upwards [hdirect, huniform] with path pathDirect pathUniform
  filter_upwards [pathDirect, pathUniform, Filter.eventually_ge_atTop 1] with
      horizon hpathDirect hpathUniform hpositive
  intro hbadOrder
  rcases hbadOrder with ⟨score, hmle, horder⟩
  let sample : Fin horizon → BinaryPairwiseReport alternatives :=
    AppliedModelingLib.finitePMFIidPathPrefix path horizon
  have hscore_mem : score ∈ cube := by
    have hgood : ¬ ∃ atom,
        atom ∈ directedTrueBinaryReports alternatives ∧
        (Probability.empiricalCount sample atom : ℝ) ≤ (horizon : ℝ) * threshold := by
      exact hpathDirect
    exact hscore_cube hpositive sample hgood score (by simpa [sample, reference] using hmle)
  have horizon_real_pos : (0 : ℝ) < horizon := by exact_mod_cast hpositive
  let empirical : ScoreVector alternatives → ℝ := fun candidate =>
    pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid candidate / (horizon : ℝ)
  have hempirical_uniform : ∀ candidate, candidate ∈ cube →
      |empirical candidate - raw candidate| ≤ tolerance := by
    intro candidate hcandidate
    have hraw_bound :
        |Probability.finiteIidScoreSum (reportScore candidate) sample -
            (horizon : ℝ) * pmfExp reportLaw (reportScore candidate)| ≤
          (horizon : ℝ) * tolerance := by
      simpa [sample] using hpathUniform candidate hcandidate
    have hraw_bound' :
        |pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid candidate -
            (horizon : ℝ) * raw candidate| ≤ (horizon : ℝ) * tolerance := by
      dsimp [reportScore, raw, alternatives] at hraw_bound ⊢
      unfold Probability.finiteIidScoreSum at hraw_bound
      rw [← PairwiseCountDataset.pairwiseLogLikelihood_ofBinaryReports_eq_sum
        sample Real.sigmoid candidate] at hraw_bound
      exact hraw_bound
    have hempirical_eq : empirical candidate - raw candidate =
        (pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid candidate -
          (horizon : ℝ) * raw candidate) / (horizon : ℝ) := by
      dsimp [empirical]
      field_simp
    rw [hempirical_eq, abs_div, abs_of_pos horizon_real_pos]
    exact (div_le_iff₀ horizon_real_pos).mpr (by simpa [mul_comm] using hraw_bound')
  have hempirical_max : IsMaxOn empirical cube score := by
    intro candidate _
    dsimp [empirical]
    apply (div_le_div_iff₀ horizon_real_pos horizon_real_pos).mpr
    exact mul_le_mul_of_nonneg_right
      (isPairwiseMLE_global_max (ofBinaryReports sample)
        sigmoidCDFLikePairwiseLink reference score (by simpa [sample, reference] using hmle)
          candidate)
      horizon_real_pos.le
  have hnot_bad := hstable empirical score hempirical_uniform hscore_mem hempirical_max
  exact hnot_bad ⟨hscore_mem, horder⟩

/-- Direct-report coverage also gives an attained finite MLE eventually
almost surely on the same literal Appendix-F.2 iid report path. -/
theorem theorem6_ae_eventually_existsFiniteMLE (beta : ℝ) :
    letI : MeasurableSpace
      (BinaryPairwiseReport (theorem6Alternative (theorem6CopyCount beta))) := ⊤
    ∀ᵐ path ∂AppliedModelingLib.finitePMFIidPathMeasure
        (theorem12OneComparisonReportLaw
          (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
          (theorem6Preference beta)),
      ∀ᶠ horizon : ℕ in Filter.atTop,
        ∃ score : ScoreVector (theorem6Alternative (theorem6CopyCount beta)),
          isPairwiseMLE
            (ofBinaryReports (AppliedModelingLib.finitePMFIidPathPrefix path horizon))
            sigmoidCDFLikePairwiseLink
            (theorem6A : theorem6Alternative (theorem6CopyCount beta)) score := by
  classical
  let alternatives : Type := theorem6Alternative (theorem6CopyCount beta)
  letI : MeasurableSpace (BinaryPairwiseReport alternatives) := ⊤
  let reportLaw : PMF (BinaryPairwiseReport alternatives) :=
    theorem12OneComparisonReportLaw (uniformPMF alternatives) (theorem6Preference beta)
  let reference : alternatives := theorem6A
  letI : Nonempty alternatives := ⟨theorem6A⟩
  letI : Nonempty (BinaryPairwiseReport alternatives) :=
    ⟨((theorem6A, theorem6A), true)⟩
  obtain ⟨threshold, hthreshold_pos, _hthreshold_lt_one, hthreshold_mass⟩ :=
    theorem6_exists_directTrueFrequencyThreshold beta
  have hdirect :=
    AppliedModelingLib.ae_eventually_finitePMFIidPath_not_finiteIidFiniteSetLowerFrequencyEvent
      reportLaw (directedTrueBinaryReports alternatives) threshold (by
        intro atom hatom
        rcases Finset.mem_image.mp hatom with ⟨pair, hpair, rfl⟩
        exact hthreshold_mass pair.1 pair.2 (Finset.mem_filter.mp hpair).2)
  filter_upwards [hdirect] with path hpath
  filter_upwards [hpath, Filter.eventually_ge_atTop 1] with horizon hdirect hpositive
  let sample : Fin horizon → BinaryPairwiseReport alternatives :=
    AppliedModelingLib.finitePMFIidPathPrefix path horizon
  apply exists_pairwiseMLE_of_allBinaryReportWins sample sigmoidCDFLikePairwiseLink reference
    continuous_sigmoidCDFLikePairwiseLink strictMono_sigmoidCDFLikePairwiseLink
  intro winner loser hneq
  have hpositiveH : (0 : ℝ) < horizon := by exact_mod_cast hpositive
  have hthresholdH : (0 : ℝ) < (horizon : ℝ) * threshold :=
    mul_pos hpositiveH hthreshold_pos
  have hnot_count_le :
      ¬ (Probability.empiricalCount sample (directTrueBinaryReport winner loser) : ℝ) ≤
          (horizon : ℝ) * threshold := by
    intro hcount
    apply hdirect
    exact ⟨directTrueBinaryReport winner loser,
      directTrueBinaryReport_mem_directedTrueBinaryReports winner loser hneq, hcount⟩
  have hcount_pos : 0 <
      (Probability.empiricalCount sample (directTrueBinaryReport winner loser) : ℝ) :=
    hthresholdH.trans (lt_of_not_ge hnot_count_le)
  have hcount_nat_pos : 0 <
      Probability.empiricalCount sample (directTrueBinaryReport winner loser) := by
    exact_mod_cast hcount_pos
  have hsuccess_pos : 0 <
      (successIndexSet (fun report : BinaryPairwiseReport alternatives =>
        report = directTrueBinaryReport winner loser) sample).card := by
    simpa [Probability.empiricalCount] using hcount_nat_pos
  obtain ⟨index, hindex⟩ := Finset.card_pos.mp hsuccess_pos
  have hreport : sample index = directTrueBinaryReport winner loser := by
    simpa [successIndexSet] using hindex
  refine ⟨index, ?_⟩
  simpa [hreport] using binaryReportWin_direct_true hneq

/-- Full source-facing finite-MLE limit in Appendix F.2: almost every literal
iid report path eventually has an attained MLE, and every attained MLE ranks
the source's `b` strictly above `a`. -/
theorem theorem6_ae_eventually_finiteMLE_rewardA_lt_rewardB
    {beta : ℝ} (hbeta : 2 ≤ beta) :
    letI : MeasurableSpace
      (BinaryPairwiseReport (theorem6Alternative (theorem6CopyCount beta))) := ⊤
    ∀ᵐ path ∂AppliedModelingLib.finitePMFIidPathMeasure
        (theorem12OneComparisonReportLaw
          (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
          (theorem6Preference beta)),
      ∀ᶠ horizon : ℕ in Filter.atTop,
        (∃ score : ScoreVector (theorem6Alternative (theorem6CopyCount beta)),
          isPairwiseMLE
            (ofBinaryReports (AppliedModelingLib.finitePMFIidPathPrefix path horizon))
            sigmoidCDFLikePairwiseLink
            (theorem6A : theorem6Alternative (theorem6CopyCount beta)) score) ∧
        ∀ score : ScoreVector (theorem6Alternative (theorem6CopyCount beta)),
          isPairwiseMLE
            (ofBinaryReports (AppliedModelingLib.finitePMFIidPathPrefix path horizon))
            sigmoidCDFLikePairwiseLink
            (theorem6A : theorem6Alternative (theorem6CopyCount beta)) score →
            score (theorem6A : theorem6Alternative (theorem6CopyCount beta)) <
              score (theorem6B : theorem6Alternative (theorem6CopyCount beta)) := by
  letI : MeasurableSpace
      (BinaryPairwiseReport (theorem6Alternative (theorem6CopyCount beta))) := ⊤
  have hexists := theorem6_ae_eventually_existsFiniteMLE beta
  have hbad := theorem6_ae_eventually_noFiniteMLEBadOrder hbeta
  filter_upwards [hexists, hbad] with path hexists hbad
  filter_upwards [hexists, hbad] with horizon hMLE hbad
  constructor
  · exact hMLE
  · intro score hmle
    exact lt_of_not_ge (by
      intro hnot
      apply hbad
      exact ⟨score, hmle, hnot⟩)

set_option maxHeartbeats 800000 in
-- This uniform-margin refinement uses compact attainment of the positive
-- population score gap in addition to the finite-iid likelihood strong law.
/-- The strict finite-MLE order in Appendix F.2 is eventually separated by a
single positive score margin, while all finite MLEs remain in one deterministic
coordinate cube.  Both constants depend only on the source instance, not on
the iid report path or the sample horizon. -/
theorem theorem6_exists_uniformFiniteMLE_scoreMargin
    {beta : ℝ} (hbeta : 2 ≤ beta) :
    ∃ cubeBound margin : ℝ, 0 ≤ cubeBound ∧ 0 < margin ∧
      letI : MeasurableSpace
        (BinaryPairwiseReport (theorem6Alternative (theorem6CopyCount beta))) := ⊤
      ∀ᵐ path ∂AppliedModelingLib.finitePMFIidPathMeasure
          (theorem12OneComparisonReportLaw
            (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
            (theorem6Preference beta)),
        ∀ᶠ horizon : ℕ in Filter.atTop,
          ∀ score : ScoreVector (theorem6Alternative (theorem6CopyCount beta)),
            isPairwiseMLE
              (ofBinaryReports (AppliedModelingLib.finitePMFIidPathPrefix path horizon))
              sigmoidCDFLikePairwiseLink
              (theorem6A : theorem6Alternative (theorem6CopyCount beta)) score →
              margin ≤
                score (theorem6B : theorem6Alternative (theorem6CopyCount beta)) -
                  score (theorem6A : theorem6Alternative (theorem6CopyCount beta)) ∧
              ∀ alternative : theorem6Alternative (theorem6CopyCount beta),
                score alternative ≤ cubeBound := by
  classical
  let alternatives : Type := theorem6Alternative (theorem6CopyCount beta)
  letI : MeasurableSpace (BinaryPairwiseReport alternatives) := ⊤
  let reportLaw : PMF (BinaryPairwiseReport alternatives) :=
    theorem12OneComparisonReportLaw (uniformPMF alternatives) (theorem6Preference beta)
  let raw : ScoreVector alternatives → ℝ := theorem6RawPopulationLogLikelihood beta
  let reference : alternatives := theorem6A
  letI : Nonempty alternatives := ⟨theorem6A⟩
  letI : Nonempty (BinaryPairwiseReport alternatives) :=
    ⟨((theorem6A, theorem6A), true)⟩
  obtain ⟨threshold, hthreshold_pos, hthreshold_lt_one, hthreshold_mass⟩ :=
    theorem6_exists_directTrueFrequencyThreshold beta
  obtain ⟨bound, hbound_pos, htail_low, htail_high⟩ :=
    CDFLikePairwiseLink.exists_pos_tailBand sigmoidCDFLikePairwiseLink threshold
      hthreshold_pos hthreshold_lt_one
  obtain ⟨base, hbase_btl⟩ := theorem6_exists_populationMLE beta
  let cubeBound : ℝ :=
    max ((Fintype.card alternatives : ℝ) * bound) (scoreSupNorm reference base)
  let cube : Set (ScoreVector alternatives) :=
    Set.univ.pi (fun _ : alternatives => Set.Icc (-cubeBound) cubeBound)
  have hcube_compact : IsCompact cube := by
    dsimp [cube]
    exact isCompact_univ_pi fun _ : alternatives => isCompact_Icc
  have hcubeBound_nonneg : 0 ≤ cubeBound := by
    apply le_trans (mul_nonneg (Nat.cast_nonneg _) hbound_pos.le) (le_max_left _ _)
  have hbase_raw : ∀ candidate : ScoreVector alternatives, raw candidate ≤ raw base := by
    dsimp [raw, alternatives]
    exact
      (theorem6_rawPopulation_globalMax_iff_bradleyTerryFit_globalMax beta base).mpr hbase_btl
  have hbase_cube : base ∈ cube := by
    change ∀ alternative : alternatives, alternative ∈ Set.univ →
      -cubeBound ≤ base alternative ∧ base alternative ≤ cubeBound
    intro alternative _
    apply abs_le.mp
    exact (abs_score_le_scoreSupNorm reference alternative base).trans (le_max_right _ _)
  have hscore_cube : ∀ {horizon : ℕ}
      (horizon_pos : 0 < horizon)
      (sample : Fin horizon → BinaryPairwiseReport alternatives)
      (hgood : ¬ ∃ atom,
        atom ∈ directedTrueBinaryReports alternatives ∧
        (Probability.empiricalCount sample atom : ℝ) ≤ (horizon : ℝ) * threshold)
      (score : ScoreVector alternatives),
      isPairwiseMLE (ofBinaryReports sample) sigmoidCDFLikePairwiseLink reference score →
        score ∈ cube := by
    intro horizon horizon_pos sample hgood score hmle
    have hscore_bound : scoreSupNorm reference score ≤
        (Fintype.card alternatives : ℝ) * bound := by
      dsimp [alternatives] at hgood ⊢
      exact theorem6_scoreSupNorm_le_of_not_directTrueFrequencyFailure
        horizon_pos hthreshold_pos sample hgood theorem6A score hmle hbound_pos htail_low htail_high
    change ∀ alternative : alternatives, alternative ∈ Set.univ →
      -cubeBound ≤ score alternative ∧ score alternative ≤ cubeBound
    intro alternative _
    apply abs_le.mp
    exact (abs_score_le_scoreSupNorm reference alternative score).trans
      (hscore_bound.trans (le_max_left _ _))
  let populationMaximizers : Set (ScoreVector alternatives) :=
    cube ∩ {score | raw base ≤ raw score}
  have hpopulationMaximizers_compact : IsCompact populationMaximizers := by
    dsimp [populationMaximizers]
    exact hcube_compact.inter_right (isClosed_le continuous_const
      (by exact continuous_theorem6RawPopulationLogLikelihood beta))
  have hpopulationMaximizers_nonempty : populationMaximizers.Nonempty := by
    refine ⟨base, hbase_cube, ?_⟩
    dsimp
    exact le_rfl
  let scoreGap : ScoreVector alternatives → ℝ := fun score =>
    score (theorem6B : alternatives) - score (theorem6A : alternatives)
  have hscoreGap_continuous : Continuous scoreGap := by
    dsimp [scoreGap]
    exact (continuous_apply (theorem6B : alternatives)).sub
      (continuous_apply (theorem6A : alternatives))
  obtain ⟨populationMargin, hpopulationMargin_pos, hpopulationMargin_le⟩ :=
    AppliedModelingLib.Optimization.exists_pos_le_on_isCompact_of_continuous_pos
      hpopulationMaximizers_compact hpopulationMaximizers_nonempty hscoreGap_continuous (by
        intro score hscore
        have hscore_btl_max : ∀ candidate,
            bradleyTerryFitObjective (theorem6Preference beta)
              (uniformPMF alternatives) candidate ≤
            bradleyTerryFitObjective (theorem6Preference beta)
              (uniformPMF alternatives) score := by
          apply (theorem6_rawPopulation_globalMax_iff_bradleyTerryFit_globalMax beta score).mp
          intro candidate
          exact (hbase_raw candidate).trans hscore.2
        have horder := theorem6_globalMLE_rewardA_lt_rewardB hbeta score (by
          simpa only [alternatives] using hscore_btl_max)
        dsimp [scoreGap]
        linarith)
  let margin : ℝ := populationMargin / 2
  have hmargin_pos : 0 < margin := by dsimp [margin]; linarith
  let bad : Set (ScoreVector alternatives) := cube ∩ {score | scoreGap score ≤ margin}
  have hbad_compact : IsCompact bad := by
    dsimp [bad]
    exact hcube_compact.inter_right (isClosed_le hscoreGap_continuous continuous_const)
  have hbad_subset : bad ⊆ cube := by
    intro score hscore
    exact hscore.1
  have hraw_continuous : Continuous raw := by
    dsimp [raw, alternatives]
    exact continuous_theorem6RawPopulationLogLikelihood beta
  have hbad_strict : ∀ score, score ∈ bad → raw score < raw base := by
    intro score hscore
    by_contra hnot
    have hbase_le : raw base ≤ raw score := le_of_not_gt hnot
    have hscore_population : score ∈ populationMaximizers := ⟨hscore.1, hbase_le⟩
    have hmargin_bound := hpopulationMargin_le score hscore_population
    have hbad_gap : scoreGap score ≤ margin := hscore.2
    dsimp [margin] at hbad_gap
    linarith
  obtain ⟨tolerance, htolerance_pos, hstable⟩ :=
    AppliedModelingLib.Optimization.exists_pos_uniformArgmaxTolerance_not_mem_of_compact_of_strictSeparation
      hbad_compact hbad_subset hraw_continuous.continuousOn
      ⟨hbase_cube, fun candidate _ => hbase_raw candidate⟩ hbad_strict
  let reportScore : ScoreVector alternatives → BinaryPairwiseReport alternatives → ℝ :=
    fun score report =>
      PairwiseCountDataset.binaryReportLogLikelihoodTerm Real.sigmoid score report
  have hreportScore_continuous : ∀ report,
      Continuous (fun score : ScoreVector alternatives => reportScore score report) := by
    intro report
    exact PairwiseCountDataset.continuous_binaryReportLogLikelihoodTerm_sigmoid report
  have hdirect :=
    AppliedModelingLib.ae_eventually_finitePMFIidPath_not_finiteIidFiniteSetLowerFrequencyEvent
      reportLaw (directedTrueBinaryReports alternatives) threshold (by
        intro atom hatom
        rcases Finset.mem_image.mp hatom with ⟨pair, hpair, rfl⟩
        exact hthreshold_mass pair.1 pair.2 (Finset.mem_filter.mp hpair).2)
  have huniform := AppliedModelingLib.ae_eventually_finitePMFIidPath_uniformScoreDeviation
    reportLaw reportScore cube hcube_compact hreportScore_continuous tolerance htolerance_pos
  refine ⟨cubeBound, margin, hcubeBound_nonneg, hmargin_pos, ?_⟩
  filter_upwards [hdirect, huniform] with path pathDirect pathUniform
  filter_upwards [pathDirect, pathUniform, Filter.eventually_ge_atTop 1] with
      horizon hpathDirect hpathUniform hpositive
  intro score hmle
  let sample : Fin horizon → BinaryPairwiseReport alternatives :=
    AppliedModelingLib.finitePMFIidPathPrefix path horizon
  have hscore_mem : score ∈ cube := by
    have hgood : ¬ ∃ atom,
        atom ∈ directedTrueBinaryReports alternatives ∧
        (Probability.empiricalCount sample atom : ℝ) ≤ (horizon : ℝ) * threshold := by
      exact hpathDirect
    exact hscore_cube hpositive sample hgood score (by simpa [sample, reference] using hmle)
  have horizon_real_pos : (0 : ℝ) < horizon := by exact_mod_cast hpositive
  let empirical : ScoreVector alternatives → ℝ := fun candidate =>
    pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid candidate / (horizon : ℝ)
  have hempirical_uniform : ∀ candidate, candidate ∈ cube →
      |empirical candidate - raw candidate| ≤ tolerance := by
    intro candidate hcandidate
    have hraw_bound :
        |Probability.finiteIidScoreSum (reportScore candidate) sample -
            (horizon : ℝ) * pmfExp reportLaw (reportScore candidate)| ≤
          (horizon : ℝ) * tolerance := by
      simpa [sample] using hpathUniform candidate hcandidate
    have hraw_bound' :
        |pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid candidate -
            (horizon : ℝ) * raw candidate| ≤ (horizon : ℝ) * tolerance := by
      dsimp [reportScore, raw, alternatives] at hraw_bound ⊢
      unfold Probability.finiteIidScoreSum at hraw_bound
      rw [← PairwiseCountDataset.pairwiseLogLikelihood_ofBinaryReports_eq_sum
        sample Real.sigmoid candidate] at hraw_bound
      exact hraw_bound
    have hempirical_eq : empirical candidate - raw candidate =
        (pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid candidate -
          (horizon : ℝ) * raw candidate) / (horizon : ℝ) := by
      dsimp [empirical]
      field_simp
    rw [hempirical_eq, abs_div, abs_of_pos horizon_real_pos]
    exact (div_le_iff₀ horizon_real_pos).mpr (by simpa [mul_comm] using hraw_bound')
  have hempirical_max : IsMaxOn empirical cube score := by
    intro candidate _
    dsimp [empirical]
    apply (div_le_div_iff₀ horizon_real_pos horizon_real_pos).mpr
    exact mul_le_mul_of_nonneg_right
      (isPairwiseMLE_global_max (ofBinaryReports sample)
        sigmoidCDFLikePairwiseLink reference score (by simpa [sample, reference] using hmle)
          candidate)
      horizon_real_pos.le
  have hnot_bad := hstable empirical score hempirical_uniform hscore_mem hempirical_max
  constructor
  · apply le_of_not_ge
    intro hnot
    apply hnot_bad
    exact ⟨hscore_mem, hnot⟩
  · intro alternative
    dsimp [cube] at hscore_mem
    exact (Set.mem_pi.mp hscore_mem alternative (Set.mem_univ alternative)).2

set_option maxHeartbeats 800000 in
/-- The finite-report completion of Appendix F.2.  For one fixed large-scale
instance, a deterministic positive reference mass works for every sufficiently
long literal iid comparison sample.  Every attained finite logistic MLE then
admits the two unit-KL policy optimizers whose welfare distortion is at least
`exp(beta) / (44 * beta)`. -/
theorem theorem6_exists_ae_eventually_finiteMLE_constrainedPolicies_exp_distortion_lower
    {beta : ℝ} (hbeta_ten : 10 ≤ beta) (hbeta_hundred : Real.log 100 ≤ beta) :
    ∃ (eta : ℝ) (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1),
      letI : MeasurableSpace
        (BinaryPairwiseReport (theorem6Alternative (theorem6CopyCount beta))) := ⊤
      ∀ᵐ path ∂AppliedModelingLib.finitePMFIidPathMeasure
          (theorem12OneComparisonReportLaw
            (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
            (theorem6Preference beta)),
        ∀ᶠ horizon : ℕ in Filter.atTop,
          ∀ reward : ScoreVector (theorem6Alternative (theorem6CopyCount beta)),
            isPairwiseMLE
              (ofBinaryReports (AppliedModelingLib.finitePMFIidPathPrefix path horizon))
              sigmoidCDFLikePairwiseLink
              (theorem6A : theorem6Alternative (theorem6CopyCount beta)) reward →
              ∃ rewardPolicy welfarePolicy : PMF
                  (theorem6Alternative (theorem6CopyCount beta)),
                finiteKLDivergence rewardPolicy
                    (theorem6Reference (theorem6Epsilon eta)
                      (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
                      (theorem6CopyCount_pos beta)) ≤ 1 ∧
                (∀ other : PMF (theorem6Alternative (theorem6CopyCount beta)),
                  finiteKLDivergence other
                      (theorem6Reference (theorem6Epsilon eta)
                        (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
                        (theorem6CopyCount_pos beta)) ≤ 1 →
                    pmfExp other reward ≤ pmfExp rewardPolicy reward) ∧
                finiteKLDivergence welfarePolicy
                    (theorem6Reference (theorem6Epsilon eta)
                      (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
                      (theorem6CopyCount_pos beta)) ≤ 1 ∧
                (∀ other : PMF (theorem6Alternative (theorem6CopyCount beta)),
                  finiteKLDivergence other
                      (theorem6Reference (theorem6Epsilon eta)
                        (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
                        (theorem6CopyCount_pos beta)) ≤ 1 →
                    pmfExp other (theorem6Welfare beta) ≤
                      pmfExp welfarePolicy (theorem6Welfare beta)) ∧
                Real.exp beta / (44 * beta) ≤
                  pmfExp welfarePolicy (theorem6Welfare beta) /
                    pmfExp rewardPolicy (theorem6Welfare beta) := by
  classical
  let alternatives : Type := theorem6Alternative (theorem6CopyCount beta)
  letI : MeasurableSpace (BinaryPairwiseReport alternatives) := ⊤
  obtain ⟨cubeBound, margin, hcubeBound_nonneg, hmargin_pos, hmargin_ae⟩ :=
    theorem6_exists_uniformFiniteMLE_scoreMargin (by linarith : 2 ≤ beta)
  let scoreThreshold : ℝ := Real.exp (-beta) / (1 + cubeBound / margin)
  have hscore_den_pos : 0 < 1 + cubeBound / margin := by
    have hquot_nonneg : 0 ≤ cubeBound / margin :=
      div_nonneg hcubeBound_nonneg hmargin_pos.le
    linarith
  have hscoreThreshold_pos : 0 < scoreThreshold := by
    dsimp [scoreThreshold]
    exact div_pos (Real.exp_pos _) hscore_den_pos
  have hwelfare_gap_pos :
      0 < (1 - theorem6MinorityMass beta) / beta - theorem6MinorityMass beta := by
    have horder := theorem6_populationAverageUtility_b_lt_a
      (copies := theorem6CopyCount beta) hbeta_ten
    rw [theorem6_populationAverageUtility_a,
      theorem6_populationAverageUtility_b] at horder
    linarith
  let welfareThreshold : ℝ := Real.exp (-beta) /
    (1 + (((1 - theorem6MinorityMass beta) / beta - theorem6MinorityMass beta)⁻¹))
  have hwelfare_den_pos : 0 <
      1 + (((1 - theorem6MinorityMass beta) / beta - theorem6MinorityMass beta)⁻¹) := by
    exact add_pos_of_pos_of_nonneg zero_lt_one (inv_nonneg.mpr hwelfare_gap_pos.le)
  have hwelfareThreshold_pos : 0 < welfareThreshold := by
    dsimp [welfareThreshold]
    exact div_pos (Real.exp_pos _) hwelfare_den_pos
  let eta : ℝ := min 1 (min scoreThreshold welfareThreshold) / 2
  have hmin_pos : 0 < min 1 (min scoreThreshold welfareThreshold) := by
    exact lt_min zero_lt_one (lt_min hscoreThreshold_pos hwelfareThreshold_pos)
  have heta_pos : 0 < eta := by
    dsimp [eta]
    positivity
  have heta_le_min : eta ≤ min 1 (min scoreThreshold welfareThreshold) := by
    dsimp [eta]
    nlinarith
  have heta_le_one : eta ≤ 1 := heta_le_min.trans (min_le_left _ _)
  have heta_score : eta ≤ scoreThreshold :=
    heta_le_min.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heta_welfare : eta ≤ welfareThreshold :=
    heta_le_min.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨eta, heta_pos, heta_le_one, ?_⟩
  filter_upwards [hmargin_ae] with path hpath
  filter_upwards [hpath] with horizon hmargin
  intro reward hmle
  let reference : PMF alternatives :=
    theorem6Reference (theorem6Epsilon eta)
      (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
      (theorem6CopyCount_pos beta)
  obtain ⟨rewardPolicy, hreward_feasible, hreward_max⟩ :=
    exists_finiteKL_maximizer reference 1 (by norm_num) reward
  obtain ⟨welfarePolicy, hwelfare_feasible, hwelfare_max⟩ :=
    exists_finiteKL_maximizer reference 1 (by norm_num) (theorem6Welfare beta)
  have hgap : margin ≤ reward (theorem6B : alternatives) := by
    have hraw_gap := (hmargin reward (by simpa [alternatives] using hmle)).1
    rw [hmle.1, sub_zero] at hraw_gap
    exact hraw_gap
  have hclone_upper : ∀ copy : Fin (theorem6CopyCount beta),
      reward (theorem6C copy : alternatives) ≤ cubeBound := by
    intro copy
    exact (hmargin reward (by simpa [alternatives] using hmle)).2 (theorem6C copy)
  have hreward_bad := theorem6_constrainedScorePolicy_badMass_le_exp_neg_of_zero_a_bGap_cloneUpper
    heta_pos heta_le_one (theorem6CopyCount_pos beta) reward cubeBound margin
    (by simpa [alternatives] using hmle.1) hmargin_pos hgap hcubeBound_nonneg hclone_upper
    rewardPolicy (by simpa [reference, alternatives] using hreward_feasible)
    (by simpa [reference, alternatives] using hreward_max) (by
      dsimp [scoreThreshold] at heta_score
      exact heta_score)
  have hwelfare_bad := theorem6_constrainedWelfarePolicy_badMass_le_exp_neg
    heta_pos heta_le_one (theorem6CopyCount_pos beta) hbeta_ten welfarePolicy
    (by simpa [reference, alternatives] using hwelfare_feasible)
    (by simpa [reference, alternatives] using hwelfare_max) (by
      dsimp [welfareThreshold] at heta_welfare
      exact heta_welfare)
  refine ⟨rewardPolicy, welfarePolicy,
    (by simpa [reference, alternatives] using hreward_feasible),
    (by simpa [reference, alternatives] using hreward_max),
    (by simpa [reference, alternatives] using hwelfare_feasible),
    (by simpa [reference, alternatives] using hwelfare_max), ?_⟩
  exact (theorem6_populationRatio_lower_exp_div hbeta_ten hbeta_hundred).trans
    (theorem6_policyWelfare_ratio_lower_of_badMass hbeta_ten rewardPolicy welfarePolicy
      hreward_bad hwelfare_bad)

end GolzHaghtalabYang2025Distortion
