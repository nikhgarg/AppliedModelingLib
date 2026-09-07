import AppliedModelingLib.GameTheory.PreferenceGame.NashMD

/-!
# Strict monotonicity for finite KL-regularized preference games

This module gives a direct finite-sum treatment of the pseudo-gradient used in
the Appendix-E uniqueness argument for KL-regularized preference games.  It
proves that the preference terms cancel by complementarity and that the log
terms are the corresponding symmetric KL divergences.
-/

open scoped BigOperators

namespace AppliedModelingLib.GameTheory.PreferenceGame

open Learning.HumanFeedback

theorem pmf_mass_difference_sum_zero
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (first second : PMF Response) :
    (∑ response : Response, ((first response).toReal - (second response).toReal)) = 0 := by
  rw [Finset.sum_sub_distrib, pmfToRealSum, pmfToRealSum]
  norm_num

/-- The log part of a finite gradient pairing is the symmetric KL sum. -/
theorem pmf_log_difference_pairing_eq_symmetric_kl
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (first second : PMF Response) :
    (∑ response : Response,
      ((first response).toReal - (second response).toReal) *
        (Real.log (first response).toReal - Real.log (second response).toReal)) =
      finiteKLDivergence first second + finiteKLDivergence second first := by
  unfold finiteKLDivergence
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro response _
  ring

theorem preference_score_difference_pairing_cancel
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference Context Response) (context : Context)
    (first second third fourth : FinitePolicy Context Response) :
    (∑ response : Response,
      ((first context response).toReal - (second context response).toReal) *
        (responsePreferenceScore preference third context response -
          responsePreferenceScore preference fourth context response)) +
      ∑ response : Response,
        ((third context response).toReal - (fourth context response).toReal) *
          (responsePreferenceScore preference first context response -
            responsePreferenceScore preference second context response) = 0 := by
  unfold responsePreferenceScore pmfExp
  simp_rw [← Finset.sum_sub_distrib]
  simp_rw [Finset.mul_sum]
  simp_rw [mul_sub]
  calc
    _ =
        (∑ response : Response, ∑ opponent : Response,
          ((first context response).toReal - (second context response).toReal) *
            ((third context opponent).toReal - (fourth context opponent).toReal) *
              preference.prob context response opponent) +
        ∑ response : Response, ∑ opponent : Response,
          ((third context response).toReal - (fourth context response).toReal) *
            ((first context opponent).toReal - (second context opponent).toReal) *
                preference.prob context response opponent := by
          apply congrArg₂ (· + ·)
          · apply Finset.sum_congr rfl
            intro response _
            apply Finset.sum_congr rfl
            intro opponent _
            ring
          · apply Finset.sum_congr rfl
            intro response _
            apply Finset.sum_congr rfl
            intro opponent _
            ring
    _ = 0 := by
      have hswap :
          (∑ response : Response, ∑ opponent : Response,
            ((third context response).toReal - (fourth context response).toReal) *
              ((first context opponent).toReal - (second context opponent).toReal) *
                preference.prob context response opponent) =
          ∑ response : Response, ∑ opponent : Response,
            ((first context response).toReal - (second context response).toReal) *
              ((third context opponent).toReal - (fourth context opponent).toReal) *
                preference.prob context opponent response := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro response _
            apply Finset.sum_congr rfl
            intro opponent _
            ring
      rw [hswap]
      simp_rw [← Finset.sum_add_distrib]
      calc
        _ = ∑ response : Response, ∑ opponent : Response,
            ((first context response).toReal - (second context response).toReal) *
              ((third context opponent).toReal - (fourth context opponent).toReal) *
                (preference.prob context response opponent +
                  preference.prob context opponent response) := by
              apply Finset.sum_congr rfl
              intro response _
              apply Finset.sum_congr rfl
              intro opponent _
              ring
        _ = ∑ response : Response, ∑ opponent : Response,
            ((first context response).toReal - (second context response).toReal) *
              ((third context opponent).toReal - (fourth context opponent).toReal) := by
              simp_rw [preference.complementary context]
              simp
        _ = (∑ response : Response,
              ((first context response).toReal - (second context response).toReal)) *
            ∑ opponent : Response,
              ((third context opponent).toReal - (fourth context opponent).toReal) := by
              rw [Finset.sum_mul_sum]
        _ = 0 := by
              rw [pmf_mass_difference_sum_zero (first context) (second context),
                pmf_mass_difference_sum_zero (third context) (fourth context)]
              norm_num

/-- The Appendix-E own-policy derivative, in the finite policy model. -/
noncomputable def regularizedPreferencePseudoGradient
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference Context Response)
    (reference policy opponent : FinitePolicy Context Response)
    (klRegularization : ℝ) : Context → Response → ℝ :=
  fun context response =>
    responsePreferenceScore preference opponent context response -
      klRegularization *
        (Real.log (policy context response).toReal - Real.log (reference context response).toReal) - 1

/-- The finite directional pairing used by the Appendix-E variational inequality. -/
noncomputable def policyGradientDifferencePairing
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (first second : FinitePolicy Context Response)
    (firstGradient secondGradient : Context → Response → ℝ) : ℝ :=
  ∑ context : Context, (contextLaw context).toReal *
    ∑ response : Response, ((first context response).toReal - (second context response).toReal) *
      (firstGradient context response - secondGradient context response)

theorem regularizedPreferencePseudoGradient_pairing_decompose
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference Context Response)
    (reference first second third fourth : FinitePolicy Context Response)
    (klRegularization : ℝ) (context : Context) :
    (∑ response : Response, ((first context response).toReal - (second context response).toReal) *
      (regularizedPreferencePseudoGradient preference reference first third klRegularization context response -
        regularizedPreferencePseudoGradient preference reference second fourth klRegularization context response)) =
      (∑ response : Response, ((first context response).toReal - (second context response).toReal) *
        (responsePreferenceScore preference third context response -
          responsePreferenceScore preference fourth context response)) -
        klRegularization *
          ∑ response : Response, ((first context response).toReal - (second context response).toReal) *
            (Real.log (first context response).toReal - Real.log (second context response).toReal) := by
  unfold regularizedPreferencePseudoGradient
  calc
    _ = ∑ response : Response,
        (((first context response).toReal - (second context response).toReal) *
            (responsePreferenceScore preference third context response -
              responsePreferenceScore preference fourth context response) -
          klRegularization * ((first context response).toReal - (second context response).toReal) *
            (Real.log (first context response).toReal - Real.log (second context response).toReal)) := by
          apply Finset.sum_congr rfl
          intro response _
          ring
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      congr 1
      calc
        ∑ response : Response,
            klRegularization * ((first context response).toReal - (second context response).toReal) *
              (Real.log (first context response).toReal - Real.log (second context response).toReal) =
            ∑ response : Response,
              klRegularization *
                (((first context response).toReal - (second context response).toReal) *
                  (Real.log (first context response).toReal - Real.log (second context response).toReal)) := by
                apply Finset.sum_congr rfl
                intro response _
                ring
        _ = _ := (Finset.mul_sum _ _ _).symm

theorem regularizedPreferencePseudoGradient_pair_sum_eq_negative_symmetricKL
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference Context Response)
    (reference first second third fourth : FinitePolicy Context Response)
    (klRegularization : ℝ) (context : Context) :
    (∑ response : Response, ((first context response).toReal - (second context response).toReal) *
      (regularizedPreferencePseudoGradient preference reference first third klRegularization context response -
        regularizedPreferencePseudoGradient preference reference second fourth klRegularization context response)) +
      ∑ response : Response, ((third context response).toReal - (fourth context response).toReal) *
        (regularizedPreferencePseudoGradient preference reference third first klRegularization context response -
          regularizedPreferencePseudoGradient preference reference fourth second klRegularization context response) =
      -klRegularization *
        (finiteKLDivergence (first context) (second context) +
          finiteKLDivergence (second context) (first context) +
          finiteKLDivergence (third context) (fourth context) +
          finiteKLDivergence (fourth context) (third context)) := by
  rw [regularizedPreferencePseudoGradient_pairing_decompose,
    regularizedPreferencePseudoGradient_pairing_decompose]
  have hscore := preference_score_difference_pairing_cancel preference context
    first second third fourth
  have hfirst := pmf_log_difference_pairing_eq_symmetric_kl
    (first context) (second context)
  have hthird := pmf_log_difference_pairing_eq_symmetric_kl
    (third context) (fourth context)
  rw [hfirst, hthird]
  linarith

/-- A full-support context law preserves the strict positivity of finite KL. -/
theorem contextAveragedPolicyKLDivergence_pos_of_ne
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (first second : FinitePolicy Context Response)
    (hcontextLaw : PMFFullSupport contextLaw) (hsecond : PolicyFullSupport second)
    (hne : first ≠ second) :
    0 < contextAveragedPolicyKLDivergence contextLaw first second := by
  obtain ⟨witness, hwitness⟩ : ∃ context, first context ≠ second context := by
    by_contra hnot
    push Not at hnot
    exact hne (finitePolicy_ext hnot)
  unfold contextAveragedPolicyKLDivergence pointwisePolicyKLDivergence pmfExp
  refine Finset.sum_pos' ?_ ?_
  · intro context _
    exact mul_nonneg ENNReal.toReal_nonneg
      (finiteKLDivergence_nonneg (first context) (second context) (hsecond context))
  · exact ⟨witness, Finset.mem_univ _,
      mul_pos (hcontextLaw witness)
        (finiteKLDivergence_pos_of_ne (first witness) (second witness)
          (hsecond witness) hwitness)⟩

/-- The finite version of the Appendix-E strict-monotonicity left side. -/
noncomputable def regularizedPreferencePseudoGradientStrictMonotonicity
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (reference first second third fourth : FinitePolicy Context Response)
    (klRegularization : ℝ) : ℝ :=
  policyGradientDifferencePairing contextLaw first second
      (regularizedPreferencePseudoGradient preference reference first third klRegularization)
      (regularizedPreferencePseudoGradient preference reference second fourth klRegularization) +
    policyGradientDifferencePairing contextLaw third fourth
      (regularizedPreferencePseudoGradient preference reference third first klRegularization)
      (regularizedPreferencePseudoGradient preference reference fourth second klRegularization)

theorem regularizedPreferencePseudoGradientStrictMonotonicity_eq
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (reference first second third fourth : FinitePolicy Context Response)
    (klRegularization : ℝ) :
    regularizedPreferencePseudoGradientStrictMonotonicity
      contextLaw preference reference first second third fourth klRegularization =
      -klRegularization *
        (contextAveragedPolicyKLDivergence contextLaw first second +
          contextAveragedPolicyKLDivergence contextLaw second first +
          contextAveragedPolicyKLDivergence contextLaw third fourth +
          contextAveragedPolicyKLDivergence contextLaw fourth third) := by
  unfold regularizedPreferencePseudoGradientStrictMonotonicity policyGradientDifferencePairing
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ context : Context, (contextLaw context).toReal *
        ((∑ response : Response, ((first context response).toReal - (second context response).toReal) *
          (regularizedPreferencePseudoGradient preference reference first third
              klRegularization context response -
            regularizedPreferencePseudoGradient preference reference second fourth
              klRegularization context response)) +
          ∑ response : Response, ((third context response).toReal - (fourth context response).toReal) *
            (regularizedPreferencePseudoGradient preference reference third first
                klRegularization context response -
              regularizedPreferencePseudoGradient preference reference fourth second
                klRegularization context response)) := by
          apply Finset.sum_congr rfl
          intro context _
          ring
    _ = ∑ context : Context, (contextLaw context).toReal *
        (-klRegularization *
          (finiteKLDivergence (first context) (second context) +
            finiteKLDivergence (second context) (first context) +
            finiteKLDivergence (third context) (fourth context) +
            finiteKLDivergence (fourth context) (third context))) := by
          apply Finset.sum_congr rfl
          intro context _
          rw [regularizedPreferencePseudoGradient_pair_sum_eq_negative_symmetricKL]
    _ = _ := by
      unfold contextAveragedPolicyKLDivergence pointwisePolicyKLDivergence pmfExp
      calc
        _ = ∑ context : Context, -klRegularization *
            ((contextLaw context).toReal *
              (finiteKLDivergence (first context) (second context) +
                finiteKLDivergence (second context) (first context) +
                finiteKLDivergence (third context) (fourth context) +
                finiteKLDivergence (fourth context) (third context))) := by
              apply Finset.sum_congr rfl
              intro context _
              ring
        _ = -klRegularization * ∑ context : Context,
            (contextLaw context).toReal *
              (finiteKLDivergence (first context) (second context) +
                finiteKLDivergence (second context) (first context) +
                finiteKLDivergence (third context) (fourth context) +
                finiteKLDivergence (fourth context) (third context)) := by
              exact (Finset.mul_sum _ _ _).symm
        _ = _ := by
              congr 1
              calc
                ∑ context : Context, (contextLaw context).toReal *
                    (finiteKLDivergence (first context) (second context) +
                      finiteKLDivergence (second context) (first context) +
                      finiteKLDivergence (third context) (fourth context) +
                      finiteKLDivergence (fourth context) (third context)) =
                    ∑ context : Context,
                      ((contextLaw context).toReal * finiteKLDivergence (first context) (second context) +
                        (contextLaw context).toReal * finiteKLDivergence (second context) (first context) +
                        (contextLaw context).toReal * finiteKLDivergence (third context) (fourth context) +
                        (contextLaw context).toReal * finiteKLDivergence (fourth context) (third context)) := by
                        apply Finset.sum_congr rfl
                        intro context _
                        ring
                _ = _ := by
                      simp only [Finset.sum_add_distrib]

/-- The Appendix-E pseudo-gradient is monotone in the source's sign convention. -/
theorem regularizedPreferencePseudoGradientStrictMonotonicity_nonpos
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (reference first second third fourth : FinitePolicy Context Response)
    (klRegularization : ℝ) (hklRegularization : 0 < klRegularization)
    (hfirst : PolicyFullSupport first) (hsecond : PolicyFullSupport second)
    (hthird : PolicyFullSupport third) (hfourth : PolicyFullSupport fourth) :
    regularizedPreferencePseudoGradientStrictMonotonicity
      contextLaw preference reference first second third fourth klRegularization ≤ 0 := by
  rw [regularizedPreferencePseudoGradientStrictMonotonicity_eq]
  have hfirstSecond := contextAveragedPolicyKLDivergence_nonneg contextLaw first second hsecond
  have hsecondFirst := contextAveragedPolicyKLDivergence_nonneg contextLaw second first hfirst
  have hthirdFourth := contextAveragedPolicyKLDivergence_nonneg contextLaw third fourth hfourth
  have hfourthThird := contextAveragedPolicyKLDivergence_nonneg contextLaw fourth third hthird
  nlinarith

/-- Equality in the finite Appendix-E display occurs only at the same policy pair. -/
theorem regularizedPreferencePseudoGradientStrictMonotonicity_eq_zero_iff
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (reference first second third fourth : FinitePolicy Context Response)
    (klRegularization : ℝ) (hcontextLaw : PMFFullSupport contextLaw)
    (hklRegularization : 0 < klRegularization)
    (hfirst : PolicyFullSupport first) (hsecond : PolicyFullSupport second)
    (hthird : PolicyFullSupport third) (hfourth : PolicyFullSupport fourth) :
    regularizedPreferencePseudoGradientStrictMonotonicity
      contextLaw preference reference first second third fourth klRegularization = 0 ↔
      first = second ∧ third = fourth := by
  constructor
  · intro hzero
    have hsum :
        contextAveragedPolicyKLDivergence contextLaw first second +
          contextAveragedPolicyKLDivergence contextLaw second first +
          contextAveragedPolicyKLDivergence contextLaw third fourth +
          contextAveragedPolicyKLDivergence contextLaw fourth third = 0 := by
      rw [regularizedPreferencePseudoGradientStrictMonotonicity_eq] at hzero
      nlinarith
    have hfirstSecond := contextAveragedPolicyKLDivergence_nonneg contextLaw first second hsecond
    have hsecondFirst := contextAveragedPolicyKLDivergence_nonneg contextLaw second first hfirst
    have hthirdFourth := contextAveragedPolicyKLDivergence_nonneg contextLaw third fourth hfourth
    have hfourthThird := contextAveragedPolicyKLDivergence_nonneg contextLaw fourth third hthird
    have hfirstEqSecond : first = second := by
      by_contra hne
      have hpositive := contextAveragedPolicyKLDivergence_pos_of_ne contextLaw first second
        hcontextLaw hsecond hne
      nlinarith
    have hthirdEqFourth : third = fourth := by
      by_contra hne
      have hpositive := contextAveragedPolicyKLDivergence_pos_of_ne contextLaw third fourth
        hcontextLaw hfourth hne
      nlinarith
    exact ⟨hfirstEqSecond, hthirdEqFourth⟩
  · rintro ⟨hfirstEqSecond, hthirdEqFourth⟩
    subst second
    subst fourth
    rw [regularizedPreferencePseudoGradientStrictMonotonicity_eq]
    have hfirstSelf : contextAveragedPolicyKLDivergence contextLaw first first = 0 := by
      unfold contextAveragedPolicyKLDivergence pointwisePolicyKLDivergence pmfExp
      simp
    have hthirdSelf : contextAveragedPolicyKLDivergence contextLaw third third = 0 := by
      unfold contextAveragedPolicyKLDivergence pointwisePolicyKLDivergence pmfExp
      simp
    rw [hfirstSelf, hthirdSelf]
    ring

end AppliedModelingLib.GameTheory.PreferenceGame
