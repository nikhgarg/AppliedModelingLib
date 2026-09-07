import AppliedModelingLib.Foundations.Probability.FiniteIidEmpiricalFrequency
import AppliedModelingLib.Foundations.Probability.IndependentProduct
import AppliedModelingLib.Foundations.Probability.UniformHoeffding

/-!
# Uniform finite-IID laws for bounded finite-alphabet score families

For a finite report alphabet, coordinatewise empirical-mass control gives a
uniform law of large numbers for any score family with one common absolute
bound.  Compactness arguments supply that bound in downstream optimization
applications.
-/

open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory

namespace AppliedModelingLib
namespace Probability

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A real-valued score family that is continuous in its parameter has one
common absolute bound on a compact parameter set when the report alphabet is
finite. -/
theorem exists_nonneg_uniform_abs_le_of_isCompact_finite
    {Θ : Type*} [TopologicalSpace Θ] (parameterSet : Set Θ)
    (hcompact : IsCompact parameterSet) (score : Θ → α → ℝ)
    (hcontinuous : ∀ atom, Continuous (fun parameter => score parameter atom)) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter ∈ parameterSet, ∀ atom,
      |score parameter atom| ≤ bound := by
  choose localBound hlocalBound using fun atom : α =>
    hcompact.bddAbove_image ((hcontinuous atom).abs.continuousOn)
  refine ⟨∑ atom : α, |localBound atom|, Finset.sum_nonneg fun atom _ => abs_nonneg _, ?_⟩
  intro parameter hparameter atom
  calc
    |score parameter atom| ≤ localBound atom :=
      hlocalBound atom ⟨parameter, hparameter, rfl⟩
    _ ≤ |localBound atom| := le_abs_self _
    _ ≤ ∑ other : α, |localBound other| := by
      exact Finset.univ.single_le_sum
        (fun other _ => abs_nonneg (localBound other)) (Finset.mem_univ atom)

/-- Coordinatewise empirical-mass control bounds the discrepancy between a
literal iid score sum and its population expectation, uniformly over any
bounded score family. -/
theorem abs_finiteIidScoreSum_sub_card_mul_pmfExp_le_of_massDeviation
    {ι Θ : Type*} [Fintype ι]
    (μ : PMF α) (score : Θ → α → ℝ) (sample : ι → α)
    (bound epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hbound : ∀ parameter atom, |score parameter atom| ≤ bound)
    (hdeviation : ∀ atom,
      |(empiricalCount sample atom : ℝ) - (Fintype.card ι : ℝ) * (μ atom).toReal| ≤
        (Fintype.card ι : ℝ) * epsilon)
    (parameter : Θ) :
    |finiteIidScoreSum (score parameter) sample -
        (Fintype.card ι : ℝ) * pmfExp μ (score parameter)| ≤
      (Fintype.card α : ℝ) * (Fintype.card ι : ℝ) * epsilon * bound := by
  have hrewrite :
      finiteIidScoreSum (score parameter) sample -
          (Fintype.card ι : ℝ) * pmfExp μ (score parameter) =
        ∑ atom : α,
          ((empiricalCount sample atom : ℝ) -
            (Fintype.card ι : ℝ) * (μ atom).toReal) * score parameter atom := by
    rw [finiteIidScoreSum_eq_sum_empiricalCount]
    unfold pmfExp
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro atom _
    ring
  rw [hrewrite]
  calc
    |∑ atom : α,
        ((empiricalCount sample atom : ℝ) -
          (Fintype.card ι : ℝ) * (μ atom).toReal) * score parameter atom| ≤
        ∑ atom : α,
          |((empiricalCount sample atom : ℝ) -
            (Fintype.card ι : ℝ) * (μ atom).toReal) * score parameter atom| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _atom : α,
        ((Fintype.card ι : ℝ) * epsilon) * bound := by
      apply Finset.sum_le_sum
      intro atom _
      rw [abs_mul]
      exact mul_le_mul (hdeviation atom) (hbound parameter atom)
        (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hepsilon)
    _ = (Fintype.card α : ℝ) * (Fintype.card ι : ℝ) * epsilon * bound := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

/-- The event that some member of a compact score family differs from its
population expectation by more than a prescribed linear-in-sample-size
amount. -/
def finiteIidUniformScoreDeviationEvent
    {Θ : Type*}
    (μ : PMF α) (score : Θ → α → ℝ) (parameterSet : Set Θ)
    (tolerance : ℝ) {n : ℕ} (sample : Fin n → α) : Prop :=
  ∃ parameter, parameter ∈ parameterSet ∧
    (n : ℝ) * tolerance <
      |finiteIidScoreSum (score parameter) sample -
        (n : ℝ) * pmfExp μ (score parameter)|

/-- The probability of the compact-family deviation event. -/
noncomputable def finiteIidUniformScoreDeviationFailure
    {Θ : Type*}
    (μ : PMF α) (score : Θ → α → ℝ) (parameterSet : Set Θ)
    (tolerance : ℝ) (n : ℕ) : ℝ :=
  by
    classical
    letI : DecidablePred
        (finiteIidUniformScoreDeviationEvent μ score parameterSet tolerance (n := n)) :=
      Classical.decPred _
    exact pmfProb (pmfProduct (Fin n) α μ)
      (finiteIidUniformScoreDeviationEvent μ score parameterSet tolerance (n := n))

/-- Unfolding form of the compact-family deviation event. -/
theorem finiteIidUniformScoreDeviationFailure_eq
    {Θ : Type*}
    (μ : PMF α) (score : Θ → α → ℝ) (parameterSet : Set Θ)
    (tolerance : ℝ) (n : ℕ) :
    finiteIidUniformScoreDeviationFailure μ score parameterSet tolerance n = by
      classical
      exact pmfProb (pmfProduct (Fin n) α μ)
        (finiteIidUniformScoreDeviationEvent μ score parameterSet tolerance (n := n)) := by
  rfl

/--
A finite parameter family of `[0,1]`-valued scores has the usual uniform
Hoeffding bound under a literal finite iid PMF sample.  The event may restrict
to an arbitrary parameter set, while the displayed cardinality is that of the
ambient finite family.  This transports the existing measure-theoretic
Hoeffding theorem through `pmfProduct`, rather than reproving concentration
for a paper-specific model.
-/
theorem finiteIidUniformScoreDeviationFailure_le_hoeffding
    {Θ : Type*} [Fintype Θ]
    (μ : PMF α) (score : Θ → α → ℝ) (parameterSet : Set Θ)
    (tolerance : ℝ) (n : ℕ) (hcount : 0 < n) (htolerance : 0 ≤ tolerance)
    (hscore : ∀ parameter atom, score parameter atom ∈ Set.Icc (0 : ℝ) 1) :
    finiteIidUniformScoreDeviationFailure μ score parameterSet tolerance n ≤
      (Fintype.card Θ : ℝ) * 2 * Real.exp (-2 * (n : ℝ) * tolerance ^ 2) := by
  classical
  letI : MeasurableSpace α := ⊤
  let observation : Θ → Fin n → (Fin n → α) → ℝ :=
    fun parameter index sample => score parameter (sample index)
  let law : Measure (Fin n → α) := (pmfProduct (Fin n) α μ).toMeasure
  have hindepependent : ∀ parameter, iIndepFun (observation parameter) law := by
    intro parameter
    change iIndepFun (fun index : Fin n => fun sample : Fin n → α =>
      score parameter (sample index)) (pmfProduct (Fin n) α μ).toMeasure
    simpa [Function.comp_def] using
      (iIndepFun_pmfProduct_eval μ).comp
        (fun _ atom => score parameter atom) (fun _ => measurable_of_finite _)
  have hmeasurable : ∀ parameter index, Measurable (observation parameter index) := by
    intro parameter index
    exact (measurable_of_finite _).comp (measurable_pi_apply index)
  have hbounded : ∀ parameter index, ∀ᵐ sample ∂law,
      observation parameter index sample ∈ Set.Icc (0 : ℝ) 1 := by
    intro parameter index
    exact Filter.Eventually.of_forall fun sample => hscore parameter (sample index)
  have hmean : ∀ parameter index,
      law[observation parameter index] = pmfExp μ (score parameter) := by
    intro parameter index
    change ∫ sample, score parameter (sample index) ∂(pmfProduct (Fin n) α μ).toMeasure = _
    rw [← pmfExp_eq_integral_toMeasure]
    exact pmfExp_pmfProduct_eval μ index (score parameter)
  have hhoeffding := finite_uniform_boundedIIndep_centeredSum_abs_upperTail_finset
    law observation hindepependent hmeasurable hbounded ((n : ℝ) * tolerance)
      (mul_nonneg (by exact_mod_cast hcount.le) htolerance)
  have hsubset : {sample : Fin n → α |
      finiteIidUniformScoreDeviationEvent μ score parameterSet tolerance sample} ⊆
      {sample | ∃ parameter,
        (n : ℝ) * tolerance ≤
          |∑ index, (observation parameter index sample -
            law[observation parameter index])|} := by
    intro sample hfailure
    rcases hfailure with ⟨parameter, _, hdeviation⟩
    refine ⟨parameter, ?_⟩
    change (n : ℝ) * tolerance ≤
      |∑ index, (score parameter (sample index) -
        law[observation parameter index])|
    simp_rw [hmean parameter]
    have hcentered :
        (∑ index, (score parameter (sample index) - pmfExp μ (score parameter))) =
          finiteIidScoreSum (score parameter) sample -
            (n : ℝ) * pmfExp μ (score parameter) := by
      unfold finiteIidScoreSum
      rw [Finset.sum_sub_distrib]
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hcentered]
    unfold finiteIidScoreSum at hdeviation
    exact le_of_lt hdeviation
  rw [finiteIidUniformScoreDeviationFailure_eq, pmfProb_eq_toMeasure_real]
  calc
    law.real {sample | finiteIidUniformScoreDeviationEvent μ score parameterSet tolerance sample} ≤
        law.real {sample | ∃ parameter,
          (n : ℝ) * tolerance ≤
            |∑ index, (observation parameter index sample -
              law[observation parameter index])|} :=
      measureReal_mono hsubset
    _ ≤ (Fintype.card Θ : ℝ) * 2 *
        Real.exp (-((n : ℝ) * tolerance) ^ 2 /
          (2 * (Fintype.card (Fin n) : ℝ) * (1 / 4 : ℝ))) := hhoeffding
    _ = (Fintype.card Θ : ℝ) * 2 * Real.exp (-2 * (n : ℝ) * tolerance ^ 2) := by
      rw [Fintype.card_fin, boundedHoeffdingExponent_eq_neg_two_mul n hcount tolerance]

/--
Finite-alphabet empirical masses have a direct Hoeffding bound.  The input
`tolerance` is strictly below the event threshold `epsilon`: this visible
slack converts the non-strict mass-deviation event to the strict uniform-score
event controlled by `finiteIidUniformScoreDeviationFailure_le_hoeffding`.
-/
theorem finiteIidAnyMassDeviationFailure_le_hoeffding
    (μ : PMF α) (epsilon tolerance : ℝ) (n : ℕ)
    (hcount : 0 < n) (htolerance : 0 ≤ tolerance) (htolerance_lt : tolerance < epsilon) :
    finiteIidAnyMassDeviationFailure μ epsilon n ≤
      (Fintype.card α : ℝ) * 2 * Real.exp (-2 * (n : ℝ) * tolerance ^ 2) := by
  classical
  letI : TopologicalSpace α := ⊤
  let indicator : α → α → ℝ := fun atom outcome => if outcome = atom then 1 else 0
  have hindicator : ∀ atom outcome, indicator atom outcome ∈ Set.Icc (0 : ℝ) 1 := by
    intro atom outcome
    by_cases h : outcome = atom <;> simp [indicator, h]
  have huniform := finiteIidUniformScoreDeviationFailure_le_hoeffding
    μ indicator Set.univ tolerance n hcount htolerance hindicator
  refine (pmfProb_le_of_imp (pmfProduct (Fin n) α μ) _ _ ?_).trans huniform
  intro sample hfailure
  rcases hfailure with ⟨atom, hmass⟩
  refine ⟨atom, Set.mem_univ _, ?_⟩
  have hsum : finiteIidScoreSum (indicator atom) sample =
      (empiricalCount sample atom : ℝ) := by
    simpa [indicator] using finiteIidScoreSum_indicator_sub_eq sample atom 0
  have hmean : pmfExp μ (indicator atom) = (μ atom).toReal := by
    simpa [indicator] using pmfExp_indicator_sub_eq μ atom 0
  rw [hsum, hmean]
  have hcount_real : 0 < (n : ℝ) := by exact_mod_cast hcount
  exact lt_of_lt_of_le
    (mul_lt_mul_of_pos_left htolerance_lt hcount_real) hmass

/--
Finite-alphabet empirical-mass concentration controls an arbitrarily indexed
bounded score family without a union bound over its parameter type.  This is
useful when a one-dimensional tuning parameter ranges over a continuum but
every score is evaluated on the same finite outcome alphabet.
-/
theorem finiteIidUniformScoreDeviationFailure_le_mass_hoeffding_of_abs_le
    {Θ : Type*}
    (μ : PMF α) (score : Θ → α → ℝ) (parameterSet : Set Θ)
    (tolerance bound : ℝ) (n : ℕ) (hcount : 0 < n)
    (hcard : 0 < (Fintype.card α : ℝ)) (hbound : 0 < bound)
    (htolerance : 0 < tolerance)
    (hscore : ∀ parameter atom, |score parameter atom| ≤ bound) :
    finiteIidUniformScoreDeviationFailure μ score parameterSet tolerance n ≤
      (Fintype.card α : ℝ) * 2 *
        Real.exp (-((n : ℝ) * tolerance ^ 2 /
          (2 * ((Fintype.card α : ℝ) * bound) ^ 2))) := by
  classical
  let epsilon : ℝ := tolerance / ((Fintype.card α : ℝ) * bound)
  have hdenom : 0 < (Fintype.card α : ℝ) * bound := mul_pos hcard hbound
  have hepsilon : 0 < epsilon := by
    exact div_pos htolerance hdenom
  have hlinear :
      (Fintype.card α : ℝ) * (Fintype.card (Fin n) : ℝ) * epsilon * bound =
        (Fintype.card (Fin n) : ℝ) * tolerance := by
    dsimp [epsilon]
    field_simp [ne_of_gt hcard, ne_of_gt hbound]
  have hsubset : ∀ sample : Fin n → α,
      finiteIidUniformScoreDeviationEvent μ score parameterSet tolerance sample →
        ∃ atom,
          (n : ℝ) * epsilon ≤
            |(empiricalCount sample atom : ℝ) - (n : ℝ) * (μ atom).toReal| := by
    intro sample hfailure
    rcases hfailure with ⟨parameter, hparameter, hdeviation⟩
    by_contra hmass
    push_neg at hmass
    have hmass' : ∀ atom,
        |(empiricalCount sample atom : ℝ) -
            (Fintype.card (Fin n) : ℝ) * (μ atom).toReal| ≤
          (Fintype.card (Fin n) : ℝ) * epsilon := by
      intro atom
      exact (by simpa only [Fintype.card_fin] using (hmass atom).le)
    have huniform := abs_finiteIidScoreSum_sub_card_mul_pmfExp_le_of_massDeviation
      μ score sample bound epsilon hepsilon.le hscore hmass' parameter
    have hupper :
        |finiteIidScoreSum (score parameter) sample -
          (n : ℝ) * pmfExp μ (score parameter)| ≤ (n : ℝ) * tolerance := by
      calc
        |finiteIidScoreSum (score parameter) sample -
            (n : ℝ) * pmfExp μ (score parameter)| ≤
            (Fintype.card α : ℝ) * (Fintype.card (Fin n) : ℝ) * epsilon * bound := by
          simpa only [Fintype.card_fin] using huniform
        _ = (Fintype.card (Fin n) : ℝ) * tolerance := hlinear
        _ = (n : ℝ) * tolerance := by rw [Fintype.card_fin]
    exact (not_lt_of_ge hupper) hdeviation
  have hmassTail := finiteIidAnyMassDeviationFailure_le_hoeffding
    μ epsilon (epsilon / 2) n hcount (by linarith) (by linarith)
  rw [finiteIidUniformScoreDeviationFailure_eq μ score parameterSet tolerance n]
  calc
    pmfProb (pmfProduct (Fin n) α μ)
        (finiteIidUniformScoreDeviationEvent μ score parameterSet tolerance) ≤
        finiteIidAnyMassDeviationFailure μ epsilon n := by
      unfold finiteIidAnyMassDeviationFailure
      exact pmfProb_le_of_imp (pmfProduct (Fin n) α μ) _ _ hsubset
    _ ≤ (Fintype.card α : ℝ) * 2 *
        Real.exp (-2 * (n : ℝ) * (epsilon / 2) ^ 2) := hmassTail
    _ = (Fintype.card α : ℝ) * 2 *
        Real.exp (-((n : ℝ) * tolerance ^ 2 /
          (2 * ((Fintype.card α : ℝ) * bound) ^ 2))) := by
      congr 3
      dsimp [epsilon]
      field_simp [ne_of_gt hdenom]

/-- Finite-alphabet iid sampling controls a continuous compact score family
uniformly at every fixed linear tolerance.  The proof reduces the whole
family to coordinatewise empirical report-mass deviations, rather than
assuming a black-box M-estimator theorem. -/
theorem finiteIidUniformScoreDeviationFailure_tendsto_zero
    {Θ : Type*} [TopologicalSpace Θ] [Nonempty α]
    (μ : PMF α) (score : Θ → α → ℝ) (parameterSet : Set Θ)
    (hcompact : IsCompact parameterSet)
    (hcontinuous : ∀ atom, Continuous (fun parameter => score parameter atom))
    (tolerance : ℝ) (htolerance : 0 < tolerance) :
    Filter.Tendsto
      (finiteIidUniformScoreDeviationFailure μ score parameterSet tolerance)
      Filter.atTop (𝓝 0) := by
  classical
  obtain ⟨bound, hbound_nonneg, hbound⟩ :=
    exists_nonneg_uniform_abs_le_of_isCompact_finite parameterSet hcompact score hcontinuous
  let epsilon : ℝ := tolerance / ((Fintype.card α : ℝ) * (bound + 1))
  have hcard_pos : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hbound_plus_pos : 0 < bound + 1 := by linarith
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    exact div_pos htolerance (mul_pos hcard_pos hbound_plus_pos)
  have hmass : Filter.Tendsto (finiteIidAnyMassDeviationFailure μ epsilon)
      Filter.atTop (𝓝 0) :=
    finiteIidAnyMassDeviationFailure_tendsto_zero μ epsilon hepsilon
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 0))
    hmass ?_ ?_
  · intro n
    exact pmfProb_nonneg (pmfProduct (Fin n) α μ) _
  · intro n
    letI : DecidablePred
        (finiteIidUniformScoreDeviationEvent μ score parameterSet tolerance (n := n)) :=
      Classical.decPred _
    unfold finiteIidUniformScoreDeviationFailure
    apply pmfProb_le_of_imp
    intro sample hfailure
    unfold finiteIidUniformScoreDeviationEvent at hfailure
    rcases hfailure with ⟨parameter, hparameter, hfailure⟩
    by_contra hmassFailure
    push_neg at hmassFailure
    have hdeviation : ∀ atom,
        |(empiricalCount sample atom : ℝ) -
            (Fintype.card (Fin n) : ℝ) * (μ atom).toReal| ≤
          (Fintype.card (Fin n) : ℝ) * epsilon := by
      intro atom
      simpa only [Fintype.card_fin] using (hmassFailure atom).le
    let restrictedScore : parameterSet → α → ℝ :=
      fun parameter => score parameter.1
    have hrestrictedBound : ∀ parameter atom,
        |restrictedScore parameter atom| ≤ bound := by
      intro parameter atom
      dsimp [restrictedScore]
      exact hbound parameter.1 parameter.property atom
    have huniform := abs_finiteIidScoreSum_sub_card_mul_pmfExp_le_of_massDeviation
      μ restrictedScore sample bound epsilon hepsilon.le hrestrictedBound hdeviation
        ⟨parameter, hparameter⟩
    dsimp [restrictedScore] at huniform
    have hratio : bound / (bound + 1) ≤ 1 := by
      apply (div_le_one₀ hbound_plus_pos).mpr
      linarith
    have hlinear :
        (Fintype.card α : ℝ) * (Fintype.card (Fin n) : ℝ) * epsilon * bound ≤
          (Fintype.card (Fin n) : ℝ) * tolerance := by
      calc
        (Fintype.card α : ℝ) * (Fintype.card (Fin n) : ℝ) * epsilon * bound =
            (Fintype.card (Fin n) : ℝ) * tolerance * (bound / (bound + 1)) := by
              dsimp [epsilon]
              field_simp [ne_of_gt hcard_pos, ne_of_gt hbound_plus_pos]
        _ ≤ (Fintype.card (Fin n) : ℝ) * tolerance * 1 :=
          mul_le_mul_of_nonneg_left hratio
            (mul_nonneg (Nat.cast_nonneg _) htolerance.le)
        _ = (Fintype.card (Fin n) : ℝ) * tolerance := by ring
    have hcontradiction : (Fintype.card (Fin n) : ℝ) * tolerance <
        (Fintype.card (Fin n) : ℝ) * tolerance := by
      have hfailure' : (Fintype.card (Fin n) : ℝ) * tolerance <
          |finiteIidScoreSum (score parameter) sample -
            (Fintype.card (Fin n) : ℝ) * pmfExp μ (score parameter)| := by
        simpa only [Fintype.card_fin] using hfailure
      exact hfailure'.trans_le (huniform.trans hlinear)
    exact (lt_irrefl _) hcontradiction

/--
A finite family of real scores bounded in absolute value by a positive
constant obeys a uniform two-sided Hoeffding bound.  This is the affine
`[-bound, bound]` form of
`finiteIidUniformScoreDeviationFailure_le_hoeffding`; the latter supplies the
union-bound concentration proof after the scores are normalized to `[0,1]`.
-/
theorem finiteIidUniformScoreDeviationFailure_le_hoeffding_of_abs_le
    {Θ : Type*} [Fintype Θ]
    (μ : PMF α) (score : Θ → α → ℝ) (parameterSet : Set Θ)
    (tolerance bound : ℝ) (n : ℕ) (hcount : 0 < n)
    (hbound : 0 < bound) (htolerance : 0 ≤ tolerance)
    (hscore : ∀ parameter atom, |score parameter atom| ≤ bound) :
    finiteIidUniformScoreDeviationFailure μ score parameterSet tolerance n ≤
      (Fintype.card Θ : ℝ) * 2 *
        Real.exp (-((n : ℝ) * tolerance ^ 2 / (2 * bound ^ 2))) := by
  classical
  let normalized : Θ → α → ℝ :=
    fun parameter atom => (score parameter atom + bound) / (2 * bound)
  have hnormalized : ∀ parameter atom, normalized parameter atom ∈ Set.Icc (0 : ℝ) 1 := by
    intro parameter atom
    have habs := hscore parameter atom
    have hdenom : 0 < 2 * bound := by positivity
    constructor
    · apply div_nonneg _ hdenom.le
      have hlower : -bound ≤ score parameter atom := by
        calc
          -bound ≤ -|score parameter atom| := neg_le_neg habs
          _ ≤ score parameter atom := neg_abs_le _
      linarith
    · rw [div_le_one₀ hdenom]
      linarith [le_abs_self (score parameter atom), habs]
  have hnormalized_formula : ∀ parameter atom,
      normalized parameter atom = (1 / (2 * bound)) * score parameter atom + 1 / 2 := by
    intro parameter atom
    dsimp [normalized]
    field_simp [ne_of_gt hbound]
  have hsum_formula : ∀ (parameter : Θ) (sample : Fin n → α),
      finiteIidScoreSum (normalized parameter) sample -
          (n : ℝ) * pmfExp μ (normalized parameter) =
        (finiteIidScoreSum (score parameter) sample -
          (n : ℝ) * pmfExp μ (score parameter)) / (2 * bound) := by
    intro parameter sample
    have hexpectation : pmfExp μ (normalized parameter) =
        (1 / (2 * bound)) * pmfExp μ (score parameter) + 1 / 2 := by
      calc
        pmfExp μ (normalized parameter) =
            pmfExp μ (fun atom =>
              (1 / (2 * bound)) * score parameter atom + 1 / 2) := by
          apply pmfExp_congr
          exact hnormalized_formula parameter
        _ = (1 / (2 * bound)) * pmfExp μ (score parameter) + 1 / 2 := by
          rw [pmfExp_add, pmfExp_const_mul, pmfExp_const]
    unfold finiteIidScoreSum
    simp_rw [hnormalized_formula]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hexpectation]
    simp [Finset.sum_const, nsmul_eq_mul]
    field_simp [ne_of_gt hbound]
    ring
  have hscaled := finiteIidUniformScoreDeviationFailure_le_hoeffding
    μ normalized parameterSet (tolerance / (2 * bound)) n hcount
      (div_nonneg htolerance (by positivity)) hnormalized
  rw [finiteIidUniformScoreDeviationFailure_eq μ normalized parameterSet
    (tolerance / (2 * bound)) n] at hscaled
  rw [finiteIidUniformScoreDeviationFailure_eq μ score parameterSet tolerance n]
  refine (pmfProb_le_of_imp (pmfProduct (Fin n) α μ)
    (finiteIidUniformScoreDeviationEvent μ score parameterSet tolerance)
    (finiteIidUniformScoreDeviationEvent μ normalized parameterSet
      (tolerance / (2 * bound))) ?_).trans ?_
  · intro sample hfailure
    rcases hfailure with ⟨parameter, hparameter, hdeviation⟩
    refine ⟨parameter, hparameter, ?_⟩
    rw [hsum_formula parameter sample, abs_div]
    have hdenom : 0 < 2 * bound := by positivity
    rw [abs_of_pos hdenom]
    have hleft : (n : ℝ) * (tolerance / (2 * bound)) =
        ((n : ℝ) * tolerance) / (2 * bound) := by ring
    rw [hleft]
    exact (div_lt_div_iff_of_pos_right hdenom).mpr hdeviation
  · calc
      pmfProb (pmfProduct (Fin n) α μ)
          (finiteIidUniformScoreDeviationEvent μ normalized parameterSet
            (tolerance / (2 * bound))) ≤
          (Fintype.card Θ : ℝ) * 2 *
            Real.exp (-2 * (n : ℝ) * (tolerance / (2 * bound)) ^ 2) := hscaled
      _ = (Fintype.card Θ : ℝ) * 2 *
            Real.exp (-((n : ℝ) * tolerance ^ 2 / (2 * bound ^ 2))) := by
          congr 3
          field_simp [ne_of_gt hbound]

/--
Replacing one score by another whose pointwise discrepancy is at most `bound`
changes its finite iid centered score sum by at most twice the sample size
times `bound`.  The two contributions are the empirical sum and population
expectation respectively.
-/
theorem abs_finiteIidCenteredScoreSum_sub_le
    {ι : Type*} [Fintype ι]
    (μ : PMF α) (first second : α → ℝ) (sample : ι → α) (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hpoint : ∀ atom, |first atom - second atom| ≤ bound) :
    |(finiteIidScoreSum first sample - (Fintype.card ι : ℝ) * pmfExp μ first) -
        (finiteIidScoreSum second sample - (Fintype.card ι : ℝ) * pmfExp μ second)| ≤
      2 * (Fintype.card ι : ℝ) * bound := by
  have hsum : |finiteIidScoreSum first sample - finiteIidScoreSum second sample| ≤
      (Fintype.card ι : ℝ) * bound := by
    unfold finiteIidScoreSum
    calc
      |(∑ index, first (sample index)) - ∑ index, second (sample index)| =
          |∑ index, (first (sample index) - second (sample index))| := by
            congr 1
            rw [← Finset.sum_sub_distrib]
      _ ≤ ∑ index, |first (sample index) - second (sample index)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _index : ι, bound := by
        apply Finset.sum_le_sum
        intro index _
        exact hpoint (sample index)
      _ = (Fintype.card ι : ℝ) * bound := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hexpectation : |pmfExp μ first - pmfExp μ second| ≤ bound := by
    apply abs_le.mpr
    constructor
    · have hle : pmfExp μ second ≤ pmfExp μ first + bound := by
        calc
          pmfExp μ second ≤ pmfExp μ (fun atom => first atom + bound) := by
            apply pmfExp_le_pmfExp_of_forall_le
            intro atom
            have h := hpoint atom
            linarith [(abs_le.mp h).1]
          _ = pmfExp μ first + bound := by rw [pmfExp_add, pmfExp_const]
      linarith
    · have hle : pmfExp μ first ≤ pmfExp μ second + bound := by
        calc
          pmfExp μ first ≤ pmfExp μ (fun atom => second atom + bound) := by
            apply pmfExp_le_pmfExp_of_forall_le
            intro atom
            have h := hpoint atom
            linarith [(abs_le.mp h).2]
          _ = pmfExp μ second + bound := by rw [pmfExp_add, pmfExp_const]
      linarith
  calc
    |(finiteIidScoreSum first sample - (Fintype.card ι : ℝ) * pmfExp μ first) -
        (finiteIidScoreSum second sample - (Fintype.card ι : ℝ) * pmfExp μ second)| =
        |(finiteIidScoreSum first sample - finiteIidScoreSum second sample) -
          (Fintype.card ι : ℝ) * (pmfExp μ first - pmfExp μ second)| := by ring
    _ ≤ |finiteIidScoreSum first sample - finiteIidScoreSum second sample| +
          |(Fintype.card ι : ℝ) * (pmfExp μ first - pmfExp μ second)| :=
      by
        simpa using
          (abs_sub_le (finiteIidScoreSum first sample - finiteIidScoreSum second sample)
            0 ((Fintype.card ι : ℝ) * (pmfExp μ first - pmfExp μ second)))
    _ ≤ (Fintype.card ι : ℝ) * bound +
          (Fintype.card ι : ℝ) * bound := by
      gcongr
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left hexpectation (Nat.cast_nonneg _)
    _ = 2 * (Fintype.card ι : ℝ) * bound := by ring

/--
A finite metric cover reduces uniform finite-iid score deviation to the same
event on its finite set of centers.  A pointwise `lipschitz` score bound makes
the empirical and population terms each change by at most the cover error,
which accounts for the factor two in the reduction.
-/
theorem finiteIidUniformScoreDeviationFailure_le_cover
    {Θ Net : Type*} [PseudoMetricSpace Θ] [Fintype Net]
    (μ : PMF α) (score : Θ → α → ℝ) (parameterSet : Set Θ)
    (center : Net → Θ) (choose : Θ → Net)
    (radius lipschitz tolerance : ℝ) (n : ℕ)
    (hcover : ∀ parameter, parameter ∈ parameterSet →
      dist parameter (center (choose parameter)) ≤ radius)
    (hlipschitz : ∀ first second atom,
      |score first atom - score second atom| ≤ lipschitz * dist first second)
    (hradius : 0 ≤ radius) (hlipschitz_nonneg : 0 ≤ lipschitz)
    (hslack : 4 * lipschitz * radius ≤ tolerance) :
    finiteIidUniformScoreDeviationFailure μ score parameterSet tolerance n ≤
      finiteIidUniformScoreDeviationFailure μ (fun index => score (center index))
        Set.univ (tolerance / 2) n := by
  classical
  rw [finiteIidUniformScoreDeviationFailure_eq μ score parameterSet tolerance n,
    finiteIidUniformScoreDeviationFailure_eq μ (fun index => score (center index))
      Set.univ (tolerance / 2) n]
  refine pmfProb_le_of_imp (pmfProduct (Fin n) α μ)
    (finiteIidUniformScoreDeviationEvent μ score parameterSet tolerance)
    (finiteIidUniformScoreDeviationEvent μ (fun index => score (center index))
      Set.univ (tolerance / 2)) ?_
  intro sample hfailure
  rcases hfailure with ⟨parameter, hparameter, hdeviation⟩
  let covered := center (choose parameter)
  have hpoint : ∀ atom, |score parameter atom - score covered atom| ≤ lipschitz * radius := by
    intro atom
    calc
      |score parameter atom - score covered atom| ≤ lipschitz * dist parameter covered :=
        hlipschitz parameter covered atom
      _ ≤ lipschitz * radius :=
        mul_le_mul_of_nonneg_left (hcover parameter hparameter) hlipschitz_nonneg
  have hchange := abs_finiteIidCenteredScoreSum_sub_le
    μ (score parameter) (score covered) sample (lipschitz * radius)
      (mul_nonneg hlipschitz_nonneg hradius) hpoint
  have hslack_half : 2 * (lipschitz * radius) ≤ tolerance / 2 := by
    nlinarith [hslack]
  have hchange_bound : 2 * (n : ℝ) * (lipschitz * radius) ≤
      (n : ℝ) * (tolerance / 2) := by
    calc
      2 * (n : ℝ) * (lipschitz * radius) =
          (n : ℝ) * (2 * (lipschitz * radius)) := by ring
      _ ≤ (n : ℝ) * (tolerance / 2) :=
        mul_le_mul_of_nonneg_left hslack_half (Nat.cast_nonneg _)
  refine ⟨choose parameter, Set.mem_univ _, ?_⟩
  have habs_triangle :
      |finiteIidScoreSum (score parameter) sample - (n : ℝ) * pmfExp μ (score parameter)| ≤
        |finiteIidScoreSum (score covered) sample - (n : ℝ) * pmfExp μ (score covered)| +
          |(finiteIidScoreSum (score parameter) sample - (n : ℝ) * pmfExp μ (score parameter)) -
            (finiteIidScoreSum (score covered) sample - (n : ℝ) * pmfExp μ (score covered))| := by
    have := abs_sub_le
      (finiteIidScoreSum (score parameter) sample - (n : ℝ) * pmfExp μ (score parameter))
      (finiteIidScoreSum (score covered) sample - (n : ℝ) * pmfExp μ (score covered)) 0
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hupper :
      |finiteIidScoreSum (score parameter) sample - (n : ℝ) * pmfExp μ (score parameter)| ≤
        |finiteIidScoreSum (score covered) sample - (n : ℝ) * pmfExp μ (score covered)| +
          (n : ℝ) * (tolerance / 2) := by
    have hchange' :
          |(finiteIidScoreSum (score parameter) sample -
              (Fintype.card (Fin n) : ℝ) * pmfExp μ (score parameter)) -
            (finiteIidScoreSum (score covered) sample -
              (Fintype.card (Fin n) : ℝ) * pmfExp μ (score covered))| ≤
            (n : ℝ) * (tolerance / 2) := by
      have hchange_bound_fin :
          2 * (Fintype.card (Fin n) : ℝ) * (lipschitz * radius) ≤
            (n : ℝ) * (tolerance / 2) := by
        simpa using hchange_bound
      exact hchange.trans hchange_bound_fin
    have hchange_n :
        |(finiteIidScoreSum (score parameter) sample -
            (n : ℝ) * pmfExp μ (score parameter)) -
          (finiteIidScoreSum (score covered) sample -
            (n : ℝ) * pmfExp μ (score covered))| ≤
          (n : ℝ) * (tolerance / 2) := by
      simpa using hchange'
    calc
      |finiteIidScoreSum (score parameter) sample - (n : ℝ) * pmfExp μ (score parameter)| ≤
          |finiteIidScoreSum (score covered) sample - (n : ℝ) * pmfExp μ (score covered)| +
            |(finiteIidScoreSum (score parameter) sample - (n : ℝ) * pmfExp μ (score parameter)) -
              (finiteIidScoreSum (score covered) sample - (n : ℝ) * pmfExp μ (score covered))| :=
        habs_triangle
      _ ≤ |finiteIidScoreSum (score covered) sample - (n : ℝ) * pmfExp μ (score covered)| +
            (n : ℝ) * (tolerance / 2) := by
        exact add_le_add (le_refl _) hchange_n
  have hstrict : (n : ℝ) * tolerance <
      |finiteIidScoreSum (score covered) sample - (n : ℝ) * pmfExp μ (score covered)| +
        (n : ℝ) * (tolerance / 2) :=
    lt_of_lt_of_le hdeviation hupper
  have hsplit : (n : ℝ) * tolerance =
      (n : ℝ) * (tolerance / 2) + (n : ℝ) * (tolerance / 2) := by ring
  change (n : ℝ) * (tolerance / 2) <
    |finiteIidScoreSum (score covered) sample - (n : ℝ) * pmfExp μ (score covered)|
  linarith

end

end Probability
end AppliedModelingLib
