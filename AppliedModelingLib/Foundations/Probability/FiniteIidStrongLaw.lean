import AppliedModelingLib.Foundations.Probability.FiniteIidUniformLaw
import AppliedModelingLib.Foundations.Probability.RenewalReward
import Mathlib.Probability.Independence.InfinitePi

/-!
# Strong laws on canonical finite-IID paths

This module supplies the almost-sure counterpart of the finite-prefix PMF
tools.  A finite PMF is lifted to the canonical countable product space and
the real strong law is stated directly in terms of the finite-PMF expectation.
Downstream papers can therefore retain literal iid report paths when their
source theorem is pathwise rather than merely in probability.
-/

open scoped BigOperators Topology

namespace AppliedModelingLib

open Filter MeasureTheory
open scoped Function ProbabilityTheory

noncomputable section

/-- Canonical infinite iid path measure associated with a finite PMF. -/
noncomputable def finitePMFIidPathMeasure
    {Signal : Type*} [MeasurableSpace Signal]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) : Measure (ℕ → Signal) := by
  exact Measure.infinitePi (fun _ : ℕ => law.toMeasure)

instance finitePMFIidPathMeasure.isProbabilityMeasure
    {Signal : Type*} [MeasurableSpace Signal]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) :
    IsProbabilityMeasure (finitePMFIidPathMeasure law) := by
  unfold finitePMFIidPathMeasure
  infer_instance

/--
Strong law for a real statistic of a canonical infinite path drawn iid from a
finite PMF.  The limit is the finite PMF expectation used by the finite-sample
library.
-/
theorem ae_tendsto_finitePMFIidPath_empirical_mean
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (statistic : Signal → ℝ) :
    letI : MeasurableSpace Signal := ⊤
    ∀ᵐ path ∂finitePMFIidPathMeasure law,
      Tendsto
        (fun N : ℕ =>
          (∑ voter ∈ Finset.range N, statistic (path voter)) / N)
        atTop (nhds (pmfExp law statistic)) := by
  letI : MeasurableSpace Signal := ⊤
  let P : Measure (ℕ → Signal) := finitePMFIidPathMeasure law
  let X : ℕ → (ℕ → Signal) → ℝ := fun voter path => statistic (path voter)
  have hstat_meas : Measurable statistic := measurable_of_countable statistic
  have hX_meas : ∀ voter, Measurable (X voter) := by
    intro voter
    exact hstat_meas.comp (measurable_pi_apply voter)
  have htoLaw :
      ∀ voter,
        ProbabilityTheory.IdentDistrib
          (X voter) statistic P law.toMeasure := by
    intro voter
    refine ⟨(hX_meas voter).aemeasurable, hstat_meas.aemeasurable, ?_⟩
    simp only [X, P, finitePMFIidPathMeasure]
    change Measure.map
        (statistic ∘ (fun path : ℕ → Signal => path voter))
        (Measure.infinitePi (fun _ : ℕ => law.toMeasure)) =
      Measure.map statistic law.toMeasure
    rw [← Measure.map_map hstat_meas (measurable_pi_apply voter),
      Measure.infinitePi_map_eval]
  have hX_integrable : Integrable (X 0) P := by
    exact (htoLaw 0).symm.integrable_snd Integrable.of_finite
  have hX_indep : Pairwise ((· ⟂ᵢ[P] ·) on X) := by
    have hiIndep : ProbabilityTheory.iIndepFun X P := by
      change ProbabilityTheory.iIndepFun
        (fun voter path => statistic (path voter))
        (Measure.infinitePi (fun _ : ℕ => law.toMeasure))
      exact ProbabilityTheory.iIndepFun_infinitePi (fun _ => hstat_meas)
    intro i j hij
    exact hiIndep.indepFun hij
  have hX_ident :
      ∀ voter,
        ProbabilityTheory.IdentDistrib (X voter) (X 0) P P := by
    intro voter
    exact (htoLaw voter).trans (htoLaw 0).symm
  have hslln :=
    ae_tendsto_empirical_mean_real_of_iid X hX_integrable hX_indep hX_ident
  have hmean :
      (∫ path, X 0 path ∂P) = pmfExp law statistic := by
    calc
      (∫ path, X 0 path ∂P) =
          ∫ signal, statistic signal ∂law.toMeasure :=
        (htoLaw 0).integral_eq
      _ = pmfExp law statistic :=
        (pmfExp_eq_integral_toMeasure law statistic).symm
  simpa [P, X, hmean] using hslln

/-- A finite prefix of a canonical iid path, presented in the literal
`Fin N → Signal` form used by the finite-sample library. -/
def finitePMFIidPathPrefix {Signal : Type*} (path : ℕ → Signal) (N : ℕ) :
    Fin N → Signal := fun voter => path voter

/-- Reindexing a path prefix between the `Fin N` and `range N` conventions. -/
theorem finiteIidScoreSum_pathPrefix_eq_sum_range
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (statistic : Signal → ℝ) (path : ℕ → Signal) (N : ℕ) :
    Probability.finiteIidScoreSum statistic (finitePMFIidPathPrefix path N) =
      ∑ voter ∈ Finset.range N, statistic (path voter) := by
  unfold Probability.finiteIidScoreSum finitePMFIidPathPrefix
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro voter hvoter
  have hvoter_lt : voter < N := Finset.mem_range.mp hvoter
  simp [hvoter_lt]

/-- The empirical mass of each fixed atom on a canonical finite-IID path
converges almost surely to that atom's PMF mass. -/
theorem ae_tendsto_finitePMFIidPath_empirical_frequency
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (atom : Signal) :
    letI : MeasurableSpace Signal := ⊤
    ∀ᵐ path ∂finitePMFIidPathMeasure law,
      Tendsto
        (fun N : ℕ =>
          (Probability.empiricalCount (finitePMFIidPathPrefix path N) atom : ℝ) / N)
        atTop (nhds (law atom).toReal) := by
  letI : MeasurableSpace Signal := ⊤
  let statistic : Signal → ℝ := fun outcome => if outcome = atom then 1 else 0
  have hslln := ae_tendsto_finitePMFIidPath_empirical_mean law statistic
  have hcount : ∀ path N,
      (Probability.empiricalCount (finitePMFIidPathPrefix path N) atom : ℝ) =
        ∑ voter ∈ Finset.range N, statistic (path voter) := by
    intro path N
    calc
      (Probability.empiricalCount (finitePMFIidPathPrefix path N) atom : ℝ) =
          Probability.finiteIidScoreSum
            (fun outcome => (if outcome = atom then (1 : ℝ) else 0) - 0)
            (finitePMFIidPathPrefix path N) := by
              symm
              simpa using
                (Probability.finiteIidScoreSum_indicator_sub_eq
                  (finitePMFIidPathPrefix path N) atom 0)
      _ = ∑ voter ∈ Finset.range N,
          ((if path voter = atom then (1 : ℝ) else 0) - 0) := by
            rw [finiteIidScoreSum_pathPrefix_eq_sum_range]
      _ = ∑ voter ∈ Finset.range N, statistic (path voter) := by
            simp [statistic]
  have hmean : pmfExp law statistic = (law atom).toReal := by
    simpa [statistic] using
      Probability.pmfExp_indicator_sub_eq law atom 0
  filter_upwards [hslln] with path hpath
  simpa only [hcount, hmean] using hpath

/-- Uniformly over the finite report alphabet, canonical iid prefixes have
eventually small empirical-mass error almost surely. -/
theorem ae_eventually_finitePMFIidPath_all_atom_massDeviation
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    letI : MeasurableSpace Signal := ⊤
    ∀ᵐ path ∂finitePMFIidPathMeasure law,
      ∀ᶠ N : ℕ in atTop, ∀ atom : Signal,
        |(Probability.empiricalCount (finitePMFIidPathPrefix path N) atom : ℝ) -
            (N : ℝ) * (law atom).toReal| ≤ (N : ℝ) * epsilon := by
  letI : MeasurableSpace Signal := ⊤
  have hatom : ∀ atom : Signal,
      ∀ᵐ path ∂finitePMFIidPathMeasure law,
        ∀ᶠ N : ℕ in atTop,
          |(Probability.empiricalCount (finitePMFIidPathPrefix path N) atom : ℝ) / N -
              (law atom).toReal| < epsilon := by
    intro atom
    have hslln := ae_tendsto_finitePMFIidPath_empirical_frequency law atom
    filter_upwards [hslln] with path hpath
    have hball := hpath.eventually (Metric.ball_mem_nhds _ hepsilon)
    filter_upwards [hball] with N hN
    simpa [Real.dist_eq] using hN
  have hallAE :
      ∀ᵐ path ∂finitePMFIidPathMeasure law,
        ∀ atom : Signal,
          ∀ᶠ N : ℕ in atTop,
            |(Probability.empiricalCount (finitePMFIidPathPrefix path N) atom : ℝ) / N -
                (law atom).toReal| < epsilon :=
    MeasureTheory.ae_all_iff.mpr hatom
  filter_upwards [hallAE] with path hpath
  have hallN :
      ∀ᶠ N : ℕ in atTop, ∀ atom : Signal,
        |(Probability.empiricalCount (finitePMFIidPathPrefix path N) atom : ℝ) / N -
            (law atom).toReal| < epsilon :=
    Filter.eventually_all.mpr hpath
  filter_upwards [hallN, Filter.eventually_ge_atTop 1] with N hmass hN
  intro atom
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hrewrite :
      (Probability.empiricalCount (finitePMFIidPathPrefix path N) atom : ℝ) -
          (N : ℝ) * (law atom).toReal =
        (N : ℝ) *
          ((Probability.empiricalCount (finitePMFIidPathPrefix path N) atom : ℝ) / N -
            (law atom).toReal) := by
    field_simp [ne_of_gt hNreal]
  rw [hrewrite, abs_mul, abs_of_pos hNreal]
  exact mul_le_mul_of_nonneg_left (hmass atom).le hNreal.le

/-- A continuous score family on a compact parameter set satisfies its
finite-alphabet uniform law eventually on almost every canonical iid path. -/
theorem ae_eventually_finitePMFIidPath_uniformScoreDeviation
    {Signal Θ : Type*} [Fintype Signal] [DecidableEq Signal] [Nonempty Signal]
    [TopologicalSpace Θ]
    (law : PMF Signal) (score : Θ → Signal → ℝ) (parameterSet : Set Θ)
    (hcompact : IsCompact parameterSet)
    (hcontinuous : ∀ atom, Continuous (fun parameter => score parameter atom))
    (tolerance : ℝ) (htolerance : 0 < tolerance) :
    letI : MeasurableSpace Signal := ⊤
    ∀ᵐ path ∂finitePMFIidPathMeasure law,
      ∀ᶠ N : ℕ in atTop, ∀ parameter, parameter ∈ parameterSet →
        |Probability.finiteIidScoreSum (score parameter) (finitePMFIidPathPrefix path N) -
            (N : ℝ) * pmfExp law (score parameter)| ≤ (N : ℝ) * tolerance := by
  letI : MeasurableSpace Signal := ⊤
  obtain ⟨bound, hbound_nonneg, hbound⟩ :=
    Probability.exists_nonneg_uniform_abs_le_of_isCompact_finite
      parameterSet hcompact score hcontinuous
  let epsilon : ℝ := tolerance / ((Fintype.card Signal : ℝ) * (bound + 1))
  have hcard_pos : 0 < (Fintype.card Signal : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hbound_plus_pos : 0 < bound + 1 := by linarith
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    exact div_pos htolerance (mul_pos hcard_pos hbound_plus_pos)
  have hmass := ae_eventually_finitePMFIidPath_all_atom_massDeviation law epsilon hepsilon
  filter_upwards [hmass] with path hmass
  filter_upwards [hmass] with N hdeviation parameter hparameter
  let restrictedScore : parameterSet → Signal → ℝ :=
    fun restrictedParameter => score restrictedParameter.1
  have hrestrictedBound : ∀ restrictedParameter atom,
      |restrictedScore restrictedParameter atom| ≤ bound := by
    intro restrictedParameter atom
    dsimp [restrictedScore]
    exact hbound restrictedParameter.1 restrictedParameter.property atom
  have hdeviation' : ∀ atom,
      |(Probability.empiricalCount (finitePMFIidPathPrefix path N) atom : ℝ) -
          (Fintype.card (Fin N) : ℝ) * (law atom).toReal| ≤
        (Fintype.card (Fin N) : ℝ) * epsilon := by
    intro atom
    simpa only [Fintype.card_fin] using hdeviation atom
  have huniform :=
    Probability.abs_finiteIidScoreSum_sub_card_mul_pmfExp_le_of_massDeviation
      law restrictedScore (finitePMFIidPathPrefix path N) bound epsilon hepsilon.le
      hrestrictedBound hdeviation' ⟨parameter, hparameter⟩
  dsimp [restrictedScore] at huniform
  have hratio : bound / (bound + 1) ≤ 1 := by
    apply (div_le_one₀ hbound_plus_pos).mpr
    linarith
  have hlinear :
      (Fintype.card Signal : ℝ) * (Fintype.card (Fin N) : ℝ) * epsilon * bound ≤
        (Fintype.card (Fin N) : ℝ) * tolerance := by
    calc
      (Fintype.card Signal : ℝ) * (Fintype.card (Fin N) : ℝ) * epsilon * bound =
          (Fintype.card (Fin N) : ℝ) * tolerance * (bound / (bound + 1)) := by
            dsimp [epsilon]
            field_simp [ne_of_gt hcard_pos, ne_of_gt hbound_plus_pos]
      _ ≤ (Fintype.card (Fin N) : ℝ) * tolerance * 1 :=
        mul_le_mul_of_nonneg_left hratio
          (mul_nonneg (Nat.cast_nonneg _) htolerance.le)
      _ = (Fintype.card (Fin N) : ℝ) * tolerance := by ring
  simpa only [Fintype.card_fin] using huniform.trans hlinear

/-- Every atom in a finite positive-margin family eventually exceeds its
prescribed lower empirical frequency on almost every canonical iid path. -/
theorem ae_eventually_finitePMFIidPath_not_finiteIidFiniteSetLowerFrequencyEvent
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (atoms : Finset Signal) (threshold : ℝ)
    (hthreshold : ∀ atom ∈ atoms, threshold < (law atom).toReal) :
    letI : MeasurableSpace Signal := ⊤
    ∀ᵐ path ∂finitePMFIidPathMeasure law,
      ∀ᶠ N : ℕ in atTop,
        ¬ Probability.finiteIidFiniteSetLowerFrequencyEvent atoms threshold
          (finitePMFIidPathPrefix path N) := by
  letI : MeasurableSpace Signal := ⊤
  let Atom := { atom : Signal // atom ∈ atoms }
  have hatom : ∀ atom : Atom,
      ∀ᵐ path ∂finitePMFIidPathMeasure law,
        ∀ᶠ N : ℕ in atTop,
          threshold <
            (Probability.empiricalCount (finitePMFIidPathPrefix path N) atom.1 : ℝ) / N := by
    intro atom
    have hslln := ae_tendsto_finitePMFIidPath_empirical_frequency law atom.1
    filter_upwards [hslln] with path hpath
    exact hpath.eventually_const_lt (hthreshold atom.1 atom.2)
  have hallAE :
      ∀ᵐ path ∂finitePMFIidPathMeasure law,
        ∀ atom : Atom,
          ∀ᶠ N : ℕ in atTop,
            threshold <
              (Probability.empiricalCount (finitePMFIidPathPrefix path N) atom.1 : ℝ) / N :=
    MeasureTheory.ae_all_iff.mpr hatom
  filter_upwards [hallAE] with path hpath
  have hallN :
      ∀ᶠ N : ℕ in atTop, ∀ atom : Atom,
        threshold <
          (Probability.empiricalCount (finitePMFIidPathPrefix path N) atom.1 : ℝ) / N :=
    Filter.eventually_all.mpr hpath
  filter_upwards [hallN, Filter.eventually_ge_atTop 1] with N hfrequency hN
  intro hbad
  rcases hbad with ⟨atom, hatom, hcount⟩
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hstrict : (N : ℝ) * threshold <
      (Probability.empiricalCount (finitePMFIidPathPrefix path N) atom : ℝ) := by
    have h := (lt_div_iff₀ hNreal).mp (hfrequency ⟨atom, hatom⟩)
    simpa [mul_comm] using h
  exact (not_lt_of_ge hcount) hstrict

end

end AppliedModelingLib
