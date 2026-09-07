import GGSG19TopThree.AlmostSureDesignInvariance
import AppliedModelingLib.Foundations.Probability.IndependentProduct
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Martingale.BorelCantelli

open scoped BigOperators

namespace GGSG19TopThree

open AppliedModelingLib.Probability
open AppliedModelingLib.SocialChoice.Ranking
open MeasureTheory
open scoped Function ProbabilityTheory Topology

noncomputable section

theorem iidPath_statistic_iIndepFun
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (statistic : Signal → ℝ) :
    letI : MeasurableSpace Signal := ⊤
    ProbabilityTheory.iIndepFun
      (fun voter path ↦ statistic (path voter))
      (finitePMFIidPathMeasure law) := by
  letI : MeasurableSpace Signal := ⊤
  change ProbabilityTheory.iIndepFun
    (fun voter path ↦ statistic (path voter))
    (Measure.infinitePi (fun _ : ℕ ↦ law.toMeasure))
  exact ProbabilityTheory.iIndepFun_infinitePi
    (fun _ ↦ (measurable_of_countable statistic))

theorem iidPath_statistic_integral
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (statistic : Signal → ℝ) (voter : ℕ) :
    letI : MeasurableSpace Signal := ⊤
    (∫ path, statistic (path voter) ∂finitePMFIidPathMeasure law) =
      AppliedModelingLib.pmfExp law statistic := by
  letI : MeasurableSpace Signal := ⊤
  have hstat_meas : Measurable statistic := measurable_of_countable statistic
  have hcoord :
      ProbabilityTheory.IdentDistrib
        (fun path : ℕ → Signal ↦ statistic (path voter))
        statistic (finitePMFIidPathMeasure law) law.toMeasure := by
    refine ⟨(hstat_meas.comp (measurable_pi_apply voter)).aemeasurable,
      hstat_meas.aemeasurable, ?_⟩
    change Measure.map
        (statistic ∘ (fun path : ℕ → Signal ↦ path voter))
        (Measure.infinitePi (fun _ : ℕ ↦ law.toMeasure)) =
      Measure.map statistic law.toMeasure
    rw [← Measure.map_map hstat_meas (measurable_pi_apply voter),
      Measure.infinitePi_map_eval]
  calc
    (∫ path, statistic (path voter) ∂finitePMFIidPathMeasure law) =
        ∫ signal, statistic signal ∂law.toMeasure := hcoord.integral_eq
    _ = AppliedModelingLib.pmfExp law statistic :=
      (AppliedModelingLib.pmfExp_eq_integral_toMeasure law statistic).symm

/-- Every coordinate of the canonical iid path lies in the PMF support almost surely. -/
theorem ae_all_iidPath_of_forall_support
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (predicate : Signal → Prop) [DecidablePred predicate]
    (hsupport : ∀ signal, 0 < (law signal).toReal → predicate signal) :
    letI : MeasurableSpace Signal := ⊤
    ∀ᵐ path ∂finitePMFIidPathMeasure law, ∀ n : ℕ, predicate (path n) := by
  letI : MeasurableSpace Signal := ⊤
  have hbase : ∀ᵐ signal ∂law.toMeasure, predicate signal := by
    rw [MeasureTheory.ae_iff]
    apply (law.toMeasure_apply_eq_zero_iff MeasurableSet.of_discrete).2
    rw [Set.disjoint_left]
    intro signal hsignal_support hsignal_bad
    apply hsignal_bad
    apply hsupport signal
    exact ENNReal.toReal_pos
      ((PMF.mem_support_iff law signal).mp hsignal_support)
      (law.apply_ne_top signal)
  apply MeasureTheory.ae_all_iff.mpr
  intro n
  have hmap :
      Measure.map (fun path : ℕ → Signal ↦ path n)
          (finitePMFIidPathMeasure law) = law.toMeasure := by
    simp [finitePMFIidPathMeasure, Measure.infinitePi_map_eval]
  rw [← hmap] at hbase
  exact (MeasureTheory.ae_map_iff
    (measurable_pi_apply n).aemeasurable MeasurableSet.of_discrete).mp hbase

/-- Every positive-mass atom appears infinitely often on almost every iid path. -/
theorem ae_frequently_iidPath_eq_of_atom_pos
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (witness : Signal)
    (hwitness_mass : 0 < (law witness).toReal) :
    letI : MeasurableSpace Signal := ⊤
    ∀ᵐ path ∂finitePMFIidPathMeasure law,
      ¬ ∀ᶠ n : ℕ in Filter.atTop, path n ≠ witness := by
  letI : MeasurableSpace Signal := ⊤
  let indicator : Signal → ℝ := fun signal ↦ if signal = witness then 1 else 0
  have hindicator_mean :
      AppliedModelingLib.pmfExp law indicator = (law witness).toReal := by
    unfold AppliedModelingLib.pmfExp indicator
    classical
    rw [Finset.sum_eq_single witness]
    · simp
    · intro signal _ hsignal
      simp [hsignal]
    · simp
  have hfrequency := ae_tendsto_finitePMFIidPath_empirical_mean law indicator
  filter_upwards [hfrequency] with path haverage
  intro havoid
  have hindicator_zero :
      Filter.Tendsto (fun n : ℕ ↦ indicator (path n))
        Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [havoid] with n hn
    simp [indicator, hn]
  have haverage_zero := hindicator_zero.cesaro
  have hzero : (law witness).toReal = 0 := by
    calc
      (law witness).toReal = AppliedModelingLib.pmfExp law indicator :=
        hindicator_mean.symm
      _ = 0 := tendsto_nhds_unique haverage (by
        simpa [div_eq_inv_mul] using haverage_zero)
  exact (ne_of_gt hwitness_mass) hzero

/-- Cumulative centered iid finite statistics form a martingale. -/
theorem iidPath_partialSum_martingale
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (statistic : Signal → ℝ)
    (hmean : AppliedModelingLib.pmfExp law statistic = 0) :
    letI : MeasurableSpace Signal := ⊤
    let X : ℕ → (ℕ → Signal) → ℝ :=
      fun voter path ↦ statistic (path voter)
    let hX : ∀ voter, StronglyMeasurable (X voter) :=
      fun voter ↦ (measurable_of_countable statistic).stronglyMeasurable.comp_measurable
        (measurable_pi_apply voter)
    let ℱ := Filtration.natural X hX
    Martingale
      (fun n path ↦ ∑ voter ∈ Finset.range (n + 1), X voter path)
      ℱ (finitePMFIidPathMeasure law) := by
  letI : MeasurableSpace Signal := ⊤
  let X : ℕ → (ℕ → Signal) → ℝ :=
    fun voter path ↦ statistic (path voter)
  have hX : ∀ voter, StronglyMeasurable (X voter) := by
    intro voter
    exact (measurable_of_countable statistic).stronglyMeasurable.comp_measurable
      (measurable_pi_apply voter)
  let ℱ := Filtration.natural X hX
  let S : ℕ → (ℕ → Signal) → ℝ :=
    fun n path ↦ ∑ voter ∈ Finset.range (n + 1), X voter path
  have hXadapted : StronglyAdapted ℱ X :=
    Filtration.stronglyAdapted_natural hX
  have hSadapted : StronglyAdapted ℱ S := by
    intro n
    have hsum :
        StronglyMeasurable[ℱ n] (∑ voter ∈ Finset.range (n + 1), X voter) :=
      Finset.stronglyMeasurable_sum (Finset.range (n + 1)) (fun voter hvoter ↦
        (hXadapted voter).mono
          (ℱ.mono (Nat.le_of_lt_succ (Finset.mem_range.mp hvoter))))
    convert hsum using 1
    ext path
    simp [S]
  have hXint : ∀ n, Integrable (X n) (finitePMFIidPathMeasure law) := by
    intro n
    refine Integrable.of_bound (hX n).aestronglyMeasurable
      (∑ signal : Signal, ‖statistic signal‖) ?_
    exact Filter.Eventually.of_forall (fun path ↦
      Finset.single_le_sum (fun signal _ ↦ norm_nonneg (statistic signal))
        (Finset.mem_univ (path n)))
  have hSint : ∀ n, Integrable (S n) (finitePMFIidPathMeasure law) := by
    intro n
    simpa [S] using
      (integrable_finset_sum (Finset.range (n + 1))
        (fun voter _ ↦ hXint voter))
  have hIndep : ProbabilityTheory.iIndepFun X (finitePMFIidPathMeasure law) := by
    simpa [X] using iidPath_statistic_iIndepFun law statistic
  have hcond :
      ∀ n,
        (finitePMFIidPathMeasure law)[S (n + 1) - S n | ℱ n] =ᵐ[
          finitePMFIidPathMeasure law] 0 := by
    intro n
    have hdiff : S (n + 1) - S n = X (n + 1) := by
      funext path
      simp [S, X, Finset.sum_range_succ]
    rw [hdiff]
    have hnext :=
      ProbabilityTheory.iIndepFun.condExp_natural_ae_eq_of_lt
        hX hIndep (Nat.lt_succ_self n)
    refine hnext.trans ?_
    have hintegral :
        ∫ path, X (n + 1) path ∂finitePMFIidPathMeasure law = 0 := by
      simpa [X, hmean] using
        (iidPath_statistic_integral law statistic (n + 1))
    exact Filter.Eventually.of_forall (fun _ ↦ by simp [hintegral])
  exact martingale_of_condExp_sub_eq_zero_nat hSadapted hSint hcond

/-- A positive-mass nonzero atom prevents centered iid partial sums from converging. -/
theorem ae_not_tendsto_iidPath_partialSum_of_support_ne_zero
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (statistic : Signal → ℝ)
    (witness : Signal)
    (hwitness_mass : 0 < (law witness).toReal)
    (hwitness_ne : statistic witness ≠ 0) :
    letI : MeasurableSpace Signal := ⊤
    ∀ᵐ path ∂finitePMFIidPathMeasure law,
      ¬ ∃ c : ℝ,
        Filter.Tendsto
          (fun n : ℕ ↦
            ∑ voter ∈ Finset.range (n + 1), statistic (path voter))
          Filter.atTop (nhds c) := by
  letI : MeasurableSpace Signal := ⊤
  let indicator : Signal → ℝ := fun signal ↦ if signal = witness then 1 else 0
  have hindicator_mean :
      AppliedModelingLib.pmfExp law indicator = (law witness).toReal := by
    unfold AppliedModelingLib.pmfExp indicator
    classical
    rw [Finset.sum_eq_single witness]
    · simp
    · intro signal _ hsignal
      simp [hsignal]
    · simp
  have hfrequency :=
    ae_tendsto_finitePMFIidPath_empirical_mean law indicator
  filter_upwards [hfrequency] with path haverage
  have hnot_avoid : ¬ ∀ᶠ n : ℕ in Filter.atTop, path n ≠ witness := by
    intro havoid
    have hindicator_zero :
        Filter.Tendsto (fun n : ℕ ↦ indicator (path n))
          Filter.atTop (nhds 0) := by
      apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [havoid] with n hn
      simp [indicator, hn]
    have haverage_zero := hindicator_zero.cesaro
    have hzero : (law witness).toReal = 0 := by
      calc
        (law witness).toReal = AppliedModelingLib.pmfExp law indicator :=
          hindicator_mean.symm
        _ = 0 := tendsto_nhds_unique haverage (by
          simpa [div_eq_inv_mul] using haverage_zero)
    exact (ne_of_gt hwitness_mass) hzero
  rintro ⟨c, hsum⟩
  have hdiff :
      Filter.Tendsto
        (fun n : ℕ ↦ statistic (path (n + 1)))
        Filter.atTop (nhds 0) := by
    have hshift := hsum.comp (Filter.tendsto_add_atTop_nat 1)
    have hsub := hshift.sub hsum
    simpa [Function.comp_def, Finset.sum_range_succ, Nat.add_assoc] using hsub
  have hshift_avoid :
      ∀ᶠ n : ℕ in Filter.atTop, path (n + 1) ≠ witness := by
    have hneValue : (0 : ℝ) ≠ statistic witness := hwitness_ne.symm
    filter_upwards [hdiff.eventually (eventually_ne_nhds hneValue)] with n hn
    intro heq
    apply hn
    simpa [heq]
  apply hnot_avoid
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hshift_avoid
  refine Filter.eventually_atTop.2 ⟨N + 1, ?_⟩
  intro n hn
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m + 1 := by
    exact ⟨n - 1, by omega⟩
  subst n
  exact hN m (by omega)

/-- A nondegenerate centered finite iid walk is not eventually nonnegative. -/
theorem ae_not_eventually_nonneg_iidPath_partialSum_of_mean_zero_of_support_ne_zero
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (statistic : Signal → ℝ)
    (hmean : AppliedModelingLib.pmfExp law statistic = 0)
    (witness : Signal)
    (hwitness_mass : 0 < (law witness).toReal)
    (hwitness_ne : statistic witness ≠ 0) :
    letI : MeasurableSpace Signal := ⊤
    ∀ᵐ path ∂finitePMFIidPathMeasure law,
      ¬ ∀ᶠ n : ℕ in Filter.atTop,
        0 ≤ ∑ voter ∈ Finset.range (n + 1), statistic (path voter) := by
  letI : MeasurableSpace Signal := ⊤
  let X : ℕ → (ℕ → Signal) → ℝ :=
    fun voter path ↦ statistic (path voter)
  have hX : ∀ voter, StronglyMeasurable (X voter) := by
    intro voter
    exact (measurable_of_countable statistic).stronglyMeasurable.comp_measurable
      (measurable_pi_apply voter)
  let ℱ := Filtration.natural X hX
  let S : ℕ → (ℕ → Signal) → ℝ :=
    fun n path ↦ ∑ voter ∈ Finset.range (n + 1), X voter path
  have hmartingale : Martingale S ℱ (finitePMFIidPathMeasure law) := by
    simpa [S, X, ℱ] using
      (iidPath_partialSum_martingale law statistic hmean)
  let C : ℝ := ∑ signal : Signal, ‖statistic signal‖
  have hC_nonneg : 0 ≤ C := by
    exact Finset.sum_nonneg (fun signal _ ↦ norm_nonneg (statistic signal))
  let R : NNReal := ⟨C, hC_nonneg⟩
  have hstat_bound : ∀ signal : Signal, ‖statistic signal‖ ≤ C := by
    intro signal
    exact Finset.single_le_sum (fun s _ ↦ norm_nonneg (statistic s))
      (Finset.mem_univ signal)
  have hincrement_bound :
      ∀ᵐ path ∂finitePMFIidPathMeasure law,
        ∀ i : ℕ, |S (i + 1) path - S i path| ≤ (R : ℝ) := by
    exact Filter.Eventually.of_forall (fun path i ↦ by
      simpa [S, X, Finset.sum_range_succ] using hstat_bound (path (i + 1)))
  have hnot_converge :=
    ae_not_tendsto_iidPath_partialSum_of_support_ne_zero
      law statistic witness hwitness_mass hwitness_ne
  have hbounded_iff_converges :=
    hmartingale.submartingale.bddAbove_iff_exists_tendsto hincrement_bound
  have hbounded_symmetric :=
    hmartingale.bddAbove_range_iff_bddBelow_range hincrement_bound
  filter_upwards [hnot_converge, hbounded_iff_converges, hbounded_symmetric]
    with path hnotconv hupperconv huppereq
  intro heventually_pos
  have hnot_upper : ¬ BddAbove (Set.range fun n ↦ S n path) := by
    intro hupper
    exact hnotconv (hupperconv.mp hupper)
  have hnot_lower : ¬ BddBelow (Set.range fun n ↦ S n path) := by
    intro hlower
    exact hnot_upper (huppereq.mpr hlower)
  apply hnot_lower
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 heventually_pos
  refine ⟨-(N : ℝ) * C, ?_⟩
  rintro value ⟨n, rfl⟩
  by_cases hn : N ≤ n
  · have hlower_nonpos : -(N : ℝ) * C ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg N)) hC_nonneg
    exact hlower_nonpos.trans (hN n hn)
  · have hnlt : n < N := Nat.lt_of_not_ge hn
    have hterm_lower : ∀ voter ∈ Finset.range (n + 1), -C ≤ X voter path := by
      intro voter _
      have habs := hstat_bound (path voter)
      exact neg_le_of_abs_le (by simpa [Real.norm_eq_abs] using habs)
    have hsum_lower := Finset.sum_le_sum hterm_lower
    have hcount : (n + 1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_iff.mpr hnlt)
    simp [X] at hsum_lower
    nlinarith

/-! ## Literal independent uniform tie breaking -/

/-- One iid election draw consists of a voter ranking and an independent tie ranking. -/
noncomputable def rankingUniformTieSignalLaw {n : ℕ}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n)) :
    PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n ×
      AppliedModelingLib.SocialChoice.Ranking.Ranking n) :=
  AppliedModelingLib.pmfProd law
    (PMF.uniformOfFintype (AppliedModelingLib.SocialChoice.Ranking.Ranking n))

/-- Cumulative source score using the voter-ranking coordinate. -/
def iidUniformTieCandidateScore
    {Candidate Signal Tie : Type*}
    (score : Candidate → Signal → ℝ)
    (path : ℕ → Signal × Tie) (N : ℕ) (candidate : Candidate) : ℝ :=
  ∑ voter ∈ Finset.range N, score candidate (path voter).1

/-- Exact tier correctness when equal cumulative scores use the fresh tie ranking. -/
def iidUniformTieTieredCorrect
    {n Stage : ℕ}
    (score : AppliedModelingLib.SocialChoice.Ranking.Candidate n →
      AppliedModelingLib.SocialChoice.Ranking.Ranking n → ℝ)
    (targetPrefix : Fin Stage →
      Finset (AppliedModelingLib.SocialChoice.Ranking.Candidate n))
    (path : ℕ → AppliedModelingLib.SocialChoice.Ranking.Ranking n ×
      AppliedModelingLib.SocialChoice.Ranking.Ranking n)
    (N : ℕ) : Prop :=
  ∀ stage : Fin Stage,
    ∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
      hi ∈ targetPrefix stage → lo ∉ targetPrefix stage →
        iidUniformTieCandidateScore score path N lo <
            iidUniformTieCandidateScore score path N hi ∨
          (iidUniformTieCandidateScore score path N lo =
              iidUniformTieCandidateScore score path N hi ∧
            AppliedModelingLib.SocialChoice.Ranking.rankOf (path N).2 hi <
              AppliedModelingLib.SocialChoice.Ranking.rankOf (path N).2 lo)

/--
Named paper-local conclusion for Proposition 1.  The structure exposes the
paper's full statement--every reasonable scoring rule is eventually correct
almost surely under independent uniform tie breaking--without presenting the
underlying ranking/tie product as anonymous witness data on the human-facing
theorem row.
-/
structure PropositionOneUniformTieConsistency
    {n Stage : ℕ}
    (law : PMF (Ranking n))
    (targetPrefix : Fin Stage → Finset (Candidate n)) : Prop where
  allReasonableRules :
    ∀ diff : RankingProperPrefixCut n → ℝ,
      ReasonablePrefixWeights diff →
        letI : MeasurableSpace (Ranking n × Ranking n) := ⊤
        ∀ᵐ path ∂finitePMFIidPathMeasure (rankingUniformTieSignalLaw law),
          ∀ᶠ N : ℕ in Filter.atTop,
            iidUniformTieTieredCorrect
              (rankingPrefixScore diff) targetPrefix path N

/-- A statistic of the voter coordinate has its original expectation. -/
theorem pmfExp_rankingUniformTieSignalLaw_fst
    {n : ℕ} (law : PMF (Ranking n)) (statistic : Ranking n → ℝ) :
    AppliedModelingLib.pmfExp (rankingUniformTieSignalLaw law)
        (fun signal ↦ statistic signal.1) =
      AppliedModelingLib.pmfExp law statistic := by
  rw [rankingUniformTieSignalLaw, AppliedModelingLib.pmfExp_pmfProd_eq_pairExp]
  exact AppliedModelingLib.pmfPairExp_ignore_right law
    (PMF.uniformOfFintype (Ranking n)) statistic

/-- Strict source prefix dominance gives almost-sure recovery with uniform ties. -/
theorem rankingTieredStrictPrefixDominance_implies_almostSure_uniformTieCorrect
    {n Stage : ℕ}
    (law : PMF (Ranking n))
    (targetPrefix : Fin Stage → Finset (Candidate n))
    (hdom :
      ∀ stage : Fin Stage,
        ∀ hi lo : Candidate n,
          hi ∈ targetPrefix stage → lo ∉ targetPrefix stage →
            ∀ cut : RankingProperPrefixCut n,
              rankingTopPrefixProb law lo cut <
                rankingTopPrefixProb law hi cut) :
    ∀ diff : RankingProperPrefixCut n → ℝ,
      ReasonablePrefixWeights diff →
        letI : MeasurableSpace (Ranking n × Ranking n) := ⊤
        ∀ᵐ path ∂finitePMFIidPathMeasure (rankingUniformTieSignalLaw law),
          ∀ᶠ N : ℕ in Filter.atTop,
            iidUniformTieTieredCorrect
              (rankingPrefixScore diff) targetPrefix path N := by
  intro diff hdiff
  letI : MeasurableSpace (Ranking n × Ranking n) := ⊤
  have hpair :
      ∀ stage : Fin Stage,
        ∀ pair : CrossTierPair (targetPrefix stage),
          ∀ᵐ path ∂finitePMFIidPathMeasure (rankingUniformTieSignalLaw law),
            ∀ᶠ N : ℕ in Filter.atTop,
              0 < ∑ voter ∈ Finset.range N,
                (rankingPrefixScore diff pair.hi (path voter).1 -
                  rankingPrefixScore diff pair.lo (path voter).1) := by
    intro stage pair
    let gap : Ranking n → ℝ := fun ranking ↦
      rankingPrefixScore diff pair.hi ranking -
        rankingPrefixScore diff pair.lo ranking
    have hmean :
        0 < AppliedModelingLib.pmfExp (rankingUniformTieSignalLaw law)
          (fun signal : Ranking n × Ranking n ↦ gap signal.1) := by
      rw [pmfExp_rankingUniformTieSignalLaw_fst law gap]
      exact pmfExp_prefixScore_gap_pos_of_strictTopPrefixDominance
        law diff rankingInTopPrefix
        (hdom stage pair.hi pair.lo pair.hi_mem pair.lo_not_mem) hdiff
    simpa [gap] using
      (ae_eventually_iidPath_score_gap_pos_of_pmfExp_pos
        (rankingUniformTieSignalLaw law)
        (fun signal : Ranking n × Ranking n ↦ gap signal.1)
        hmean)
  have hallAE :
      ∀ᵐ path ∂finitePMFIidPathMeasure (rankingUniformTieSignalLaw law),
        ∀ stage : Fin Stage,
          ∀ pair : CrossTierPair (targetPrefix stage),
            ∀ᶠ N : ℕ in Filter.atTop,
              0 < ∑ voter ∈ Finset.range N,
                (rankingPrefixScore diff pair.hi (path voter).1 -
                  rankingPrefixScore diff pair.lo (path voter).1) :=
    MeasureTheory.ae_all_iff.mpr (fun stage ↦
      MeasureTheory.ae_all_iff.mpr (hpair stage))
  filter_upwards [hallAE] with path hpath
  have hallN :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ stage : Fin Stage,
          ∀ pair : CrossTierPair (targetPrefix stage),
            0 < ∑ voter ∈ Finset.range N,
              (rankingPrefixScore diff pair.hi (path voter).1 -
                rankingPrefixScore diff pair.lo (path voter).1) :=
    Filter.eventually_all.mpr (fun stage ↦
      Filter.eventually_all.mpr (hpath stage))
  filter_upwards [hallN] with N hN
  intro stage hi lo hhi hlo
  left
  have hstrict := hN stage
    (⟨(hi, lo), hhi, hlo⟩ : CrossTierPair (targetPrefix stage))
  simpa [iidUniformTieCandidateScore, Finset.sum_sub_distrib] using hstrict

/--
Source Proposition 1 with its literal independent uniform tie breaking.  Exact
cross-tier prefix equalities are rejected probabilistically, so no generic
no-tie premise is needed.
-/
theorem rankingTieredStrictPrefixDominance_iff_almostSure_uniformTieCorrect
    {n Stage : ℕ}
    (law : PMF (Ranking n))
    (targetPrefix : Fin Stage → Finset (Candidate n)) :
    (∀ stage : Fin Stage,
      ∀ hi lo : Candidate n,
        hi ∈ targetPrefix stage → lo ∉ targetPrefix stage →
          ∀ cut : RankingProperPrefixCut n,
            rankingTopPrefixProb law lo cut <
              rankingTopPrefixProb law hi cut) ↔
      (∀ diff : RankingProperPrefixCut n → ℝ,
        ReasonablePrefixWeights diff →
          letI : MeasurableSpace (Ranking n × Ranking n) := ⊤
          ∀ᵐ path ∂finitePMFIidPathMeasure (rankingUniformTieSignalLaw law),
            ∀ᶠ N : ℕ in Filter.atTop,
              iidUniformTieTieredCorrect
                (rankingPrefixScore diff) targetPrefix path N) := by
  classical
  constructor
  · exact
      rankingTieredStrictPrefixDominance_implies_almostSure_uniformTieCorrect
        law targetPrefix
  · intro hADI stage hi lo hhi hlo cut
    by_contra hnotStrict
    have hweakReverse :
        rankingTopPrefixProb law hi cut ≤
          rankingTopPrefixProb law lo cut := le_of_not_gt hnotStrict
    rcases lt_or_eq_of_le hweakReverse with hreverse | hequal
    · let diff : RankingProperPrefixCut n → ℝ :=
        fun k ↦ if k = cut then 1 else 0
      letI : MeasurableSpace (Ranking n × Ranking n) := ⊤
      have hconverges := hADI diff (ReasonablePrefixWeights.indicator cut)
      let reverseGap : Ranking n → ℝ := fun ranking ↦
        rankingPrefixScore diff lo ranking -
          rankingPrefixScore diff hi ranking
      have hmeanReverse :
          0 < AppliedModelingLib.pmfExp (rankingUniformTieSignalLaw law)
            (fun signal ↦ reverseGap signal.1) := by
        rw [pmfExp_rankingUniformTieSignalLaw_fst law reverseGap]
        rw [show reverseGap = (fun ranking ↦
          rankingPrefixScore diff lo ranking -
            rankingPrefixScore diff hi ranking) by rfl,
          AppliedModelingLib.pmfExp_sub]
        change 0 < AppliedModelingLib.pmfExp law
            (prefixScoreFromEvent diff rankingInTopPrefix lo) -
          AppliedModelingLib.pmfExp law
            (prefixScoreFromEvent diff rankingInTopPrefix hi)
        rw [
          pmfExp_prefixScoreFromEvent_eq_prefixExpectedScore,
          pmfExp_prefixScoreFromEvent_eq_prefixExpectedScore]
        simpa [reverseGap, rankingPrefixScore, rankingTopPrefixProb,
          prefixExpectedScore, diff, sub_pos] using hreverse
      have hreversed :=
        ae_eventually_iidPath_score_gap_pos_of_pmfExp_pos
          (rankingUniformTieSignalLaw law)
          (fun signal ↦ reverseGap signal.1) hmeanReverse
      have hfalse :
          ∀ᵐ path ∂finitePMFIidPathMeasure (rankingUniformTieSignalLaw law),
            False := by
        filter_upwards [hconverges, hreversed] with path hcorrect hrev
        rcases (hcorrect.and hrev).exists with ⟨N, hNcorrect, hNrev⟩
        have hpairCorrect := hNcorrect stage hi lo hhi hlo
        rcases hpairCorrect with hscore | ⟨hscore, _⟩
        · have :
              0 < iidUniformTieCandidateScore
                    (rankingPrefixScore diff) path N lo -
                  iidUniformTieCandidateScore
                    (rankingPrefixScore diff) path N hi := by
            simpa [iidUniformTieCandidateScore, reverseGap,
              Finset.sum_sub_distrib] using hNrev
          linarith
        · have :
              0 < iidUniformTieCandidateScore
                    (rankingPrefixScore diff) path N lo -
                  iidUniformTieCandidateScore
                    (rankingPrefixScore diff) path N hi := by
            simpa [iidUniformTieCandidateScore, reverseGap,
              Finset.sum_sub_distrib] using hNrev
          linarith
      rcases hfalse.exists with ⟨_, h⟩
      exact h
    · let diff : RankingProperPrefixCut n → ℝ :=
        fun k ↦ if k = cut then 1 else 0
      let gap : Ranking n → ℝ := fun ranking ↦
        rankingPrefixScore diff hi ranking -
          rankingPrefixScore diff lo ranking
      let productGap : Ranking n × Ranking n → ℝ :=
        fun signal ↦ gap signal.1
      letI : MeasurableSpace (Ranking n × Ranking n) := ⊤
      have hmeanGapLaw : AppliedModelingLib.pmfExp law gap = 0 := by
        rw [show gap = (fun ranking ↦
          rankingPrefixScore diff hi ranking -
            rankingPrefixScore diff lo ranking) by rfl,
          AppliedModelingLib.pmfExp_sub]
        change AppliedModelingLib.pmfExp law
            (prefixScoreFromEvent diff rankingInTopPrefix hi) -
          AppliedModelingLib.pmfExp law
            (prefixScoreFromEvent diff rankingInTopPrefix lo) = 0
        rw [
          pmfExp_prefixScoreFromEvent_eq_prefixExpectedScore,
          pmfExp_prefixScoreFromEvent_eq_prefixExpectedScore]
        apply sub_eq_zero.mpr
        simpa [gap, rankingPrefixScore, rankingTopPrefixProb,
          prefixExpectedScore, diff] using hequal
      have hmeanProduct :
          AppliedModelingLib.pmfExp (rankingUniformTieSignalLaw law) productGap = 0 := by
        rw [show productGap = (fun signal ↦ gap signal.1) by rfl,
          pmfExp_rankingUniformTieSignalLaw_fst law gap, hmeanGapLaw]
      have hconverges := hADI diff (ReasonablePrefixWeights.indicator cut)
      by_cases hnondegenerate :
          ∃ ranking : Ranking n,
            0 < (law ranking).toReal ∧ gap ranking ≠ 0
      · rcases hnondegenerate with
          ⟨rankingWitness, hrankingMass, hrankingGap⟩
        let tieWitness : Ranking n := Equiv.refl (Candidate n)
        let signalWitness : Ranking n × Ranking n :=
          (rankingWitness, tieWitness)
        have htieMass :
            0 < ((PMF.uniformOfFintype (Ranking n)) tieWitness).toReal := by
          apply ENNReal.toReal_pos
          · exact ((PMF.apply_pos_iff _ _).mpr
              (by simpa using PMF.mem_support_uniformOfFintype tieWitness)).ne'
          · exact (PMF.uniformOfFintype (Ranking n)).apply_ne_top tieWitness
        have hsignalMass :
            0 < ((rankingUniformTieSignalLaw law) signalWitness).toReal := by
          simp only [rankingUniformTieSignalLaw, signalWitness,
            AppliedModelingLib.pmfProd_apply_toReal]
          exact mul_pos hrankingMass htieMass
        have hsignalGap : productGap signalWitness ≠ 0 := by
          simpa [productGap, signalWitness] using hrankingGap
        have hnotEventually :=
          ae_not_eventually_nonneg_iidPath_partialSum_of_mean_zero_of_support_ne_zero
            (rankingUniformTieSignalLaw law) productGap hmeanProduct
            signalWitness hsignalMass hsignalGap
        have hfalse :
            ∀ᵐ path ∂finitePMFIidPathMeasure (rankingUniformTieSignalLaw law),
              False := by
          filter_upwards [hconverges, hnotEventually] with path hcorrect hnotNonneg
          apply hnotNonneg
          have hcorrectShift :=
            (Filter.tendsto_add_atTop_nat 1).eventually hcorrect
          filter_upwards [hcorrectShift] with N hNcorrect
          have hpairCorrect := hNcorrect stage hi lo hhi hlo
          rcases hpairCorrect with hscore | ⟨hscore, _⟩
          · have hgapScore :
                0 < iidUniformTieCandidateScore
                      (rankingPrefixScore diff) path (N + 1) hi -
                    iidUniformTieCandidateScore
                      (rankingPrefixScore diff) path (N + 1) lo := by
              linarith
            simpa [productGap, gap, iidUniformTieCandidateScore,
              Finset.sum_sub_distrib] using hgapScore.le
          · have hgapScore :
                iidUniformTieCandidateScore
                      (rankingPrefixScore diff) path (N + 1) hi -
                    iidUniformTieCandidateScore
                      (rankingPrefixScore diff) path (N + 1) lo = 0 := by
              linarith
            simpa [productGap, gap, iidUniformTieCandidateScore,
              Finset.sum_sub_distrib] using hgapScore.ge
        rcases hfalse.exists with ⟨_, h⟩
        exact h
      · push Not at hnondegenerate
        have hsupportZero :
            ∀ signal : Ranking n × Ranking n,
              0 < ((rankingUniformTieSignalLaw law) signal).toReal →
                productGap signal = 0 := by
          intro signal hsignal
          have hprod :
              0 < (law signal.1).toReal *
                ((PMF.uniformOfFintype (Ranking n)) signal.2).toReal := by
            simpa [rankingUniformTieSignalLaw,
              AppliedModelingLib.pmfProd_apply_toReal] using hsignal
          have hfirstNonneg : 0 ≤ (law signal.1).toReal := ENNReal.toReal_nonneg
          have hsecondNonneg :
              0 ≤ ((PMF.uniformOfFintype (Ranking n)) signal.2).toReal :=
            ENNReal.toReal_nonneg
          have hfirstPos : 0 < (law signal.1).toReal := by
            rcases (mul_pos_iff.mp hprod) with hpositive | hnegative
            · exact hpositive.1
            · exact False.elim ((not_lt_of_ge hfirstNonneg) hnegative.1)
          exact hnondegenerate signal.1 hfirstPos
        have hallZero := ae_all_iidPath_of_forall_support
          (rankingUniformTieSignalLaw law) (fun signal ↦ productGap signal = 0)
          hsupportZero
        have hneCandidates : hi ≠ lo := by
          intro heqCandidates
          subst lo
          exact hlo hhi
        let baseTie : Ranking n := Equiv.refl (Candidate n)
        let badTie : Ranking n :=
          if h : rankOf baseTie lo < rankOf baseTie hi then baseTie
          else swapCandidatePositions baseTie hi lo
        have hbadTie : rankOf badTie lo < rankOf badTie hi := by
          dsimp [badTie]
          split
          next h => exact h
          next h =>
            rw [rankOf_swapCandidatePositions_right,
              rankOf_swapCandidatePositions_left]
            have hrankNe : rankOf baseTie hi ≠ rankOf baseTie lo := by
              intro hrank
              exact hneCandidates (baseTie.symm.injective hrank)
            exact lt_of_le_of_ne (le_of_not_gt h) hrankNe
        obtain ⟨rankingWitness, hrankingMass⟩ :=
          exists_pmf_toReal_pos law
        let badSignal : Ranking n × Ranking n := (rankingWitness, badTie)
        have hbadTieMass :
            0 < ((PMF.uniformOfFintype (Ranking n)) badTie).toReal := by
          apply ENNReal.toReal_pos
          · exact ((PMF.apply_pos_iff _ _).mpr
              (by simpa using PMF.mem_support_uniformOfFintype badTie)).ne'
          · exact (PMF.uniformOfFintype (Ranking n)).apply_ne_top badTie
        have hbadSignalMass :
            0 < ((rankingUniformTieSignalLaw law) badSignal).toReal := by
          simp only [rankingUniformTieSignalLaw, badSignal,
            AppliedModelingLib.pmfProd_apply_toReal]
          exact mul_pos hrankingMass hbadTieMass
        have hbadOccurs := ae_frequently_iidPath_eq_of_atom_pos
          (rankingUniformTieSignalLaw law) badSignal hbadSignalMass
        have hfalse :
            ∀ᵐ path ∂finitePMFIidPathMeasure (rankingUniformTieSignalLaw law),
              False := by
          filter_upwards [hconverges, hallZero, hbadOccurs]
            with path hcorrect hzero hnotAvoid
          apply hnotAvoid
          filter_upwards [hcorrect] with N hNcorrect
          intro hbadAtN
          have hpairCorrect := hNcorrect stage hi lo hhi hlo
          have hscoreEq :
              iidUniformTieCandidateScore
                  (rankingPrefixScore diff) path N hi =
                iidUniformTieCandidateScore
                  (rankingPrefixScore diff) path N lo := by
            apply sub_eq_zero.mp
            simp only [iidUniformTieCandidateScore]
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_eq_zero
            intro voter hvoter
            have hz := hzero voter
            simpa [productGap, gap] using hz
          rcases hpairCorrect with hscore | ⟨_, htie⟩
          · linarith
          · rw [hbadAtN] at htie
            exact (not_lt_of_ge hbadTie.le) htie
        rcases hfalse.exists with ⟨_, h⟩
        exact h

end

end GGSG19TopThree
