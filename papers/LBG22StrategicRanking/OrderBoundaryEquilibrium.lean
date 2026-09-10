import LBG22StrategicRanking.UniquenessPrimitiveRepairs
import LBG22StrategicRanking.MultidimensionalPrimitiveRepairs

/-!
# Known score-priority boundaries and almost-everywhere equilibrium

Applicants compare scores first and use their publicly known, fixed priority
at a score tie. This is the author's clarified reading of the stated model,
not an additional economic assumption or a correction to the admission rule.

An order boundary is completed by including a key when every strictly higher
key has rank above the cutoff. This distinguishes scores inside an empty
score gap from the actual admission boundary. Its reward is bounded below
by the strict-percentile reward and above by that reward at every strictly
higher score. Continuity of effort cost therefore transports best responses
against *all* nonnegative deviations. Equality on realized applicants alone
would not justify this strategic conclusion.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory Filter
open scoped Topology

/-- Population mass weakly below a specified score-priority key. The priority
argument specifies a comparison key; it is not an action available to an
applicant. In all strategic comparisons the applicant's own priority is fixed. -/
noncomputable def scorePriorityRank {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (score tie : α → ℝ) (v priority : ℝ) : ℝ :=
  (μ {y | score y < v ∨ score y = v ∧ tie y ≤ priority}).toReal

theorem scorePriorityRank_at_applicant {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (score tie : α → ℝ) (x : α) (v : ℝ) :
    scorePriorityRank μ score tie v (tie x) =
      counterfactualTieBrokenRank μ score tie x v := rfl

theorem scorePriorityRank_mono_priority {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (score tie : α → ℝ) (v : ℝ) :
    Monotone (scorePriorityRank μ score tie v) := by
  intro p q hpq
  apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
  rintro y (hy | ⟨hy, ht⟩)
  · exact Or.inl hy
  · exact Or.inr ⟨hy, ht.trans hpq⟩

theorem scorePriorityRank_le_of_score_lt {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (score tie : α → ℝ)
    {v w : ℝ} (hvw : v < w) (p q : ℝ) :
    scorePriorityRank μ score tie v p ≤ scorePriorityRank μ score tie w q := by
  apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
  rintro y (hy | ⟨hy, _⟩)
  · exact Or.inl (hy.trans hvw)
  · exact Or.inl (hy ▸ hvw)

/-- A score-priority key is above a completed order boundary when every
strictly higher key has contour mass strictly above the population cutoff.
The weak/strict choice for the one boundary applicant is immaterial to the
almost-everywhere equilibrium theorem below. -/
def ScorePriorityAboveCutoff {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (score tie : α → ℝ) (cutoff v priority : ℝ) : Prop :=
  ∀ w q : ℝ, v < w ∨ v = w ∧ priority < q →
    cutoff < scorePriorityRank μ score tie w q

theorem scorePriorityAboveCutoff_of_rank_lt {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (score tie : α → ℝ)
    {c v p : ℝ} (h : c < scorePriorityRank μ score tie v p) :
    ScorePriorityAboveCutoff μ score tie c v p := by
  intro w q hw
  rcases hw with hw | ⟨rfl, hp⟩
  · exact h.trans_le (scorePriorityRank_le_of_score_lt μ score tie hw p q)
  · exact h.trans_le (scorePriorityRank_mono_priority μ score tie v hp.le)

/-- Right continuity in the priority coordinate follows from continuity of
finite measures from above; no independence or density assumption is used. -/
theorem scorePriorityRank_rightContinuous {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {score tie : α → ℝ}
    (hscore : Measurable score) (htie : Measurable tie) (v p : ℝ) :
    Tendsto (scorePriorityRank μ score tie v) (𝓝[>] p)
      (𝓝 (scorePriorityRank μ score tie v p)) := by
  let S : ℝ → Set α := fun q => {y | score y < v ∨ score y = v ∧ tie y ≤ q}
  have hS (q : ℝ) : MeasurableSet (S q) :=
    (measurableSet_lt hscore measurable_const).union
      ((measurableSet_eq_fun hscore measurable_const).inter
        (measurableSet_le htie measurable_const))
  have hinter : (⋂ q > p, S q) = S p := by
    ext y
    simp only [mem_iInter, S, mem_setOf_eq]
    constructor
    · intro h
      rcases h (p + 1) (by linarith) with hlt | ⟨heq, _⟩
      · exact Or.inl hlt
      · refine Or.inr ⟨heq, le_of_forall_gt_imp_ge_of_dense ?_⟩
        intro q hpq
        rcases h q hpq with hlt | ⟨_, hle⟩
        · exact (not_lt_of_ge heq.ge hlt).elim
        · exact hle
    · intro h q hpq
      rcases h with h | ⟨h, ht⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, ht.trans hpq.le⟩
  have hlim := tendsto_measure_biInter_gt (μ := μ) (s := S)
    (a := p) (fun q _ => (hS q).nullMeasurableSet)
    (fun i j _ hij y hy => by
      rcases hy with hy | ⟨hy, ht⟩
      · exact Or.inl hy
      · exact Or.inr ⟨hy, ht.trans hij⟩)
    ⟨p + 1, by linarith, measure_ne_top μ _⟩
  rw [hinter] at hlim
  exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp hlim

theorem cutoff_le_scorePriorityRank_of_above {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {score tie : α → ℝ}
    (hscore : Measurable score) (htie : Measurable tie) {c v p : ℝ}
    (h : ScorePriorityAboveCutoff μ score tie c v p) :
    c ≤ scorePriorityRank μ score tie v p := by
  apply ge_of_tendsto (scorePriorityRank_rightContinuous μ hscore htie v p)
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (h v q (Or.inr ⟨rfl, hq⟩)).le

/-- The finite reward level selected by the score-priority order boundaries. -/
noncomputable def scorePriorityBand {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (score tie : α → ℝ) {n : ℕ}
    (cutoff : Fin (n + 1) → ℝ) (v priority : ℝ) : Fin (n + 1) := by
  classical
  exact Finset.univ.sup
    (fun i => if ScorePriorityAboveCutoff μ score tie (cutoff i) v priority then i else 0)

theorem finiteLowerRankBand_le_scorePriorityBand {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (score tie : α → ℝ) {n : ℕ}
    (cutoff : Fin (n + 1) → ℝ) (v p : ℝ) :
    finiteLowerRankBand cutoff (scorePriorityRank μ score tie v p) ≤
      scorePriorityBand μ score tie cutoff v p := by
  classical
  apply Finset.sup_le_iff.mpr
  intro i _
  split_ifs with hi
  · have h := scorePriorityAboveCutoff_of_rank_lt μ score tie hi
    simpa only [if_pos h] using
      (Finset.le_sup (f := fun j =>
        if ScorePriorityAboveCutoff μ score tie (cutoff j) v p then j else 0)
        (Finset.mem_univ i))
  · exact Fin.zero_le _

theorem scorePriorityBand_le_finiteLowerRankBand_of_score_lt
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (score tie : α → ℝ) {n : ℕ} (cutoff : Fin (n + 1) → ℝ)
    {v w : ℝ} (hvw : v < w) (p q : ℝ) :
    scorePriorityBand μ score tie cutoff v p ≤
      finiteLowerRankBand cutoff (scorePriorityRank μ score tie w q) := by
  classical
  apply Finset.sup_le_iff.mpr
  intro i _
  split_ifs with hi
  · exact le_finiteLowerRankBand_of_cutoff_lt (hi w q (Or.inl hvw))
  · exact Fin.zero_le _

/-- Off the finitely many cutoff percentiles, the order-boundary and
strict-percentile representations select exactly the same reward level. -/
theorem scorePriorityBand_eq_of_rank_ne_cutoffs
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {score tie : α → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    {n : ℕ} (cutoff : Fin (n + 1) → ℝ) (v p : ℝ)
    (hne : ∀ i, scorePriorityRank μ score tie v p ≠ cutoff i) :
    scorePriorityBand μ score tie cutoff v p =
      finiteLowerRankBand cutoff (scorePriorityRank μ score tie v p) := by
  classical
  apply le_antisymm _ (finiteLowerRankBand_le_scorePriorityBand μ score tie cutoff v p)
  apply Finset.sup_le_iff.mpr
  intro i _
  split_ifs with hi
  · exact le_finiteLowerRankBand_of_cutoff_lt
      (lt_of_le_of_ne (cutoff_le_scorePriorityRank_of_above μ hscore htie hi) (hne i).symm)
  · exact Fin.zero_le _

/-- The applicant exceptional set is the preimage of a finite set of ranks.
It is null for the source's fixed injective tie order, even with score atoms. -/
theorem scorePriorityBand_current_ae_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {score tie : α → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    [NoAtoms (Measure.map tie μ)] {n : ℕ} (cutoff : Fin (n + 1) → ℝ) :
    ∀ᵐ x ∂μ, scorePriorityBand μ score tie cutoff (score x) (tie x) =
      finiteLowerRankBand cutoff (tieBrokenRank μ score tie x) := by
  have hneq (i : Fin (n + 1)) : ∀ᵐ x ∂μ, tieBrokenRank μ score tie x ≠ cutoff i := by
    have hnull := congrArg (fun ν : Measure ℝ => ν {cutoff i})
      (tieBrokenRank_map_eq_uniform_of_noAtoms_tie μ hscore htie)
    dsimp only at hnull
    rw [Measure.map_apply (measurable_tieBrokenRank hscore htie)
      (measurableSet_singleton _), measure_singleton] at hnull
    rw [ae_iff]
    simpa only [not_not] using hnull
  filter_upwards [ae_all_iff.mpr hneq] with x hx
  exact scorePriorityBand_eq_of_rank_ne_cutoffs μ hscore htie cutoff (score x) (tie x) hx

/-- Increasing an effort slightly can attain every order-boundary reward.
Continuity of cost then transports *all* deviation comparisons at once;
there is no deviation-dependent exceptional applicant set. -/
theorem nonnegativeBestResponse_boundary_iff
    {cost lower upper : ℝ → ℝ} {e : ℝ}
    (hp : ContinuousOn cost (Ici 0))
    (hle : ∀ d, 0 ≤ d → lower d ≤ upper d)
    (happrox : ∀ d u, 0 ≤ d → d < u → upper d ≤ lower u)
    (heq : lower e = upper e) :
    (∀ d, 0 ≤ d → lower d - cost d ≤ lower e - cost e) ↔
      (∀ d, 0 ≤ d → upper d - cost d ≤ upper e - cost e) := by
  constructor
  · intro hbest d hd
    have hcost : Tendsto cost (𝓝[>] d) (𝓝 (cost d)) :=
      (hp d hd).mono (fun u hu => hd.trans hu.le)
    apply le_of_tendsto (tendsto_const_nhds.sub hcost)
    filter_upwards [self_mem_nhdsWithin] with u hu
    have h := hbest u (hd.trans hu.le)
    have ha := happrox d u hd hu
    rw [heq] at h
    linarith
  · intro hbest d hd
    have h := hbest d hd
    have hl := hle d hd
    rw [← heq] at h
    linarith

/-- The strict-percentile representation of a best response on an arbitrary
population. On the source unit-rank population this is definitionally the
existing `SourceFiniteBestResponseAt` predicate. -/
def StrictPercentileBestResponseAt {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (cost production : ℝ → ℝ) (skill score tie : α → ℝ)
    {n : ℕ} (cutoff : Fin (n + 1) → ℝ) (reward : ℕ → ℝ) (x : α) (e : ℝ) : Prop :=
  0 ≤ e ∧ score x = production e * skill x ∧
  ∀ d : ℝ, 0 ≤ d →
    reward (finiteLowerRankBand cutoff
      (counterfactualTieBrokenRank μ score tie x (production d * skill x))).val - cost d ≤
    reward (finiteLowerRankBand cutoff (tieBrokenRank μ score tie x)).val - cost e

/-- Feasibility and every nonnegative effort deviation under the known
score-priority order. Population scores and the applicant's priority remain
fixed across deviations. Equilibrium requires this predicate almost everywhere. -/
def ScorePriorityBestResponseAt {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (cost production : ℝ → ℝ) (skill score tie : α → ℝ)
    {n : ℕ} (cutoff : Fin (n + 1) → ℝ) (reward : ℕ → ℝ) (x : α) (e : ℝ) : Prop :=
  0 ≤ e ∧ score x = production e * skill x ∧
  ∀ d : ℝ, 0 ≤ d →
    reward (scorePriorityBand μ score tie cutoff (production d * skill x) (tie x)).val - cost d ≤
    reward (scorePriorityBand μ score tie cutoff (score x) (tie x)).val - cost e

/-- At an applicant whose realized rewards agree, the two representations
have exactly the same best responses. Strictly higher effort gives strictly
higher score at positive skill, so the approximation uses only feasible
effort choices and never changes the known priority. -/
theorem scorePriorityBestResponseAt_iff_of_current_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {cost production : ℝ → ℝ} {skill score tie : α → ℝ}
    {n : ℕ} (cutoff : Fin (n + 1) → ℝ) {reward : ℕ → ℝ}
    (hp : ContinuousOn cost (Ici 0)) (hg : StrictMonoOn production (Ici 0))
    (hr : MonotoneOn reward (Icc (0 : ℕ) n)) {x : α} (hf : 0 < skill x)
    (hcurrent : scorePriorityBand μ score tie cutoff (score x) (tie x) =
      finiteLowerRankBand cutoff (tieBrokenRank μ score tie x)) (e : ℝ) :
    StrictPercentileBestResponseAt μ cost production skill score tie cutoff reward x e ↔
      ScorePriorityBestResponseAt μ cost production skill score tie cutoff reward x e := by
  have hreward : Monotone (fun i : Fin (n + 1) => reward i.val) := by
    intro i j hij
    exact hr ⟨Nat.zero_le _, Nat.le_of_lt_succ i.isLt⟩
      ⟨Nat.zero_le _, Nat.le_of_lt_succ j.isLt⟩ hij
  let lower : ℝ → ℝ := fun d => reward (finiteLowerRankBand cutoff
    (scorePriorityRank μ score tie (production d * skill x) (tie x))).val
  let upper : ℝ → ℝ := fun d =>
    reward (scorePriorityBand μ score tie cutoff (production d * skill x) (tie x)).val
  have hle (d : ℝ) (_hd : 0 ≤ d) : lower d ≤ upper d :=
    hreward (finiteLowerRankBand_le_scorePriorityBand μ score tie cutoff _ _)
  have happrox (d u : ℝ) (hd : 0 ≤ d) (hdu : d < u) : upper d ≤ lower u :=
    hreward (scorePriorityBand_le_finiteLowerRankBand_of_score_lt μ score tie cutoff
      (mul_lt_mul_of_pos_right (hg hd (hd.trans hdu.le) hdu) hf) _ _)
  by_cases he : 0 ≤ e
  · by_cases hs : score x = production e * skill x
    · have heq : lower e = upper e := by
        dsimp [lower, upper]
        rw [← hs, hcurrent]
        rfl
      have hiff := nonnegativeBestResponse_boundary_iff hp hle happrox heq
      have hown : counterfactualTieBrokenRank μ score tie x (production e * skill x) =
          tieBrokenRank μ score tie x := by rw [← hs]; rfl
      simp only [StrictPercentileBestResponseAt, ScorePriorityBestResponseAt, he, hs, true_and]
      simpa only [lower, upper, scorePriorityRank_at_applicant, hown] using hiff
    · simp only [StrictPercentileBestResponseAt, ScorePriorityBestResponseAt, hs,
        false_and, and_false]
  · simp only [StrictPercentileBestResponseAt, ScorePriorityBestResponseAt, he, false_and]

/-- Equality of equilibrium predicates on one common full-measure applicant
set, with every deviation quantified inside that set. The hypotheses are
ordinary source primitives: positive skill almost everywhere, continuous
cost, strictly increasing production, and the fixed nonatomic tie order. -/
theorem scorePriorityBestResponse_ae_iff
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {cost production : ℝ → ℝ} {skill score tie effort : α → ℝ}
    {n : ℕ} (cutoff : Fin (n + 1) → ℝ) {reward : ℕ → ℝ}
    (hp : ContinuousOn cost (Ici 0)) (hg : StrictMonoOn production (Ici 0))
    (hr : MonotoneOn reward (Icc (0 : ℕ) n)) (hf : ∀ᵐ x ∂μ, 0 < skill x)
    (hscore : Measurable score) (htie : Measurable tie) [NoAtoms (Measure.map tie μ)] :
    (∀ᵐ x ∂μ, StrictPercentileBestResponseAt μ cost production skill score tie cutoff reward
      x (effort x)) ↔
    (∀ᵐ x ∂μ, ScorePriorityBestResponseAt μ cost production skill score tie cutoff reward
      x (effort x)) := by
  apply eventually_congr
  filter_upwards [hf, scorePriorityBand_current_ae_eq μ hscore htie cutoff] with x hfx hx
  exact scorePriorityBestResponseAt_iff_of_current_eq μ cutoff hp hg hr hfx hx (effort x)

/-- For the source uniform skill-rank population, positive skill almost
everywhere and nonatomic priorities follow from the existing model
assumptions; neither is added as a new economic restriction. -/
theorem sourceFiniteBestResponse_ae_iff_scorePriority
    {cost production skill score tie effort : ℝ → ℝ} {n : ℕ}
    (cutoff : Fin (n + 1) → ℝ) {reward : ℕ → ℝ}
    (hp : ContinuousOn cost (Ici 0)) (hg : StrictMonoOn production (Ici 0))
    (hr : MonotoneOn reward (Icc (0 : ℕ) n))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hscore : Measurable score) (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1)) :
    (∀ᵐ t ∂unitRankMeasure,
      SourceFiniteBestResponseAt cost production skill score tie cutoff reward t (effort t)) ↔
    (∀ᵐ t ∂unitRankMeasure,
      ScorePriorityBestResponseAt unitRankMeasure cost production skill score tie cutoff reward
        t (effort t)) := by
  letI := noAtoms_map_tie_of_injOn_unitRank htie hinj
  have hfpos : ∀ᵐ t ∂unitRankMeasure, 0 < skill t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hf0.trans_lt (hf ⟨le_rfl, zero_le_one⟩ ⟨ht.1.le, ht.2⟩ ht.1)
  exact scorePriorityBestResponse_ae_iff unitRankMeasure cutoff hp hg hr hfpos hscore htie

/-- The old score-gap example is rejected by the stated order-boundary rule:
an empty gap is not the admission boundary, regardless of the fixed priority.
Its profitable-deviation calculation for inclusive numeric percentiles
therefore does not refute the clarified source model. -/
theorem rankBoundary_gap_not_scorePriorityAboveCutoff
    (tie : ℝ → ℝ) (x : ℝ) {v : ℝ} (hv : 0 < v) (hvhalf : v < 1 / 2) :
    ¬ ScorePriorityAboveCutoff unitRankMeasure rankBoundaryScore tie (1 / 2) v (tie x) := by
  intro h
  have hr := h ((v + 1 / 2) / 2) (tie x) (Or.inl (by linarith))
  rw [scorePriorityRank_at_applicant,
    rankBoundary_gap_rank tie x (by linarith) (by linarith)] at hr
  exact (lt_irrefl _ hr)

/-- The appendix's hard-budget action space, with the same known order
boundary for admission. This definition does not settle the separately
pending manuscript wording about enforcement of the budget. -/
def ScorePriorityHardBudgetBestResponseAt
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (cost production : ℝ → ℝ) (skill score tie : α → ℝ)
    (B rho c : ℝ) (x : α) (eM eU : ℝ) : Prop :=
  0 ≤ eM ∧ 0 ≤ eU ∧ eM + eU = B ∧ score x = production eM * skill x ∧
    ∀ dM dU : ℝ, 0 ≤ dM → 0 ≤ dU → dM + dU = B →
      sourceTwoLevelReward rho c
        (scorePriorityBand μ score tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
          (production dM * skill x) (tie x)).val - sourceMultitaskCost cost B dM dU ≤
      sourceTwoLevelReward rho c
        (scorePriorityBand μ score tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
          (score x) (tie x)).val - sourceMultitaskCost cost B eM eU

/-- The budget endpoint causes no missing deviation: at or beyond the budget
cost is at least one, whereas admission is at most one and the zero measured
effort action is feasible. Thus the hard-budget/scalar reduction also holds
for the order-boundary representation. -/
theorem scorePriorityHardBudgetBestResponseAt_iff_scalar
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {cost production : ℝ → ℝ} {skill score tie : α → ℝ} {B rho c eM eU : ℝ} {x : α}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hB : 0 ≤ B)
    (hpM : MonotoneOn cost (Ici 0)) (hp0 : cost 0 = 0) (hpB : 1 ≤ cost B) :
    ScorePriorityHardBudgetBestResponseAt μ cost production skill score tie B rho c x eM eU ↔
      eM ≤ B ∧ eU = B - eM ∧
        ScorePriorityBestResponseAt μ cost production skill score tie
          (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) x eM := by
  let R := fun v => sourceTwoLevelReward rho c
    (scorePriorityBand μ score tie (fun i : Fin 2 => sourceTwoLevelCutoff c i) v (tie x)).val
  have hc1 : c < 1 := by linarith [hc.2]
  have hq : rho / (1 - c) ∈ Icc (0 : ℝ) 1 :=
    ⟨(div_pos hrho (sub_pos.mpr hc1)).le,
      (div_le_one (sub_pos.mpr hc1)).mpr (by linarith [hc.2])⟩
  have hR (v : ℝ) : R v ∈ Icc (0 : ℝ) 1 := by
    dsimp only [R, sourceTwoLevelReward]
    split_ifs
    · exact ⟨le_rfl, zero_le_one⟩
    · exact hq
  constructor
  · intro hbest
    have hbudget := hbest.2.2.1
    refine ⟨by linarith [hbest.2.1], by linarith, hbest.1, hbest.2.2.2.1, ?_⟩
    have hzero := hbest.2.2.2.2 0 B le_rfl hB (zero_add B)
    rw [sourceMultitaskCost_eq_of_budget (zero_add B),
      sourceMultitaskCost_eq_of_budget hbudget, hp0, sub_zero] at hzero
    have hown : 0 ≤ R (score x) - cost eM := (hR _).1.trans hzero
    intro d hd
    by_cases hdB : d ≤ B
    · have h := hbest.2.2.2.2 d (B - d) hd (sub_nonneg.mpr hdB) (by ring)
      rw [sourceMultitaskCost_eq_of_budget (show d + (B - d) = B by ring),
        sourceMultitaskCost_eq_of_budget hbudget] at h
      exact h
    · have hcost : 1 ≤ cost d := hpB.trans (hpM hB hd (le_of_not_ge hdB))
      exact (sub_nonpos.mpr ((hR _).2.trans hcost)).trans hown
  · rintro ⟨he, rfl, hbest⟩
    have hbudget : eM + (B - eM) = B := by ring
    refine ⟨hbest.1, sub_nonneg.mpr he, hbudget, hbest.2.1, ?_⟩
    intro dM dU hdM _hdU hd
    rw [sourceMultitaskCost_eq_of_budget hd, sourceMultitaskCost_eq_of_budget hbudget]
    exact hbest.2.2 dM hdM

/-- The appendix hard-budget equilibria are unchanged by making the stated
score-priority convention explicit. In particular, no infeasible upward
perturbation at the budget endpoint is used. -/
theorem sourceHardBudgetBestResponse_ae_iff_scorePriority
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {cost production : ℝ → ℝ} {skill score tie eM eU : α → ℝ} {B rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hB : 0 ≤ B)
    (hp : ContinuousOn cost (Ici 0)) (hpM : MonotoneOn cost (Ici 0))
    (hp0 : cost 0 = 0) (hpB : 1 ≤ cost B) (hg : StrictMonoOn production (Ici 0))
    (hf : ∀ᵐ x ∂μ, 0 < skill x) (hscore : Measurable score) (htie : Measurable tie)
    [NoAtoms (Measure.map tie μ)] :
    (∀ᵐ x ∂μ, SourceHardBudgetBestResponseAt μ cost production skill score tie B rho c
      x (eM x) (eU x)) ↔
    (∀ᵐ x ∂μ, ScorePriorityHardBudgetBestResponseAt μ cost production skill score tie B rho c
      x (eM x) (eU x)) := by
  have hr := (sourceTwoLevelReward_strictMono hrho (by linarith [hc.2] : c < 1)).monotoneOn
  apply eventually_congr
  filter_upwards [hf, scorePriorityBand_current_ae_eq μ hscore htie
    (fun i : Fin 2 => sourceTwoLevelCutoff c i)] with x hfx hx
  rw [sourceHardBudgetBestResponseAt_iff_scalar μ hrho hc hB hpM hp0 hpB,
    scorePriorityHardBudgetBestResponseAt_iff_scalar μ hrho hc hB hpM hp0 hpB]
  exact and_congr Iff.rfl (and_congr Iff.rfl
    (scorePriorityBestResponseAt_iff_of_current_eq μ _ hp hg hr hfx hx (eM x)))

/-- Linear multidimensional production with endogenous total effort and the
known score-priority boundary. Every nonnegative vector is an available
deviation; no budget or preselected best coordinate is imposed. -/
def ScorePriorityMultidimensionalBestResponseAt
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) [IsFiniteMeasure μ] (cost : ℝ → ℝ) (coefficient : α → ι → ℝ)
    (score tie : α → ℝ) (h : ℝ) {n : ℕ}
    (cutoff : Fin (n + 1) → ℝ) (reward : ℕ → ℝ) (x : α) (effort : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ effort i) ∧ score x = h * ∑ i, effort i * coefficient x i ∧
    ∀ d : ι → ℝ, (∀ i, 0 ≤ d i) →
      reward (scorePriorityBand μ score tie cutoff
        (h * ∑ i, d i * coefficient x i) (tie x)).val - cost (∑ i, d i) ≤
      reward (scorePriorityBand μ score tie cutoff (score x) (tie x)).val - cost (∑ i, effort i)

/-- At positive combined skill, adding an arbitrarily small effort to a
positive-weight coordinate strictly raises score. Applying continuity to
the cost of the resulting total effort proves the full vector-deviation
bridge, not merely a comparison of concentrated effort vectors. -/
theorem sourceMultidimensionalBestResponseAt_iff_scorePriority_of_current_eq
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) [IsFiniteMeasure μ] {cost : ℝ → ℝ} {coefficient : α → ι → ℝ}
    {score tie : α → ℝ} {h : ℝ} {n : ℕ} (cutoff : Fin (n + 1) → ℝ)
    {reward : ℕ → ℝ} {x : α} {effort : ι → ℝ}
    (hp : ContinuousOn cost (Ici 0)) (hh : 0 < h)
    (hr : MonotoneOn reward (Icc (0 : ℕ) n)) (hpositive : ∃ i, 0 < coefficient x i)
    (hcurrent : scorePriorityBand μ score tie cutoff (score x) (tie x) =
      finiteLowerRankBand cutoff (tieBrokenRank μ score tie x)) :
    SourceMultidimensionalBestResponseAt μ cost coefficient score tie h
      (fun r => reward (finiteLowerRankBand cutoff r).val) x effort ↔
    ScorePriorityMultidimensionalBestResponseAt μ cost coefficient score tie h cutoff reward
      x effort := by
  classical
  have hreward : Monotone (fun i : Fin (n + 1) => reward i.val) := by
    intro i j hij
    exact hr ⟨Nat.zero_le _, Nat.le_of_lt_succ i.isLt⟩
      ⟨Nat.zero_le _, Nat.le_of_lt_succ j.isLt⟩ hij
  constructor
  · intro hb
    refine ⟨hb.1, hb.2.1, ?_⟩
    intro d hd
    obtain ⟨j, hj⟩ := hpositive
    let total : ℝ := ∑ i, d i
    have ht : 0 ≤ total := Finset.sum_nonneg (fun i _ => hd i)
    let deviation : ℝ → ι → ℝ := fun u i => d i + if i = j then u - total else 0
    have hfeasible (u : ℝ) (hu : total < u) : ∀ i, 0 ≤ deviation u i := by
      intro i
      dsimp only [deviation]
      split_ifs
      · exact add_nonneg (hd i) (sub_nonneg.mpr hu.le)
      · simpa only [add_zero] using hd i
    have hsum (u : ℝ) : (∑ i, deviation u i) = u := by
      simp [deviation, Finset.sum_add_distrib, total]
    have hscore (u : ℝ) : h * (∑ i, deviation u i * coefficient x i) =
        h * (∑ i, d i * coefficient x i) + h * (u - total) * coefficient x j := by
      simp only [deviation, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    have hcost : Tendsto cost (𝓝[>] total) (𝓝 (cost total)) :=
      (hp total ht).mono (fun u hu => ht.trans hu.le)
    rw [hcurrent]
    apply le_of_tendsto (tendsto_const_nhds.sub hcost)
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hbetter : h * (∑ i, d i * coefficient x i) <
        h * (∑ i, deviation u i * coefficient x i) := by
      rw [hscore]
      exact lt_add_of_pos_right _ (mul_pos (mul_pos hh (sub_pos.mpr hu)) hj)
    have hgain := hreward
      (scorePriorityBand_le_finiteLowerRankBand_of_score_lt μ score tie cutoff hbetter (tie x) (tie x))
    rw [scorePriorityRank_at_applicant] at hgain
    have hbest := hb.2.2 (deviation u) (hfeasible u hu)
    rw [hsum] at hbest
    dsimp only at hbest
    linarith
  · intro hb
    refine ⟨hb.1, hb.2.1, ?_⟩
    intro d hd
    have hbest := hb.2.2 d hd
    rw [hcurrent] at hbest
    have hgain := hreward (finiteLowerRankBand_le_scorePriorityBand μ score tie cutoff
      (h * ∑ i, d i * coefficient x i) (tie x))
    rw [scorePriorityRank_at_applicant] at hgain
    exact (sub_le_sub_right hgain _).trans hbest

/-- The same one-null-set equivalence holds for all nonnegative effort
vectors in Appendix B.1. The positive combined skill condition is inherited
from the source population and weights. -/
theorem sourceMultidimensionalBestResponse_ae_iff_scorePriority
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] [Nonempty ι]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {cost : ℝ → ℝ} {coefficient : α → ι → ℝ} {score tie : α → ℝ}
    {effort : α → ι → ℝ} {h : ℝ} {n : ℕ} (cutoff : Fin (n + 1) → ℝ)
    {reward : ℕ → ℝ} (hp : ContinuousOn cost (Ici 0)) (hh : 0 < h)
    (hr : MonotoneOn reward (Icc (0 : ℕ) n))
    (hpositive : ∀ᵐ x ∂μ, 0 < sourceCombinedSkill (coefficient x))
    (hscore : Measurable score) (htie : Measurable tie) [NoAtoms (Measure.map tie μ)] :
    (∀ᵐ x ∂μ, SourceMultidimensionalBestResponseAt μ cost coefficient score tie h
      (fun r => reward (finiteLowerRankBand cutoff r).val) x (effort x)) ↔
    (∀ᵐ x ∂μ, ScorePriorityMultidimensionalBestResponseAt μ cost coefficient score tie h
      cutoff reward x (effort x)) := by
  apply eventually_congr
  filter_upwards [hpositive, scorePriorityBand_current_ae_eq μ hscore htie cutoff] with x hpos hx
  obtain ⟨i, hi⟩ := sourceCombinedSkill_attained (coefficient x)
  exact sourceMultidimensionalBestResponseAt_iff_scorePriority_of_current_eq μ cutoff hp hh hr
    ⟨i, hi ▸ hpos⟩ hx

/-- Away from an atom of the population score distribution, changing only
the comparison priority changes a null subset of the lower contour. -/
theorem scorePriorityRank_eq_of_score_atom_null
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (score tie : α → ℝ)
    {v : ℝ} (hnull : μ {y | score y = v} = 0) (p q : ℝ) :
    scorePriorityRank μ score tie v p = scorePriorityRank μ score tie v q := by
  have hne : ∀ᵐ y ∂μ, score y ≠ v := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  have hsets : {y | score y < v ∨ score y = v ∧ tie y ≤ p} =ᵐ[μ]
      {y | score y < v ∨ score y = v ∧ tie y ≤ q} := by
    filter_upwards [hne] with y hy
    apply propext
    change (score y < v ∨ score y = v ∧ tie y ≤ p) ↔
      (score y < v ∨ score y = v ∧ tie y ≤ q)
    simp only [hy, false_and, or_false]
  exact congrArg ENNReal.toReal (measure_congr hsets)

/-- No boundary reward discrepancy is possible at a score that is not a
population atom, even if its numerical percentile equals a cutoff. -/
theorem scorePriorityBand_eq_of_score_atom_null
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (score tie : α → ℝ) {n : ℕ} (cutoff : Fin (n + 1) → ℝ)
    {v : ℝ} (hnull : μ {y | score y = v} = 0) (p : ℝ) :
    scorePriorityBand μ score tie cutoff v p =
      finiteLowerRankBand cutoff (scorePriorityRank μ score tie v p) := by
  classical
  apply le_antisymm _ (finiteLowerRankBand_le_scorePriorityBand μ score tie cutoff v p)
  apply Finset.sup_le_iff.mpr
  intro i _
  split_ifs with hi
  · have h := hi v (p + 1) (Or.inr ⟨rfl, by linarith⟩)
    rw [scorePriorityRank_eq_of_score_atom_null μ score tie hnull (p + 1) p] at h
    exact le_finiteLowerRankBand_of_cutoff_lt h
  · exact Fin.zero_le _

/-- A diffuse family of counterfactual scores avoids all population score
atoms almost everywhere: a finite measure has only countably many atoms.
No independence between the two score functions is required. -/
theorem scorePriorityBand_diffuse_scores_ae_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {score tie counterScore : α → ℝ} (hscore : Measurable score)
    (hcounter : AEMeasurable counterScore μ) [NoAtoms (Measure.map counterScore μ)]
    {n : ℕ} (cutoff : Fin (n + 1) → ℝ) :
    ∀ᵐ x ∂μ, scorePriorityBand μ score tie cutoff (counterScore x) (tie x) =
      finiteLowerRankBand cutoff (counterfactualTieBrokenRank μ score tie x (counterScore x)) := by
  have hcount := Measure.countable_meas_level_set_pos (μ := μ) hscore
  have havoid : ∀ᵐ x ∂μ, counterScore x ∉ {v | 0 < μ {y | score y = v}} :=
    (ae_map_iff hcounter hcount.measurableSet.compl).mp
      (hcount.ae_notMem (Measure.map counterScore μ))
  filter_upwards [havoid] with x hx
  apply scorePriorityBand_eq_of_score_atom_null μ score tie cutoff
  exact le_antisymm (le_of_not_gt hx) (zero_le _)

/-- Bounded-action version of the all-deviation transport. Only interior
deviations are approximated from above; at the upper endpoint the reward
representations agree. No condition on the size of the budget or its cost
is needed. -/
theorem boundedBestResponse_boundary_iff
    {cost lower upper : ℝ → ℝ} {e B : ℝ}
    (hp : ContinuousOn cost (Icc 0 B))
    (hle : ∀ d ∈ Icc 0 B, lower d ≤ upper d)
    (happrox : ∀ d u, 0 ≤ d → d < u → u ≤ B → upper d ≤ lower u)
    (heq : lower e = upper e) (htop : lower B = upper B) :
    (∀ d ∈ Icc 0 B, lower d - cost d ≤ lower e - cost e) ↔
      (∀ d ∈ Icc 0 B, upper d - cost d ≤ upper e - cost e) := by
  constructor
  · intro hbest d hd
    rcases lt_or_eq_of_le hd.2 with hdB | rfl
    · have hcost : Tendsto cost (𝓝[>] d) (𝓝 (cost d)) := by
        apply (hp d hd).mono_of_mem_nhdsWithin
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hdB)] with u hu huB
        exact ⟨hd.1.trans hu.le, huB⟩
      apply le_of_tendsto (tendsto_const_nhds.sub hcost)
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hdB)] with u hu huB
      have h := hbest u ⟨hd.1.trans hu.le, huB⟩
      have ha := happrox d u hd.1 hu huB
      rw [heq] at h
      linarith
    · simpa only [heq, htop] using hbest d hd
  · intro hbest d hd
    have h := hbest d hd
    have hl := hle d hd
    rw [← heq] at h
    linarith

/-- At an applicant with matching current and maximal-score rewards, all
hard-budget deviations transfer without any lower bound on budget cost. -/
theorem sourceHardBudgetBestResponseAt_iff_scorePriority_of_endpoint_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {cost production : ℝ → ℝ} {skill score tie : α → ℝ} {B rho c eM eU : ℝ} {x : α}
    (hrho : 0 < rho) (hc : c < 1)
    (hp : ContinuousOn cost (Icc 0 B)) (hg : StrictMonoOn production (Icc 0 B))
    (hf : 0 < skill x)
    (hcurrent : scorePriorityBand μ score tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
      (score x) (tie x) = finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (tieBrokenRank μ score tie x))
    (htop : scorePriorityBand μ score tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
      (production B * skill x) (tie x) =
      finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (counterfactualTieBrokenRank μ score tie x (production B * skill x))) :
    SourceHardBudgetBestResponseAt μ cost production skill score tie B rho c x eM eU ↔
      ScorePriorityHardBudgetBestResponseAt μ cost production skill score tie B rho c x eM eU := by
  let cuts := fun i : Fin 2 => sourceTwoLevelCutoff c i
  let R := fun i : Fin 2 => sourceTwoLevelReward rho c i.val
  have hR : Monotone R := by
    intro i j hij
    exact (sourceTwoLevelReward_strictMono hrho hc).monotoneOn
      ⟨Nat.zero_le _, Nat.le_of_lt_succ i.isLt⟩
      ⟨Nat.zero_le _, Nat.le_of_lt_succ j.isLt⟩ hij
  constructor
  · intro hb
    have hbudget := hb.2.2.1
    have he : eM ∈ Icc 0 B := ⟨hb.1, by linarith [hb.2.1]⟩
    let lower := fun d => R (finiteLowerRankBand cuts
      (counterfactualTieBrokenRank μ score tie x (production d * skill x)))
    let upper := fun d => R (scorePriorityBand μ score tie cuts (production d * skill x) (tie x))
    have hle (d : ℝ) (_hd : d ∈ Icc 0 B) : lower d ≤ upper d :=
      hR (finiteLowerRankBand_le_scorePriorityBand μ score tie cuts _ _)
    have happrox (d u : ℝ) (hd : 0 ≤ d) (hdu : d < u) (huB : u ≤ B) : upper d ≤ lower u :=
      hR (scorePriorityBand_le_finiteLowerRankBand_of_score_lt μ score tie cuts
        (mul_lt_mul_of_pos_right (hg ⟨hd, hdu.le.trans huB⟩
          ⟨hd.trans hdu.le, huB⟩ hdu) hf) _ _)
    have hown : counterfactualTieBrokenRank μ score tie x (production eM * skill x) =
        tieBrokenRank μ score tie x := by rw [← hb.2.2.2.1]; rfl
    have heq : lower eM = upper eM := by
      dsimp only [lower, upper, cuts]
      rw [← hb.2.2.2.1, hcurrent]
      rfl
    have htop' : lower B = upper B := congrArg R htop.symm
    have hbest : ∀ d ∈ Icc 0 B, lower d - cost d ≤ lower eM - cost eM := by
      intro d hd
      have h := hb.2.2.2.2 d (B - d) hd.1 (sub_nonneg.mpr hd.2) (by ring)
      rw [sourceMultitaskCost_eq_of_budget (show d + (B - d) = B by ring),
        sourceMultitaskCost_eq_of_budget hbudget] at h
      simpa only [lower, hown] using h
    have hnew := (boundedBestResponse_boundary_iff hp hle happrox heq htop').mp hbest
    refine ⟨hb.1, hb.2.1, hbudget, hb.2.2.2.1, ?_⟩
    intro dM dU hdM hdU hd
    rw [sourceMultitaskCost_eq_of_budget hd, sourceMultitaskCost_eq_of_budget hbudget,
      hb.2.2.2.1]
    exact hnew dM ⟨hdM, by linarith⟩
  · intro hb
    refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, ?_⟩
    intro dM dU hdM hdU hd
    have hbest := hb.2.2.2.2 dM dU hdM hdU hd
    rw [hcurrent] at hbest
    have hgain := hR (finiteLowerRankBand_le_scorePriorityBand μ score tie cuts
      (production dM * skill x) (tie x))
    exact (sub_le_sub_right hgain _).trans hbest

/-- General hard-budget equivalence from the ordinary atomless skill model.
The maximal feasible score is a nonzero multiple of skill, so its law is
nonatomic. It therefore avoids the countably many population score atoms
almost everywhere, giving the endpoint equality used in the bounded proof.
No assumption about `cost B`, `cost 0`, or a sufficiently large budget remains. -/
theorem sourceHardBudgetBestResponse_ae_iff_scorePriority_of_noAtoms_skill
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {cost production : ℝ → ℝ} {skill score tie eM eU : α → ℝ} {B rho c : ℝ}
    (hB : 0 < B) (hrho : 0 < rho) (hc : c < 1)
    (hp : ContinuousOn cost (Icc 0 B)) (hg : StrictMonoOn production (Icc 0 B))
    (hg0 : 0 ≤ production 0) (hskill : AEMeasurable skill μ)
    [NoAtoms (Measure.map skill μ)] (hf : ∀ᵐ x ∂μ, 0 < skill x)
    (hscore : Measurable score) (htie : Measurable tie) [NoAtoms (Measure.map tie μ)] :
    (∀ᵐ x ∂μ, SourceHardBudgetBestResponseAt μ cost production skill score tie B rho c
      x (eM x) (eU x)) ↔
    (∀ᵐ x ∂μ, ScorePriorityHardBudgetBestResponseAt μ cost production skill score tie B rho c
      x (eM x) (eU x)) := by
  have hgB : 0 < production B := hg0.trans_lt (hg ⟨le_rfl, hB.le⟩ ⟨hB.le, le_rfl⟩ hB)
  have hmax : AEMeasurable (fun x => production B * skill x) μ := aemeasurable_const.mul hskill
  haveI : NoAtoms (Measure.map (fun x => production B * skill x) μ) := by
    constructor
    intro z
    rw [Measure.map_apply_of_aemeasurable hmax (measurableSet_singleton z)]
    have hset : (fun x => production B * skill x) ⁻¹' {z} = skill ⁻¹' {z / production B} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff]
      rw [eq_div_iff hgB.ne', mul_comm]
    rw [hset, ← Measure.map_apply_of_aemeasurable hskill (measurableSet_singleton _), measure_singleton]
  apply eventually_congr
  filter_upwards [hf, scorePriorityBand_current_ae_eq μ hscore htie
    (fun i : Fin 2 => sourceTwoLevelCutoff c i),
    scorePriorityBand_diffuse_scores_ae_eq μ hscore hmax
      (fun i : Fin 2 => sourceTwoLevelCutoff c i)] with x hfx hx htop
  exact sourceHardBudgetBestResponseAt_iff_scorePriority_of_endpoint_eq μ hrho hc hp hg hfx hx htop

/-- The source independent-rank multitask population satisfies all premises
of the bounded bridge at every positive budget. Regularity is required only
on the actual unit skill interval and feasible effort interval. -/
theorem sourceIndependentHardBudgetBestResponse_ae_iff_scorePriority
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {cost production skill : ℝ → ℝ} {score tie eM eU : ℝ × α → ℝ} {B rho c : ℝ}
    (hB : 0 < B) (hrho : 0 < rho) (hc : c < 1)
    (hp : ContinuousOn cost (Icc 0 B)) (hg : StrictMonoOn production (Icc 0 B))
    (hg0 : 0 ≤ production 0) (hfc : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hscore : Measurable score) (htie : Measurable tie)
    [NoAtoms (Measure.map tie (unitRankMeasure.prod μ))] :
    (∀ᵐ x ∂unitRankMeasure.prod μ, SourceHardBudgetBestResponseAt (unitRankMeasure.prod μ)
      cost production (fun x => skill x.1) score tie B rho c x (eM x) (eU x)) ↔
    (∀ᵐ x ∂unitRankMeasure.prod μ, ScorePriorityHardBudgetBestResponseAt (unitRankMeasure.prod μ)
      cost production (fun x => skill x.1) score tie B rho c x (eM x) (eU x)) := by
  let f := fun x : ℝ × α => sourceClampedSkill skill x.1
  have hm := (continuous_sourceClampedSkill hfc).measurable
  have hfm : Measurable f := hm.comp measurable_fst
  have hmem : ∀ᵐ x ∂unitRankMeasure.prod μ, x.1 ∈ Ioc (0 : ℝ) 1 :=
    (measurePreserving_fst (μ := unitRankMeasure) (ν := μ)).quasiMeasurePreserving.ae
      (ae_restrict_mem measurableSet_Ioc)
  have heq : f =ᵐ[unitRankMeasure.prod μ] (fun x => skill x.1) := by
    filter_upwards [hmem] with x hx
    exact sourceClampedSkill_eq ⟨hx.1.le, hx.2⟩
  have hmap : Measure.map (fun x : ℝ × α => skill x.1) (unitRankMeasure.prod μ) =
      Measure.map (sourceClampedSkill skill) unitRankMeasure := by
    rw [← Measure.map_congr heq]
    change Measure.map (sourceClampedSkill skill ∘ Prod.fst) _ = _
    rw [← Measure.map_map hm measurable_fst,
      (measurePreserving_fst (μ := unitRankMeasure) (ν := μ)).map_eq]
  haveI : NoAtoms (Measure.map (fun x : ℝ × α => skill x.1) (unitRankMeasure.prod μ)) := by
    rw [hmap]
    apply noAtoms_map_tie_of_injOn_unitRank hm
    intro x hx y hy hxy
    rw [sourceClampedSkill_eq ⟨hx.1.le, hx.2⟩, sourceClampedSkill_eq ⟨hy.1.le, hy.2⟩] at hxy
    exact hf.injOn ⟨hx.1.le, hx.2⟩ ⟨hy.1.le, hy.2⟩ hxy
  have hpos : ∀ᵐ x ∂unitRankMeasure.prod μ, 0 < skill x.1 := by
    filter_upwards [hmem] with x hx
    exact hf0.trans_lt (hf ⟨le_rfl, zero_le_one⟩ ⟨hx.1.le, hx.2⟩ hx.1)
  exact sourceHardBudgetBestResponse_ae_iff_scorePriority_of_noAtoms_skill (unitRankMeasure.prod μ)
    hB hrho hc hp hg hg0 (hfm.aemeasurable.congr heq) hpos hscore htie

/-- Every population integral depending on the realized reward band is
unchanged. This covers admission capacity, applicant utility, and school
output for the same effort and score profile, without altering incentives. -/
theorem scorePriorityBand_integral_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {score tie : α → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    [NoAtoms (Measure.map tie μ)] {n : ℕ} (cutoff : Fin (n + 1) → ℝ)
    (observable : α → Fin (n + 1) → ℝ) :
    (∫ x, observable x (scorePriorityBand μ score tie cutoff (score x) (tie x)) ∂μ) =
      ∫ x, observable x (finiteLowerRankBand cutoff (tieBrokenRank μ score tie x)) ∂μ := by
  apply integral_congr_ae
  filter_upwards [scorePriorityBand_current_ae_eq μ hscore htie cutoff] with x hx
  rw [hx]

/-- Except for the null set of applicants exactly at one cutoff percentile,
the realized order-boundary admission decision equals the strict rank test.
This result is about outcomes; the separate best-response bridges compare
all counterfactual deviations. -/
theorem scorePriorityAboveCutoff_current_ae_iff
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {score tie : α → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    [NoAtoms (Measure.map tie μ)] (c : ℝ) :
    ∀ᵐ x ∂μ, ScorePriorityAboveCutoff μ score tie c (score x) (tie x) ↔
      c < tieBrokenRank μ score tie x := by
  have hnull := congrArg (fun ν : Measure ℝ => ν {c})
    (tieBrokenRank_map_eq_uniform_of_noAtoms_tie μ hscore htie)
  dsimp only at hnull
  rw [Measure.map_apply (measurable_tieBrokenRank hscore htie)
    (measurableSet_singleton _), measure_singleton] at hnull
  have hne : ∀ᵐ x ∂μ, tieBrokenRank μ score tie x ≠ c := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  filter_upwards [hne] with x hx
  exact ⟨fun h => lt_of_le_of_ne
      (cutoff_le_scorePriorityRank_of_above μ hscore htie h) hx.symm,
    fun h => scorePriorityAboveCutoff_of_rank_lt μ score tie h⟩

/-- The source's independent admission lottery with the publicly known
score-priority boundary. The lottery does not supply or change the tie key. -/
def scorePriorityTwoLevelAdmissionEvent {α : Type*}
    (score tie : ℝ → ℝ) (rho c : ℝ) : Set ((ℝ × ℝ) × α) :=
  {z | ScorePriorityAboveCutoff unitRankMeasure score tie c (score z.1.1) (tie z.1.1) ∧
    z.1.2 ∈ Ioc (0 : ℝ) (rho / (1 - c))}

/-- Admission outcomes agree for the same lottery draw, outside a fixed
null applicant set. There is no resampling or coupling of a different lottery. -/
theorem scorePriorityTwoLevelAdmissionEvent_ae_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {score tie : ℝ → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    [NoAtoms (Measure.map tie unitRankMeasure)] (rho c : ℝ) :
    scorePriorityTwoLevelAdmissionEvent (α := α) score tie rho c =ᵐ[independentSkillPopulation μ]
      sourceActualTwoLevelAdmissionEvent score tie rho c := by
  have hbase := scorePriorityAboveCutoff_current_ae_iff unitRankMeasure hscore htie c
  have hprod : ∀ᵐ z ∂unitRankMeasure.prod unitRankMeasure,
      ScorePriorityAboveCutoff unitRankMeasure score tie c (score z.1) (tie z.1) ↔
        c < tieBrokenRank unitRankMeasure score tie z.1 :=
    (measurePreserving_fst (μ := unitRankMeasure) (ν := unitRankMeasure)).quasiMeasurePreserving.ae hbase
  have hfull := (measurePreserving_fst (μ := unitRankMeasure.prod unitRankMeasure)
    (ν := μ)).quasiMeasurePreserving.ae hprod
  filter_upwards [hfull] with z hz
  apply propext
  exact and_congr_left (fun _ => hz)

/-- The probability of actual admission is invariant under the two
equivalent representations of the stated model. -/
theorem scorePriorityTwoLevelAdmissionEvent_measure_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {score tie : ℝ → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    [NoAtoms (Measure.map tie unitRankMeasure)] (rho c : ℝ) :
    independentSkillPopulation μ (scorePriorityTwoLevelAdmissionEvent score tie rho c) =
      independentSkillPopulation μ (sourceActualTwoLevelAdmissionEvent score tie rho c) :=
  measure_congr (scorePriorityTwoLevelAdmissionEvent_ae_eq μ hscore htie rho c)

/-- Conditional admission laws agree, including the zero-probability branch
of the conditional-measure definition. Positive-capacity results may use
their existing capacity proof, without an extra event-probability premise. -/
theorem scorePriorityTwoLevelAdmissionEvent_cond_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {score tie : ℝ → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    [NoAtoms (Measure.map tie unitRankMeasure)] (rho c : ℝ) :
    ProbabilityTheory.cond (independentSkillPopulation μ)
        (scorePriorityTwoLevelAdmissionEvent score tie rho c) =
      ProbabilityTheory.cond (independentSkillPopulation μ)
        (sourceActualTwoLevelAdmissionEvent score tie rho c) := by
  have hevent := scorePriorityTwoLevelAdmissionEvent_ae_eq μ hscore htie rho c
  unfold ProbabilityTheory.cond
  rw [measure_congr hevent, Measure.restrict_congr_set hevent]

/-- The source conditional-score objective evaluated with the known
score-priority boundary and the actual independent admission lottery. -/
noncomputable def scorePriorityTwoLevelConditionalScoreUtility
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (score tie : ℝ → ℝ) (rho c : ℝ) : ℝ :=
  ∫ z : (ℝ × ℝ) × α, score z.1.1
    ∂ProbabilityTheory.cond (independentSkillPopulation μ)
      (scorePriorityTwoLevelAdmissionEvent score tie rho c)

theorem scorePriorityTwoLevelConditionalScoreUtility_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {score tie : ℝ → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    [NoAtoms (Measure.map tie unitRankMeasure)] (rho c : ℝ) :
    scorePriorityTwoLevelConditionalScoreUtility μ score tie rho c =
      sourceActualTwoLevelConditionalScoreUtility μ score tie rho c := by
  unfold scorePriorityTwoLevelConditionalScoreUtility sourceActualTwoLevelConditionalScoreUtility
  rw [scorePriorityTwoLevelAdmissionEvent_cond_eq μ hscore htie]

/-- Measurable-task admission uses the fixed applicant priority and an
independent lottery on the full joint skill population. -/
def scorePriorityMultitaskAdmissionEvent
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (score tie : ℝ × α → ℝ) (rho c : ℝ) : Set ((ℝ × ℝ) × α) :=
  {z | ScorePriorityAboveCutoff (unitRankMeasure.prod μ) score tie c
      (score (z.1.1, z.2)) (tie (z.1.1, z.2)) ∧
    z.1.2 ∈ Ioc (0 : ℝ) (rho / (1 - c))}

theorem scorePriorityMultitaskAdmissionEvent_ae_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {score tie : ℝ × α → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    [NoAtoms (Measure.map tie (unitRankMeasure.prod μ))] (rho c : ℝ) :
    scorePriorityMultitaskAdmissionEvent μ score tie rho c =ᵐ[independentSkillPopulation μ]
      sourceMultitaskAdmissionEvent μ score tie rho c := by
  have hbase := scorePriorityAboveCutoff_current_ae_iff (unitRankMeasure.prod μ) hscore htie c
  have hfull := (independentSkillPopulation_applicant_measurePreserving μ).quasiMeasurePreserving.ae hbase
  filter_upwards [hfull] with z hz
  apply propext
  exact and_congr_left (fun _ => hz)

theorem scorePriorityMultitaskAdmissionEvent_measure_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {score tie : ℝ × α → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    [NoAtoms (Measure.map tie (unitRankMeasure.prod μ))] (rho c : ℝ) :
    independentSkillPopulation μ (scorePriorityMultitaskAdmissionEvent μ score tie rho c) =
      independentSkillPopulation μ (sourceMultitaskAdmissionEvent μ score tie rho c) :=
  measure_congr (scorePriorityMultitaskAdmissionEvent_ae_eq μ hscore htie rho c)

theorem scorePriorityMultitaskAdmissionEvent_cond_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {score tie : ℝ × α → ℝ} (hscore : Measurable score) (htie : Measurable tie)
    [NoAtoms (Measure.map tie (unitRankMeasure.prod μ))] (rho c : ℝ) :
    ProbabilityTheory.cond (independentSkillPopulation μ)
        (scorePriorityMultitaskAdmissionEvent μ score tie rho c) =
      ProbabilityTheory.cond (independentSkillPopulation μ)
        (sourceMultitaskAdmissionEvent μ score tie rho c) := by
  have hevent := scorePriorityMultitaskAdmissionEvent_ae_eq μ hscore htie rho c
  unfold ProbabilityTheory.cond
  rw [measure_congr hevent, Measure.restrict_congr_set hevent]

/-- The school's measurable/unmeasurable weighted-score objective conditional
on actual admission under the known score-priority boundary model. -/
noncomputable def scorePriorityMultitaskSchoolUtility
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (production skillM : ℝ → ℝ) (skillU : α → ℝ)
    (effortM effortU score tie : ℝ × α → ℝ) (rho beta c : ℝ) : ℝ :=
  ∫ z : (ℝ × ℝ) × α,
    beta * (production (effortM (z.1.1, z.2)) * skillM z.1.1) +
      (1 - beta) * (production (effortU (z.1.1, z.2)) * skillU z.2)
    ∂ProbabilityTheory.cond (independentSkillPopulation μ)
      (scorePriorityMultitaskAdmissionEvent μ score tie rho c)

/-- Equality of the actual conditional utility, with the same population,
efforts, technologies, school weights, and lottery. All policy comparisons
and supporting-weight claims therefore use the identical objective. -/
theorem scorePriorityMultitaskSchoolUtility_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (production skillM : ℝ → ℝ) (skillU : α → ℝ)
    (effortM effortU : ℝ × α → ℝ) {score tie : ℝ × α → ℝ}
    (hscore : Measurable score) (htie : Measurable tie)
    [NoAtoms (Measure.map tie (unitRankMeasure.prod μ))] (rho beta c : ℝ) :
    scorePriorityMultitaskSchoolUtility μ production skillM skillU effortM effortU score tie rho beta c =
      sourceActualMultitaskSchoolUtility μ production skillM skillU effortM effortU score tie rho beta c := by
  unfold scorePriorityMultitaskSchoolUtility sourceActualMultitaskSchoolUtility
  rw [scorePriorityMultitaskAdmissionEvent_cond_eq μ hscore htie]

end LBG22StrategicRanking
