import AppliedModelingLib.Foundations.Probability.PoissonProcess
import AppliedModelingLib.Foundations.Probability.ForwardPoisson
import AppliedModelingLib.Foundations.Probability.Processes.Palm.Core
import AppliedModelingLib.Queueing.Core

/-!
# Count-level stationary M/M/1 tail calculation

This module formalizes the analytic count-mixture step behind the stationary
`M/M/1` response-tail calculation.  Its hypotheses deliberately expose the
stationary/Palm semantics that a queue construction must establish: a tagged
probability law, a geometric pre-arrival queue-length tail, an independent
future potential-service count with the Poisson law, and the event identity
linking those counts to the tagged response time.

It does not construct a stationary Palm measure from a queue path, derive the
geometric stationary law, or prove the GPS-to-FCFS service comparison.  Those
are separate proof obligations.  The main response-tail result is strict;
`measureReal_weakTail_eq_strictTail_of_atom_zero` records the separate no-atom
bridge required for a weak `T >= z` paper convention.
-/

namespace AppliedModelingLib
namespace Probability
namespace Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The one-time post-tag completion-count facts used by the analytic M/M/1
tail calculation.  This deliberately does not assert a chronological Poisson
process: monotonicity and independent increments are useful for path models,
but are not consumed by the count-mixture proof. -/
structure PostTagPoissonCompletionCountMarginals
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  /-- Potential-service rate. -/
  rate : ℝ
  rate_pos : 0 < rate
  /-- Completion count at each real post-tag horizon. -/
  completionCount : ℝ → Ω → ℕ
  completionCount_measurable : ∀ z, Measurable (completionCount z)
  /-- Fixed-horizon Poisson marginal for each nonnegative horizon. -/
  completionCount_poisson_law : ∀ z : ℝ, 0 ≤ z → ∀ k : ℕ,
    P.real {ω | completionCount z ω = k} =
      PoissonProcess.countLikelihood 1 (rate * z) k

namespace PostTagPoissonCompletionCountMarginals

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Forget the path-only fields of a forward Poisson process when only its
fixed-horizon completion-count marginals are needed. -/
def ofForwardProcess
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    PostTagPoissonCompletionCountMarginals Ω P where
  rate := H.rate
  rate_pos := H.rate_pos
  completionCount := fun z => H.count z.toNNReal
  completionCount_measurable := fun z => H.measurable_count z.toNNReal
  completionCount_poisson_law := by
    intro z hz k
    exact H.count_prob_atReal_eq_unit_rate_product hz k

end PostTagPoissonCompletionCountMarginals

/--
The exact stationary-Palm/PASTA consequences needed for the count-level
M/M/1 response-tail proof.

This is a proof-facing certificate, not a construction of a Palm measure.
The fields state the consequences that a future stationary queue/Palm/PASTA
construction must establish: the tag is at time zero, the pre-arrival number
of jobs has the stationary geometric tail, future potential service is Poisson
and independent of that pre-arrival state, and the strict response event has
the corresponding count identity almost everywhere.  `preArrivalQueueLength`
excludes the tagged job, so `completionCount z ≤ preArrivalQueueLength` is the
correct strict-tail event.
-/
structure TaggedPASTAMM1CountCertificate
    (Ω : Type*) [MeasurableSpace Ω]
    extends TaggedArrivalAtZero Ω where
  /-- Arrival rate of the isolated stable M/M/1 comparator. -/
  arrivalRate : ℝ
  /-- Potential-service rate of the isolated stable M/M/1 comparator. -/
  serviceRate : ℝ
  arrivalRate_pos : 0 < arrivalRate
  serviceRate_pos : 0 < serviceRate
  stable : arrivalRate < serviceRate
  /-- Number of jobs ahead of the tagged job immediately before time zero. -/
  preArrivalQueueLength : Ω → ℕ
  /-- Potential service completions in the post-tag interval `[0,z]`. -/
  completionCount : ℝ → Ω → ℕ
  /-- Tagged response time. -/
  response : Ω → ℝ
  preArrivalQueueLength_measurable : Measurable preArrivalQueueLength
  completionCount_measurable : ∀ z : ℝ, Measurable (completionCount z)
  response_measurable : Measurable response
  /-- Future potential completions are independent of the tagged pre-arrival state. -/
  preArrivalQueueLength_indep_completionCount : ∀ z : ℝ, 0 ≤ z →
    IndepFun preArrivalQueueLength (completionCount z) Ptag
  /-- Stationary/Palm pre-arrival geometric queue-length tail. -/
  stationary_preArrivalQueueLength_tail : ∀ k : ℕ,
    Ptag.real {ω | k ≤ preArrivalQueueLength ω} =
      (arrivalRate / serviceRate) ^ k
  /-- Poisson law of potential completions over each nonnegative horizon. -/
  completionCount_poisson_law : ∀ (z : ℝ), 0 ≤ z → ∀ k : ℕ,
    Ptag.real {ω | completionCount z ω = k} =
      PoissonProcess.countLikelihood 1 (serviceRate * z) k
  /-- Almost-everywhere count identity for the strict tagged response event. -/
  strict_response_event : ∀ z : ℝ, 0 ≤ z →
    {ω | z < response ω} =ᵐ[Ptag]
      {ω | completionCount z ω ≤ preArrivalQueueLength ω}
  /-- No response-time atom, needed only to use a weak-tail convention. -/
  response_atom_zero : ∀ z : ℝ,
    Ptag.real {ω | response ω = z} = 0

namespace TaggedPASTAMM1CountCertificate

/-- Build the analytic M/M/1 count certificate from fixed-horizon post-tag
completion-count marginals.  This is the minimal interface used by the tail
mixture; it makes no claim that the supplied counts form a full process. -/
noncomputable def ofPostTagPoissonCompletionCountMarginals
    {Ω : Type*} [MeasurableSpace Ω]
    (tagged : TaggedArrivalAtZero Ω)
    (arrivalRate : ℝ) (harrivalRate : 0 < arrivalRate)
    (service : PostTagPoissonCompletionCountMarginals Ω tagged.Ptag)
    (hstable : arrivalRate < service.rate)
    (preArrivalQueueLength : Ω → ℕ) (response : Ω → ℝ)
    (hpreArrivalQueueLength_measurable : Measurable preArrivalQueueLength)
    (hresponse_measurable : Measurable response)
    (hpreArrivalQueueLength_indep_service : ∀ z : ℝ, 0 ≤ z →
      IndepFun preArrivalQueueLength (service.completionCount z) tagged.Ptag)
    (hstationary_preArrivalQueueLength_tail : ∀ k : ℕ,
      tagged.Ptag.real {ω | k ≤ preArrivalQueueLength ω} =
        (arrivalRate / service.rate) ^ k)
    (hstrict_response_event : ∀ z : ℝ, 0 ≤ z →
      {ω | z < response ω} =ᵐ[tagged.Ptag]
      {ω | service.completionCount z ω ≤ preArrivalQueueLength ω})
    (hresponse_atom_zero : ∀ z : ℝ,
      tagged.Ptag.real {ω | response ω = z} = 0) :
    TaggedPASTAMM1CountCertificate Ω where
  toTaggedArrivalAtZero := tagged
  arrivalRate := arrivalRate
  serviceRate := service.rate
  arrivalRate_pos := harrivalRate
  serviceRate_pos := service.rate_pos
  stable := hstable
  preArrivalQueueLength := preArrivalQueueLength
  completionCount := service.completionCount
  response := response
  preArrivalQueueLength_measurable := hpreArrivalQueueLength_measurable
  completionCount_measurable := service.completionCount_measurable
  response_measurable := hresponse_measurable
  preArrivalQueueLength_indep_completionCount := hpreArrivalQueueLength_indep_service
  stationary_preArrivalQueueLength_tail := hstationary_preArrivalQueueLength_tail
  completionCount_poisson_law := service.completionCount_poisson_law
  strict_response_event := hstrict_response_event
  response_atom_zero := hresponse_atom_zero

/--
Build the count-level stationary/Palm certificate from a tagged-arrival path
and a forward post-tag Poisson potential-service process.  The constructor
derives the service-count law and measurability rather than accepting them as
unstructured premises.  It still requires the genuinely Palm/queue-specific
facts: stable pre-arrival geometric queue law, independence of that state from
future service, the tagged response-count identity, and no response atom.  Its
public event premise remains literal equality for backwards compatibility and
is promoted internally to the certificate's almost-everywhere field.
-/
def ofForwardServiceProcess
    {Ω : Type*} [MeasurableSpace Ω]
    (tagged : TaggedArrivalAtZero Ω)
    (arrivalRate : ℝ) (harrivalRate : 0 < arrivalRate)
    (service : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw
      Ω tagged.Ptag)
    (hstable : arrivalRate < service.rate)
    (preArrivalQueueLength : Ω → ℕ) (response : Ω → ℝ)
    (hpreArrivalQueueLength_measurable : Measurable preArrivalQueueLength)
    (hresponse_measurable : Measurable response)
    (hpreArrivalQueueLength_indep_service : ∀ z : ℝ, 0 ≤ z →
      IndepFun preArrivalQueueLength (service.count z.toNNReal) tagged.Ptag)
    (hstationary_preArrivalQueueLength_tail : ∀ k : ℕ,
      tagged.Ptag.real {ω | k ≤ preArrivalQueueLength ω} =
        (arrivalRate / service.rate) ^ k)
    (hstrict_response_event : ∀ z : ℝ, 0 ≤ z →
      {ω | z < response ω} =
        {ω | service.count z.toNNReal ω ≤ preArrivalQueueLength ω})
    (hresponse_atom_zero : ∀ z : ℝ,
      tagged.Ptag.real {ω | response ω = z} = 0) :
    TaggedPASTAMM1CountCertificate Ω where
  toTaggedArrivalAtZero := tagged
  arrivalRate := arrivalRate
  serviceRate := service.rate
  arrivalRate_pos := harrivalRate
  serviceRate_pos := service.rate_pos
  stable := hstable
  preArrivalQueueLength := preArrivalQueueLength
  completionCount := fun z => service.count z.toNNReal
  response := response
  preArrivalQueueLength_measurable := hpreArrivalQueueLength_measurable
  completionCount_measurable := fun z => service.measurable_count z.toNNReal
  response_measurable := hresponse_measurable
  preArrivalQueueLength_indep_completionCount := by
    intro z hz
    exact hpreArrivalQueueLength_indep_service z hz
  stationary_preArrivalQueueLength_tail := hstationary_preArrivalQueueLength_tail
  completionCount_poisson_law := by
    intro z hz k
    exact service.count_prob_atReal_eq_unit_rate_product hz k
  strict_response_event := by
    intro z hz
    rw [hstrict_response_event z hz]
  response_atom_zero := hresponse_atom_zero

/--
Build the count-level stationary/Palm certificate from a tagged-arrival path
and a forward post-tag Poisson potential-service process when the response
count identity is supplied almost everywhere.  This is the natural interface
for a chronological path construction, where response times are defined up to
tagged-law null sets.
-/
def ofForwardServiceProcessAE
    {Ω : Type*} [MeasurableSpace Ω]
    (tagged : TaggedArrivalAtZero Ω)
    (arrivalRate : ℝ) (harrivalRate : 0 < arrivalRate)
    (service : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw
      Ω tagged.Ptag)
    (hstable : arrivalRate < service.rate)
    (preArrivalQueueLength : Ω → ℕ) (response : Ω → ℝ)
    (hpreArrivalQueueLength_measurable : Measurable preArrivalQueueLength)
    (hresponse_measurable : Measurable response)
    (hpreArrivalQueueLength_indep_service : ∀ z : ℝ, 0 ≤ z →
      IndepFun preArrivalQueueLength (service.count z.toNNReal) tagged.Ptag)
    (hstationary_preArrivalQueueLength_tail : ∀ k : ℕ,
      tagged.Ptag.real {ω | k ≤ preArrivalQueueLength ω} =
        (arrivalRate / service.rate) ^ k)
    (hstrict_response_event : ∀ z : ℝ, 0 ≤ z →
      {ω | z < response ω} =ᵐ[tagged.Ptag]
        {ω | service.count z.toNNReal ω ≤ preArrivalQueueLength ω})
    (hresponse_atom_zero : ∀ z : ℝ,
      tagged.Ptag.real {ω | response ω = z} = 0) :
    TaggedPASTAMM1CountCertificate Ω where
  toTaggedArrivalAtZero := tagged
  arrivalRate := arrivalRate
  serviceRate := service.rate
  arrivalRate_pos := harrivalRate
  serviceRate_pos := service.rate_pos
  stable := hstable
  preArrivalQueueLength := preArrivalQueueLength
  completionCount := fun z => service.count z.toNNReal
  response := response
  preArrivalQueueLength_measurable := hpreArrivalQueueLength_measurable
  completionCount_measurable := fun z => service.measurable_count z.toNNReal
  response_measurable := hresponse_measurable
  preArrivalQueueLength_indep_completionCount := by
    intro z hz
    exact hpreArrivalQueueLength_indep_service z hz
  stationary_preArrivalQueueLength_tail := hstationary_preArrivalQueueLength_tail
  completionCount_poisson_law := by
    intro z hz k
    exact service.count_prob_atReal_eq_unit_rate_product hz k
  strict_response_event := hstrict_response_event
  response_atom_zero := hresponse_atom_zero

end TaggedPASTAMM1CountCertificate

/-- Analytic Poisson probability-generating-function identity. -/
theorem hasSum_poissonCountLikelihood_mul_pow
    (mean rho : ℝ) :
    HasSum
      (fun n : ℕ => PoissonProcess.countLikelihood 1 mean n * rho ^ n)
      (PoissonProcess.noArrivalProb (1 - rho) mean) := by
  have h := PoissonProcess.hasSum_countLikelihood_mul_binomialThinningMass
    mean (1 - rho) 0
  convert h using 1
  · funext n
    simp [PoissonProcess.binomialThinningMass]
  · simp [PoissonProcess.countLikelihood, PoissonProcess.noArrivalProb]
    ring

/-- Rate-specialized form of the stationary M/M/1 Poisson mixture. -/
theorem hasSum_stationaryMM1_mixture
    (arrivalRate serviceRate z : ℝ) (hservice : serviceRate ≠ 0) :
    HasSum
      (fun n : ℕ =>
        PoissonProcess.countLikelihood 1 (serviceRate * z) n *
          (arrivalRate / serviceRate) ^ n)
      (Real.exp (-((serviceRate - arrivalRate) * z))) := by
  rw [← PoissonProcess.noArrivalProb]
  convert hasSum_poissonCountLikelihood_mul_pow
    (serviceRate * z) (arrivalRate / serviceRate) using 1
  simp only [PoissonProcess.noArrivalProb]
  congr 1
  field_simp [hservice]

/--
Count-level stationary M/M/1 tail calculation.

The premises are semantic ingredients of an already constructed stationary
Palm tagged-arrival model.  In particular, `Ptag` is an actual probability
measure, not merely a finite measure; `hqueue_tail` must come from the
stationary pre-arrival queue state; and `h_indep` plus `hservice_law` must
describe future potential completions independent of that pre-arrival state.
This theorem derives their analytic consequence but does not establish any of
those premises from a queue path.
-/
theorem measureReal_geometric_poisson_mixture
    {Ω : Type*} [MeasurableSpace Ω] (Ptag : Measure Ω)
    [IsProbabilityMeasure Ptag]
    (queueLength serviceCount : Ω → ℕ)
    (hqueue_meas : Measurable queueLength)
    (hservice_meas : Measurable serviceCount)
    (h_indep : IndepFun queueLength serviceCount Ptag)
    (rho mean : ℝ)
    (hqueue_tail : ∀ k : ℕ,
      Ptag.real {ω | k ≤ queueLength ω} = rho ^ k)
    (hservice_law : ∀ k : ℕ,
      Ptag.real {ω | serviceCount ω = k} =
        PoissonProcess.countLikelihood 1 mean k) :
    Ptag.real {ω | serviceCount ω ≤ queueLength ω} =
      PoissonProcess.noArrivalProb (1 - rho) mean := by
  let A : ℕ → Set Ω := fun k =>
    {ω | serviceCount ω = k ∧ k ≤ queueLength ω}
  have hA_meas : ∀ k : ℕ, MeasurableSet (A k) := by
    intro k
    change MeasurableSet
      (serviceCount ⁻¹' ({k} : Set ℕ) ∩ queueLength ⁻¹' Set.Ici k)
    exact (hservice_meas (measurableSet_singleton k)).inter
      (hqueue_meas measurableSet_Ici)
  have hA_disjoint : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro ω hAi hAj
    have hi : serviceCount ω = i := hAi.1
    have hj : serviceCount ω = j := hAj.1
    exact hij (hi.symm.trans hj)
  have hA_real : ∀ k : ℕ,
      Ptag.real (A k) =
        PoissonProcess.countLikelihood 1 mean k * rho ^ k := by
    intro k
    have hinter := h_indep.measure_inter_preimage_eq_mul
      (s := Set.Ici k) (t := ({k} : Set ℕ))
      measurableSet_Ici (measurableSet_singleton k)
    have hA_eq : A k =
        queueLength ⁻¹' Set.Ici k ∩ serviceCount ⁻¹' ({k} : Set ℕ) := by
      ext ω
      simp [A, and_comm]
    rw [hA_eq, Measure.real, hinter, ENNReal.toReal_mul]
    rw [show (Ptag (queueLength ⁻¹' Set.Ici k)).toReal = rho ^ k by
      simpa [Measure.real] using hqueue_tail k]
    rw [show (Ptag (serviceCount ⁻¹' ({k} : Set ℕ))).toReal =
        PoissonProcess.countLikelihood 1 mean k by
      simpa [Measure.real] using hservice_law k]
    ring
  have hUnion : (⋃ k : ℕ, A k) =
      {ω | serviceCount ω ≤ queueLength ω} := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨k, hk⟩
      change serviceCount ω = k ∧ k ≤ queueLength ω at hk
      simpa [hk.1] using hk.2
    · intro hω
      exact Set.mem_iUnion.mpr ⟨serviceCount ω, ⟨rfl, hω⟩⟩
  rw [← hUnion, Measure.real, measure_iUnion hA_disjoint hA_meas,
    ENNReal.tsum_toReal_eq (fun k => measure_ne_top Ptag (A k))]
  change (∑' k : ℕ, Ptag.real (A k)) =
    PoissonProcess.noArrivalProb (1 - rho) mean
  rw [tsum_congr hA_real]
  exact hasSum_poissonCountLikelihood_mul_pow mean rho |>.tsum_eq

/--
Strict M/M/1 response tail from an explicitly stationary/Palm count coupling.

The almost-everywhere equality `hresponse` is deliberately exposed: a
queue-theoretic proof must show that a tagged arrival at time zero remains
unfinished past `z` exactly up to a null set when the stationary jobs preceding
it have not all been cleared by the future potential-service count. Stability
and `z ≥ 0` are also semantic conditions needed to construct a meaningful
model; they are not inferred merely from the algebraic premises below.
-/
theorem responseTail_strict_eq_of_stationaryPalmCountCoupling
    {Ω : Type*} [MeasurableSpace Ω] (Ptag : Measure Ω)
    [IsProbabilityMeasure Ptag]
    (queueLength serviceCount : Ω → ℕ) (response : Ω → ℝ)
    (hqueue_meas : Measurable queueLength)
    (hservice_meas : Measurable serviceCount)
    (h_indep : IndepFun queueLength serviceCount Ptag)
    (arrivalRate serviceRate z : ℝ) (hserviceRate : serviceRate ≠ 0)
    (hqueue_tail : ∀ k : ℕ,
      Ptag.real {ω | k ≤ queueLength ω} =
        (arrivalRate / serviceRate) ^ k)
    (hservice_law : ∀ k : ℕ,
      Ptag.real {ω | serviceCount ω = k} =
        PoissonProcess.countLikelihood 1 (serviceRate * z) k)
    (hresponse : {ω | z < response ω} =ᵐ[Ptag]
      {ω | serviceCount ω ≤ queueLength ω}) :
    Ptag.real {ω | z < response ω} =
      Real.exp (-((serviceRate - arrivalRate) * z)) := by
  calc
    Ptag.real {ω | z < response ω} =
        Ptag.real {ω | serviceCount ω ≤ queueLength ω} :=
      congrArg ENNReal.toReal (measure_congr hresponse)
    _ = PoissonProcess.noArrivalProb
        (1 - arrivalRate / serviceRate) (serviceRate * z) :=
      measureReal_geometric_poisson_mixture Ptag queueLength serviceCount
        hqueue_meas hservice_meas h_indep (arrivalRate / serviceRate)
        (serviceRate * z) hqueue_tail hservice_law
    _ = Real.exp (-((serviceRate - arrivalRate) * z)) :=
      (hasSum_poissonCountLikelihood_mul_pow
        (serviceRate * z) (arrivalRate / serviceRate) |>.tsum_eq).symm.trans
      (hasSum_stationaryMM1_mixture
          arrivalRate serviceRate z hserviceRate |>.tsum_eq)

/--
A continuous strict-tail formula rules out response-time atoms at every
nonnegative threshold.  This is the continuity bridge appropriate after the
stationary/Palm count calculation: it uses neither a transient initial state
nor a separate pathwise response-time construction.

The formula is required on all nonnegative times, rather than merely at the
displayed threshold, because an atom is detected by approaching that threshold
from the left.
-/
theorem response_atom_zero_of_strictTail_exponential
    {Ω : Type*} [MeasurableSpace Ω] (Ptag : Measure Ω)
    [IsProbabilityMeasure Ptag]
    (response : Ω → ℝ) (hresponse_meas : Measurable response)
    (a : ℝ)
    (htail : ∀ t : ℝ, 0 ≤ t →
      Ptag.real {ω | t < response ω} = Real.exp (-a * t))
    (z : ℝ) (hz : 0 ≤ z) :
    Ptag.real {ω | response ω = z} = 0 := by
  let atom : Set Ω := {ω | response ω = z}
  let strictTail : ℝ → Set Ω := fun t => {ω | t < response ω}
  have hstrict_meas : ∀ t : ℝ, MeasurableSet (strictTail t) := by
    intro t
    exact measurableSet_lt measurable_const hresponse_meas
  have hatom_nonneg : 0 ≤ Ptag.real atom := MeasureTheory.measureReal_nonneg
  by_cases hz_zero : z = 0
  · subst z
    have htail_zero : Ptag.real (strictTail 0) = 1 := by
      rw [htail 0 le_rfl]
      simp
    have hcompl : Ptag.real (strictTail 0)ᶜ = 0 := by
      rw [MeasureTheory.measureReal_compl (hstrict_meas 0)]
      simp [htail_zero]
    apply MeasureTheory.measureReal_mono_null ?_ hcompl
    intro ω hω
    change response ω = 0 at hω
    change ¬ 0 < response ω
    linarith
  · have hz_pos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz_zero)
    apply le_antisymm ?_ hatom_nonneg
    apply le_of_forall_pos_le_add
    intro ε hε
    let f : ℝ → ℝ := fun t => Real.exp (-a * t)
    have hf_cont : Continuous f := by
      have hlin : Continuous (fun t : ℝ => -a * t) :=
        continuous_const.mul continuous_id
      exact Real.continuous_exp.comp hlin
    rcases Metric.continuousAt_iff.mp
      (hf_cont.continuousAt : ContinuousAt f z) ε hε with
      ⟨δ, hδ_pos, hδ⟩
    let d : ℝ := min (δ / 2) (z / 2)
    have hd_pos : 0 < d := by
      dsimp [d]
      exact lt_min (by linarith) (by linarith)
    have hd_lt_delta : d < δ := by
      calc
        d ≤ δ / 2 := min_le_left _ _
        _ < δ := by linarith
    have hd_lt_z : d < z := by
      calc
        d ≤ z / 2 := min_le_right _ _
        _ < z := by linarith
    let t : ℝ := z - d
    have ht_nonneg : 0 ≤ t := by
      dsimp [t]
      linarith
    have ht_lt_z : t < z := by
      dsimp [t]
      linarith
    have htail_subset : strictTail z ⊆ strictTail t := by
      intro ω hω
      change z < response ω at hω
      change t < response ω
      exact lt_trans ht_lt_z hω
    have hatom_subset : atom ⊆ strictTail t \ strictTail z := by
      intro ω hω
      change response ω = z at hω
      constructor
      · change t < response ω
        rw [hω]
        exact ht_lt_z
      · change ¬ z < response ω
        rw [hω]
        exact lt_irrefl z
    have hdiff : Ptag.real (strictTail t \ strictTail z) = f t - f z := by
      rw [MeasureTheory.measureReal_diff htail_subset (hstrict_meas z)]
      rw [htail t ht_nonneg, htail z hz]
    have hdist : dist (f t) (f z) < ε := by
      apply hδ
      rw [Real.dist_eq]
      rw [show t - z = -d by dsimp [t]; ring, abs_neg, abs_of_pos hd_pos]
      exact hd_lt_delta
    have hdiff_lt : f t - f z < ε := by
      calc
        f t - f z ≤ |f t - f z| := le_abs_self _
        _ = dist (f t) (f z) := by rw [Real.dist_eq]
        _ < ε := hdist
    have hatom_le_diff : Ptag.real atom ≤ Ptag.real (strictTail t \ strictTail z) :=
      MeasureTheory.measureReal_mono hatom_subset
    have hatom_lt : Ptag.real atom < ε := by
      rw [hdiff] at hatom_le_diff
      exact lt_of_le_of_lt hatom_le_diff hdiff_lt
    linarith

/--
Under a finite measure, a response-time atom at `z` bridges the strict and
weak tail conventions.  A stationary M/M/1 application must separately prove
the displayed no-atom premise before using a strict-tail formula for
`Ptag.real {ω | z ≤ response ω}`.
-/
theorem measureReal_weakTail_eq_strictTail_of_atom_zero
    {Ω : Type*} [MeasurableSpace Ω] (Ptag : Measure Ω)
    [IsFiniteMeasure Ptag]
    (response : Ω → ℝ) (hresponse_meas : Measurable response)
    (z : ℝ) (hatom : Ptag.real {ω | response ω = z} = 0) :
    Ptag.real {ω | z ≤ response ω} = Ptag.real {ω | z < response ω} := by
  let strictTail : Set Ω := {ω | z < response ω}
  let atom : Set Ω := {ω | response ω = z}
  have hstrict_meas : MeasurableSet strictTail := by
    exact measurableSet_lt measurable_const hresponse_meas
  have hatom_meas : MeasurableSet atom := by
    change MeasurableSet (response ⁻¹' ({z} : Set ℝ))
    exact hresponse_meas (measurableSet_singleton z)
  have hdisjoint : Disjoint strictTail atom := by
    rw [Set.disjoint_left]
    intro ω hstrict h_at_z
    change z < response ω at hstrict
    change response ω = z at h_at_z
    linarith
  have hunion : strictTail ∪ atom = {ω | z ≤ response ω} := by
    ext ω
    constructor
    · intro hω
      rcases hω with hω | hω
      · change z < response ω at hω
        exact le_of_lt hω
      · change response ω = z at hω
        exact le_of_eq hω.symm
    · intro hω
      change z ≤ response ω at hω
      rcases lt_or_eq_of_le hω with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr heq.symm
  rw [← hunion, measureReal_union hdisjoint hatom_meas]
  change Ptag.real strictTail + Ptag.real atom = Ptag.real strictTail
  rw [show Ptag.real atom = 0 by simpa [atom] using hatom, add_zero]

/--
Weak M/M/1 response tail when the tagged response law has no atom at `z`.

This is only a packaging theorem: the stationary/Palm count coupling and the
no-atom premise remain explicit inputs, so it cannot be used to turn an
arbitrary initial-state response law into a steady-state tail formula.
-/
theorem responseTail_weak_eq_of_stationaryPalmCountCoupling
    {Ω : Type*} [MeasurableSpace Ω] (Ptag : Measure Ω)
    [IsProbabilityMeasure Ptag]
    (queueLength serviceCount : Ω → ℕ) (response : Ω → ℝ)
    (hqueue_meas : Measurable queueLength)
    (hservice_meas : Measurable serviceCount)
    (hresponse_meas : Measurable response)
    (h_indep : IndepFun queueLength serviceCount Ptag)
    (arrivalRate serviceRate z : ℝ) (hserviceRate : serviceRate ≠ 0)
    (hqueue_tail : ∀ k : ℕ,
      Ptag.real {ω | k ≤ queueLength ω} =
        (arrivalRate / serviceRate) ^ k)
    (hservice_law : ∀ k : ℕ,
      Ptag.real {ω | serviceCount ω = k} =
        PoissonProcess.countLikelihood 1 (serviceRate * z) k)
    (hresponse : {ω | z < response ω} =ᵐ[Ptag]
      {ω | serviceCount ω ≤ queueLength ω})
    (hatom : Ptag.real {ω | response ω = z} = 0) :
    Ptag.real {ω | z ≤ response ω} =
      Real.exp (-((serviceRate - arrivalRate) * z)) := by
  calc
    Ptag.real {ω | z ≤ response ω} = Ptag.real {ω | z < response ω} :=
      measureReal_weakTail_eq_strictTail_of_atom_zero Ptag response
        hresponse_meas z hatom
    _ = Real.exp (-((serviceRate - arrivalRate) * z)) :=
      responseTail_strict_eq_of_stationaryPalmCountCoupling Ptag
        queueLength serviceCount response hqueue_meas hservice_meas h_indep
        arrivalRate serviceRate z hserviceRate hqueue_tail hservice_law hresponse

/--
Weak stationary/Palm response tail with its no-atom bridge derived internally
from the strict count-tail formula on every nonnegative horizon.  Thus a
path-level model need only establish the strict response/count event identity;
it need not separately supply atomlessness at the nonnegative paper delay.
-/
theorem responseTail_weak_eq_of_stationaryPalmCountCoupling_autoAtom
    {Ω : Type*} [MeasurableSpace Ω] (Ptag : Measure Ω)
    [IsProbabilityMeasure Ptag]
    (queueLength : Ω → ℕ) (completionCount : ℝ → Ω → ℕ) (response : Ω → ℝ)
    (hqueue_meas : Measurable queueLength)
    (hcompletion_meas : ∀ t : ℝ, Measurable (completionCount t))
    (hresponse_meas : Measurable response)
    (h_indep : ∀ t : ℝ, 0 ≤ t → IndepFun queueLength (completionCount t) Ptag)
    (arrivalRate serviceRate : ℝ) (hserviceRate : serviceRate ≠ 0)
    (hqueue_tail : ∀ k : ℕ,
      Ptag.real {ω | k ≤ queueLength ω} =
        (arrivalRate / serviceRate) ^ k)
    (hcompletion_law : ∀ (t : ℝ), 0 ≤ t → ∀ k : ℕ,
      Ptag.real {ω | completionCount t ω = k} =
        PoissonProcess.countLikelihood 1 (serviceRate * t) k)
    (hresponse : ∀ t : ℝ, 0 ≤ t →
      {ω | t < response ω} =ᵐ[Ptag]
        {ω | completionCount t ω ≤ queueLength ω})
    (z : ℝ) (hz : 0 ≤ z) :
    Ptag.real {ω | z ≤ response ω} =
      Real.exp (-((serviceRate - arrivalRate) * z)) := by
  refine responseTail_weak_eq_of_stationaryPalmCountCoupling
    Ptag queueLength (completionCount z) response hqueue_meas
    (hcompletion_meas z) hresponse_meas (h_indep z hz)
    arrivalRate serviceRate z hserviceRate hqueue_tail
    (hcompletion_law z hz) (hresponse z hz) ?_
  refine response_atom_zero_of_strictTail_exponential Ptag response hresponse_meas
    (serviceRate - arrivalRate) ?_ z hz
  intro t ht
  simpa only [neg_mul] using
    (responseTail_strict_eq_of_stationaryPalmCountCoupling
      Ptag queueLength (completionCount t) response hqueue_meas
      (hcompletion_meas t) (h_indep t ht)
      arrivalRate serviceRate t hserviceRate hqueue_tail
      (hcompletion_law t ht) (hresponse t ht))

namespace TaggedPASTAMM1CountCertificate

/--
The strict stationary M/M/1 response tail extracted from a certified Palm/PASTA
count coupling.  The tagged sample is fixed at index zero by the parent
certificate; no arbitrary array index is treated as a Palm tag here.
-/
theorem strict_responseTail_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (H : TaggedPASTAMM1CountCertificate Ω) (z : ℝ) (hz : 0 ≤ z) :
    H.Ptag.real {ω | z < H.response ω} =
      Real.exp (-((H.serviceRate - H.arrivalRate) * z)) := by
  letI : IsProbabilityMeasure H.Ptag := H.isProbability
  exact responseTail_strict_eq_of_stationaryPalmCountCoupling H.Ptag
    H.preArrivalQueueLength (H.completionCount z) H.response
    H.preArrivalQueueLength_measurable (H.completionCount_measurable z)
    (H.preArrivalQueueLength_indep_completionCount z hz)
    H.arrivalRate H.serviceRate z H.serviceRate_pos.ne'
    H.stationary_preArrivalQueueLength_tail
    (H.completionCount_poisson_law z hz)
    (H.strict_response_event z hz)

/--
The weak stationary M/M/1 response tail extracted from the same certificate.
The no-atom condition is explicit in the certificate because the analytic
count argument proves a strict tail before this continuity bridge is applied.
-/
theorem weak_responseTail_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (H : TaggedPASTAMM1CountCertificate Ω) (z : ℝ) (hz : 0 ≤ z) :
    H.Ptag.real {ω | z ≤ H.response ω} =
      Real.exp (-((H.serviceRate - H.arrivalRate) * z)) := by
  letI : IsProbabilityMeasure H.Ptag := H.isProbability
  exact responseTail_weak_eq_of_stationaryPalmCountCoupling H.Ptag
    H.preArrivalQueueLength (H.completionCount z) H.response
    H.preArrivalQueueLength_measurable (H.completionCount_measurable z)
    H.response_measurable
    (H.preArrivalQueueLength_indep_completionCount z hz)
    H.arrivalRate H.serviceRate z H.serviceRate_pos.ne'
    H.stationary_preArrivalQueueLength_tail
    (H.completionCount_poisson_law z hz)
    (H.strict_response_event z hz)
    (H.response_atom_zero z)

end TaggedPASTAMM1CountCertificate

end Queueing
end Probability
end AppliedModelingLib
