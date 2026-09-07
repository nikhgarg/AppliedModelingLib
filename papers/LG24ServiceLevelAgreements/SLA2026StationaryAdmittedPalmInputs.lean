import AppliedModelingLib.Foundations.Probability.MulticlassStationaryPoisson
import AppliedModelingLib.Foundations.Probability.PalmCampbellProductLift
import AppliedModelingLib.Foundations.Probability.PalmTaggedArrivalFiniteLedger
import LG24ServiceLevelAgreements.SLA2026StochasticPrimitives

/-!
# Stationary tagged admitted-input construction for the SLA source model

The active SLA source states that, after independent admission, the admitted
requests of each category form independent Poisson streams of rates `s`, with
iid unit-mean exponential work.  This module constructs exactly that direct
admitted-input model for one Borough, selects one target category at a Palm
arrival, and rec enters every passive category at the target event's physical
epoch.

It deliberately constructs input and Palm provenance only.  It makes no GPS
execution, backlog, stationary-queue, response-time, or tail claim.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.Palm
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The finite family of SLA categories other than a chosen target category. -/
abbrev PassiveCategory (target : Category) := {k : Category // k ≠ target}

/-- One direct admitted stationary class input: its Poisson suspension and
its complete two-sided unit-exponential work-mark path. -/
abbrev StationaryAdmittedClassInput := GoodSuspensionState × (ℤ → ℝ)

/-- The full finite family of direct admitted stationary source inputs.  This
is the carrier consumed by a finite event executor before Palm selection. -/
abbrev StationaryAdmittedAllClassInput (Category : Type*) :=
  Category → StationaryAdmittedClassInput

/-- A full direct admitted source input split into one target class and all
remaining passive classes. -/
abbrev StationaryAdmittedTargetPassiveBaseInput (target : Category) :=
  StationaryAdmittedClassInput × (PassiveCategory target → StationaryAdmittedClassInput)

/-- The target's Palm-tagged gap/work paths together with the complete
stationary passive family.  The tagged target retains its full work path; it
is not reduced to a single work mark. -/
abbrev StationaryAdmittedTargetPassiveTaggedInput (target : Category) :=
  ((ℤ → ℝ) × (ℤ → ℝ)) ×
    (PassiveCategory target → StationaryAdmittedClassInput)

/-- The direct admitted stationary input for all SLA categories.  Every
coordinate has source rate `s = admittedRate` and an iid unit-exponential
work path. -/
noncomputable def stationaryAdmittedAllClassBaseLaw
    (M : SLA2026BoroughQueueingInput Category) :
    ShiftInvariantProbabilityLaw (StationaryAdmittedAllClassInput Category) :=
  multiclassStationaryPoissonWorkShiftInvariantLaw M.admittedRate M.admittedRate_pos

/-- Pack a split target/passive base state into the full category-indexed
state used by the finite scheduler. -/
def packStationaryAdmittedTargetPassiveBase
    (target : Category) :
    StationaryAdmittedTargetPassiveBaseInput target →
      StationaryAdmittedAllClassInput Category :=
  fun x k => if h : k = target then x.1 else x.2 ⟨k, h⟩

/-- Split a full category-indexed stationary source state into a selected
target coordinate and its passive complement. -/
def unpackStationaryAdmittedTargetPassiveBase
    (target : Category) :
    StationaryAdmittedAllClassInput Category → StationaryAdmittedTargetPassiveBaseInput target :=
  fun omega => (omega target, fun k => omega k.1)

omit [Fintype Category] in
/-- Splitting a packed state recovers each complete arrival/work path exactly. -/
theorem unpack_packStationaryAdmittedTargetPassiveBase
    (target : Category) (x : StationaryAdmittedTargetPassiveBaseInput target) :
    unpackStationaryAdmittedTargetPassiveBase target
      (packStationaryAdmittedTargetPassiveBase target x) = x := by
  apply Prod.ext
  · simp [unpackStationaryAdmittedTargetPassiveBase,
      packStationaryAdmittedTargetPassiveBase]
  · funext k
    simp [unpackStationaryAdmittedTargetPassiveBase,
      packStationaryAdmittedTargetPassiveBase, k.2]

omit [Fintype Category] in
/-- Packing a split full state recovers every category coordinate exactly. -/
theorem pack_unpackStationaryAdmittedTargetPassiveBase
    (target : Category) (omega : StationaryAdmittedAllClassInput Category) :
    packStationaryAdmittedTargetPassiveBase target
      (unpackStationaryAdmittedTargetPassiveBase target omega) = omega := by
  funext k
  by_cases h : k = target
  · subst k
    simp [packStationaryAdmittedTargetPassiveBase,
      unpackStationaryAdmittedTargetPassiveBase]
  · simp [packStationaryAdmittedTargetPassiveBase,
      unpackStationaryAdmittedTargetPassiveBase, h]

/-- The source-faithful stationary admitted input of a chosen target category:
a Poisson stream of rate `s_target` with an iid unit-exponential work path. -/
noncomputable def stationaryAdmittedTargetBaseLaw
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ShiftInvariantProbabilityLaw (GoodSuspensionState × (ℤ → ℝ)) :=
  stationaryPoissonWorkShiftInvariantLaw (M.admittedRate_pos target)

/-- The all-event Palm tag for the direct admitted target stream. -/
noncomputable def stationaryAdmittedTargetTaggedArrivalAtZero
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    TaggedArrivalAtZero ((ℤ → ℝ) × (ℤ → ℝ)) :=
  stationaryPoissonWorkTaggedArrivalAtZero (M.admittedRate_pos target)

/-- The target stream's genuine all-event Campbell/Palm provenance. -/
noncomputable def stationaryAdmittedTargetCampbellCertificate
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    CampbellPalmTaggedArrivalCertificate
      (M.stationaryAdmittedTargetBaseLaw target)
      (M.stationaryAdmittedTargetTaggedArrivalAtZero target) :=
  stationaryPoissonWorkCampbellCertificate (M.admittedRate_pos target)

/-- The independent stationary admitted input for every passive category. -/
noncomputable def stationaryAdmittedPassiveBaseLaw
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ShiftInvariantProbabilityLaw
      (PassiveCategory target → (GoodSuspensionState × (ℤ → ℝ))) :=
  multiclassStationaryPoissonWorkShiftInvariantLaw
    (fun k : PassiveCategory target => M.admittedRate k.1)
    (fun k => M.admittedRate_pos k.1)

/-- The passive finite-class flow is jointly measurable in time and in all
complete passive arrival/work paths, as required to shift it at a random
target arrival epoch. -/
theorem measurable_uncurry_stationaryAdmittedPassiveShift
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    Measurable (Function.uncurry
      (M.stationaryAdmittedPassiveBaseLaw target).shift) := by
  simpa only [stationaryAdmittedPassiveBaseLaw] using
    (measurable_uncurry_multiclassStationaryPoissonWorkShift
      (Class := PassiveCategory target)
      (fun k : PassiveCategory target => M.admittedRate k.1)
      (fun k => M.admittedRate_pos k.1))

/-- The jointly stationary base law containing the target admitted stream and
all passive admitted streams.  This is the independent source-input product,
not a queue state. -/
noncomputable def stationaryAdmittedTargetPassiveBaseLaw
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ShiftInvariantProbabilityLaw
      ((GoodSuspensionState × (ℤ → ℝ)) ×
        (PassiveCategory target → (GoodSuspensionState × (ℤ → ℝ)))) :=
  targetPassiveProductBaseLaw (M.stationaryAdmittedTargetBaseLaw target)
    (M.stationaryAdmittedPassiveBaseLaw target)

/-- The target/passive split commutes with the common real-time translation.
Thus packing it into the executor's full category-indexed carrier preserves
the actual time origin, including the synchronous reindexing of every work
path. -/
theorem pack_stationaryAdmittedTargetPassiveBase_shift
    (M : SLA2026BoroughQueueingInput Category) (target : Category)
    (t : ℝ) (x : StationaryAdmittedTargetPassiveBaseInput target) :
    packStationaryAdmittedTargetPassiveBase target
      ((M.stationaryAdmittedTargetPassiveBaseLaw target).shift t x) =
      (M.stationaryAdmittedAllClassBaseLaw).shift t
        (packStationaryAdmittedTargetPassiveBase target x) := by
  funext k
  by_cases h : k = target
  · subst k
    simp [packStationaryAdmittedTargetPassiveBase,
      stationaryAdmittedTargetPassiveBaseLaw,
      stationaryAdmittedTargetBaseLaw,
      stationaryAdmittedPassiveBaseLaw,
      stationaryAdmittedAllClassBaseLaw,
      targetPassiveProductBaseLaw,
      multiclassStationaryPoissonWorkShiftInvariantLaw,
      multiclassStationaryPoissonWorkFlow,
      Queueing.stationaryPoissonWorkShiftInvariantLaw,
      Queueing.timedEmbeddedSuspensionShiftInvariantLaw_of_intPathShift]
  · simp [packStationaryAdmittedTargetPassiveBase,
      stationaryAdmittedTargetPassiveBaseLaw,
      stationaryAdmittedTargetBaseLaw,
      stationaryAdmittedPassiveBaseLaw,
      stationaryAdmittedAllClassBaseLaw,
      targetPassiveProductBaseLaw,
      multiclassStationaryPoissonWorkShiftInvariantLaw,
      multiclassStationaryPoissonWorkFlow,
      Queueing.stationaryPoissonWorkShiftInvariantLaw,
      Queueing.timedEmbeddedSuspensionShiftInvariantLaw_of_intPathShift, h]

/-- The all-event tagged admitted input: the target stream is Palm-tagged and
every passive category retains its stationary input law.  Its Palm provenance
is supplied by `stationaryAdmittedTargetPassiveCampbellCertificate`, not by
this product definition alone. -/
noncomputable def stationaryAdmittedTargetPassiveTaggedInput
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    TaggedArrivalAtZero
      (((ℤ → ℝ) × (ℤ → ℝ)) ×
        (PassiveCategory target → (GoodSuspensionState × (ℤ → ℝ)))) :=
  targetPassiveTaggedArrivalAtZero (M.stationaryAdmittedTargetTaggedArrivalAtZero target)
    (M.stationaryAdmittedPassiveBaseLaw target)

/-- The complete work-mark path of the Palm-tagged target.  The tag carries
all integer-indexed work marks, not only the selected job's mark. -/
def stationaryAdmittedTargetPalmWorkPath
    (target : Category) :
    StationaryAdmittedTargetPassiveTaggedInput target → (ℤ → ℝ) :=
  fun z => z.1.2

/-- The selected target job's source work requirement in the tagged input. -/
def stationaryAdmittedTargetPalmWorkAtZero
    (target : Category) :
    StationaryAdmittedTargetPassiveTaggedInput target → ℝ :=
  fun z => stationaryAdmittedTargetPalmWorkPath target z 0

/-- A passive category retains its complete stationary arrival/work input
after the target event's physical-time recentering. -/
def stationaryAdmittedPassiveInputAtTargetPalm
    (target : Category) (k : PassiveCategory target) :
    StationaryAdmittedTargetPassiveTaggedInput target → StationaryAdmittedClassInput :=
  fun z => z.2 k

omit [DecidableEq Category] in
/-- The entire tagged target work-mark path has the canonical iid
unit-exponential path law, rather than only a selected-coordinate marginal. -/
theorem stationaryAdmittedTargetPalmWorkPath_hasLaw
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    HasLaw (fun z : ((ℤ → ℝ) × (ℤ → ℝ)) => z.2)
      (twoSidedInterarrivalMeasure 1)
      (M.stationaryAdmittedTargetTaggedArrivalAtZero target).Ptag := by
  let P : Measure (ℤ → ℝ) := twoSidedInterarrivalMeasure 1
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  have htag := timedEmbeddedTaggedArrivalAtZero_pathStatistic_hasLaw P
    id measurable_id (M.admittedRate target) (M.admittedRate_pos target)
  simpa [P] using htag

omit [DecidableEq Category] in
/-- The tagged target's index-zero work requirement has the source's
unit-exponential law.  This is an input fact before any GPS execution. -/
theorem stationaryAdmittedTargetPalmWorkAtZero_hasLaw
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    HasLaw (fun z : ((ℤ → ℝ) × (ℤ → ℝ)) => z.2 0)
      (expMeasure 1)
      (M.stationaryAdmittedTargetTaggedArrivalAtZero target).Ptag := by
  let P : Measure (ℤ → ℝ) := twoSidedInterarrivalMeasure 1
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure
      (twoSidedInterarrivalMeasure (M.admittedRate target)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (M.admittedRate_pos target)
  have htag := timedEmbeddedTaggedArrivalAtZero_pathStatistic_hasLaw P
    (fun work : ℤ → ℝ => work 0) (measurable_pi_apply 0)
    (M.admittedRate target) (M.admittedRate_pos target)
  have hwork := twoSidedGap_hasLaw (by norm_num : 0 < (1 : ℝ)) 0
  refine ⟨((measurable_pi_apply 0).comp measurable_snd).aemeasurable, ?_⟩
  change Measure.map (fun z : ((ℤ → ℝ) × (ℤ → ℝ)) => z.2 0)
      (timedEmbeddedTaggedArrivalAtZero (M.admittedRate target)
        (M.admittedRate_pos target) P).Ptag = expMeasure 1
  calc
    Measure.map (fun z : ((ℤ → ℝ) × (ℤ → ℝ)) => z.2 0)
        (timedEmbeddedTaggedArrivalAtZero (M.admittedRate target)
          (M.admittedRate_pos target) P).Ptag =
        P.map (fun work : ℤ → ℝ => work 0) := htag.map_eq
    _ = expMeasure 1 := by
      simpa [P, twoSidedGap] using hwork.map_eq

omit [DecidableEq Category] in
/-- Every work mark retained by the tagged target is strictly positive almost
surely, including the index-zero job used by a later response-time adapter. -/
theorem ae_all_stationaryAdmittedTargetPalmWork_positive
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetTaggedArrivalAtZero target).Ptag,
      ∀ i : ℤ, 0 < z.2 i := by
  let P : Measure (ℤ → ℝ) := twoSidedInterarrivalMeasure 1
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure
      (twoSidedInterarrivalMeasure (M.admittedRate target)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (M.admittedRate_pos target)
  change ∀ᵐ z ∂(timedEmbeddedTaggedArrivalAtZero (M.admittedRate target)
      (M.admittedRate_pos target) P).Ptag, ∀ i : ℤ, 0 < z.2 i
  refine ae_of_ae_map
    (μ := (twoSidedInterarrivalMeasure (M.admittedRate target)).prod P)
    (f := Prod.snd) (p := fun work : ℤ → ℝ => ∀ i : ℤ, 0 < work i)
    measurable_snd.aemeasurable ?_
  rw [Measure.map_snd_prod, measure_univ, one_smul]
  simpa [P, twoSidedGap] using
    (ae_all_twoSidedGap_positive (by norm_num : 0 < (1 : ℝ)))

/-- The target gap path carried by the direct admitted Palm law satisfies the
finite-ledger good-carrier condition almost surely.  This supplies the
two-sided ordering and nonexplosion facts used by the literal tagged arrival
enumerator; it is an input-law fact, not a queue-state assertion. -/
theorem ae_stationaryAdmittedTargetPalmGoodCarrier
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetTaggedArrivalAtZero target).Ptag,
      palmTaggedArrivalGoodCarrier z.1 := by
  let P : Measure (ℤ → ℝ) := twoSidedInterarrivalMeasure 1
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure
      (twoSidedInterarrivalMeasure (M.admittedRate target)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (M.admittedRate_pos target)
  change ∀ᵐ z ∂(timedEmbeddedTaggedArrivalAtZero (M.admittedRate target)
      (M.admittedRate_pos target) P).Ptag, palmTaggedArrivalGoodCarrier z.1
  refine ae_of_ae_map
    (μ := (twoSidedInterarrivalMeasure (M.admittedRate target)).prod P)
    (f := Prod.fst) (p := palmTaggedArrivalGoodCarrier)
    measurable_fst.aemeasurable ?_
  rw [Measure.map_fst_prod, measure_univ, one_smul]
  exact ae_palmTaggedArrivalGoodCarrier (M.admittedRate_pos target)

/-- The genuine target/passive tagged law still retains the target's complete
iid work-mark path.  Adding recentered passive paths does not replace the
target path with a mere one-dimensional marginal. -/
theorem stationaryAdmittedTargetPassivePalmWorkPath_hasLaw
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    HasLaw (stationaryAdmittedTargetPalmWorkPath target)
      (twoSidedInterarrivalMeasure 1)
      (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag := by
  let targetTag := M.stationaryAdmittedTargetTaggedArrivalAtZero target
  let passiveBase := M.stationaryAdmittedPassiveBaseLaw target
  letI : IsProbabilityMeasure targetTag.Ptag := targetTag.isProbability
  letI : IsProbabilityMeasure passiveBase.Pbase := passiveBase.isProbability
  simpa [stationaryAdmittedTargetPalmWorkPath,
    stationaryAdmittedTargetPassiveTaggedInput,
    targetPassiveTaggedArrivalAtZero, targetTag, passiveBase] using
    (stationaryAdmittedTargetPalmWorkPath_hasLaw M target).comp
      ((measurePreserving_fst : MeasurePreserving Prod.fst
        (targetTag.Ptag.prod passiveBase.Pbase) targetTag.Ptag).hasLaw)

/-- The target's index-zero work requirement remains unit exponential in the
genuine target/passive Palm law.  Passive paths are present in the carrier,
but do not alter the target work marginal. -/
theorem stationaryAdmittedTargetPassivePalmWorkAtZero_hasLaw
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    HasLaw (stationaryAdmittedTargetPalmWorkAtZero target)
      (expMeasure 1)
      (M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag := by
  let targetTag := M.stationaryAdmittedTargetTaggedArrivalAtZero target
  let passiveBase := M.stationaryAdmittedPassiveBaseLaw target
  letI : IsProbabilityMeasure targetTag.Ptag := targetTag.isProbability
  letI : IsProbabilityMeasure passiveBase.Pbase := passiveBase.isProbability
  simpa [stationaryAdmittedTargetPalmWorkAtZero,
    stationaryAdmittedTargetPalmWorkPath,
    stationaryAdmittedTargetPassiveTaggedInput,
    targetPassiveTaggedArrivalAtZero, targetTag, passiveBase] using
    (M.stationaryAdmittedTargetPalmWorkAtZero_hasLaw target).comp
      ((measurePreserving_fst : MeasurePreserving Prod.fst
        (targetTag.Ptag.prod passiveBase.Pbase) targetTag.Ptag).hasLaw)

/-- The target job at the Palm event has strictly positive work almost surely
under the genuine target/passive tagged law. -/
theorem ae_stationaryAdmittedTargetPassivePalmWorkAtZero_positive
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      0 < stationaryAdmittedTargetPalmWorkAtZero target z := by
  let targetTag := M.stationaryAdmittedTargetTaggedArrivalAtZero target
  let passiveBase := M.stationaryAdmittedPassiveBaseLaw target
  letI : IsProbabilityMeasure targetTag.Ptag := targetTag.isProbability
  letI : IsProbabilityMeasure passiveBase.Pbase := passiveBase.isProbability
  have htarget : ∀ᵐ z ∂targetTag.Ptag, 0 < z.2 0 := by
    filter_upwards [M.ae_all_stationaryAdmittedTargetPalmWork_positive target] with z hz
    exact hz 0
  refine ae_of_ae_map (μ := targetTag.Ptag.prod passiveBase.Pbase) (f := Prod.fst)
    (p := fun z : (ℤ → ℝ) × (ℤ → ℝ) => 0 < z.2 0)
    measurable_fst.aemeasurable ?_
  rw [Measure.map_fst_prod, measure_univ, one_smul]
  simpa [stationaryAdmittedTargetPalmWorkAtZero,
    stationaryAdmittedTargetPalmWorkPath,
    stationaryAdmittedTargetPassiveTaggedInput,
    targetPassiveTaggedArrivalAtZero, targetTag, passiveBase] using htarget

/-- The target/passive Palm product retains the target finite-ledger good
carrier almost surely.  Passive coordinates do not alter the tagged target
gap path. -/
theorem ae_stationaryAdmittedTargetPassivePalmGoodCarrier
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      palmTaggedArrivalGoodCarrier z.1.1 := by
  let targetTag := M.stationaryAdmittedTargetTaggedArrivalAtZero target
  let passiveBase := M.stationaryAdmittedPassiveBaseLaw target
  letI : IsProbabilityMeasure targetTag.Ptag := targetTag.isProbability
  letI : IsProbabilityMeasure passiveBase.Pbase := passiveBase.isProbability
  have htarget : ∀ᵐ z ∂targetTag.Ptag, palmTaggedArrivalGoodCarrier z.1 := by
    simpa [targetTag] using M.ae_stationaryAdmittedTargetPalmGoodCarrier target
  refine ae_of_ae_map (μ := targetTag.Ptag.prod passiveBase.Pbase) (f := Prod.fst)
    (p := fun z : (ℤ → ℝ) × (ℤ → ℝ) => palmTaggedArrivalGoodCarrier z.1)
    measurable_fst.aemeasurable ?_
  rw [Measure.map_fst_prod, measure_univ, one_smul]
  simpa [stationaryAdmittedTargetPassiveTaggedInput,
    targetPassiveTaggedArrivalAtZero, targetTag, passiveBase] using htarget

/-- Every target and passive direct-admitted work mark is strictly positive
almost surely under the genuine tagged product law.  This is the joint
pathwise input invariant consumed by finite tagged GPS/FCFS execution. -/
theorem ae_all_stationaryAdmittedTargetPassivePalmWork_positive
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      (∀ n : ℤ, 0 < z.1.2 n) ∧
        ∀ k : PassiveCategory target, ∀ n : ℤ, 0 < (z.2 k).2 n := by
  let targetTag := M.stationaryAdmittedTargetTaggedArrivalAtZero target
  let passiveBase := M.stationaryAdmittedPassiveBaseLaw target
  letI : IsProbabilityMeasure targetTag.Ptag := targetTag.isProbability
  letI : IsProbabilityMeasure passiveBase.Pbase := passiveBase.isProbability
  have htarget : ∀ᵐ z ∂targetTag.Ptag, ∀ n : ℤ, 0 < z.2 n := by
    simpa [targetTag] using M.ae_all_stationaryAdmittedTargetPalmWork_positive target
  have hpassive : ∀ᵐ x ∂passiveBase.Pbase,
      ∀ k : PassiveCategory target, ∀ n : ℤ, 0 < (x k).2 n := by
    simpa [passiveBase, stationaryAdmittedPassiveBaseLaw,
      multiclassStationaryPoissonWorkRequirement] using
      (ae_all_multiclassStationaryPoissonWorkRequirement_positive
        (fun k : PassiveCategory target => M.admittedRate k.1)
        (fun k => M.admittedRate_pos k.1))
  have htarget_product : ∀ᵐ z ∂targetTag.Ptag.prod passiveBase.Pbase,
      ∀ n : ℤ, 0 < z.1.2 n := by
    refine ae_of_ae_map (μ := targetTag.Ptag.prod passiveBase.Pbase) (f := Prod.fst)
      (p := fun z : (ℤ → ℝ) × (ℤ → ℝ) => ∀ n : ℤ, 0 < z.2 n)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact htarget
  have hpassive_product : ∀ᵐ z ∂targetTag.Ptag.prod passiveBase.Pbase,
      ∀ k : PassiveCategory target, ∀ n : ℤ, 0 < (z.2 k).2 n := by
    refine ae_of_ae_map (μ := targetTag.Ptag.prod passiveBase.Pbase) (f := Prod.snd)
      (p := fun x : PassiveCategory target → StationaryAdmittedClassInput =>
        ∀ k : PassiveCategory target, ∀ n : ℤ, 0 < (x k).2 n)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hpassive
  filter_upwards [htarget_product, hpassive_product] with z htarget_z hpassive_z
  exact ⟨htarget_z, hpassive_z⟩

/-- The genuine target/passive all-event Campbell certificate for the direct
admitted source streams.  At every selected target arrival, passive categories
are translated by that target arrival's physical epoch. -/
noncomputable def stationaryAdmittedTargetPassiveCampbellCertificate
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    CampbellPalmTaggedArrivalCertificate
      (M.stationaryAdmittedTargetPassiveBaseLaw target)
      (M.stationaryAdmittedTargetPassiveTaggedInput target) :=
  targetPassiveCampbellCertificate
    (M.stationaryAdmittedTargetCampbellCertificate target)
    (M.stationaryAdmittedPassiveBaseLaw target)
    (M.measurable_uncurry_stationaryAdmittedPassiveShift target)

/-- The target/passive sample obtained by recentering at a labelled target
arrival.  The target component has that event at time zero, and the passive
component is shifted by the same physical target epoch. -/
def stationaryAdmittedTargetPassiveRecenter
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ((GoodSuspensionState × (ℤ → ℝ)) ×
      (PassiveCategory target → (GoodSuspensionState × (ℤ → ℝ)))) → ℤ →
      (((ℤ → ℝ) × (ℤ → ℝ)) ×
        (PassiveCategory target → (GoodSuspensionState × (ℤ → ℝ)))) :=
  targetPassiveRecenter (M.stationaryAdmittedTargetCampbellCertificate target)
    (M.stationaryAdmittedPassiveBaseLaw target)

/-- The passive coordinate is explicitly recentered at the target's physical
arrival epoch, not left as an unshifted independent sample. -/
theorem stationaryAdmittedTargetPassiveRecenter_passive
    (M : SLA2026BoroughQueueingInput Category) (target : Category)
    (x : (GoodSuspensionState × (ℤ → ℝ)) ×
      (PassiveCategory target → (GoodSuspensionState × (ℤ → ℝ))))
    (i : ℤ) :
    (M.stationaryAdmittedTargetPassiveRecenter target x i).2 =
      (M.stationaryAdmittedPassiveBaseLaw target).shift
        (stationaryPoissonWorkArrival x.1 i) x.2 := rfl

/-- The target component of the recentered input is an actual Palm-tagged
arrival at time zero.  Its first coordinate is the tagged *gap* path, so this
statement uses the tagged arrival map rather than incorrectly asserting that
the gap at index zero is itself zero. -/
theorem ae_stationaryAdmittedTargetPassiveRecenter_target_at_zero
    (M : SLA2026BoroughQueueingInput Category) (target : Category) (i : ℤ) :
    ∀ᵐ x ∂(M.stationaryAdmittedTargetPassiveBaseLaw target).Pbase,
      (M.stationaryAdmittedTargetPassiveTaggedInput target).arrivals
        (M.stationaryAdmittedTargetPassiveRecenter target x i) 0 = 0 := by
  let targetBase := M.stationaryAdmittedTargetBaseLaw target
  let passiveBase := M.stationaryAdmittedPassiveBaseLaw target
  have htarget := (M.stationaryAdmittedTargetCampbellCertificate target).recenter_arrivals
  have hproduct : ∀ᵐ x ∂(targetBase.Pbase.prod passiveBase.Pbase),
      ∀ i j,
        (M.stationaryAdmittedTargetTaggedArrivalAtZero target).arrivals
          ((M.stationaryAdmittedTargetCampbellCertificate target).recenterAt x.1 i) j =
          (M.stationaryAdmittedTargetCampbellCertificate target).baseArrivals x.1 (i + j) -
            (M.stationaryAdmittedTargetCampbellCertificate target).baseArrivals x.1 i := by
    letI : IsProbabilityMeasure targetBase.Pbase := targetBase.isProbability
    letI : IsProbabilityMeasure passiveBase.Pbase := passiveBase.isProbability
    refine ae_of_ae_map (μ := targetBase.Pbase.prod passiveBase.Pbase) (f := Prod.fst)
      (p := fun x => ∀ i j,
        (M.stationaryAdmittedTargetTaggedArrivalAtZero target).arrivals
          ((M.stationaryAdmittedTargetCampbellCertificate target).recenterAt x i) j =
          (M.stationaryAdmittedTargetCampbellCertificate target).baseArrivals x (i + j) -
            (M.stationaryAdmittedTargetCampbellCertificate target).baseArrivals x i)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact htarget
  filter_upwards [hproduct] with x hx
  simpa [stationaryAdmittedTargetPassiveBaseLaw,
    stationaryAdmittedTargetPassiveTaggedInput,
    stationaryAdmittedTargetPassiveRecenter, targetPassiveRecenter] using hx i 0

omit [DecidableEq Category] in
/-- The source's direct admitted target work marks remain iid unit-exponential
on the target base input. This is an input-law fact only, before GPS service. -/
theorem stationaryAdmittedTargetWorkRequirement_hasLaw
    (M : SLA2026BoroughQueueingInput Category) (target : Category) (i : ℤ) :
    HasLaw (fun x : GoodSuspensionState × (ℤ → ℝ) =>
      stationaryPoissonWorkRequirement x i)
      (expMeasure 1)
      (M.stationaryAdmittedTargetBaseLaw target).Pbase := by
  simpa only [stationaryAdmittedTargetBaseLaw] using
    (stationaryPoissonWorkRequirement_hasLaw (M.admittedRate_pos target) i)

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
