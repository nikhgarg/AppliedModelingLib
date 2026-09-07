import AppliedModelingLib.Foundations.Probability.PoissonSuspensionWorkMarks
import AppliedModelingLib.Foundations.Probability.PalmMarkedCampbell
import AppliedModelingLib.Foundations.Probability.Processes.TimedEmbedded.MarkedPointSet
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Stationary Poisson input with iid admission and work marks

This module constructs one source-faithful stationary raw Poisson input whose
arrival-indexed marks are independent Bernoulli admissions and independent
unit-exponential work requirements.  It proves the all-event Campbell/Palm
certificate and the selected-true-mark Palm certificate while retaining the
original all-event integer enumeration.

It deliberately does not re-enumerate the surviving admitted events, claim a
standalone admitted Poisson path, combine several classes under a selected
Palm law, construct queue dynamics, or prove a response-time tail.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open PoissonProcess

noncomputable section

/-- The Bernoulli admission mark law for one raw request. -/
def admissionMarkMeasure (p : ℝ≥0) (hp : p ≤ 1) : Measure Bool :=
  (PMF.bernoulli p hp).toMeasure

/-- The independent admission/work law for one raw request. -/
def admissionWorkMarkMeasure (p : ℝ≥0) (hp : p ≤ 1) : Measure (Bool × ℝ) :=
  (admissionMarkMeasure p hp).prod (ProbabilityTheory.expMeasure 1)

/-- A two-sided iid path of admission/work marks, synchronized with the
integer-indexed raw Poisson arrivals. -/
def twoSidedAdmissionWorkPathMeasure (p : ℝ≥0) (hp : p ≤ 1) :
    Measure (ℤ → (Bool × ℝ)) :=
  Measure.infinitePi fun _ : ℤ => admissionWorkMarkMeasure p hp

theorem isProbabilityMeasure_admissionMarkMeasure
    (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (admissionMarkMeasure p hp) := by
  unfold admissionMarkMeasure
  infer_instance

theorem isProbabilityMeasure_admissionWorkMarkMeasure
    (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (admissionWorkMarkMeasure p hp) := by
  letI : IsProbabilityMeasure (admissionMarkMeasure p hp) :=
    isProbabilityMeasure_admissionMarkMeasure p hp
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (1 : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  simpa [admissionWorkMarkMeasure] using
    (inferInstance : IsProbabilityMeasure
      ((admissionMarkMeasure p hp).prod (ProbabilityTheory.expMeasure 1)))

theorem isProbabilityMeasure_twoSidedAdmissionWorkPathMeasure
    (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (twoSidedAdmissionWorkPathMeasure p hp) := by
  let μ : Measure (Bool × ℝ) := admissionWorkMarkMeasure p hp
  letI : ∀ i : ℤ, IsProbabilityMeasure μ := fun _ =>
    isProbabilityMeasure_admissionWorkMarkMeasure p hp
  simpa [twoSidedAdmissionWorkPathMeasure, μ] using
    (inferInstance : IsProbabilityMeasure (Measure.infinitePi fun _ : ℤ => μ))

/-- The admission/work mark at one arrival index of the two-sided iid path. -/
def twoSidedAdmissionWorkMark (i : ℤ) :
    (ℤ → (Bool × ℝ)) → (Bool × ℝ) := fun x => x i

theorem measurable_twoSidedAdmissionWorkMark (i : ℤ) :
    Measurable (twoSidedAdmissionWorkMark i) := by
  simpa [twoSidedAdmissionWorkMark] using
    (measurable_pi_apply i : Measurable (fun x : ℤ → (Bool × ℝ) => x i))

theorem twoSidedAdmissionWorkMark_hasLaw
    (p : ℝ≥0) (hp : p ≤ 1) (i : ℤ) :
    HasLaw (twoSidedAdmissionWorkMark i) (admissionWorkMarkMeasure p hp)
      (twoSidedAdmissionWorkPathMeasure p hp) := by
  exact (@measurePreserving_eval_infinitePi ℤ (fun _ : ℤ => Bool × ℝ)
    (fun _ => inferInstance)
    (fun _ : ℤ => admissionWorkMarkMeasure p hp)
    (fun _ => isProbabilityMeasure_admissionWorkMarkMeasure p hp) i).hasLaw

/-- The complete arrival-indexed admission/work pairs are iid. -/
theorem iIndepFun_twoSidedAdmissionWorkMark
    (p : ℝ≥0) (hp : p ≤ 1) :
    iIndepFun twoSidedAdmissionWorkMark
      (twoSidedAdmissionWorkPathMeasure p hp) := by
  simpa [twoSidedAdmissionWorkMark, twoSidedAdmissionWorkPathMeasure] using
    (@iIndepFun_infinitePi ℤ (fun _ : ℤ => Bool × ℝ)
      (fun _ => inferInstance) (fun _ : ℤ => Bool × ℝ)
      (fun _ => inferInstance)
      (fun _ : ℤ => admissionWorkMarkMeasure p hp)
      (fun _ => isProbabilityMeasure_admissionWorkMarkMeasure p hp)
      (fun _ => id) (fun _ => measurable_id))

theorem twoSidedAdmissionWorkMark_admission_hasLaw
    (p : ℝ≥0) (hp : p ≤ 1) (i : ℤ) :
    HasLaw (fun x : ℤ → (Bool × ℝ) => (twoSidedAdmissionWorkMark i x).1)
      (admissionMarkMeasure p hp) (twoSidedAdmissionWorkPathMeasure p hp) := by
  let B : Measure Bool := admissionMarkMeasure p hp
  let W : Measure ℝ := ProbabilityTheory.expMeasure 1
  letI : IsProbabilityMeasure B := isProbabilityMeasure_admissionMarkMeasure p hp
  letI : IsProbabilityMeasure W :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hpair := twoSidedAdmissionWorkMark_hasLaw p hp i
  simpa [B, W, admissionWorkMarkMeasure, twoSidedAdmissionWorkMark,
    Function.comp_def] using
    ((measurePreserving_fst : MeasurePreserving Prod.fst (B.prod W) B).hasLaw.comp hpair)

theorem twoSidedAdmissionWorkMark_work_hasLaw
    (p : ℝ≥0) (hp : p ≤ 1) (i : ℤ) :
    HasLaw (fun x : ℤ → (Bool × ℝ) => (twoSidedAdmissionWorkMark i x).2)
      (ProbabilityTheory.expMeasure 1) (twoSidedAdmissionWorkPathMeasure p hp) := by
  let B : Measure Bool := admissionMarkMeasure p hp
  let W : Measure ℝ := ProbabilityTheory.expMeasure 1
  letI : IsProbabilityMeasure B := isProbabilityMeasure_admissionMarkMeasure p hp
  letI : IsProbabilityMeasure W :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hpair := twoSidedAdmissionWorkMark_hasLaw p hp i
  simpa [B, W, admissionWorkMarkMeasure, twoSidedAdmissionWorkMark,
    Function.comp_def] using
    ((measurePreserving_snd : MeasurePreserving Prod.snd (B.prod W) W).hasLaw.comp hpair)

/-- Integer reindexing preserves the iid two-sided admission/work mark path. -/
theorem intPathShift_measurePreserving_twoSidedAdmissionWorkPathMeasure
    (p : ℝ≥0) (hp : p ≤ 1) (k : ℤ) :
    MeasurePreserving (intPathShift (α := Bool × ℝ) k)
      (twoSidedAdmissionWorkPathMeasure p hp)
      (twoSidedAdmissionWorkPathMeasure p hp) := by
  refine ⟨measurable_intPathShift (α := Bool × ℝ) k, ?_⟩
  change Measure.map (fun x i => twoSidedAdmissionWorkMark (k + i) x)
    (twoSidedAdmissionWorkPathMeasure p hp) =
      twoSidedAdmissionWorkPathMeasure p hp
  letI : IsProbabilityMeasure (twoSidedAdmissionWorkPathMeasure p hp) :=
    isProbabilityMeasure_twoSidedAdmissionWorkPathMeasure p hp
  have hshift : iIndepFun
      (fun i x => twoSidedAdmissionWorkMark (k + i) x)
      (twoSidedAdmissionWorkPathMeasure p hp) := by
    exact iIndepFun.precomp
      (g := fun i : ℤ => k + i)
      (by intro a b hab; exact add_left_cancel hab)
      (iIndepFun_twoSidedAdmissionWorkMark p hp)
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun i => measurable_twoSidedAdmissionWorkMark (k + i)) |>.mp hshift]
  simp only [twoSidedAdmissionWorkPathMeasure]
  congr 1
  funext i
  exact (twoSidedAdmissionWorkMark_hasLaw p hp (k + i)).map_eq

theorem admissionMarkMeasure_true_mass
    (p : ℝ≥0) (hp : p ≤ 1) :
    admissionMarkMeasure p hp {true} = (p : ℝ≥0∞) := by
  simp [admissionMarkMeasure]

theorem admissionMarkMeasure_true_mass_ofReal
    (p : ℝ≥0) (hp : p ≤ 1) :
    admissionMarkMeasure p hp {true} = ENNReal.ofReal (p : ℝ) := by
  simpa only [ENNReal.ofReal_coe_nnreal] using admissionMarkMeasure_true_mass p hp

theorem admissionMarkMeasure_true_mass_ne_zero
    {p : ℝ≥0} (hp : p ≤ 1) (hp_pos : 0 < p) :
    admissionMarkMeasure p hp {true} ≠ 0 := by
  rw [admissionMarkMeasure_true_mass]
  exact ENNReal.coe_ne_zero.mpr (ne_of_gt hp_pos)

/-- A stationary raw Poisson input with an iid admission/work mark pair at
each raw arrival. -/
noncomputable def stationaryPoissonAdmissionWorkMeasure
    (arrivalRate : ℝ) (p : ℝ≥0) (hp : p ≤ 1) :
    Measure (GoodSuspensionState × (ℤ → (Bool × ℝ))) :=
  timedEmbeddedSuspensionProductMeasure arrivalRate
    (twoSidedAdmissionWorkPathMeasure p hp)

theorem isProbabilityMeasure_stationaryPoissonAdmissionWorkMeasure
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (stationaryPoissonAdmissionWorkMeasure arrivalRate p hp) := by
  letI : IsProbabilityMeasure (goodSuspensionMeasure arrivalRate) :=
    isProbabilityMeasure_goodSuspensionMeasure harrivalRate
  letI : IsProbabilityMeasure (twoSidedAdmissionWorkPathMeasure p hp) :=
    isProbabilityMeasure_twoSidedAdmissionWorkPathMeasure p hp
  simpa [stationaryPoissonAdmissionWorkMeasure,
    timedEmbeddedSuspensionProductMeasure] using
    (inferInstance : IsProbabilityMeasure
      ((goodSuspensionMeasure arrivalRate).prod
        (twoSidedAdmissionWorkPathMeasure p hp)))

/-- The raw stationary Poisson configuration is independent of the complete
admission/work mark path. -/
theorem indepFun_stationaryPoissonAdmissionWork_arrivals_marks
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (p : ℝ≥0) (hp : p ≤ 1) :
    IndepFun (fun z : GoodSuspensionState × (ℤ → (Bool × ℝ)) => z.1)
      (fun z : GoodSuspensionState × (ℤ → (Bool × ℝ)) => z.2)
      (stationaryPoissonAdmissionWorkMeasure arrivalRate p hp) := by
  let G : Measure GoodSuspensionState := goodSuspensionMeasure arrivalRate
  let P : Measure (ℤ → (Bool × ℝ)) := twoSidedAdmissionWorkPathMeasure p hp
  letI : IsProbabilityMeasure G := isProbabilityMeasure_goodSuspensionMeasure harrivalRate
  letI : IsProbabilityMeasure P :=
    isProbabilityMeasure_twoSidedAdmissionWorkPathMeasure p hp
  simpa [stationaryPoissonAdmissionWorkMeasure,
    timedEmbeddedSuspensionProductMeasure, G, P] using
    (indepFun_prod (μ := G) (ν := P) (X := id) (Y := id)
      measurable_id measurable_id)

/-- The real-time invariant law of the stationary raw marked input. -/
noncomputable def stationaryPoissonAdmissionWorkShiftInvariantLaw
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (p : ℝ≥0) (hp : p ≤ 1) :
    Palm.ShiftInvariantProbabilityLaw
      (GoodSuspensionState × (ℤ → (Bool × ℝ))) := by
  letI : IsProbabilityMeasure (twoSidedAdmissionWorkPathMeasure p hp) :=
    isProbabilityMeasure_twoSidedAdmissionWorkPathMeasure p hp
  exact timedEmbeddedSuspensionShiftInvariantLaw_of_intPathShift harrivalRate
    (twoSidedAdmissionWorkPathMeasure p hp)
    (fun k => intPathShift_measurePreserving_twoSidedAdmissionWorkPathMeasure
      p hp k)

/-- The all-event tagged-arrival law for the stationary raw marked input. -/
noncomputable def stationaryPoissonAdmissionWorkTaggedArrivalAtZero
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (p : ℝ≥0) (hp : p ≤ 1) :
    TaggedArrivalAtZero ((ℤ → ℝ) × (ℤ → (Bool × ℝ))) := by
  letI : IsProbabilityMeasure (twoSidedAdmissionWorkPathMeasure p hp) :=
    isProbabilityMeasure_twoSidedAdmissionWorkPathMeasure p hp
  exact timedEmbeddedTaggedArrivalAtZero arrivalRate harrivalRate
    (twoSidedAdmissionWorkPathMeasure p hp)

/-- The all-event Campbell/Palm certificate of the stationary raw marked
input. -/
noncomputable def stationaryPoissonAdmissionWorkCampbellCertificate
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (p : ℝ≥0) (hp : p ≤ 1) :
    Palm.CampbellPalmTaggedArrivalCertificate
      (stationaryPoissonAdmissionWorkShiftInvariantLaw harrivalRate p hp)
      (stationaryPoissonAdmissionWorkTaggedArrivalAtZero harrivalRate p hp) := by
  letI : IsProbabilityMeasure (twoSidedAdmissionWorkPathMeasure p hp) :=
    isProbabilityMeasure_twoSidedAdmissionWorkPathMeasure p hp
  simpa only [stationaryPoissonAdmissionWorkShiftInvariantLaw,
    stationaryPoissonAdmissionWorkTaggedArrivalAtZero] using
    (timedEmbeddedCampbellCertificate_of_independentPath harrivalRate
      (twoSidedAdmissionWorkPathMeasure p hp)
      (fun k => intPathShift_measurePreserving_twoSidedAdmissionWorkPathMeasure
        p hp k))

/-- The Boolean admission mark at a raw stationary arrival. -/
def stationaryPoissonAdmissionWorkMarkAt
    (z : GoodSuspensionState × (ℤ → (Bool × ℝ))) (i : ℤ) : Bool :=
  (z.2 i).1

/-- The service work attached to a raw stationary arrival. -/
def stationaryPoissonAdmissionWorkRequirement
    (z : GoodSuspensionState × (ℤ → (Bool × ℝ))) (i : ℤ) : ℝ :=
  (z.2 i).2

theorem stationaryPoissonAdmissionWorkMarkPair_hasLaw
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (p : ℝ≥0) (hp : p ≤ 1) (i : ℤ) :
    HasLaw (fun z : GoodSuspensionState × (ℤ → (Bool × ℝ)) => z.2 i)
      (admissionWorkMarkMeasure p hp)
      (stationaryPoissonAdmissionWorkMeasure arrivalRate p hp) := by
  let G : Measure GoodSuspensionState := goodSuspensionMeasure arrivalRate
  let P : Measure (ℤ → (Bool × ℝ)) := twoSidedAdmissionWorkPathMeasure p hp
  letI : IsProbabilityMeasure G := isProbabilityMeasure_goodSuspensionMeasure harrivalRate
  letI : IsProbabilityMeasure P :=
    isProbabilityMeasure_twoSidedAdmissionWorkPathMeasure p hp
  have hprojection : MeasurePreserving
      (fun z : GoodSuspensionState × (ℤ → (Bool × ℝ)) => z.2) (G.prod P) P :=
    measurePreserving_snd
  have hpair := twoSidedAdmissionWorkMark_hasLaw p hp i
  simpa [stationaryPoissonAdmissionWorkMeasure,
    timedEmbeddedSuspensionProductMeasure, G, P, twoSidedAdmissionWorkMark,
    Function.comp_def] using hpair.comp hprojection.hasLaw

theorem stationaryPoissonAdmissionWorkRequirement_hasLaw
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (p : ℝ≥0) (hp : p ≤ 1) (i : ℤ) :
    HasLaw (fun z : GoodSuspensionState × (ℤ → (Bool × ℝ)) =>
      stationaryPoissonAdmissionWorkRequirement z i)
      (ProbabilityTheory.expMeasure 1)
      (stationaryPoissonAdmissionWorkMeasure arrivalRate p hp) := by
  let B : Measure Bool := admissionMarkMeasure p hp
  let W : Measure ℝ := ProbabilityTheory.expMeasure 1
  letI : IsProbabilityMeasure B := isProbabilityMeasure_admissionMarkMeasure p hp
  letI : IsProbabilityMeasure W :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hpair := stationaryPoissonAdmissionWorkMarkPair_hasLaw
    harrivalRate p hp i
  simpa [B, W, admissionWorkMarkMeasure,
    stationaryPoissonAdmissionWorkRequirement, Function.comp_def] using
    ((measurePreserving_snd : MeasurePreserving Prod.snd (B.prod W) W).hasLaw.comp hpair)

/-- The tag's admission mark in the all-event Palm law. -/
def stationaryPoissonAdmissionWorkTaggedMark :
    ((ℤ → ℝ) × (ℤ → (Bool × ℝ))) → Bool :=
  fun z => (z.2 0).1

theorem measurable_stationaryPoissonAdmissionWorkTaggedMark :
    Measurable stationaryPoissonAdmissionWorkTaggedMark := by
  exact measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)

theorem stationaryPoissonAdmissionWorkMark_recenterAt_zero
    (z : GoodSuspensionState × (ℤ → (Bool × ℝ))) (i : ℤ) :
    stationaryPoissonAdmissionWorkMarkAt z i =
      stationaryPoissonAdmissionWorkTaggedMark (timedEmbeddedRecenterAt z i) := by
  simp [stationaryPoissonAdmissionWorkMarkAt,
    stationaryPoissonAdmissionWorkTaggedMark, timedEmbeddedRecenterAt,
    intPathShift]

theorem stationaryPoissonAdmissionWorkTaggedAdmissionWork_hasLaw
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (p : ℝ≥0) (hp : p ≤ 1) :
    HasLaw (fun z : ((ℤ → ℝ) × (ℤ → (Bool × ℝ))) => z.2 0)
      (admissionWorkMarkMeasure p hp)
      (stationaryPoissonAdmissionWorkTaggedArrivalAtZero harrivalRate p hp).Ptag := by
  let P : Measure (ℤ → (Bool × ℝ)) := twoSidedAdmissionWorkPathMeasure p hp
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_twoSidedAdmissionWorkPathMeasure p hp
  have htag := timedEmbeddedTaggedArrivalAtZero_pathStatistic_hasLaw P
    (fun x : ℤ → (Bool × ℝ) => x 0) (measurable_pi_apply 0)
    arrivalRate harrivalRate
  have hpair := twoSidedAdmissionWorkMark_hasLaw p hp 0
  refine ⟨((measurable_pi_apply 0).comp measurable_snd).aemeasurable, ?_⟩
  change Measure.map (fun z : ((ℤ → ℝ) × (ℤ → (Bool × ℝ))) => z.2 0)
      (timedEmbeddedTaggedArrivalAtZero arrivalRate harrivalRate P).Ptag =
        admissionWorkMarkMeasure p hp
  calc
    Measure.map (fun z : ((ℤ → ℝ) × (ℤ → (Bool × ℝ))) => z.2 0)
        (timedEmbeddedTaggedArrivalAtZero arrivalRate harrivalRate P).Ptag =
        P.map (fun x : ℤ → (Bool × ℝ) => x 0) := htag.map_eq
    _ = admissionWorkMarkMeasure p hp := by
      simpa [P, twoSidedAdmissionWorkMark] using hpair.map_eq

theorem stationaryPoissonAdmissionWorkTaggedMark_hasLaw
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (p : ℝ≥0) (hp : p ≤ 1) :
    HasLaw stationaryPoissonAdmissionWorkTaggedMark
      (admissionMarkMeasure p hp)
      (stationaryPoissonAdmissionWorkTaggedArrivalAtZero harrivalRate p hp).Ptag := by
  let B : Measure Bool := admissionMarkMeasure p hp
  let W : Measure ℝ := ProbabilityTheory.expMeasure 1
  letI : IsProbabilityMeasure B := isProbabilityMeasure_admissionMarkMeasure p hp
  letI : IsProbabilityMeasure W :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hpair := stationaryPoissonAdmissionWorkTaggedAdmissionWork_hasLaw
    harrivalRate p hp
  simpa [B, W, admissionWorkMarkMeasure,
    stationaryPoissonAdmissionWorkTaggedMark, Function.comp_def] using
    ((measurePreserving_fst : MeasurePreserving Prod.fst (B.prod W) B).hasLaw.comp hpair)

theorem stationaryPoissonAdmissionWorkTaggedMark_true_mass
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (p : ℝ≥0) (hp : p ≤ 1) :
    (stationaryPoissonAdmissionWorkTaggedArrivalAtZero harrivalRate p hp).Ptag
      (stationaryPoissonAdmissionWorkTaggedMark ⁻¹' ({true} : Set Bool)) =
        ENNReal.ofReal (p : ℝ) := by
  have hmark := stationaryPoissonAdmissionWorkTaggedMark_hasLaw harrivalRate p hp
  rw [← Measure.map_apply_of_aemeasurable hmark.aemeasurable
    (MeasurableSet.singleton true), hmark.map_eq]
  exact admissionMarkMeasure_true_mass_ofReal p hp

theorem stationaryPoissonAdmissionWorkTaggedMark_true_mass_ne_zero
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    {p : ℝ≥0} (hp : p ≤ 1) (hp_pos : 0 < p) :
    (stationaryPoissonAdmissionWorkTaggedArrivalAtZero harrivalRate p hp).Ptag
      (stationaryPoissonAdmissionWorkTaggedMark ⁻¹' ({true} : Set Bool)) ≠ 0 := by
  rw [stationaryPoissonAdmissionWorkTaggedMark_true_mass harrivalRate p hp]
  exact ENNReal.ofReal_ne_zero_iff.mpr (by exact_mod_cast hp_pos)

/-- Conditioning a pair-valued random variable on a positive `true` Boolean
first coordinate preserves the independent second-coordinate law.  This is a
measure-level lemma, so it applies to the selected tagged law below without
assuming a survivor re-enumeration. -/
theorem hasLaw_snd_conditionOn_true_of_pair_product
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (m : Ω → Bool × β) (hm : Measurable m)
    {B : Measure Bool} [IsProbabilityMeasure B]
    {W : Measure β} [IsProbabilityMeasure W]
    (H : HasLaw m (B.prod W) P) (htrue : B {true} ≠ 0) :
    HasLaw (fun ω => (m ω).2) W (P[| {ω | (m ω).1 = true}]) := by
  let E : Set Ω := {ω | (m ω).1 = true}
  let A : Set β → Set Ω := fun s => {ω | (m ω).2 ∈ s}
  have hE : MeasurableSet E :=
    (measurableSet_singleton true).preimage (measurable_fst.comp hm)
  have hPE : P E = B {true} := by
    calc
      P E = Measure.map m P (({true} : Set Bool) ×ˢ Set.univ) := by
        rw [Measure.map_apply hm ((measurableSet_singleton _).prod MeasurableSet.univ)]
        congr 1
        ext ω
        simp [E]
      _ = (B.prod W) (({true} : Set Bool) ×ˢ Set.univ) := by
        rw [H.map_eq]
      _ = B {true} := by
        rw [Measure.prod_prod, measure_univ, mul_one]
  have hPEA : ∀ s : Set β, MeasurableSet s →
      P (E ∩ A s) = B {true} * W s := by
    intro s hs
    calc
      P (E ∩ A s) = Measure.map m P (({true} : Set Bool) ×ˢ s) := by
        rw [Measure.map_apply hm ((measurableSet_singleton _).prod hs)]
        apply congrArg P
        ext ω
        rcases m ω with ⟨b, x⟩
        simp [E, A]
      _ = (B.prod W) (({true} : Set Bool) ×ˢ s) := by
        rw [H.map_eq]
      _ = B {true} * W s := by
        rw [Measure.prod_prod, mul_comm]
  refine ⟨(measurable_snd.comp hm).aemeasurable, ?_⟩
  apply Measure.ext
  intro s hs
  change Measure.map (Prod.snd ∘ m) (P[| E]) s = W s
  rw [Measure.map_apply (measurable_snd.comp hm) hs]
  change P[A s | E] = W s
  rw [ProbabilityTheory.cond_apply hE P (A s), hPE, hPEA s hs,
    ← mul_assoc, ENNReal.inv_mul_cancel htrue (measure_ne_top B {true}), one_mul]

/-- The selected admitted tagged law is the all-event tagged law conditioned
on the tag's independently sampled admission mark being `true`. -/
noncomputable def stationaryPoissonAdmissionWorkAdmittedTaggedArrivalAtZero
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (p : ℝ≥0) (hp : p ≤ 1) (hp_pos : 0 < p) :
    TaggedArrivalAtZero ((ℤ → ℝ) × (ℤ → (Bool × ℝ))) :=
  (stationaryPoissonAdmissionWorkTaggedArrivalAtZero harrivalRate p hp).conditionOn
    (stationaryPoissonAdmissionWorkTaggedMark ⁻¹' ({true} : Set Bool))
    (stationaryPoissonAdmissionWorkTaggedMark_true_mass_ne_zero
      harrivalRate hp hp_pos)

/-- Conditioning on admission preserves the tagged job's independent
unit-exponential work law. -/
theorem stationaryPoissonAdmissionWorkAdmittedTaggedWork_hasLaw
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (p : ℝ≥0) (hp : p ≤ 1) (hp_pos : 0 < p) :
    HasLaw (fun z : ((ℤ → ℝ) × (ℤ → (Bool × ℝ))) => (z.2 0).2)
      (ProbabilityTheory.expMeasure 1)
      (stationaryPoissonAdmissionWorkAdmittedTaggedArrivalAtZero
        harrivalRate p hp hp_pos).Ptag := by
  let B : Measure Bool := admissionMarkMeasure p hp
  let W : Measure ℝ := ProbabilityTheory.expMeasure 1
  let T := stationaryPoissonAdmissionWorkTaggedArrivalAtZero harrivalRate p hp
  letI : IsProbabilityMeasure B := isProbabilityMeasure_admissionMarkMeasure p hp
  letI : IsProbabilityMeasure W :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure T.Ptag := T.isProbability
  have hpair := stationaryPoissonAdmissionWorkTaggedAdmissionWork_hasLaw
    harrivalRate p hp
  have htrue : B {true} ≠ 0 := by
    dsimp [B]
    exact admissionMarkMeasure_true_mass_ne_zero hp hp_pos
  have hconditioned := hasLaw_snd_conditionOn_true_of_pair_product
    (m := fun z : ((ℤ → ℝ) × (ℤ → (Bool × ℝ))) => z.2 0)
    (hm := (measurable_pi_apply 0).comp measurable_snd)
    (B := B) (W := W) hpair htrue
  change HasLaw (fun z : ((ℤ → ℝ) × (ℤ → (Bool × ℝ))) => (z.2 0).2) W
    (T.conditionOn (stationaryPoissonAdmissionWorkTaggedMark ⁻¹'
      ({true} : Set Bool))
      (stationaryPoissonAdmissionWorkTaggedMark_true_mass_ne_zero
        harrivalRate hp hp_pos)).Ptag
  rw [TaggedArrivalAtZero.conditionOn_Ptag]
  simpa [T, B, W, stationaryPoissonAdmissionWorkTaggedMark] using hconditioned

/-- The selected-true-mark Campbell/Palm certificate.  It retains the raw
all-event indexing and marks selected raw indices, rather than postulating a
separate admitted-event enumeration. -/
noncomputable def stationaryPoissonAdmissionWorkAdmittedCampbellCertificate
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (p : ℝ≥0) (hp : p ≤ 1) (hp_pos : 0 < p) :
    Palm.MarkedCampbellPalmTaggedArrivalCertificate
      (stationaryPoissonAdmissionWorkShiftInvariantLaw harrivalRate p hp)
      (stationaryPoissonAdmissionWorkAdmittedTaggedArrivalAtZero
        harrivalRate p hp hp_pos) := by
  let H := stationaryPoissonAdmissionWorkCampbellCertificate harrivalRate p hp
  let markAt : (GoodSuspensionState × (ℤ → (Bool × ℝ))) → ℤ → Bool :=
    stationaryPoissonAdmissionWorkMarkAt
  have hmark : ∀ z i, markAt z i =
      stationaryPoissonAdmissionWorkTaggedMark (H.recenterAt z i) := by
    intro z i
    change (z.2 i).1 =
      stationaryPoissonAdmissionWorkTaggedMark (timedEmbeddedRecenterAt z i)
    exact stationaryPoissonAdmissionWorkMark_recenterAt_zero z i
  have hpointShift : ∀ t, ∀ᵐ z ∂
      (stationaryPoissonAdmissionWorkShiftInvariantLaw harrivalRate p hp).Pbase,
      Palm.trueMarkedPointSet H.baseArrivals markAt
          ((stationaryPoissonAdmissionWorkShiftInvariantLaw harrivalRate p hp).shift t z) =
        (fun u : ℝ => u - t) '' Palm.trueMarkedPointSet H.baseArrivals markAt z := by
    intro t
    filter_upwards [] with z
    change timedEmbeddedSelectedPointSet Prod.fst
        (timedEmbeddedSuspensionFlow (α := Bool × ℝ) t z) =
      (fun u : ℝ => u - t) '' timedEmbeddedSelectedPointSet Prod.fst z
    exact timedEmbeddedSelectedPointSet_flow Prod.fst z t
  have hmass :
      (stationaryPoissonAdmissionWorkTaggedArrivalAtZero harrivalRate p hp).Ptag
        (stationaryPoissonAdmissionWorkTaggedMark ⁻¹' ({true} : Set Bool)) =
        ENNReal.ofReal (p : ℝ) :=
    stationaryPoissonAdmissionWorkTaggedMark_true_mass harrivalRate p hp
  have htrue :
      (stationaryPoissonAdmissionWorkTaggedArrivalAtZero harrivalRate p hp).Ptag
        (stationaryPoissonAdmissionWorkTaggedMark ⁻¹' ({true} : Set Bool)) ≠ 0 :=
    stationaryPoissonAdmissionWorkTaggedMark_true_mass_ne_zero
      harrivalRate hp hp_pos
  have hselectedRate : 0 < arrivalRate * (p : ℝ) := by
    exact mul_pos harrivalRate (by exact_mod_cast hp_pos)
  exact Palm.markedCampbellCertificate_conditionOnTrue H
    stationaryPoissonAdmissionWorkTaggedMark
    measurable_stationaryPoissonAdmissionWorkTaggedMark markAt hmark
    hpointShift (p : ℝ) hmass htrue hselectedRate

theorem stationaryPoissonAdmissionWorkAdmittedCampbellCertificate_arrivalRate
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (p : ℝ≥0) (hp : p ≤ 1) (hp_pos : 0 < p) :
    (stationaryPoissonAdmissionWorkAdmittedCampbellCertificate
      harrivalRate p hp hp_pos).arrivalRate = arrivalRate * (p : ℝ) :=
  rfl

theorem stationaryPoissonAdmissionWorkAdmittedCampbellCertificate_arrivalRate_pos
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (p : ℝ≥0) (hp : p ≤ 1) (hp_pos : 0 < p) :
    0 < (stationaryPoissonAdmissionWorkAdmittedCampbellCertificate
      harrivalRate p hp hp_pos).arrivalRate :=
  (stationaryPoissonAdmissionWorkAdmittedCampbellCertificate
    harrivalRate p hp hp_pos).arrivalRate_pos

end

end AppliedModelingLib.Probability.Queueing
