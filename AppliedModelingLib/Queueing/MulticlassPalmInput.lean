import AppliedModelingLib.Foundations.Probability.MulticlassStationaryPoisson
import AppliedModelingLib.Foundations.Probability.PalmCampbellProductLift
import AppliedModelingLib.Foundations.Probability.PalmTaggedPoissonWorkPastRate
import AppliedModelingLib.Foundations.Probability.PalmCampbellTimeIntensity
import AppliedModelingLib.Foundations.Probability.Processes.Palm.SelectedMarkedTransport
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Multiclass stationary Poisson Palm input

This module packages a finite collection of independent stationary marked
Poisson input streams around one distinguished class arrival.  The
distinguished stream is put under its concrete one-class Campbell/Palm law;
all other streams remain independent stationary inputs and are translated by
the distinguished arrival's physical epoch.  Thus the resulting tagged law is
a genuine multiclass Palm law, rather than an unshifted product construction.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory
open Probability
open scoped ENNReal

noncomputable section

variable {Class : Type*} [Fintype Class]

local instance : DecidableEq Class := Classical.decEq Class

/-- The complete stationary input path of one Poisson class: a literal
two-sided arrival suspension and a two-sided iid unit-exponential work path. -/
abbrev StationaryPoissonWorkPath :=
  Probability.PoissonProcess.GoodSuspensionState × (Int → Real)

/-- Split a finite multiclass stationary input into one distinguished class
path and the remaining class paths.  This is only a change of coordinates on
the literal finite product carrier. -/
def multiclassStationaryPoissonWorkClassSplit
    {Class : Type*} (i : Class) :
    (Class → StationaryPoissonWorkPath) →
      StationaryPoissonWorkPath × ({j : Class // j ≠ i} → StationaryPoissonWorkPath) :=
  fun omega => (omega i, fun j => omega j)

/-- Assemble a full finite multiclass input from a distinguished class path
and paths for the remaining classes. -/
def multiclassStationaryPoissonWorkClassAssemble
    {Class : Type*} (i : Class) :
    StationaryPoissonWorkPath × ({j : Class // j ≠ i} → StationaryPoissonWorkPath) →
      Class → StationaryPoissonWorkPath :=
  fun x j => if hji : j = i then x.1 else x.2 ⟨j, hji⟩

@[simp]
theorem multiclassStationaryPoissonWorkClassAssemble_apply_eq
    {Class : Type*} (i : Class)
    (x : StationaryPoissonWorkPath × ({j : Class // j ≠ i} → StationaryPoissonWorkPath)) :
    multiclassStationaryPoissonWorkClassAssemble i x i = x.1 := by
  simp [multiclassStationaryPoissonWorkClassAssemble]

@[simp]
theorem multiclassStationaryPoissonWorkClassAssemble_apply_ne
    {Class : Type*} (i j : Class) (hji : j ≠ i)
    (x : StationaryPoissonWorkPath × ({k : Class // k ≠ i} → StationaryPoissonWorkPath)) :
    multiclassStationaryPoissonWorkClassAssemble i x j = x.2 ⟨j, hji⟩ := by
  simp [multiclassStationaryPoissonWorkClassAssemble, hji]

/-- Splitting an assembled carrier recovers its distinguished and passive
coordinates. -/
theorem multiclassStationaryPoissonWorkClassSplit_assemble
    {Class : Type*} (i : Class)
    (x : StationaryPoissonWorkPath × ({j : Class // j ≠ i} → StationaryPoissonWorkPath)) :
    multiclassStationaryPoissonWorkClassSplit i
      (multiclassStationaryPoissonWorkClassAssemble i x) = x := by
  apply Prod.ext
  · exact multiclassStationaryPoissonWorkClassAssemble_apply_eq i x
  · funext j
    exact multiclassStationaryPoissonWorkClassAssemble_apply_ne i j.1 j.2 x

/-- Assembling the distinguished coordinate and all passive coordinates of a
full input recovers that input. -/
theorem multiclassStationaryPoissonWorkClassAssemble_split
    {Class : Type*} (i : Class) (omega : Class → StationaryPoissonWorkPath) :
    multiclassStationaryPoissonWorkClassAssemble i
      (multiclassStationaryPoissonWorkClassSplit i omega) = omega := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [multiclassStationaryPoissonWorkClassAssemble,
      multiclassStationaryPoissonWorkClassSplit]
  · simp [multiclassStationaryPoissonWorkClassAssemble,
      multiclassStationaryPoissonWorkClassSplit, hji]

/-- Splitting the finite product carrier is measurable. -/
theorem measurable_multiclassStationaryPoissonWorkClassSplit
    {Class : Type*} (i : Class) :
    Measurable (multiclassStationaryPoissonWorkClassSplit i :
      (Class → StationaryPoissonWorkPath) →
        StationaryPoissonWorkPath ×
          ({j : Class // j ≠ i} → StationaryPoissonWorkPath)) := by
  exact (measurable_pi_apply i).prodMk
    (measurable_pi_iff.mpr fun j => measurable_pi_apply j.1)

/-- Assembling the finite product carrier is measurable. -/
theorem measurable_multiclassStationaryPoissonWorkClassAssemble
    {Class : Type*} (i : Class) :
    Measurable (multiclassStationaryPoissonWorkClassAssemble i :
      (StationaryPoissonWorkPath ×
        ({j : Class // j ≠ i} → StationaryPoissonWorkPath)) →
          Class → StationaryPoissonWorkPath) := by
  apply measurable_pi_iff.mpr
  intro j
  by_cases hji : j = i
  · subst j
    simpa [multiclassStationaryPoissonWorkClassAssemble] using
      (measurable_fst : Measurable (fun x :
        StationaryPoissonWorkPath × ({k : Class // k ≠ i} → StationaryPoissonWorkPath) => x.1))
  · simpa [multiclassStationaryPoissonWorkClassAssemble, hji] using
      ((measurable_pi_apply
        (X := fun _ : {k : Class // k ≠ i} => StationaryPoissonWorkPath)
        ⟨j, hji⟩).comp measurable_snd :
        Measurable (fun x : StationaryPoissonWorkPath ×
          ({k : Class // k ≠ i} → StationaryPoissonWorkPath) => x.2 ⟨j, hji⟩))

/-- The measurable equivalence between a full finite multiclass input and
one distinguished path paired with all remaining paths. -/
noncomputable def multiclassStationaryPoissonWorkClassSplitEquiv
    {Class : Type*} (i : Class) :
    (Class → StationaryPoissonWorkPath) ≃ᵐ
      StationaryPoissonWorkPath × ({j : Class // j ≠ i} → StationaryPoissonWorkPath) where
  toEquiv :=
    { toFun := multiclassStationaryPoissonWorkClassSplit i
      invFun := multiclassStationaryPoissonWorkClassAssemble i
      left_inv := multiclassStationaryPoissonWorkClassAssemble_split i
      right_inv := multiclassStationaryPoissonWorkClassSplit_assemble i }
  measurable_toFun := measurable_multiclassStationaryPoissonWorkClassSplit i
  measurable_invFun := measurable_multiclassStationaryPoissonWorkClassAssemble i

@[simp]
theorem multiclassStationaryPoissonWorkClassSplitEquiv_apply
    {Class : Type*} (i : Class) (omega : Class → StationaryPoissonWorkPath) :
    multiclassStationaryPoissonWorkClassSplitEquiv i omega =
      multiclassStationaryPoissonWorkClassSplit i omega := rfl

@[simp]
theorem multiclassStationaryPoissonWorkClassSplitEquiv_symm_apply
    {Class : Type*} (i : Class)
    (x : StationaryPoissonWorkPath × ({j : Class // j ≠ i} → StationaryPoissonWorkPath)) :
    (multiclassStationaryPoissonWorkClassSplitEquiv i).symm x =
      multiclassStationaryPoissonWorkClassAssemble i x := rfl

/-- The complete input carrier seen from one selected class arrival.  The
selected class uses its Palm-recentered arrival and mark paths, while every
other class retains a shifted stationary marked-Poisson path. -/
abbrev MulticlassStationaryPoissonWorkClassTaggedSample
    (Class : Type*) (i : Class) :=
  ((Int → Real) × (Int → Real)) ×
    ({j : Class // j ≠ i} → StationaryPoissonWorkPath)

/-- View a global multiclass stationary input at a time where the selected
class has zero phase.  The selected coordinate then has exactly the Palm
arrival-and-mark representation, while all other coordinates remain literal
stationary paths. -/
def multiclassStationaryPoissonWorkClassTaggedView
    {Class : Type*} (i : Class) :
    (Class → StationaryPoissonWorkPath) →
      MulticlassStationaryPoissonWorkClassTaggedSample Class i :=
  fun omega => (((omega i).1.1.1, (omega i).2), fun j => omega j)

/-- The arrival epoch of any labelled class customer on the selected-arrival
carrier.  The selected class is indexed relative to its customer at zero;
all other class paths have already been shifted to that same epoch. -/
def multiclassStationaryPoissonWorkClassTaggedArrival
    {Class : Type*} (i : Class) :
    MulticlassStationaryPoissonWorkClassTaggedSample Class i → Class → Int → Real :=
  fun z j k => if hji : j = i then
    Probability.PoissonProcess.candidatePalmArrival z.1.1 k
  else
    Probability.Queueing.stationaryPoissonWorkArrival (z.2 ⟨j, hji⟩) k

/-- The right-closed physical count of one passive input after the selected
arrival epoch.  It is the canonical renewal count of that class's literal
stationary suspension, started at its own phase. -/
noncomputable def multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount
    {Class : Type*} (i : Class)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i)
    (j : {k : Class // k ≠ i}) (t : ℝ) : ℕ :=
  Probability.PoissonProcess.suspensionBaseFutureCount (z.2 j).1 t

/-- The passive physical count is the cardinality of the literal stationary
arrival ledger in `(0,t]`. -/
theorem multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount_eq_card
    {Class : Type*} (i : Class)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i)
    (j : {k : Class // k ≠ i}) (t : ℝ) (ht : 0 ≤ t) :
    multiclassStationaryPoissonWorkClassTaggedPassiveFutureCount i z j t =
      (Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed
        0 t (z.2 j).1).card := by
  symm
  exact Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed_zero_card_eq_futureCount
    (z.2 j).1 t ht

/-- The work requirement of any labelled class customer on the
selected-arrival carrier.  This is the unscaled unit-exponential mark; client
models apply their class-specific mean-service factor separately. -/
def multiclassStationaryPoissonWorkClassTaggedRequirementAt
    {Class : Type*} (i : Class) :
    MulticlassStationaryPoissonWorkClassTaggedSample Class i → Class → Int → Real :=
  fun z j k => if hji : j = i then z.1.2 k else (z.2 ⟨j, hji⟩).2 k

/-- If the selected stationary coordinate is observed at phase zero, its
tagged-view arrival epochs are exactly the literal labelled epochs of the
full multiclass input. -/
theorem multiclassStationaryPoissonWorkClassTaggedArrival_view_eq_multiclassArrival
    {Class : Type*} (i j : Class)
    (omega : Class → StationaryPoissonWorkPath) (k : Int)
    (hphase : (omega i).1.1.2 = 0) :
    multiclassStationaryPoissonWorkClassTaggedArrival i
      (multiclassStationaryPoissonWorkClassTaggedView i omega) j k =
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival j omega k := by
  by_cases hji : j = i
  · subst j
    simp only [multiclassStationaryPoissonWorkClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedView,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival,
      Probability.Queueing.stationaryPoissonWorkArrival,
      Probability.Queueing.timedEmbeddedArrival,
      Probability.PoissonProcess.suspensionBaseArrival]
    rw [hphase]
    simp
  · simp [multiclassStationaryPoissonWorkClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedView,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival,
      hji]

/-- The tagged view preserves every unscaled work-mark coordinate of the
full multiclass input, independently of the selected coordinate's phase. -/
theorem multiclassStationaryPoissonWorkClassTaggedRequirementAt_view_eq_multiclassRequirement
    {Class : Type*} (i j : Class)
    (omega : Class → StationaryPoissonWorkPath) (k : Int) :
    multiclassStationaryPoissonWorkClassTaggedRequirementAt i
      (multiclassStationaryPoissonWorkClassTaggedView i omega) j k =
      Probability.PoissonProcess.multiclassStationaryPoissonWorkRequirement j omega k := by
  by_cases hji : j = i
  · subst j
    simp [multiclassStationaryPoissonWorkClassTaggedRequirementAt,
      multiclassStationaryPoissonWorkClassTaggedView,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkRequirement,
      Probability.Queueing.stationaryPoissonWorkRequirement]
  · simp [multiclassStationaryPoissonWorkClassTaggedRequirementAt,
      multiclassStationaryPoissonWorkClassTaggedView,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkRequirement,
      Probability.Queueing.stationaryPoissonWorkRequirement, hji]

/-- The distinguished class's zero-indexed arrival is at the Palm origin. -/
theorem multiclassStationaryPoissonWorkClassTaggedArrival_tag_zero
    {Class : Type*} (i : Class)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) :
    multiclassStationaryPoissonWorkClassTaggedArrival i z i 0 = 0 := by
  simp [multiclassStationaryPoissonWorkClassTaggedArrival,
    Probability.PoissonProcess.candidatePalmArrival_zero]

/-- On every passive class, the combined tagged carrier uses exactly that
class's shifted stationary marked-Poisson arrival path. -/
theorem multiclassStationaryPoissonWorkClassTaggedArrival_of_ne
    {Class : Type*} (i j : Class) (hji : j ≠ i)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) (k : Int) :
    multiclassStationaryPoissonWorkClassTaggedArrival i z j k =
      Probability.Queueing.stationaryPoissonWorkArrival (z.2 ⟨j, hji⟩) k := by
  simp [multiclassStationaryPoissonWorkClassTaggedArrival, hji]

/-- On every passive class, the combined tagged carrier uses exactly that
class's shifted stationary work-mark path. -/
theorem multiclassStationaryPoissonWorkClassTaggedRequirementAt_of_ne
    {Class : Type*} (i j : Class) (hji : j ≠ i)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) (k : Int) :
    multiclassStationaryPoissonWorkClassTaggedRequirementAt i z j k =
      (z.2 ⟨j, hji⟩).2 k := by
  simp [multiclassStationaryPoissonWorkClassTaggedRequirementAt, hji]

/-- Every fixed arrival coordinate of the combined selected-arrival carrier
is measurable.  The proof distinguishes the Palm path of the selected class
from the shifted stationary path of a passive class. -/
theorem measurable_multiclassStationaryPoissonWorkClassTaggedArrival
    {Class : Type*} [MeasurableSpace Class] (i j : Class) (k : Int) :
    Measurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
      multiclassStationaryPoissonWorkClassTaggedArrival i z j k) := by
  by_cases hji : j = i
  · subst j
    simpa [multiclassStationaryPoissonWorkClassTaggedArrival] using
      ((Probability.PoissonProcess.measurable_candidatePalmArrival k).comp
        (measurable_fst.comp measurable_fst :
          Measurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
            z.1.1)))
  · rw [show (fun z : MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
        multiclassStationaryPoissonWorkClassTaggedArrival i z j k) =
        (fun z => Probability.Queueing.stationaryPoissonWorkArrival
          (z.2 ⟨j, hji⟩) k) by
      funext z
      exact multiclassStationaryPoissonWorkClassTaggedArrival_of_ne i j hji z k]
    exact Probability.Queueing.measurable_timedEmbeddedArrival k |>.comp
      ((measurable_pi_apply
        (X := fun _ : {j : Class // j ≠ i} => StationaryPoissonWorkPath)
        ⟨j, hji⟩).comp measurable_snd)

/-- Every fixed work-mark coordinate of the combined selected-arrival carrier
is measurable. -/
theorem measurable_multiclassStationaryPoissonWorkClassTaggedRequirementAt
    {Class : Type*} [MeasurableSpace Class] (i j : Class) (k : Int) :
    Measurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
      multiclassStationaryPoissonWorkClassTaggedRequirementAt i z j k) := by
  by_cases hji : j = i
  · subst j
    simpa [multiclassStationaryPoissonWorkClassTaggedRequirementAt] using
      ((measurable_pi_apply k).comp
        (measurable_snd.comp measurable_fst) :
        Measurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
          z.1.2 k))
  · rw [show (fun z : MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
        multiclassStationaryPoissonWorkClassTaggedRequirementAt i z j k) =
        (fun z => (z.2 ⟨j, hji⟩).2 k) by
      funext z
      exact multiclassStationaryPoissonWorkClassTaggedRequirementAt_of_ne i j hji z k]
    exact (measurable_pi_apply k).comp
      (measurable_snd.comp ((measurable_pi_apply
        (X := fun _ : {j : Class // j ≠ i} => StationaryPoissonWorkPath)
        ⟨j, hji⟩).comp measurable_snd))

/-- The independently sampled stationary marked inputs of every class other
than `i`.  A finite subtype makes the omitted-class decomposition explicit. -/
noncomputable def multiclassStationaryPoissonWorkRestLaw
    (arrivalRate : Class → Real) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    Probability.Palm.ShiftInvariantProbabilityLaw
      ({j : Class // j ≠ i} → StationaryPoissonWorkPath) := by
  classical
  exact Probability.PoissonProcess.multiclassStationaryPoissonWorkShiftInvariantLaw
    (Class := {j : Class // j ≠ i})
    (fun j => arrivalRate j.1) (fun j => harrivalRate j.1)

/-- Splitting a multiclass input into one distinguished class and the
remaining classes commutes with their common physical-time flow. -/
theorem multiclassStationaryPoissonWorkClassAssemble_flow
    (arrivalRate : Class → Real) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class)
    (x : StationaryPoissonWorkPath ×
      ({j : Class // j ≠ i} → StationaryPoissonWorkPath))
    (t : Real) :
    Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow t
      (multiclassStationaryPoissonWorkClassAssemble i x) =
      multiclassStationaryPoissonWorkClassAssemble i
        ((Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw
            (harrivalRate i)).shift t x.1,
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).shift t x.2) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow,
      multiclassStationaryPoissonWorkClassAssemble,
      Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw,
      Probability.Queueing.timedEmbeddedSuspensionShiftInvariantLaw_of_intPathShift,
      Probability.Queueing.timedEmbeddedSuspensionFlow]
  · simp [Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow,
      multiclassStationaryPoissonWorkClassAssemble,
      multiclassStationaryPoissonWorkRestLaw,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkShiftInvariantLaw,
      hji]

/-- The finite-product decomposition into a distinguished stationary path and
the remaining stationary paths preserves the literal multiclass input law. -/
theorem measurePreserving_multiclassStationaryPoissonWorkClassSplit
    (arrivalRate : Class → Real) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    MeasurePreserving (multiclassStationaryPoissonWorkClassSplitEquiv i)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
      (((Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw
          (harrivalRate i)).Pbase).prod
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase) := by
  classical
  let μ : Class → Measure StationaryPoissonWorkPath := fun j =>
    Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j)
  letI : ∀ j, IsProbabilityMeasure (μ j) := fun j => by
    dsimp [μ]
    exact Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate j)
  letI : ∀ j, SigmaFinite (μ j) := fun _ => by infer_instance
  let p : Class → Prop := fun j => j = i
  letI : Unique {j : Class // p j} :=
    { default := ⟨i, rfl⟩
      uniq := fun j => Subtype.ext j.property }
  letI : Fintype {j : Class // p j} := Subtype.fintype p
  let e : (Class → StationaryPoissonWorkPath) ≃ᵐ
      ({j : Class // p j} → StationaryPoissonWorkPath) ×
        ({j : Class // ¬ p j} → StationaryPoissonWorkPath) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Class => StationaryPoissonWorkPath) p
  let q : ({j : Class // p j} → StationaryPoissonWorkPath) ≃ᵐ
      StationaryPoissonWorkPath :=
    MeasurableEquiv.piUnique (fun _ : {j : Class // p j} => StationaryPoissonWorkPath)
  let r := MeasurableEquiv.prodCongr q
    (MeasurableEquiv.refl ({j : Class // ¬ p j} → StationaryPoissonWorkPath))
  have he := MeasureTheory.measurePreserving_piEquivPiSubtypeProd μ p
  have hq := MeasureTheory.measurePreserving_piUnique
    (fun j : {j : Class // p j} => μ j.1)
  have hid := MeasurePreserving.id (Measure.pi fun j : {j : Class // ¬ p j} => μ j.1)
  have hr := MeasurePreserving.prod hq hid
  have hr' : MeasurePreserving r
      ((Measure.pi fun j : {j : Class // p j} => μ j.1).prod
        (Measure.pi fun j : {j : Class // ¬ p j} => μ j.1))
      ((μ i).prod (Measure.pi fun j : {j : Class // ¬ p j} => μ j.1)) := by
    simpa [r, q, p] using hr
  have her := he.trans hr'
  have htarget : MeasurePreserving (e.trans r)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
      (((Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw
          (harrivalRate i)).Pbase).prod
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase) := by
    simpa [μ, p, e, r, q,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure,
      Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw,
      Probability.Queueing.timedEmbeddedSuspensionShiftInvariantLaw_of_intPathShift,
      multiclassStationaryPoissonWorkRestLaw,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkShiftInvariantLaw] using her
  simpa [e, r, q, p, multiclassStationaryPoissonWorkClassSplitEquiv,
    multiclassStationaryPoissonWorkClassSplit] using htarget

/-- Reassembling the distinguished and passive stationary paths preserves
their product law and returns the literal multiclass stationary input law. -/
theorem measurePreserving_multiclassStationaryPoissonWorkClassAssemble
    (arrivalRate : Class → Real) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    MeasurePreserving (multiclassStationaryPoissonWorkClassAssemble i)
      (((Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw
          (harrivalRate i)).Pbase).prod
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  simpa only [multiclassStationaryPoissonWorkClassSplitEquiv_symm_apply] using
    MeasurePreserving.symm (multiclassStationaryPoissonWorkClassSplitEquiv i)
      (measurePreserving_multiclassStationaryPoissonWorkClassSplit
        arrivalRate harrivalRate i)

/-- Assemble a distinguished stationary class with the passive classes and
then replace an elapsed-time coordinate by the corresponding physical epoch.
The map preserves the product of the class-split input law with Lebesgue time.
-/
theorem measurePreserving_multiclassStationaryPoissonWorkClassAssemble_add_arrival
    (arrivalRate : Class → Real) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) (k : Int) :
    MeasurePreserving
      (fun p :
        (StationaryPoissonWorkPath ×
          ({j : Class // j ≠ i} → StationaryPoissonWorkPath)) × ℝ =>
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival i
            (multiclassStationaryPoissonWorkClassAssemble i p.1) k + p.2,
          multiclassStationaryPoissonWorkClassAssemble i p.1))
      ((((Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw
          (harrivalRate i)).Pbase).prod
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase).prod
          volume)
      (volume.prod
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) := by
  have harrival : Measurable (fun omega : Class → StationaryPoissonWorkPath =>
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival i omega k) := by
    exact (Probability.PoissonProcess.measurable_suspensionBaseArrival k).comp
      (measurable_fst.comp (measurable_pi_apply i))
  letI : IsProbabilityMeasure
      (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw
        (harrivalRate i)).Pbase :=
    (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw
      (harrivalRate i)).isProbability
  letI : IsProbabilityMeasure
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase :=
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).isProbability
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) :=
    Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  have hassemble := measurePreserving_multiclassStationaryPoissonWorkClassAssemble
    arrivalRate harrivalRate i
  have hproduct := hassemble.prod
    (MeasurePreserving.id (μ := (volume : Measure ℝ)))
  have hshift := Probability.Palm.measurePreserving_prod_add_measurable_swap
    (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
    (fun omega =>
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival i omega k)
    harrival
  simpa only [Function.comp_apply, Prod.map_apply] using hshift.comp hproduct

/-- The passive multiclass real-time flow is jointly measurable, so it can be
evaluated at the random physical epoch of a distinguished-class arrival. -/
theorem measurable_uncurry_multiclassStationaryPoissonWorkRestShift
    (arrivalRate : Class → Real) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    Measurable (Function.uncurry
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).shift) := by
  classical
  simpa only [multiclassStationaryPoissonWorkRestLaw] using
    (PoissonProcess.measurable_uncurry_multiclassStationaryPoissonWorkShift
      (Class := {j : Class // j ≠ i})
      (fun j => arrivalRate j.1) (fun j => harrivalRate j.1))

/-- The concrete Campbell/Palm certificate for arrivals of class `i` jointly
with all other classes.  At each selected class-`i` arrival, every other
class's complete stationary input path is translated to that same physical
time before the tagged sample is observed. -/
noncomputable def multiclassStationaryPoissonWorkClassCampbellCertificate
    (arrivalRate : Class → Real) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    Probability.Palm.CampbellPalmTaggedArrivalCertificate
      (Probability.Palm.targetPassiveProductBaseLaw
        (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)) := by
  exact Probability.Palm.targetPassiveCampbellCertificate
    (Probability.Queueing.stationaryPoissonWorkCampbellCertificate (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)
    (measurable_uncurry_multiclassStationaryPoissonWorkRestShift
      arrivalRate harrivalRate i)

/-- The selected-class coordinate of the multiclass Campbell certificate is
the literal stationary arrival epoch of its distinguished input path. -/
theorem multiclassStationaryPoissonWorkClassCampbellBaseArrival_eq
    (arrivalRate : Class → Real) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class)
    (x : StationaryPoissonWorkPath ×
      ({j : Class // j ≠ i} → StationaryPoissonWorkPath)) (k : Int) :
    (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i).baseArrivals
      x k = Probability.Queueing.timedEmbeddedArrival x.1 k := rfl

/-- Recentring any labelled selected-class base arrival produces a good
two-sided Palm gap path.  This is deterministic because the base carrier
already stores a good stationary suspension and recentering only reindexes
its gaps. -/
theorem multiclassStationaryPoissonWorkClassCampbellRecenter_gapPath_good
    (arrivalRate : Class → Real) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class)
    (x : StationaryPoissonWorkPath ×
      ({j : Class // j ≠ i} → StationaryPoissonWorkPath)) (k : Int) :
    Probability.PoissonProcess.suspensionGoodGapPath
      ((multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i).recenterAt x k).1.1 := by
  change Probability.PoissonProcess.suspensionGoodGapPath
    (Probability.Queueing.timedEmbeddedRecenterAt x.1 k).1
  exact Probability.Queueing.suspensionGoodGapPath_timedEmbeddedRecenterAt x.1 k

/-- Recentring the distinguished Campbell customer is the same literal input
as flowing the assembled multiclass path to that customer's arrival epoch and
then taking its zero-phase selected-class view. -/
theorem multiclassStationaryPoissonWorkClassCampbellRecenter_eq_taggedView_flow_at_baseArrival
    (arrivalRate : Class → Real) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class)
    (x : StationaryPoissonWorkPath ×
      ({j : Class // j ≠ i} → StationaryPoissonWorkPath)) (k : Int) :
    (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i).recenterAt
      x k =
      multiclassStationaryPoissonWorkClassTaggedView i
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k)
          (multiclassStationaryPoissonWorkClassAssemble i x)) := by
  let target := Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  let H := Probability.Queueing.stationaryPoissonWorkCampbellCertificate (harrivalRate i)
  rw [multiclassStationaryPoissonWorkClassAssemble_flow arrivalRate harrivalRate i x]
  change Probability.Palm.targetPassiveRecenter H passive x k =
    multiclassStationaryPoissonWorkClassTaggedView i
      (multiclassStationaryPoissonWorkClassAssemble i
        (target.shift (Probability.Queueing.timedEmbeddedArrival x.1 k) x.1,
          passive.shift (Probability.Queueing.timedEmbeddedArrival x.1 k) x.2))
  unfold Probability.Palm.targetPassiveRecenter
  simp only [multiclassStationaryPoissonWorkClassTaggedView,
    multiclassStationaryPoissonWorkClassAssemble_apply_eq]
  apply Prod.ext
  · simpa [target, H, Probability.Queueing.stationaryPoissonWorkCampbellCertificate,
      Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw] using
      (Probability.Queueing.timedEmbeddedSuspensionFlow_at_timedEmbeddedArrival_eq_recenter x.1 k).symm
  · have hbase : H.baseArrivals x.1 k = Probability.Queueing.timedEmbeddedArrival x.1 k := by
      change Probability.Queueing.timedEmbeddedArrival x.1 k =
        Probability.Queueing.timedEmbeddedArrival x.1 k
      rfl
    funext j
    change (passive.shift (H.baseArrivals x.1 k) x.2) j =
      (multiclassStationaryPoissonWorkClassAssemble i
        (target.shift (Probability.Queueing.timedEmbeddedArrival x.1 k) x.1,
          passive.shift (Probability.Queueing.timedEmbeddedArrival x.1 k) x.2) j.1)
    rw [multiclassStationaryPoissonWorkClassAssemble_apply_ne i j.1 j.2]
    rw [hbase]

/-- Flowing the assembled multiclass input to a selected class arrival puts
that selected stationary suspension at phase zero. -/
theorem multiclassStationaryPoissonWorkClassFlow_at_baseArrival_phase_zero
    (arrivalRate : Class → Real) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class)
    (x : StationaryPoissonWorkPath ×
      ({j : Class // j ≠ i} → StationaryPoissonWorkPath)) (k : Int) :
    ((Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
      (Probability.Queueing.timedEmbeddedArrival x.1 k)
      (multiclassStationaryPoissonWorkClassAssemble i x)) i).1.1.2 = 0 := by
  rw [multiclassStationaryPoissonWorkClassAssemble_flow arrivalRate harrivalRate i x]
  simp only [multiclassStationaryPoissonWorkClassAssemble_apply_eq]
  simpa [Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw,
    Probability.Queueing.timedEmbeddedSuspensionShiftInvariantLaw_of_intPathShift] using
    (Probability.Queueing.timedEmbeddedSuspensionFlow_at_timedEmbeddedArrival_phase_zero
      x.1 k)

/-- Under the common stationary flow, a selected-class arrival label is
restored by the literal suspension crossing index and its physical epoch is
translated by the common clock. -/
theorem multiclassStationaryPoissonWorkClassCampbellBaseArrival_flow_restore
    (arrivalRate : Class → Real) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class)
    (x : StationaryPoissonWorkPath ×
      ({j : Class // j ≠ i} → StationaryPoissonWorkPath))
    (t : Real) (j : Int) :
    (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i).baseArrivals
      ((Probability.Palm.targetPassiveProductBaseLaw
        (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).shift t x) j =
      (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i).baseArrivals
        x (Probability.PoissonProcess.suspensionCrossingIndexPastClosed t x.1.1.1 + j) - t := by
  let target := Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i)
  let H := Probability.Queueing.stationaryPoissonWorkCampbellCertificate (harrivalRate i)
  let c : Int := Probability.PoissonProcess.suspensionCrossingIndexPastClosed t x.1.1.1
  change H.baseArrivals (target.shift t x.1) j = H.baseArrivals x.1 (c + j) - t
  simpa [target, H, c, Probability.Queueing.stationaryPoissonWorkCampbellCertificate,
    Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw] using
    (Probability.Queueing.timedEmbeddedArrival_flow x.1 t j)

/-- The concrete multiclass Palm recentering map commutes with physical-time
translation after restoring the selected class's shifted arrival label.  The
passive paths are translated first by the common clock and then by the
selected arrival epoch, so the two translations combine to the original
physical selected-arrival time. -/
theorem multiclassStationaryPoissonWorkClassCampbellRecenter_flow_restore
    (arrivalRate : Class → Real) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class)
    (x : StationaryPoissonWorkPath ×
      ({j : Class // j ≠ i} → StationaryPoissonWorkPath))
    (t : Real) (j : Int) :
    (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i).recenterAt
      ((Probability.Palm.targetPassiveProductBaseLaw
        (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).shift t x) j =
      (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i).recenterAt
        x (Probability.PoissonProcess.suspensionCrossingIndexPastClosed t x.1.1.1 + j) := by
  let target := Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  let H := Probability.Queueing.stationaryPoissonWorkCampbellCertificate (harrivalRate i)
  let c : Int := Probability.PoissonProcess.suspensionCrossingIndexPastClosed t x.1.1.1
  change Probability.Palm.targetPassiveRecenter H passive
      (target.shift t x.1, passive.shift t x.2) j =
    Probability.Palm.targetPassiveRecenter H passive x (c + j)
  unfold Probability.Palm.targetPassiveRecenter
  apply Prod.ext
  · simpa [target, H, c] using
      Probability.Queueing.timedEmbeddedRecenterAt_flow_restore x.1 t j
  · have harrival : H.baseArrivals (target.shift t x.1) j =
      H.baseArrivals x.1 (c + j) - t := by
        simpa [target, H, c, Probability.Queueing.stationaryPoissonWorkCampbellCertificate,
          Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw] using
          (Probability.Queueing.timedEmbeddedArrival_flow x.1 t j)
    change passive.shift (H.baseArrivals (target.shift t x.1) j)
        (passive.shift t x.2) =
      passive.shift (H.baseArrivals x.1 (c + j)) x.2
    rw [harrival]
    rw [show passive.shift (H.baseArrivals x.1 (c + j) - t)
          (passive.shift t x.2) =
        passive.shift ((H.baseArrivals x.1 (c + j) - t) + t) x.2 by
          simpa [Function.comp_apply] using
            (congrFun (passive.shift_add
              (H.baseArrivals x.1 (c + j) - t) t) x.2).symm]
    have htime : (H.baseArrivals x.1 (c + j) - t) + t =
        H.baseArrivals x.1 (c + j) := by ring
    rw [htime]

/-- Every weighted arrival summand is covariant under the common physical
flow: its time event is translated and its label is restored exactly. -/
theorem arrivalTimeCampbellSetWeightedSummand_multiclassStationaryPoissonWorkClass_flow_restore
    (arrivalRate : Class → Real) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class)
    (f : MulticlassStationaryPoissonWorkClassTaggedSample Class i → ℝ≥0∞)
    (s : Set ℝ)
    (x : StationaryPoissonWorkPath ×
      ({j : Class // j ≠ i} → StationaryPoissonWorkPath))
    (t : Real) (j : Int) :
    Probability.Palm.arrivalTimeCampbellSetWeightedSummand
      (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i)
      f s j
      ((Probability.Palm.targetPassiveProductBaseLaw
        (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).shift t x) =
      Probability.Palm.arrivalTimeCampbellSetWeightedSummand
        (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i)
        f (Probability.Palm.arrivalTimeTranslateSet t s)
        (Probability.PoissonProcess.suspensionCrossingIndexPastClosed t x.1.1.1 + j) x := by
  classical
  let H := multiclassStationaryPoissonWorkClassCampbellCertificate
    arrivalRate harrivalRate i
  let base := Probability.Palm.targetPassiveProductBaseLaw
    (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)
  let c : Int := Probability.PoissonProcess.suspensionCrossingIndexPastClosed t x.1.1.1
  change (if H.baseArrivals (base.shift t x) j ∈ s then
      f (H.recenterAt (base.shift t x) j) else 0) =
    if H.baseArrivals x (c + j) ∈ Probability.Palm.arrivalTimeTranslateSet t s then
      f (H.recenterAt x (c + j)) else 0
  rw [multiclassStationaryPoissonWorkClassCampbellBaseArrival_flow_restore
    arrivalRate harrivalRate i x t j,
    multiclassStationaryPoissonWorkClassCampbellRecenter_flow_restore
      arrivalRate harrivalRate i x t j]
  rfl

/-- The full weighted arrival-time intensity is invariant under physical-time
translation.  This is proved from the concrete common-flow preservation and
label restoration, rather than postulated as a reward-rate certificate. -/
theorem arrivalTimeCampbellIntensity_multiclassStationaryPoissonWorkClass_translate
    (arrivalRate : Class → Real) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class)
    (f : MulticlassStationaryPoissonWorkClassTaggedSample Class i → ℝ≥0∞)
    (hf : Measurable f)
    (s : Set ℝ) (hs : MeasurableSet s) (t : Real) :
    Probability.Palm.arrivalTimeCampbellIntensity
      (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i)
      f s =
      Probability.Palm.arrivalTimeCampbellIntensity
        (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i)
        f (Probability.Palm.arrivalTimeTranslateSet t s) := by
  classical
  let base := Probability.Palm.targetPassiveProductBaseLaw
    (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)
  let H := multiclassStationaryPoissonWorkClassCampbellCertificate
    arrivalRate harrivalRate i
  let G : Set ℝ →
      (StationaryPoissonWorkPath × ({j : Class // j ≠ i} → StationaryPoissonWorkPath)) →
        ℝ≥0∞ := fun u x => ∑' j : ℤ,
          Probability.Palm.arrivalTimeCampbellSetWeightedSummand H f u j x
  have hGmeas : ∀ (u : Set ℝ), MeasurableSet u → AEMeasurable (G u) base.Pbase := by
    intro u hu
    apply AEMeasurable.ennreal_tsum
    intro j
    exact (Probability.Palm.measurable_arrivalTimeCampbellSetWeightedSummand
      H f hf u hu j).aemeasurable
  have hpoint : ∀ x,
      G s (base.shift t x) = G (Probability.Palm.arrivalTimeTranslateSet t s) x := by
    intro x
    let c : Int := Probability.PoissonProcess.suspensionCrossingIndexPastClosed t x.1.1.1
    calc
      G s (base.shift t x) = ∑' j : ℤ,
          Probability.Palm.arrivalTimeCampbellSetWeightedSummand H f
            (Probability.Palm.arrivalTimeTranslateSet t s) (c + j) x := by
            apply tsum_congr
            intro j
            exact arrivalTimeCampbellSetWeightedSummand_multiclassStationaryPoissonWorkClass_flow_restore
              arrivalRate harrivalRate i f s x t j
      _ = G (Probability.Palm.arrivalTimeTranslateSet t s) x := by
        exact (Equiv.addLeft c).tsum_eq
          (fun j : ℤ => Probability.Palm.arrivalTimeCampbellSetWeightedSummand H f
            (Probability.Palm.arrivalTimeTranslateSet t s) j x)
  have hflow : ∫⁻ x, G s (base.shift t x) ∂base.Pbase =
      ∫⁻ x, G s x ∂base.Pbase := by
    let hshift := base.shift_preserving t
    calc
      (∫⁻ x, G s (base.shift t x) ∂base.Pbase) =
          ∫⁻ x, G s x ∂Measure.map (base.shift t) base.Pbase := by
            simpa only [Function.comp_apply] using
              (MeasureTheory.lintegral_comp'
                (show AEMeasurable (G s) (Measure.map (base.shift t) base.Pbase) by
                  rw [hshift.map_eq]
                  exact hGmeas s hs)
                hshift.measurable.aemeasurable)
      _ = ∫⁻ x, G s x ∂base.Pbase := by rw [hshift.map_eq]
  have htranslateMeas : MeasurableSet (Probability.Palm.arrivalTimeTranslateSet t s) :=
    Probability.Palm.measurableSet_arrivalTimeTranslateSet t hs
  calc
    Probability.Palm.arrivalTimeCampbellIntensity H f s = ∫⁻ x, G s x ∂base.Pbase :=
      Probability.Palm.arrivalTimeCampbellIntensity_apply_eq_lintegral_tsum H f hf s hs
    _ = ∫⁻ x, G s (base.shift t x) ∂base.Pbase := hflow.symm
    _ = ∫⁻ x, G (Probability.Palm.arrivalTimeTranslateSet t s) x ∂base.Pbase := by
      apply MeasureTheory.lintegral_congr
      exact hpoint
    _ = Probability.Palm.arrivalTimeCampbellIntensity H f
        (Probability.Palm.arrivalTimeTranslateSet t s) :=
      (Probability.Palm.arrivalTimeCampbellIntensity_apply_eq_lintegral_tsum
        H f hf _ htranslateMeas).symm

/-- The literal sum of a nonnegative statistic over any translated unit
arrival slab has the same Campbell intensity as the unit slab at the origin.
The proof uses concrete label restoration and the measure-preserving common
physical-time flow; it introduces no reward-rate premise. -/
theorem lintegral_sum_multiclassStationaryPoissonWorkClassCampbell_translatedUnit
    (arrivalRate : Class → Real) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (t : Real)
    (f : MulticlassStationaryPoissonWorkClassTaggedSample Class i → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ x, (∑ j ∈
      (multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i).arrivalsIn t (t + 1) x,
      f ((multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i).recenterAt x j)) ∂
        (Probability.Palm.targetPassiveProductBaseLaw
          (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase =
      ENNReal.ofReal (arrivalRate i) *
        (∫⁻ z, f z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) := by
  let base := Probability.Palm.targetPassiveProductBaseLaw
    (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)
  let H := multiclassStationaryPoissonWorkClassCampbellCertificate
    arrivalRate harrivalRate i
  have hsum : ∀ x,
      (∑ j ∈ H.arrivalsIn t (t + 1) x, f (H.recenterAt x j)) =
        ∑ j ∈ H.arrivalsIn 0 1 (base.shift t x),
          f (H.recenterAt (base.shift t x) j) := by
    intro x
    change
      (∑ j ∈ Probability.Queueing.timedEmbeddedArrivalIndices t (t + 1) x.1,
        f (H.recenterAt x j)) =
        ∑ j ∈ Probability.Queueing.timedEmbeddedArrivalIndices 0 1
          (Probability.Queueing.timedEmbeddedSuspensionFlow t x.1),
          f (H.recenterAt (base.shift t x) j)
    rw [← Probability.Queueing.timedEmbeddedArrivalIndices_flow_restore x.1 t t (t + 1),
      Finset.sum_map]
    simp only [sub_self, add_sub_cancel_left,
      Probability.Queueing.timedEmbeddedFlowRestoreEmbedding]
    apply Finset.sum_congr rfl
    intro j hj
    change f (H.recenterAt x
      (Probability.PoissonProcess.suspensionCrossingIndexPastClosed t x.1.1.1 + j)) =
        f (H.recenterAt (base.shift t x) j)
    rw [multiclassStationaryPoissonWorkClassCampbellRecenter_flow_restore
      arrivalRate harrivalRate i x t j]
  have htsum : AEMeasurable (fun x => ∑' j : ℤ,
      Probability.Palm.unitWindowCampbellWeightedSummand H f j x) base.Pbase := by
    apply AEMeasurable.ennreal_tsum
    intro j
    exact (Probability.Palm.measurable_unitWindowCampbellWeightedSummand H f hf j).aemeasurable
  have hunit : AEMeasurable (fun x =>
      ∑ j ∈ H.arrivalsIn 0 1 x, f (H.recenterAt x j)) base.Pbase := by
    exact htsum.congr
      ((Probability.Palm.ae_sum_unitWindow_arrivalsIn_recenter_eq_tsum H f).mono
        fun _ h => h.symm)
  change ∫⁻ x, (∑ j ∈ H.arrivalsIn t (t + 1) x, f (H.recenterAt x j)) ∂base.Pbase =
    ENNReal.ofReal H.arrivalRate * (∫⁻ z, f z ∂
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag)
  calc
    (∫⁻ x, (∑ j ∈ H.arrivalsIn t (t + 1) x, f (H.recenterAt x j)) ∂base.Pbase) =
        ∫⁻ x, (∑ j ∈ H.arrivalsIn 0 1 (base.shift t x),
          f (H.recenterAt (base.shift t x) j)) ∂base.Pbase := by
          apply MeasureTheory.lintegral_congr
          intro x
          exact hsum x
    _ = ∫⁻ x, (∑ j ∈ H.arrivalsIn 0 1 x, f (H.recenterAt x j)) ∂base.Pbase := by
          let hshift := base.shift_preserving t
          calc
            (∫⁻ x, (∑ j ∈ H.arrivalsIn 0 1 (base.shift t x),
                f (H.recenterAt (base.shift t x) j)) ∂base.Pbase) =
                ∫⁻ x, (∑ j ∈ H.arrivalsIn 0 1 x, f (H.recenterAt x j)) ∂
                  Measure.map (base.shift t) base.Pbase := by
                    simpa only [Function.comp_apply] using
                      (MeasureTheory.lintegral_comp'
                        (show AEMeasurable (fun x =>
                          ∑ j ∈ H.arrivalsIn 0 1 x, f (H.recenterAt x j))
                          (Measure.map (base.shift t) base.Pbase) by
                            rw [hshift.map_eq]
                            exact hunit)
                        hshift.measurable.aemeasurable)
            _ = ∫⁻ x, (∑ j ∈ H.arrivalsIn 0 1 x, f (H.recenterAt x j)) ∂base.Pbase := by
                  rw [hshift.map_eq]
    _ = ENNReal.ofReal H.arrivalRate * (∫⁻ z, f z ∂
        (Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) :=
      Probability.Palm.lintegral_sum_unitWindow_arrivalsIn_recenter H f hf

/-- The literal weighted arrival process of a selected class has the
Campbell mass on every translated unit interval.  This is the time-measure
form of the concrete finite-slab identity. -/
theorem arrivalTimeCampbellIntensity_multiclassStationaryPoissonWorkClass_Ico
    (arrivalRate : Class → Real) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (t : Real)
    (f : MulticlassStationaryPoissonWorkClassTaggedSample Class i → ℝ≥0∞)
    (hf : Measurable f) :
    Probability.Palm.arrivalTimeCampbellIntensity
      (multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i) f (Set.Ico t (t + 1)) =
      ENNReal.ofReal (arrivalRate i) *
        (∫⁻ z, f z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) := by
  let H := multiclassStationaryPoissonWorkClassCampbellCertificate
    arrivalRate harrivalRate i
  calc
    Probability.Palm.arrivalTimeCampbellIntensity H f (Set.Ico t (t + 1)) =
        ∫⁻ x, (∑ j ∈ H.arrivalsIn t (t + 1) x, f (H.recenterAt x j)) ∂
          (Probability.Palm.targetPassiveProductBaseLaw
            (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase := by
          exact Probability.Palm.arrivalTimeCampbellIntensity_apply_Ico H f hf t (t + 1)
    _ = ENNReal.ofReal (arrivalRate i) *
        (∫⁻ z, f z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) := by
      exact lintegral_sum_multiclassStationaryPoissonWorkClassCampbell_translatedUnit
        arrivalRate harrivalRate i t f hf

/-- A finite selected reward has a full physical-time Campbell measure: its
literal weighted arrival intensity is its Palm reward mean times Lebesgue
measure.  The proof first establishes concrete translation invariance by
label restoration, then invokes Haar uniqueness with locally finite unit
intervals. -/
theorem arrivalTimeCampbellIntensity_multiclassStationaryPoissonWorkClass_eq_rate_smul_volume
    (arrivalRate : Class → Real) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class)
    (f : MulticlassStationaryPoissonWorkClassTaggedSample Class i → ℝ≥0∞)
    (hf : Measurable f)
    (hfinite : (∫⁻ z, f z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) ≠ ∞) :
    Probability.Palm.arrivalTimeCampbellIntensity
      (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i) f =
      (ENNReal.ofReal (arrivalRate i) *
        (∫⁻ z, f z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag)) •
        (MeasureTheory.volume : Measure ℝ) := by
  classical
  let H := multiclassStationaryPoissonWorkClassCampbellCertificate
    arrivalRate harrivalRate i
  let ν : Measure ℝ := Probability.Palm.arrivalTimeCampbellIntensity H f
  let q : ℝ≥0∞ := ENNReal.ofReal (arrivalRate i) *
    (∫⁻ z, f z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag)
  have hunit : ∀ t : ℝ, ν (Set.Ico t (t + 1)) = q := by
    intro t
    simpa [ν, H, q] using
      (arrivalTimeCampbellIntensity_multiclassStationaryPoissonWorkClass_Ico
        arrivalRate harrivalRate i t f hf)
  have hqfinite : q ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite
  letI : SigmaFinite ν := by
    refine Measure.sigmaFinite_of_countable
      (S := Set.range fun k : ℤ => Set.Ico (k : ℝ) ((k : ℝ) + 1))
      (Set.countable_range _) ?_ ?_
    · intro u hu
      rcases hu with ⟨k, rfl⟩
      simpa [hunit (k : ℝ)] using hqfinite.lt_top
    · rw [Set.sUnion_range]
      exact iUnion_Ico_intCast ℝ
  letI : Measure.IsAddLeftInvariant ν :=
    ⟨fun a => by
      ext s hs
      rw [Measure.map_apply (f := fun x : ℝ => a + x)
        (by fun_prop) hs]
      have hpre : (fun x : ℝ => a + x) ⁻¹' s =
          Probability.Palm.arrivalTimeTranslateSet (-a) s := by
        ext x
        simp [Probability.Palm.arrivalTimeTranslateSet, add_comm]
      rw [hpre]
      exact (arrivalTimeCampbellIntensity_multiclassStationaryPoissonWorkClass_translate
        arrivalRate harrivalRate i f hf s hs (-a)).symm⟩
  let K : Set ℝ := Set.Icc 0 (1 / 2 : ℝ)
  have hKcompact : IsCompact K := by
    exact isCompact_Icc
  have hKinterior : (interior K).Nonempty := by
    rw [show K = Set.Icc 0 (1 / 2 : ℝ) by rfl, interior_Icc]
    exact ⟨(1 / 4 : ℝ), by constructor <;> norm_num⟩
  have hKsubset : K ⊆ Set.Ico 0 1 := by
    intro x hx
    dsimp [K] at hx
    constructor
    · exact hx.1
    · linarith [hx.2]
  have hKfinite : ν K ≠ ∞ := by
    have hunit0 : ν (Set.Ico 0 1) < ∞ := by
      simpa using (hunit 0).trans_lt hqfinite.lt_top
    exact (lt_of_le_of_lt (measure_mono hKsubset)
      hunit0).ne
  letI : Measure.Regular ν :=
    Measure.regular_of_isAddLeftInvariant hKcompact hKinterior hKfinite
  have hhaar : ν = Measure.addHaarScalarFactor ν (MeasureTheory.volume : Measure ℝ) •
      (MeasureTheory.volume : Measure ℝ) :=
    Measure.isAddLeftInvariant_eq_smul_of_regular ν (MeasureTheory.volume : Measure ℝ)
  have hscalar : Measure.addHaarScalarFactor ν (MeasureTheory.volume : Measure ℝ) = q := by
    have hunit0 : ν (Set.Ico 0 1) = q := by
      simpa using hunit 0
    have happly := congrArg (fun μ : Measure ℝ => μ (Set.Ico 0 1)) hhaar
    change ν (Set.Ico 0 1) =
      (Measure.addHaarScalarFactor ν (MeasureTheory.volume : Measure ℝ) •
        (MeasureTheory.volume : Measure ℝ)) (Set.Ico 0 1) at happly
    rw [hunit0, Measure.smul_apply, Real.volume_Ico] at happly
    simpa [ENNReal.smul_def, smul_eq_mul] using happly.symm
  calc
    Probability.Palm.arrivalTimeCampbellIntensity H f = ν := rfl
    _ = Measure.addHaarScalarFactor ν (MeasureTheory.volume : Measure ℝ) •
        (MeasureTheory.volume : Measure ℝ) := hhaar
    _ = q • (MeasureTheory.volume : Measure ℝ) := by
      change (↑(Measure.addHaarScalarFactor ν (MeasureTheory.volume : Measure ℝ)) : ℝ≥0∞) •
          (MeasureTheory.volume : Measure ℝ) = q • (MeasureTheory.volume : Measure ℝ)
      rw [hscalar]

/-- The work requirement of the class-`i` customer pinned at time zero in the
multiclass Palm representation. -/
def multiclassStationaryPoissonWorkClassTaggedRequirement
    (i : Class) :
    ((ℤ → ℝ) × (ℤ → ℝ)) ×
      ({j : Class // j ≠ i} → StationaryPoissonWorkPath) → ℝ :=
  fun z => z.1.2 0

/-- The pinned class-`i` customer's work has the unit-exponential law.  The
proof projects the genuine joint Palm law to its distinguished tagged
coordinate; passive-class stationarity is retained in the carrier rather than
discarded in the Campbell construction. -/
theorem multiclassStationaryPoissonWorkClassTaggedRequirement_hasLaw
    (arrivalRate : Class → Real) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    HasLaw (multiclassStationaryPoissonWorkClassTaggedRequirement i)
      (expMeasure 1)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  have htag : HasLaw (fun z : (ℤ → ℝ) × (ℤ → ℝ) => z.2 0)
      (expMeasure 1) tagged.Ptag := by
    let pathMeasure : Measure (ℤ → ℝ) :=
      Probability.PoissonProcess.twoSidedInterarrivalMeasure 1
    letI : IsProbabilityMeasure pathMeasure :=
      Probability.PoissonProcess.isProbabilityMeasure_twoSidedInterarrivalMeasure
        (by norm_num)
    have hpath := Probability.Queueing.timedEmbeddedTaggedArrivalAtZero_pathStatistic_hasLaw
      pathMeasure (fun path : ℤ → ℝ => path 0) (measurable_pi_apply 0)
      (arrivalRate i) (harrivalRate i)
    have hzero := Probability.PoissonProcess.twoSidedGap_hasLaw
      (by norm_num : (0 : ℝ) < 1) 0
    refine ⟨((measurable_pi_apply 0).comp measurable_snd).aemeasurable, ?_⟩
    change Measure.map (fun z : (ℤ → ℝ) × (ℤ → ℝ) => z.2 0)
        (Probability.Queueing.timedEmbeddedTaggedArrivalAtZero
          (arrivalRate i) (harrivalRate i) pathMeasure).Ptag = expMeasure 1
    calc
      Measure.map (fun z : (ℤ → ℝ) × (ℤ → ℝ) => z.2 0)
          (Probability.Queueing.timedEmbeddedTaggedArrivalAtZero
            (arrivalRate i) (harrivalRate i) pathMeasure).Ptag =
          pathMeasure.map (fun path : ℤ → ℝ => path 0) := hpath.map_eq
      _ = expMeasure 1 := by
        simpa [pathMeasure, Probability.PoissonProcess.twoSidedGap] using hzero.map_eq
  exact htag.comp
    (measurePreserving_fst : MeasurePreserving Prod.fst
      (tagged.Ptag.prod passive.Pbase) tagged.Ptag).hasLaw

/-- The selected class's Palm-recentered gap path retains the literal
two-sided iid exponential-gap law after adjoining all independently shifted
passive-class inputs. -/
theorem multiclassStationaryPoissonWorkClassTaggedGapPath_hasLaw
    (arrivalRate : Class → Real) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    HasLaw (fun z : MulticlassStationaryPoissonWorkClassTaggedSample Class i => z.1.1)
      (Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)) :=
    Probability.PoissonProcess.isProbabilityMeasure_twoSidedInterarrivalMeasure
      (harrivalRate i)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_twoSidedInterarrivalMeasure
      (by norm_num)
  have htag : HasLaw (fun z : (ℤ → ℝ) × (ℤ → ℝ) => z.1)
      (Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i))
      tagged.Ptag := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    change Measure.map Prod.fst
        ((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
          (Probability.PoissonProcess.twoSidedInterarrivalMeasure 1)) =
        Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  exact htag.comp
    (measurePreserving_fst : MeasurePreserving Prod.fst
      (tagged.Ptag.prod passive.Pbase) tagged.Ptag).hasLaw

/-- The selected class's Palm-recentered gap path is almost surely in the
full finite-ledger carrier.  This transports the Poisson path property through
the genuine multiclass Campbell/Palm tagged law rather than assuming it in a
priority-queue response theorem. -/
theorem ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
    (arrivalRate : Class → Real) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      Probability.PoissonProcess.suspensionGoodGapPath z.1.1 := by
  have hlaw := multiclassStationaryPoissonWorkClassTaggedGapPath_hasLaw
    arrivalRate harrivalRate i
  refine ae_of_ae_map
    (μ := (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag)
    (f := fun z : MulticlassStationaryPoissonWorkClassTaggedSample Class i => z.1.1)
    (p := Probability.PoissonProcess.suspensionGoodGapPath)
    (measurable_fst.comp measurable_fst).aemeasurable ?_
  rw [hlaw.map_eq]
  exact Probability.PoissonProcess.ae_suspensionGoodGapPath (harrivalRate i)

/-- Every labelled unit-work mark is strictly positive almost surely on the
complete selected-arrival carrier.  The selected class uses the independent
Palm mark path and each passive class retains its own stationary mark path. -/
theorem ae_all_multiclassStationaryPoissonWorkClassTaggedRequirement_positive
    (arrivalRate : Class → Real) (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ j : Class, ∀ k : ℤ,
        0 < multiclassStationaryPoissonWorkClassTaggedRequirementAt i z j k := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)) :=
    Probability.PoissonProcess.isProbabilityMeasure_twoSidedInterarrivalMeasure
      (harrivalRate i)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_twoSidedInterarrivalMeasure
      (by norm_num)
  have hselectedWorkPath : HasLaw (fun y : (ℤ → ℝ) × (ℤ → ℝ) => y.2)
      (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ)) tagged.Ptag := by
    simpa [tagged, Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero] using
      (Probability.Queueing.timedEmbeddedTaggedArrivalAtZero_pathStatistic_hasLaw
        (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ))
        id measurable_id (arrivalRate i) (harrivalRate i))
  have hselectedBase : ∀ᵐ y ∂tagged.Ptag, ∀ k : ℤ, 0 < y.2 k := by
    refine ae_of_ae_map (μ := tagged.Ptag) (f := Prod.snd)
      (p := fun work : ℤ → ℝ => ∀ k : ℤ, 0 < work k)
      measurable_snd.aemeasurable ?_
    rw [hselectedWorkPath.map_eq]
    simpa [Probability.PoissonProcess.twoSidedGap] using
      (Probability.PoissonProcess.ae_all_twoSidedGap_positive
        (by norm_num : (0 : ℝ) < 1))
  have hselected : ∀ᵐ z ∂(tagged.Ptag.prod passive.Pbase), ∀ k : ℤ, 0 < z.1.2 k := by
    refine ae_of_ae_map (μ := tagged.Ptag.prod passive.Pbase) (f := Prod.fst)
      (p := fun y : (ℤ → ℝ) × (ℤ → ℝ) => ∀ k : ℤ, 0 < y.2 k)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact hselectedBase
  have hpassiveBase : ∀ᵐ w ∂passive.Pbase,
      ∀ j : {j : Class // j ≠ i}, ∀ k : ℤ, 0 < (w j).2 k := by
    simpa [passive, multiclassStationaryPoissonWorkRestLaw,
      Probability.Queueing.stationaryPoissonWorkRequirement,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkRequirement] using
      (Probability.PoissonProcess.ae_all_multiclassStationaryPoissonWorkRequirement_positive
        (Class := {j : Class // j ≠ i})
        (fun j => arrivalRate j.1) (fun j => harrivalRate j.1))
  have hpassive : ∀ᵐ z ∂(tagged.Ptag.prod passive.Pbase),
      ∀ j : {j : Class // j ≠ i}, ∀ k : ℤ, 0 < (z.2 j).2 k := by
    refine ae_of_ae_map (μ := tagged.Ptag.prod passive.Pbase) (f := Prod.snd)
      (p := fun w : {j : Class // j ≠ i} → StationaryPoissonWorkPath =>
        ∀ j : {j : Class // j ≠ i}, ∀ k : ℤ, 0 < (w j).2 k)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hpassiveBase
  change ∀ᵐ z ∂(tagged.Ptag.prod passive.Pbase),
    ∀ j : Class, ∀ k : ℤ,
      0 < multiclassStationaryPoissonWorkClassTaggedRequirementAt i z j k
  filter_upwards [hselected, hpassive] with z hselected hpassive
  intro j k
  by_cases hji : j = i
  · subst j
    simpa [multiclassStationaryPoissonWorkClassTaggedRequirementAt] using hselected k
  · rw [multiclassStationaryPoissonWorkClassTaggedRequirementAt_of_ne i j hji z k]
    exact hpassive ⟨j, hji⟩ k

end

end AppliedModelingLib.Queueing
