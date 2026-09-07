import AppliedModelingLib.Foundations.Probability.MulticlassQueueingPrimitives
import LG24ServiceLevelAgreements.SLA2026Model
import Mathlib.Tactic

/-!
# Primitive stochastic input for the active SLA model

The active source specifies the queue separately for each Borough: independent
raw Poisson category streams of rates `lambda`, independent admission with
probability `s / lambda`, and iid unit-mean exponential job work.  This module
maps those stated inputs to concrete product probability spaces.

It intentionally stops before the missing queueing layer.  In particular, the
raw marked construction and the directly constructed admitted-Poisson carrier
are both real constructions, but their pathwise thinning coupling, GPS/FCFS
execution, stationary construction, and Palm transport remain separate proof
obligations.  No response-tail proposition appears here.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open MeasureTheory
open scoped NNReal

noncomputable section

/-- The stochastic data of one fixed Borough in the active source.  Positivity
and `s <= lambda` are source-domain conditions, retained explicitly so the
admission probability is derived rather than supplied as an opaque parameter. -/
structure SLA2026BoroughQueueingInput (Category : Type*) [Fintype Category] where
  arrivalRate : Category → Real
  admittedRate : Category → Real
  arrivalRate_pos : ∀ k, 0 < arrivalRate k
  admittedRate_pos : ∀ k, 0 < admittedRate k
  admittedRate_le_arrivalRate : ∀ k, admittedRate k ≤ arrivalRate k

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category]

/-- The source’s independent admission probability `s / lambda`, represented
as a nonnegative real only after its sign has been proved from source data. -/
def admissionProbability (M : SLA2026BoroughQueueingInput Category) :
    Category → ℝ≥0 :=
  fun k => ⟨M.admittedRate k / M.arrivalRate k,
    div_nonneg (M.admittedRate_pos k).le (M.arrivalRate_pos k).le⟩

/-- Source positivity of both total and admitted rates makes every admission
probability strictly positive.  This retains the manuscript's
`pi in (0, 1]` convention rather than only retaining the upper bound needed
to form a Bernoulli law. -/
theorem admissionProbability_pos
    (M : SLA2026BoroughQueueingInput Category) (k : Category) :
    0 < M.admissionProbability k := by
  rw [← NNReal.coe_pos]
  exact div_pos (M.admittedRate_pos k) (M.arrivalRate_pos k)

/-- The derived admission probability is at most one. -/
theorem admissionProbability_le_one
    (M : SLA2026BoroughQueueingInput Category) (k : Category) :
    M.admissionProbability k ≤ 1 := by
  exact_mod_cast (div_le_one (M.arrivalRate_pos k)).mpr
    (M.admittedRate_le_arrivalRate k)

/-- The coercion of the derived probability is exactly the source fraction. -/
theorem admissionProbability_coe
    (M : SLA2026BoroughQueueingInput Category) (k : Category) :
    (M.admissionProbability k : Real) = M.admittedRate k / M.arrivalRate k :=
  rfl

/-- Literal raw-arrival/admission/work primitive carrier for one Borough. -/
def rawMarkedPrimitiveMeasure (M : SLA2026BoroughQueueingInput Category) :
    Measure (Category → ForwardQueueingPrimitivePath) :=
  multiclassForwardQueueingPrimitiveMeasure M.arrivalRate M.admissionProbability
    M.admissionProbability_le_one

/-- The raw marked primitive carrier is a probability space. -/
theorem isProbabilityMeasure_rawMarkedPrimitiveMeasure
    (M : SLA2026BoroughQueueingInput Category) :
    IsProbabilityMeasure M.rawMarkedPrimitiveMeasure := by
  exact isProbabilityMeasure_multiclassForwardQueueingPrimitiveMeasure
    M.arrivalRate M.arrivalRate_pos M.admissionProbability
    M.admissionProbability_le_one

/-- The source’s separately stated post-thinning admitted-stream carrier.
This is the carrier used by the future scheduler: it gives each category its
independent admitted Poisson stream at rate `s`. -/
def admittedArrivalMeasure (M : SLA2026BoroughQueueingInput Category) :
    Measure (Category → ℕ → Real) :=
  multiclassForwardArrivalMeasure M.admittedRate

/-- The direct admitted-stream carrier is a probability space. -/
theorem isProbabilityMeasure_admittedArrivalMeasure
    (M : SLA2026BoroughQueueingInput Category) :
    IsProbabilityMeasure M.admittedArrivalMeasure := by
  exact isProbabilityMeasure_multiclassForwardArrivalMeasure M.admittedRate
    M.admittedRate_pos

/-- A concrete admitted Poisson counting process for one category. -/
def admittedPoissonCountingProcess
    (M : SLA2026BoroughQueueingInput Category) (k : Category) :
    ForwardHomogeneousPoissonCountingProcessByLaw (Category → ℕ → Real)
      M.admittedArrivalMeasure :=
  multiclassForwardPoissonCountingProcess M.admittedRate M.admittedRate_pos k

/-- Complete admitted arrival paths are independent across categories. -/
theorem iIndepFun_admittedArrivalPaths
    (M : SLA2026BoroughQueueingInput Category) :
    ProbabilityTheory.iIndepFun (fun k (ω : Category → ℕ → Real) => ω k)
      M.admittedArrivalMeasure :=
  iIndepFun_multiclassForwardArrivalPaths M.admittedRate M.admittedRate_pos

/-- The admitted input has a simultaneous finite arrival ledger for all
categories and all finite horizons. -/
theorem ae_mem_admittedArrivalIndices_iff
    (M : SLA2026BoroughQueueingInput Category) :
    ∀ᵐ ω ∂M.admittedArrivalMeasure, ∀ k : Category, ∀ t : Real, ∀ n : ℕ,
      n ∈ multiclassForwardArrivalIndices k t ω ↔ arrivalTime n (ω k) ≤ t :=
  ae_mem_multiclassForwardArrivalIndices_iff M.admittedRate M.admittedRate_pos

/-- The admitted input’s class paths are simultaneously nonexplosive and
strictly ordered. -/
theorem ae_admittedArrivalPaths_nonexplosive_strict
    (M : SLA2026BoroughQueueingInput Category) :
    ∀ᵐ ω ∂M.admittedArrivalMeasure, ∀ k : Category,
      Filter.Tendsto (fun n : ℕ => arrivalTime n (ω k)) Filter.atTop Filter.atTop ∧
        StrictMono (fun n : ℕ => arrivalTime n (ω k)) :=
  ae_multiclassForwardArrivalPaths_nonexplosive_strict M.admittedRate
    M.admittedRate_pos

/-- A joint carrier for the directly stated admitted streams and their iid
unit-mean exponential job-work paths.  The unused all-true admission-mark
factor is retained so this is an instance of the reusable primitive product
construction, rather than a separate hand-built probability space. -/
def admittedWorkPrimitiveMeasure (M : SLA2026BoroughQueueingInput Category) :
    Measure (Category → ForwardQueueingPrimitivePath) :=
  multiclassForwardQueueingPrimitiveMeasure M.admittedRate (fun _ => 1)
    (fun _ => by simp)

/-- The admitted-arrival/work carrier is a probability space. -/
theorem isProbabilityMeasure_admittedWorkPrimitiveMeasure
    (M : SLA2026BoroughQueueingInput Category) :
    IsProbabilityMeasure M.admittedWorkPrimitiveMeasure := by
  exact isProbabilityMeasure_multiclassForwardQueueingPrimitiveMeasure
    M.admittedRate M.admittedRate_pos (fun _ => 1) (fun _ => by simp)

/-- Complete admitted-arrival/work paths are independent across categories.
This is stronger than independence of selected count variables: it preserves
the joint source input needed by a multiclass event scheduler. -/
theorem iIndepFun_admittedWorkPrimitivePaths
    (M : SLA2026BoroughQueueingInput Category) :
    ProbabilityTheory.iIndepFun
      (fun k (omega : Category -> ForwardQueueingPrimitivePath) => omega k)
      M.admittedWorkPrimitiveMeasure := by
  simpa [admittedWorkPrimitiveMeasure] using
    (iIndepFun_multiclassForwardQueueingPrimitivePaths M.admittedRate
      M.admittedRate_pos (fun _ => 1) (fun _ => by simp))

/-- A concrete admitted Poisson process on the carrier that also contains its
class’s work-mark path. -/
def admittedWorkPoissonCountingProcess
    (M : SLA2026BoroughQueueingInput Category) (k : Category) :
    ForwardHomogeneousPoissonCountingProcessByLaw
      (Category → ForwardQueueingPrimitivePath)
      M.admittedWorkPrimitiveMeasure :=
  multiclassForwardQueueingPrimitiveRawPoissonCountingProcess M.admittedRate
    M.admittedRate_pos (fun _ => 1) (fun _ => by simp) k

/-- The finite ledger of actual admitted arrival indices on the carrier that
also holds the job work marks. -/
noncomputable def admittedWorkArrivalIndices
    (M : SLA2026BoroughQueueingInput Category) (k : Category) (t : Real) :
    (Category → ForwardQueueingPrimitivePath) → Finset ℕ :=
  multiclassForwardQueueingPrimitiveArrivalIndices k t

/-- Exact simultaneous arrival enumeration on the joint admitted-arrival/work
carrier.  This supplies the finite event lists a GPS execution must process;
the work marks used for those events live on the same `omega`. -/
theorem ae_mem_admittedWorkArrivalIndices_iff
    (M : SLA2026BoroughQueueingInput Category) :
    ∀ᵐ ω ∂M.admittedWorkPrimitiveMeasure, ∀ k : Category, ∀ t : Real, ∀ n : ℕ,
      n ∈ M.admittedWorkArrivalIndices k t ω ↔
        arrivalTime n
          (multiclassForwardQueueingPrimitiveRawInterarrivals k ω) ≤ t := by
  simpa [admittedWorkPrimitiveMeasure, admittedWorkArrivalIndices] using
    (ae_mem_multiclassPrimitiveArrivalIndices_iff M.admittedRate
      M.admittedRate_pos (fun _ => 1) (fun _ => by simp))

/-- Admitted arrival paths are simultaneously nonexplosive and strictly
ordered on the same carrier as their service work requirements. -/
theorem ae_admittedWorkArrivalPaths_nonexplosive_strict
    (M : SLA2026BoroughQueueingInput Category) :
    ∀ᵐ ω ∂M.admittedWorkPrimitiveMeasure, ∀ k : Category,
      Filter.Tendsto (fun n : ℕ => arrivalTime n
        (multiclassForwardQueueingPrimitiveRawInterarrivals k ω))
        Filter.atTop Filter.atTop ∧
      StrictMono (fun n : ℕ => arrivalTime n
        (multiclassForwardQueueingPrimitiveRawInterarrivals k ω)) := by
  simpa [admittedWorkPrimitiveMeasure] using
    (ae_multiclassPrimitiveRawArrivalPaths_nonexplosive_strict M.admittedRate
      M.admittedRate_pos (fun _ => 1) (fun _ => by simp))

/-- The iid unit-exponential work-mark path of one admitted category. -/
def admittedWorkMarks (M : SLA2026BoroughQueueingInput Category) (k : Category) :
    (Category → ForwardQueueingPrimitivePath) → (ℕ → Real) :=
  multiclassForwardQueueingPrimitiveWorkMarks k

/-- Work marks of each category have the canonical iid unit-exponential path
law on the joint admitted-arrival/work carrier. -/
theorem measurePreserving_admittedWorkMarks
    (M : SLA2026BoroughQueueingInput Category) (k : Category) :
    MeasurePreserving (M.admittedWorkMarks k) M.admittedWorkPrimitiveMeasure
      (exponentialInterarrivalMeasure 1) := by
  simpa [admittedWorkPrimitiveMeasure, admittedWorkMarks] using
    measurePreserving_multiclassPrimitiveWorkMarks M.admittedRate
      M.admittedRate_pos (fun _ => 1) (fun _ => by simp) k

/-- The actual work requirement assigned to a particular admitted request. -/
def admittedWorkRequirement (M : SLA2026BoroughQueueingInput Category)
    (k : Category) (n : ℕ) : (Category → ForwardQueueingPrimitivePath) → Real :=
  fun ω => interarrival n (M.admittedWorkMarks k ω)

/-- On the admitted-arrival/work carrier, every concrete job requirement is
strictly positive almost surely, simultaneously across the finite category
set and all job indices.  This comes from the source's exponential work law;
it is not a scheduler-side assumption. -/
theorem ae_all_admittedWorkRequirements_positive
    (M : SLA2026BoroughQueueingInput Category) :
    ∀ᵐ ω ∂M.admittedWorkPrimitiveMeasure, ∀ k : Category, ∀ n : ℕ,
      0 < M.admittedWorkRequirement k n ω := by
  simpa [admittedWorkRequirement, admittedWorkMarks,
    admittedWorkPrimitiveMeasure] using
    (ae_all_multiclassPrimitiveWorkMarks_positive M.admittedRate
      M.admittedRate_pos (fun _ => 1) (fun _ => by simp))

/-- Each assigned work requirement has the source’s unit-mean exponential law. -/
theorem admittedWorkRequirement_hasLaw
    (M : SLA2026BoroughQueueingInput Category) (k : Category) (n : ℕ) :
    ProbabilityTheory.HasLaw (M.admittedWorkRequirement k n)
      (ProbabilityTheory.expMeasure 1) M.admittedWorkPrimitiveMeasure := by
  simpa [admittedWorkRequirement] using
    (interarrival_hasLaw (by norm_num : 0 < (1 : Real)) n).comp
      (M.measurePreserving_admittedWorkMarks k).hasLaw

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
