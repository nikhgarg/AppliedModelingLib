import PG24NoisyMatchingMarkets.Theorem4GlobalCoalitionAEMatchSemantics
import Mathlib.Tactic

/-!
# PG24 Theorem 4 Source-Model Sampling Adapter

The extended source model has a probability law `rho` on rich student states
and, conditional on that state, iid coalition noise.  A rich state may retain
arbitrary preferences, true values outside the coalition, and external
signals.  This module proves the only local marginal used by the Theorem 4
analysis instead of taking it as a theorem-sized premise.
-/

open MeasureTheory

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v

/--
The source sampling data for one extended-model coalition.

`StudentType` is deliberately unconstrained: it can contain the paper's full
true-value vector, the student's preference order, and arbitrary external
state.  The local iid condition is recorded at the source `rho × D^C` level;
the eta-by-iid local-coordinate law is derived below.
-/
structure PG24CoalitionSourceSampling
    (C : ℕ) (noiseLaw eta : Measure ℝ)
    (StudentType : Type v) [MeasurableSpace StudentType]
    (Outcome : Type u) [MeasurableSpace Outcome] where
  studentLaw : Measure StudentType
  studentLaw_isProbability : IsProbabilityMeasure studentLaw
  outcomeLaw : Measure Outcome
  outcomeLaw_isProbability : IsProbabilityMeasure outcomeLaw
  commonValue : StudentType → ℝ
  commonValue_measurable : Measurable commonValue
  commonValue_map :
    Measure.map commonValue studentLaw = eta
  sourceStudent : Outcome → StudentType
  coalitionNoise : Outcome → Fin (C + 1) → ℝ
  sourceCoordinates_measurable :
    Measurable (fun outcome => (sourceStudent outcome, coalitionNoise outcome))
  sourceCoordinates_map :
    Measure.map (fun outcome => (sourceStudent outcome, coalitionNoise outcome))
      outcomeLaw =
        studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))

namespace PG24CoalitionSourceSampling

variable {C : ℕ} {noiseLaw eta : Measure ℝ}
variable {StudentType : Type v} [MeasurableSpace StudentType]
variable {Outcome : Type u} [MeasurableSpace Outcome]

/-- The local common-value/noise coordinates used by `p_mu`. -/
def localCoordinates
    (sampling : PG24CoalitionSourceSampling C noiseLaw eta StudentType Outcome) :
    Outcome → ℝ × (Fin (C + 1) → ℝ) :=
  fun outcome =>
    (sampling.commonValue (sampling.sourceStudent outcome),
      sampling.coalitionNoise outcome)

/-- The local coordinate map is measurable from the source sampling data. -/
theorem localCoordinates_measurable
    (sampling : PG24CoalitionSourceSampling C noiseLaw eta StudentType Outcome) :
    Measurable sampling.localCoordinates := by
  let transform : StudentType × (Fin (C + 1) → ℝ) →
      ℝ × (Fin (C + 1) → ℝ) :=
    fun source => (sampling.commonValue source.1, source.2)
  have htransform : Measurable transform := by
    exact sampling.commonValue_measurable.prodMap measurable_id
  have hcoordinates :
      Measurable (fun outcome : Outcome =>
        (sampling.sourceStudent outcome, sampling.coalitionNoise outcome)) :=
    sampling.sourceCoordinates_measurable
  have hcomposition : sampling.localCoordinates = transform ∘
      (fun outcome : Outcome =>
        (sampling.sourceStudent outcome, sampling.coalitionNoise outcome)) := by
    funext outcome
    rfl
  rw [hcomposition]
  exact htransform.comp hcoordinates

/--
The source's `rho` marginal for the common coalition value and its conditional
iid coalition noise imply the eta-by-iid law used by the analytic proof.
-/
theorem localCoordinates_map_eq_eta_prod_iid
    (sampling : PG24CoalitionSourceSampling C noiseLaw eta StudentType Outcome)
    [IsProbabilityMeasure noiseLaw] :
    Measure.map sampling.localCoordinates sampling.outcomeLaw =
      eta.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) := by
  let sourceCoordinates : Outcome → StudentType × (Fin (C + 1) → ℝ) :=
    fun outcome => (sampling.sourceStudent outcome, sampling.coalitionNoise outcome)
  let transform : StudentType × (Fin (C + 1) → ℝ) →
      ℝ × (Fin (C + 1) → ℝ) :=
    fun source => (sampling.commonValue source.1, source.2)
  have htransform : Measurable transform := by
    exact sampling.commonValue_measurable.prodMap measurable_id
  have hsourceCoordinates : Measurable sourceCoordinates :=
    sampling.sourceCoordinates_measurable
  letI : IsProbabilityMeasure sampling.studentLaw :=
    sampling.studentLaw_isProbability
  have hlocal : sampling.localCoordinates = transform ∘ sourceCoordinates := by
    funext outcome
    rfl
  rw [hlocal, ← Measure.map_map htransform hsourceCoordinates,
    sampling.sourceCoordinates_map]
  have hproduct := Measure.map_prod_map sampling.studentLaw
    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
    sampling.commonValue_measurable measurable_id
  have htransform_eq : transform = Prod.map sampling.commonValue id := by
    rfl
  rw [htransform_eq, ← hproduct, sampling.commonValue_map]
  simp

end PG24CoalitionSourceSampling

end

end PG24NoisyMatchingMarkets
