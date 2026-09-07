import AppliedModelingLib.Queueing.MM1.Marked.Uniformization
import AppliedModelingLib.Foundations.Probability.IndependentProduct
import Mathlib.Tactic

/-!
# Mark-indexed stationary M/M/1 uniformization trajectories

This module packages the reflected uniformized M/M/1 chain with the actual
Boolean event mark that drives each transition.  An augmented state is
`(Q_n, M_n)`, where `M_n = true` means that the `n`-th embedded event is an
arrival and `M_n = false` means a potential-service attempt.  One augmented
step deterministically applies `M_n` to `Q_n`, then draws a fresh Bernoulli
mark `M_(n+1)`.

We prove the literal invariant law `geometric × Bernoulli`, lift it to a
stationary Ionescu--Tulcea trajectory, and prove that two consecutive marks
have the independent Bernoulli product law.  These are embedded discrete-time
facts only.  This module does not introduce Poisson event times, identify a
CTMC, prove thinning, construct a two-sided shift-invariant path, or establish
Palm/PASTA semantics.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-- The product PMF of a queue state and its current Bernoulli event mark,
written monadically so the queue-state coordinate can be countable. -/
def markedStatePMF (π : PMF ℕ) (p : ℝ≥0) (hp : p ≤ 1) : PMF (ℕ × Bool) :=
  π.bind fun q => (uniformizationArrivalMark p hp).map fun mark => (q, mark)

/-- A step consumes the current mark to update the queue, then samples a fresh
Bernoulli mark for the next embedded event. -/
def markedStateUniformizationKernel (p : ℝ≥0) (hp : p ≤ 1) :
    CountableMarkovKernel (ℕ × Bool) :=
  fun z => (uniformizationArrivalMark p hp).map
    fun nextMark => (reflectedBirthDeathUpdate z.1 z.2, nextMark)

/-- Measure-valued realization of the state/current-mark embedded kernel. -/
noncomputable def markedStateUniformizationMeasureKernel (p : ℝ≥0) (hp : p ≤ 1) :
    Kernel (ℕ × Bool) (ℕ × Bool) :=
  countablePMFKernel (markedStateUniformizationKernel p hp)

instance (p : ℝ≥0) (hp : p ≤ 1) :
    IsMarkovKernel (markedStateUniformizationMeasureKernel p hp) := by
  unfold markedStateUniformizationMeasureKernel
  infer_instance

/-- Running the marked-state kernel from the state/mark product law is the
same as first running the unmarked reflected kernel and then drawing a fresh
mark. -/
theorem markedStatePMF_bind_kernel
    (π : PMF ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    (markedStatePMF π p hp).bind (markedStateUniformizationKernel p hp) =
      markedStatePMF (π.bind (reflectedBirthDeathKernel p hp)) p hp := by
  let B := uniformizationArrivalMark p hp
  calc
    (markedStatePMF π p hp).bind (markedStateUniformizationKernel p hp) =
        π.bind fun q =>
          ((B.map (fun mark => reflectedBirthDeathUpdate q mark)).bind fun q' =>
            B.map fun nextMark => (q', nextMark)) := by
          unfold markedStatePMF markedStateUniformizationKernel
          rw [PMF.bind_bind]
          congr 1
          funext q
          rw [PMF.bind_map, PMF.bind_map]
          rfl
    _ = (π.bind (reflectedBirthDeathKernel p hp)).bind fun q =>
          B.map fun nextMark => (q, nextMark) := by
          rw [PMF.bind_bind]
          rfl
    _ = markedStatePMF (π.bind (reflectedBirthDeathKernel p hp)) p hp := rfl

/-- If the unmarked chain has invariant PMF `π`, then the augmented chain
with the current event mark has invariant law `π × Bernoulli(p)`. -/
theorem markedStatePMF_stationary
    {π : PMF ℕ} (p : ℝ≥0) (hp : p ≤ 1)
    (hstationary : PMFStationary (reflectedBirthDeathKernel p hp) π) :
    PMFStationary (markedStateUniformizationKernel p hp) (markedStatePMF π p hp) := by
  unfold PMFStationary
  rw [markedStatePMF_bind_kernel, hstationary]

/-- The PMF invariant law lifts to the measure-valued kernel used by the
stationary embedded trajectory construction. -/
theorem markedStatePMF_kernelInvariant
    {π : PMF ℕ} (p : ℝ≥0) (hp : p ≤ 1)
    (hstationary : PMFStationary (reflectedBirthDeathKernel p hp) π) :
    Kernel.Invariant (markedStateUniformizationMeasureKernel p hp)
      (markedStatePMF π p hp).toMeasure := by
  simpa only [markedStateUniformizationMeasureKernel] using
    (markedStatePMF_stationary p hp hstationary).kernelInvariant

/-- The marked M/M/1 uniformization has a literal invariant state/current-mark
PMF.  It is still a discrete embedded-chain statement. -/
theorem geoNNPMF_markedState_stationary
    (rho : ℝ≥0) (hrho : rho < 1) :
    PMFStationary
      (markedStateUniformizationKernel (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho))
      (markedStatePMF (geoNNPMF rho hrho) (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho)) := by
  apply markedStatePMF_stationary
  exact geoNNPMF_uniformized_stationary rho hrho

/-- The measure-valued augmented M/M/1 kernel has the literal stationary
geometric-state/Bernoulli-mark law. -/
theorem geoNNPMF_markedState_kernelInvariant
    (rho : ℝ≥0) (hrho : rho < 1) :
    Kernel.Invariant
      (markedStateUniformizationMeasureKernel (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho))
      (markedStatePMF (geoNNPMF rho hrho) (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho)).toMeasure := by
  apply markedStatePMF_kernelInvariant
  exact geoNNPMF_uniformized_stationary rho hrho

/-- The one-step PMF that retains both consecutive augmented states. -/
def markedStatePairPMF (π : PMF ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    PMF ((ℕ × Bool) × (ℕ × Bool)) :=
  (markedStatePMF π p hp).bind fun z =>
    (markedStateUniformizationKernel p hp z).map fun z' => (z, z')

/-- Forget the queue coordinates of two consecutive augmented states. -/
def consecutiveMarks : ((ℕ × Bool) × (ℕ × Bool)) → Bool × Bool :=
  fun z => (z.1.2, z.2.2)

private theorem pmf_map_pair_apply {α β : Type*} (ν : PMF β) (a : α) (b : β) :
    (ν.map (fun x => (a, x))) (a, b) = ν b := by
  classical
  rw [PMF.map_apply]
  rw [tsum_eq_single b]
  · simp
  · intro x hxb
    split_ifs with h
    · exact (hxb (congrArg Prod.snd h).symm).elim
    · rfl

private theorem pmf_map_pair_apply_of_ne {α β : Type*} (ν : PMF β)
    {a a' : α} (haa' : a' ≠ a) (b : β) :
    (ν.map (fun x => (a, x))) (a', b) = 0 := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_eq_zero]
  intro x
  simp [haa']

private theorem markedStatePMF_apply
    (π : PMF ℕ) (p : ℝ≥0) (hp : p ≤ 1) (q : ℕ) (mark : Bool) :
    markedStatePMF π p hp (q, mark) =
      π q * uniformizationArrivalMark p hp mark := by
  unfold markedStatePMF
  rw [PMF.bind_apply, tsum_eq_single q]
  · rw [pmf_map_pair_apply]
  · intro other hother
    rw [pmf_map_pair_apply_of_ne
      (uniformizationArrivalMark p hp) (Ne.symm hother) mark]
    simp

/-- The literal invariant marked-state PMF is the product of its queue-state
PMF and the current Bernoulli event-mark PMF. -/
theorem markedStatePMF_toMeasure_eq_prod
    (π : PMF ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    (markedStatePMF π p hp).toMeasure =
      π.toMeasure.prod (uniformizationArrivalMark p hp).toMeasure := by
  apply Measure.ext_of_singleton
  rintro ⟨q, mark⟩
  rw [PMF.toMeasure_apply_singleton (markedStatePMF π p hp)
      (q, mark) (measurableSet_singleton _), markedStatePMF_apply,
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    π.toMeasure_apply_singleton q (measurableSet_singleton _),
    (uniformizationArrivalMark p hp).toMeasure_apply_singleton mark
      (measurableSet_singleton _)]

private theorem markedStatePairPMF_apply
    (π : PMF ℕ) (p : ℝ≥0) (hp : p ≤ 1)
    (z z' : ℕ × Bool) :
    markedStatePairPMF π p hp (z, z') =
      markedStatePMF π p hp z * markedStateUniformizationKernel p hp z z' := by
  classical
  unfold markedStatePairPMF
  rw [PMF.bind_apply]
  rw [tsum_eq_single z]
  · rw [pmf_map_pair_apply]
  · intro x hxz
    rw [pmf_map_pair_apply_of_ne
      (markedStateUniformizationKernel p hp x) (Ne.symm hxz) z']
    simp

private theorem markedStatePairPMF_toMeasure_eq_compProd
    (π : PMF ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    (markedStatePairPMF π p hp).toMeasure =
      (markedStatePMF π p hp).toMeasure ⊗ₘ
        markedStateUniformizationMeasureKernel p hp := by
  apply Measure.ext_of_singleton
  rintro ⟨z, z'⟩
  rw [PMF.toMeasure_apply_singleton (markedStatePairPMF π p hp)
      (z, z') (measurableSet_singleton _), markedStatePairPMF_apply,
    ← Set.singleton_prod_singleton,
    Measure.compProd_apply_prod (measurableSet_singleton z)
      (measurableSet_singleton z'), MeasureTheory.lintegral_singleton]
  change markedStatePMF π p hp z * markedStateUniformizationKernel p hp z z' =
    (markedStateUniformizationKernel p hp z).toMeasure {z'} *
      (markedStatePMF π p hp).toMeasure {z}
  rw [(markedStateUniformizationKernel p hp z).toMeasure_apply_singleton z'
      (measurableSet_singleton _),
    (markedStatePMF π p hp).toMeasure_apply_singleton z (measurableSet_singleton _)]
  rw [mul_comm]

private theorem bernoulliPair_bind_eq_pmfProd (B : PMF Bool) :
    B.bind (fun mark => B.map fun nextMark => (mark, nextMark)) =
      AppliedModelingLib.pmfProd B B := by
  apply PMF.ext
  rintro ⟨mark, nextMark⟩
  cases mark <;> cases nextMark <;>
    simp [PMF.bind_apply, PMF.map_apply, AppliedModelingLib.pmfProd_apply]

/-- The finite two-mark marginal of the literal state/current-mark transition
is the product of two Bernoulli event-mark PMFs. -/
theorem markedStatePairPMF_map_consecutiveMarks
    (π : PMF ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    (markedStatePairPMF π p hp).map consecutiveMarks =
      AppliedModelingLib.pmfProd (uniformizationArrivalMark p hp)
        (uniformizationArrivalMark p hp) := by
  let B := uniformizationArrivalMark p hp
  calc
    (markedStatePairPMF π p hp).map consecutiveMarks =
        π.bind fun _q => B.bind fun mark =>
          B.map fun nextMark => (mark, nextMark) := by
          unfold markedStatePairPMF markedStatePMF markedStateUniformizationKernel
          rw [PMF.map_bind, PMF.bind_bind]
          congr 1
          funext q
          simp only [PMF.map_comp]
          rw [PMF.bind_map]
          rfl
    _ = B.bind fun mark => B.map fun nextMark => (mark, nextMark) := by
          rw [PMF.bind_const]
    _ = AppliedModelingLib.pmfProd B B := bernoulliPair_bind_eq_pmfProd B

/-- At every embedded event index, the pre-event queue state and current
arrival-versus-potential-service mark have their exact product law.  This is
the embedded-event independence needed before a future real-time/Palm
construction can establish PASTA; it does not by itself make a continuous-time
arrival tag. -/
theorem stationaryMarkedStateTraj_stateMark_hasLaw
    {π : PMF ℕ} (p : ℝ≥0) (hp : p ≤ 1)
    (hstationary : PMFStationary (reflectedBirthDeathKernel p hp) π)
    (n : ℕ) :
    HasLaw (fun x : ℕ → (ℕ × Bool) => x n)
      (π.toMeasure.prod (uniformizationArrivalMark p hp).toMeasure)
      (stationaryTrajMeasure (markedStatePMF π p hp).toMeasure
        (markedStateUniformizationMeasureKernel p hp)) := by
  refine ⟨(measurable_pi_apply n).aemeasurable, ?_⟩
  rw [stationaryTrajMeasure_marginal
    (markedStatePMF_kernelInvariant p hp hstationary) n,
    markedStatePMF_toMeasure_eq_prod]

/-- Stable uniformized M/M/1 specialization of the embedded state/current-mark
product law. -/
theorem geoNNPMF_stationaryMarkedStateTraj_stateMark_hasLaw
    (rho : ℝ≥0) (hrho : rho < 1) (n : ℕ) :
    HasLaw (fun x : ℕ → (ℕ × Bool) => x n)
      ((geoNNPMF rho hrho).toMeasure.prod
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure)
      (stationaryTrajMeasure
        (markedStatePMF (geoNNPMF rho hrho) (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure
        (markedStateUniformizationMeasureKernel (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho))) := by
  apply stationaryMarkedStateTraj_stateMark_hasLaw
  exact geoNNPMF_uniformized_stationary rho hrho

/-- The embedded event that the pre-event queue exceeds a threshold and the
current mark is an arrival factors exactly into the geometric (or supplied
stationary) state tail and the Bernoulli arrival-mark mass.  This is an
embedded-event PASTA precursor only; a real-time Palm selection still requires
the marked suspension construction. -/
theorem stationaryMarkedStateTraj_measure_state_ge_and_arrivalMark_eq
    {π : PMF ℕ} (p : ℝ≥0) (hp : p ≤ 1)
    (hstationary : PMFStationary (reflectedBirthDeathKernel p hp) π)
    (n k : ℕ) :
    (stationaryTrajMeasure (markedStatePMF π p hp).toMeasure
      (markedStateUniformizationMeasureKernel p hp))
        {x | k ≤ (x n).1 ∧ (x n).2 = true} =
      (uniformizationArrivalMark p hp).toMeasure {true} *
        π.toMeasure {q | k ≤ q} := by
  exact measure_preState_ge_and_arrivalMark_eq_of_hasLaw
    (stationaryMarkedStateTraj_stateMark_hasLaw p hp hstationary n) k

/-- In the stationary trajectory of the augmented embedded kernel, two
consecutive event marks have the independent Bernoulli product law.  This is
an embedded discrete-time statement; it does not construct a Poisson clock or
assert Palm/PASTA semantics. -/
theorem stationaryMarkedStateTraj_consecutiveMarks_hasLaw
    {π : PMF ℕ} (p : ℝ≥0) (hp : p ≤ 1)
    (hstationary : PMFStationary (reflectedBirthDeathKernel p hp) π)
    (n : ℕ) :
    HasLaw
      (fun x : ℕ → (ℕ × Bool) => ((x n).2, (x (n + 1)).2))
      (AppliedModelingLib.pmfProd (uniformizationArrivalMark p hp)
        (uniformizationArrivalMark p hp)).toMeasure
      (stationaryTrajMeasure (markedStatePMF π p hp).toMeasure
        (markedStateUniformizationMeasureKernel p hp)) := by
  let P := stationaryTrajMeasure (markedStatePMF π p hp).toMeasure
    (markedStateUniformizationMeasureKernel p hp)
  let pair : (ℕ → (ℕ × Bool)) → (ℕ × Bool) × (ℕ × Bool) :=
    fun x => (x n, x (n + 1))
  have hpair : Measurable pair :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hmarks : Measurable consecutiveMarks := measurable_of_countable _
  refine ⟨(hmarks.comp hpair).aemeasurable, ?_⟩
  change Measure.map (fun x : ℕ → (ℕ × Bool) => ((x n).2, (x (n + 1)).2)) P = _
  calc
    Measure.map (fun x : ℕ → (ℕ × Bool) => ((x n).2, (x (n + 1)).2)) P =
        Measure.map consecutiveMarks (Measure.map pair P) := by
          symm
          rw [Measure.map_map hmarks hpair]
          rfl
    _ = Measure.map consecutiveMarks
          ((markedStatePMF π p hp).toMeasure ⊗ₘ
            markedStateUniformizationMeasureKernel p hp) := by
          rw [stationaryTrajMeasure_consecutivePair
            (markedStatePMF_kernelInvariant p hp hstationary) n]
    _ = Measure.map consecutiveMarks (markedStatePairPMF π p hp).toMeasure := by
          rw [markedStatePairPMF_toMeasure_eq_compProd]
    _ = ((markedStatePairPMF π p hp).map consecutiveMarks).toMeasure := by
          rw [PMF.toMeasure_map consecutiveMarks (markedStatePairPMF π p hp) hmarks]
    _ = (AppliedModelingLib.pmfProd (uniformizationArrivalMark p hp)
          (uniformizationArrivalMark p hp)).toMeasure := by
          rw [markedStatePairPMF_map_consecutiveMarks]

/-- Stable uniformized M/M/1 specialization of the two-consecutive-event-mark
product law. -/
theorem geoNNPMF_stationaryMarkedStateTraj_consecutiveMarks_hasLaw
    (rho : ℝ≥0) (hrho : rho < 1) (n : ℕ) :
    HasLaw
      (fun x : ℕ → (ℕ × Bool) => ((x n).2, (x (n + 1)).2))
      (AppliedModelingLib.pmfProd
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho))
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho))).toMeasure
      (stationaryTrajMeasure
        (markedStatePMF (geoNNPMF rho hrho) (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure
        (markedStateUniformizationMeasureKernel (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho))) := by
  apply stationaryMarkedStateTraj_consecutiveMarks_hasLaw
  exact geoNNPMF_uniformized_stationary rho hrho

end

end AppliedModelingLib.Probability.Queueing
