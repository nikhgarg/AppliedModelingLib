import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Independence.Process.HasIndepIncrements.IsGaussianProcess
import AppliedModelingLib.Foundations.Probability.SkorokhodJ1
import AppliedModelingLib.Foundations.Probability.TendstoInDistributionTight

/-!
# Standard Brownian motion

This file supplies a compact interface for a real standard Brownian motion on
nonnegative time.  It is intentionally an interface rather than a construction:
the construction of Wiener measure belongs to a separate probability-space
development, while queueing diffusion limits need a stable way to state the
continuous Gaussian driving process and to derive its finite-dimensional
Gaussian structure.
-/

namespace AppliedModelingLib.Probability

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal

/-- A standard real Brownian motion indexed by nonnegative time.  The process
has almost-surely continuous paths, independent increments, and the centered
Gaussian marginal with variance equal to elapsed time. -/
structure IsStandardBrownianMotion
    {Ω : Type*} [MeasurableSpace Ω] (process : ℝ≥0 → Ω → ℝ)
    (law : Measure Ω) : Prop where
  aemeasurable_apply : ∀ time, AEMeasurable (process time) law
  ae_continuous : ∀ᵐ omega ∂law, Continuous fun time : ℝ≥0 => process time omega
  ae_zero : ∀ᵐ omega ∂law, process 0 omega = 0
  marginal_hasLaw : ∀ time,
    HasLaw (process time) (gaussianReal 0 time) law
  independentIncrements : HasIndepIncrements process law

namespace IsStandardBrownianMotion

variable {Ω : Type*} [MeasurableSpace Ω] {process : ℝ≥0 → Ω → ℝ}
  {law : Measure Ω}

/-- A standard Brownian motion is carried by a probability measure. -/
theorem isProbabilityMeasure (hprocess : IsStandardBrownianMotion process law) :
    IsProbabilityMeasure law := by
  exact (hprocess.marginal_hasLaw 0).isProbabilityMeasure

/-- Every fixed-time Brownian marginal is Gaussian. -/
theorem marginal_hasGaussianLaw
    (hprocess : IsStandardBrownianMotion process law) (time : ℝ≥0) :
    HasGaussianLaw (process time) law := by
  exact (hprocess.marginal_hasLaw time).hasGaussianLaw

/-- A Brownian increment over an interval of length `duration` is centered
Gaussian with variance `duration`.  This is derived from the defining
independent-increment and marginal-law properties, rather than added as an
extra axiom of the Brownian-motion interface. -/
theorem increment_hasLaw
    (hprocess : IsStandardBrownianMotion process law) (start duration : ℝ≥0) :
    HasLaw (fun omega => process (start + duration) omega - process start omega)
      (gaussianReal 0 duration) law := by
  let X : Ω → ℝ := process start
  let Y : Ω → ℝ := fun omega => process (start + duration) omega - process start omega
  have hX : HasLaw X (gaussianReal 0 start) law := by
    simpa only [X] using hprocess.marginal_hasLaw start
  have hYGaussian : HasGaussianLaw Y law := by
    simpa only [Y] using
      (hprocess.independentIncrements.isGaussianProcess
        (fun time => hprocess.marginal_hasGaussianLaw time) hprocess.ae_zero).hasGaussianLaw_fun_sub
        (s := start + duration) (t := start)
  have hindependent : IndepFun X Y law := by
    simpa only [X, Y] using
      hprocess.independentIncrements.indepFun_eval_sub (r := 0) (s := start)
        (t := start + duration) (by simp) (by simp) hprocess.ae_zero
  have hsum : law.map (X + Y) = gaussianReal 0 (start + duration) := by
    have hXY : X + Y = process (start + duration) := by
      ext omega
      simp only [X, Y, Pi.add_apply, add_sub_cancel]
    rw [hXY]
    exact (hprocess.marginal_hasLaw (start + duration)).map_eq
  have hYlaw : law.map Y = gaussianReal (∫ omega, Y omega ∂law)
      Var[Y; law].toNNReal := by
    have hYlaw' := hYGaussian.isGaussian_map.eq_gaussianReal
    rw [integral_map hYGaussian.aemeasurable
      hYGaussian.isGaussian_map.integrable_id.aestronglyMeasurable,
      variance_id_map hYGaussian.aemeasurable] at hYlaw'
    simpa only [Function.id_comp] using hYlaw'
  have hsumGaussian : law.map (X + Y) =
      gaussianReal (0 + ∫ omega, Y omega ∂law) (start + Var[Y; law].toNNReal) := by
    exact gaussianReal_add_gaussianReal_of_indepFun hindependent hX.map_eq hYlaw
  have hparameters : 0 + ∫ omega, Y omega ∂law = 0 ∧
      start + Var[Y; law].toNNReal = start + duration := by
    exact gaussianReal_ext_iff.mp (hsumGaussian.symm.trans hsum)
  have hmean : ∫ omega, Y omega ∂law = 0 := by
    simpa using hparameters.1
  have hvariance : Var[Y; law].toNNReal = duration := by
    exact add_left_cancel hparameters.2
  refine ⟨hYGaussian.aemeasurable, ?_⟩
  simpa only [Y, hmean, hvariance] using hYlaw

/-- The increments of a Brownian motion on a finite ordered time grid have
the product of their centered Gaussian laws. -/
theorem finiteIncrementVector_hasLaw_pi
    (hprocess : IsStandardBrownianMotion process law) {n : ℕ}
    (times : Fin (n + 1) → ℝ≥0) (htimes : Monotone times) :
    HasLaw
      (fun omega (index : Fin n) =>
        process (times index.succ) omega - process (times index.castSucc) omega)
      (Measure.pi fun index => gaussianReal 0 (times index.succ - times index.castSucc)) law := by
  letI : IsProbabilityMeasure law := hprocess.isProbabilityMeasure
  let increment : Fin n → Ω → ℝ := fun index omega =>
    process (times index.succ) omega - process (times index.castSucc) omega
  have hmeasurable : ∀ index, AEMeasurable (increment index) law := by
    intro index
    exact (hprocess.aemeasurable_apply _).sub (hprocess.aemeasurable_apply _)
  have hindependent : iIndepFun increment law := by
    simpa only [increment] using hprocess.independentIncrements n times htimes
  have hcomponent : ∀ index, law.map (increment index) =
      gaussianReal 0 (times index.succ - times index.castSucc) := by
    intro index
    have htime : times index.castSucc + (times index.succ - times index.castSucc) =
        times index.succ :=
      add_tsub_cancel_of_le (htimes index.castSucc_le_succ)
    simpa only [increment, htime] using
      (hprocess.increment_hasLaw (times index.castSucc)
        (times index.succ - times index.castSucc)).map_eq
  refine ⟨aemeasurable_pi_lambda _ hmeasurable, ?_⟩
  change law.map (fun omega index => increment index omega) =
    Measure.pi fun index => gaussianReal 0 (times index.succ - times index.castSucc)
  rw [(iIndepFun_iff_map_fun_eq_pi_map hmeasurable).mp hindependent]
  exact congrArg Measure.pi (funext hcomponent)

/-- Scaling every increment on a finite Brownian time grid scales each
variance by the square of the deterministic coefficient. -/
theorem const_mul_finiteIncrementVector_hasLaw_pi
    (hprocess : IsStandardBrownianMotion process law) (constant : ℝ) {n : ℕ}
    (times : Fin (n + 1) → ℝ≥0) (htimes : Monotone times) :
    HasLaw
      (fun omega (index : Fin n) => constant *
        (process (times index.succ) omega - process (times index.castSucc) omega))
      (Measure.pi fun index => gaussianReal 0
        (NNReal.mk (constant ^ 2) (sq_nonneg _) *
          (times index.succ - times index.castSucc))) law := by
  let increment : Ω → Fin n → ℝ := fun omega index =>
    process (times index.succ) omega - process (times index.castSucc) omega
  have hincrements : HasLaw increment
      (Measure.pi fun index => gaussianReal 0
        (times index.succ - times index.castSucc)) law := by
    simpa only [increment] using hprocess.finiteIncrementVector_hasLaw_pi times htimes
  have hscale : HasLaw (fun values (index : Fin n) => constant * values index)
      (Measure.pi fun index => gaussianReal 0
        (NNReal.mk (constant ^ 2) (sq_nonneg _) *
          (times index.succ - times index.castSucc)))
      (Measure.pi fun index => gaussianReal 0
        (times index.succ - times index.castSucc)) := by
    refine ⟨aemeasurable_pi_iff.mpr (fun index =>
      (show Measurable (fun values : Fin n → ℝ => constant * values index) by fun_prop).aemeasurable), ?_⟩
    rw [Measure.pi_map_pi (fun _ => by fun_prop)]
    apply congrArg Measure.pi
    funext index
    change Measure.map (fun value : ℝ => constant * value)
      (gaussianReal 0 (times index.succ - times index.castSucc)) = _
    simpa only [mul_zero] using
      (gaussianReal_map_const_mul (μ := 0)
        (v := times index.succ - times index.castSucc) constant)
  simpa only [increment, Function.comp_def] using hscale.comp hincrements

/-- The finite-dimensional distributions of a standard Brownian motion are
Gaussian. -/
theorem isGaussianProcess
    (hprocess : IsStandardBrownianMotion process law) :
    IsGaussianProcess process law := by
  exact hprocess.independentIncrements.isGaussianProcess
    (fun time => hprocess.marginal_hasGaussianLaw time) hprocess.ae_zero

/-- Scaling a Brownian sample path preserves its almost-sure continuity. -/
theorem ae_continuous_const_mul
    (hprocess : IsStandardBrownianMotion process law) (constant : ℝ) :
    ∀ᵐ omega ∂law, Continuous fun time : ℝ≥0 => constant * process time omega := by
  filter_upwards [hprocess.ae_continuous] with omega homega
  exact continuous_const.mul homega

/-- The scaled Brownian sample, extended constantly to negative times, as a
total local-`J₁` path.  On the almost-sure event of continuous Brownian
paths, this is the direct continuous-path embedding; the zero fallback only
makes the map total off that event. -/
noncomputable def constMulLocalPath
    (hprocess : IsStandardBrownianMotion process law) (constant : ℝ) (omega : Ω) :
    SkorokhodJ1LocalPath ℝ := by
  classical
  exact if hcontinuous : Continuous (fun time : ℝ =>
    constant * process time.toNNReal omega) then
    SkorokhodJ1LocalPath.ofContinuous _ hcontinuous
  else
    SkorokhodJ1LocalPath.ofContinuous (fun _ : ℝ => 0) continuous_const

/-- The total local-path representation agrees with the scaled Brownian
sample at every real time almost surely. -/
theorem ae_forall_constMulLocalPath_eq
    (hprocess : IsStandardBrownianMotion process law) (constant : ℝ) :
    ∀ᵐ omega ∂law, ∀ time : ℝ,
      hprocess.constMulLocalPath constant omega time =
        constant * process time.toNNReal omega := by
  filter_upwards [hprocess.ae_continuous_const_mul constant] with omega hcontinuous
  intro time
  have hrealContinuous : Continuous (fun realTime : ℝ =>
      constant * process realTime.toNNReal omega) :=
    hcontinuous.comp continuous_real_toNNReal
  simp [constMulLocalPath, hrealContinuous]

/-- Finite step paths whose values are sampled from a scaled Brownian motion
at deterministic nonnegative times are measurable for the local `J₁` Borel
space.  This is the finite-grid measurability layer used to approximate a
continuous Brownian sample path. -/
theorem aemeasurable_constMul_finiteStepLocalPath
    (hprocess : IsStandardBrownianMotion process law) (constant : ℝ)
    {count : ℕ} (jumpTimes : Fin count → ℝ)
    (sampleTimes : Fin (count + 1) → ℝ≥0) (hstrict : StrictMono jumpTimes) :
    letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
    letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
    AEMeasurable (fun omega => finiteStepLocalPath jumpTimes
      (fun index => constant * process (sampleTimes index) omega) hstrict) law := by
  letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
  letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
  apply SkorokhodJ1LocalEntourage.aemeasurable_finiteStepLocalPath_of_forall_aemeasurable_values
    jumpTimes hstrict
  intro index
  exact (hprocess.aemeasurable_apply (sampleTimes index)).const_mul constant

/-- The regular finite-grid approximation of a scaled Brownian sample.  At
mesh `m` it has spacing `1 / m` through time `m`, which is enough to
approximate every fixed compact time horizon along diverging meshes. -/
noncomputable def constMulUniformMeshLocalPath
    (hprocess : IsStandardBrownianMotion process law) (constant : ℝ)
    (mesh : ℕ) (hmesh : 0 < mesh) (omega : Ω) : SkorokhodJ1LocalPath ℝ :=
  finiteStepLocalPath (uniformMeshJumpTimes mesh)
    (fun index => constant * process (uniformMeshSampleTime mesh index) omega)
    (strictMono_uniformMeshJumpTimes hmesh)

/-- Every regular finite-grid Brownian approximation is almost-everywhere
measurable for the exact local `J₁` Borel structure. -/
theorem aemeasurable_constMulUniformMeshLocalPath
    (hprocess : IsStandardBrownianMotion process law) (constant : ℝ)
    (mesh : ℕ) (hmesh : 0 < mesh) :
    letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
    letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
    AEMeasurable (hprocess.constMulUniformMeshLocalPath constant mesh hmesh) law := by
  simpa [constMulUniformMeshLocalPath] using
    hprocess.aemeasurable_constMul_finiteStepLocalPath constant
      (uniformMeshJumpTimes mesh) (uniformMeshSampleTime mesh)
      (strictMono_uniformMeshJumpTimes hmesh)

/-- At a time within the grid's covered range, the finite-grid Brownian path
uses the sample indexed by the corresponding regular floor mesh. -/
theorem constMulUniformMeshLocalPath_apply
    (hprocess : IsStandardBrownianMotion process law) (constant : ℝ)
    {mesh : ℕ} (hmesh : 0 < mesh) (omega : Ω) (time : ℝ) :
    hprocess.constMulUniformMeshLocalPath constant mesh hmesh omega time =
      constant * process (uniformMeshSampleTime mesh
        (finiteStepIndex (uniformMeshJumpTimes mesh) time)) omega := by
  simp [constMulUniformMeshLocalPath]

/-- Along the regular meshes, the finite-step paths of a scaled Brownian
sample converge almost surely in local `J₁` to its continuous-path
representation.  This is a pathwise approximation statement, not a
functional central limit theorem. -/
theorem ae_locallyConverges_constMulUniformMeshLocalPaths
    (hprocess : IsStandardBrownianMotion process law) (constant : ℝ) :
    ∀ᵐ omega ∂law,
      SkorokhodJ1LocallyConverges
        (fun n : ℕ => hprocess.constMulUniformMeshLocalPath constant (n + 1)
          (Nat.succ_pos n) omega)
        (hprocess.constMulLocalPath constant omega) := by
  filter_upwards [hprocess.ae_continuous_const_mul constant] with omega hcontinuous
  let realPath : ℝ → ℝ := fun time => constant * process time.toNNReal omega
  have hrealContinuous : Continuous realPath :=
    hcontinuous.comp continuous_real_toNNReal
  have hconverges :=
    SkorokhodJ1LocallyConverges.uniformMeshFiniteStepLocalPath_locallyConverges_of_continuous
      realPath hrealContinuous
  have hpaths :
      (fun n : ℕ => hprocess.constMulUniformMeshLocalPath constant (n + 1)
        (Nat.succ_pos n) omega) =
        (fun n : ℕ => uniformMeshFiniteStepLocalPath realPath (n + 1)
          (Nat.succ_pos n)) := by
    funext n
    apply SkorokhodJ1LocalPath.ext
    intro time
    simp only [constMulUniformMeshLocalPath, uniformMeshFiniteStepLocalPath,
      finiteStepLocalPath_apply, finiteStepPath_apply_eq_activeValue, realPath,
      toNNReal_coe_uniformMeshSampleTime]
  have hpathFunctions :
      (fun n : ℕ => fun time : ℝ =>
        hprocess.constMulUniformMeshLocalPath constant (n + 1) (Nat.succ_pos n) omega time) =
        (fun n : ℕ => fun time : ℝ =>
          uniformMeshFiniteStepLocalPath realPath (n + 1) (Nat.succ_pos n) time) := by
    funext n time
    exact congrArg (fun path : SkorokhodJ1LocalPath ℝ => path time) (congrFun hpaths n)
  change SkorokhodJ1LocallyConverges
    (fun n : ℕ => fun time : ℝ =>
      hprocess.constMulUniformMeshLocalPath constant (n + 1) (Nat.succ_pos n) omega time)
    (fun time : ℝ => hprocess.constMulLocalPath constant omega time)
  rw [hpathFunctions]
  simpa [constMulLocalPath, realPath, hrealContinuous] using hconverges

/-- The scaled Brownian local-path representation is almost-everywhere
measurable for the exact local `J₁` Borel structure.  It is obtained as the
almost-sure local-`J₁` limit of measurable finite-grid paths. -/
theorem aemeasurable_constMulLocalPath
    (hprocess : IsStandardBrownianMotion process law) (constant : ℝ) :
    letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
    letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
    AEMeasurable (hprocess.constMulLocalPath constant) law := by
  letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
  letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
  apply SkorokhodJ1LocallyConverges.aemeasurable_of_ae_locallyConverges
    (fun n => hprocess.aemeasurable_constMulUniformMeshLocalPath constant (n + 1)
      (Nat.succ_pos n))
  exact hprocess.ae_locallyConverges_constMulUniformMeshLocalPaths constant

/-- The regular finite-grid paths of a scaled Brownian motion converge in
distribution in the local `J₁` topology to its continuous-path
representation.  This is a law-level consequence of the almost-sure mesh
approximation, independent of any prelimit functional central-limit theorem.
-/
theorem tendstoInDistribution_constMulUniformMeshLocalPaths
    (hprocess : IsStandardBrownianMotion process law) (constant : ℝ) :
    letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
    letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
    letI : BorelSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.borelSpace (State := ℝ)
    letI : IsProbabilityMeasure law := hprocess.isProbabilityMeasure
    TendstoInDistribution
      (fun n : ℕ => hprocess.constMulUniformMeshLocalPath constant (n + 1)
        (Nat.succ_pos n))
      atTop (hprocess.constMulLocalPath constant) (fun _ => law) law := by
  letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
  letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
  letI : BorelSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.borelSpace (State := ℝ)
  letI : IsProbabilityMeasure law := hprocess.isProbabilityMeasure
  apply tendstoInDistribution_of_ae_tendsto
    (fun n => hprocess.aemeasurable_constMulUniformMeshLocalPath constant (n + 1)
      (Nat.succ_pos n))
    (hprocess.aemeasurable_constMulLocalPath constant)
  filter_upwards [hprocess.ae_locallyConverges_constMulUniformMeshLocalPaths constant]
    with omega homega
  exact SkorokhodJ1LocallyConverges.tendsto_iff.mpr homega

/-- The scaled Brownian process still has independent increments. -/
theorem independentIncrements_const_mul
    (hprocess : IsStandardBrownianMotion process law) (constant : ℝ) :
    HasIndepIncrements (fun time omega => constant * process time omega) law := by
  simpa [smul_eq_mul] using hprocess.independentIncrements.smul constant

/-- A scaled Brownian marginal is centered Gaussian with the expected scaled
variance. -/
theorem const_mul_marginal_hasLaw
    (hprocess : IsStandardBrownianMotion process law) (constant : ℝ)
    (time : ℝ≥0) :
    HasLaw (fun omega => constant * process time omega)
      (gaussianReal 0 (NNReal.mk (constant ^ 2) (sq_nonneg _) * time)) law := by
  simpa using gaussianReal_const_mul (hprocess.marginal_hasLaw time) constant

end IsStandardBrownianMotion

end AppliedModelingLib.Probability
