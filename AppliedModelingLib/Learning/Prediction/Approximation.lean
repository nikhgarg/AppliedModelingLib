import AppliedModelingLib.Learning.Prediction.Omniprediction
import AppliedModelingLib.Learning.Prediction.ThresholdBasis
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-!
# Finite approximate bases for prediction tests

The finite-basis interface used in omniprediction arguments.  The source
paper's approximation is represented by an explicitly indexed finite linear
combination; this avoids imposing decidable equality on function spaces and
retains both the sparsity and coefficient-norm data used by runtime bounds.
-/

namespace AppliedModelingLib.Learning.Prediction

open scoped BigOperators

/-- A finite signed coefficient measure, represented by its positive and
negative finite measures.  This is the integration-ready form of a signed
measure: its coefficient action is the positive integral minus the negative
integral, and the displayed mass is a total-variation upper bound. -/
structure SignedMeasureCoefficientPair (Ω : Type*) [MeasurableSpace Ω] where
  positive : MeasureTheory.Measure Ω
  negative : MeasureTheory.Measure Ω
  positiveFinite : MeasureTheory.IsFiniteMeasure positive
  negativeFinite : MeasureTheory.IsFiniteMeasure negative

/-- Integrate a real-valued coordinate against a finite signed coefficient
pair. -/
noncomputable def signedMeasureCoefficientPairIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (coefficient : SignedMeasureCoefficientPair Ω) (f : Ω → ℝ) : ℝ :=
  (∫ omega, f omega ∂coefficient.positive) -
    ∫ omega, f omega ∂coefficient.negative

/-- The total mass of the positive and negative parts.  For the Jordan pair
of a signed measure this is its total variation on the whole space. -/
noncomputable def signedMeasureCoefficientPairMass
    {Ω : Type*} [MeasurableSpace Ω]
    (coefficient : SignedMeasureCoefficientPair Ω) : ℝ :=
  coefficient.positive.real Set.univ + coefficient.negative.real Set.univ

/-- The Jordan decomposition turns every Mathlib signed measure into the
positive/negative coefficient representation used here. -/
noncomputable def signedMeasureCoefficientPairOfSignedMeasure
    {Ω : Type*} [MeasurableSpace Ω] (coefficient : MeasureTheory.SignedMeasure Ω) :
    SignedMeasureCoefficientPair Ω where
  positive := coefficient.toJordanDecomposition.posPart
  negative := coefficient.toJordanDecomposition.negPart
  positiveFinite := inferInstance
  negativeFinite := inferInstance

/-- The coefficient-pair mass of a Jordan decomposition is exactly the total
variation mass of the underlying signed measure. -/
theorem signedMeasureCoefficientPairMass_ofSignedMeasure
    {Ω : Type*} [MeasurableSpace Ω] (coefficient : MeasureTheory.SignedMeasure Ω) :
    signedMeasureCoefficientPairMass
      (signedMeasureCoefficientPairOfSignedMeasure coefficient) =
        coefficient.totalVariation.real Set.univ := by
  unfold signedMeasureCoefficientPairMass signedMeasureCoefficientPairOfSignedMeasure
    MeasureTheory.SignedMeasure.totalVariation
  rw [MeasureTheory.measureReal_add_apply]

/-- The signed integral of a uniformly bounded coordinate is controlled by
the total mass of its positive and negative coefficient measures. -/
theorem abs_signedMeasureCoefficientPairIntegral_le_of_forall_abs_le
    {Ω : Type*} [MeasurableSpace Ω]
    (coefficient : SignedMeasureCoefficientPair Ω) (f : Ω → ℝ) (bound : ℝ)
    (hpositiveIntegrable : MeasureTheory.Integrable f coefficient.positive)
    (hnegativeIntegrable : MeasureTheory.Integrable f coefficient.negative)
    (hpoint : ∀ omega, |f omega| ≤ bound) :
    |signedMeasureCoefficientPairIntegral coefficient f| ≤
      bound * signedMeasureCoefficientPairMass coefficient := by
  letI : MeasureTheory.IsFiniteMeasure coefficient.positive := coefficient.positiveFinite
  letI : MeasureTheory.IsFiniteMeasure coefficient.negative := coefficient.negativeFinite
  unfold signedMeasureCoefficientPairIntegral signedMeasureCoefficientPairMass
  calc
    |(∫ omega, f omega ∂coefficient.positive) -
        ∫ omega, f omega ∂coefficient.negative| ≤
        |∫ omega, f omega ∂coefficient.positive| +
          |∫ omega, f omega ∂coefficient.negative| := by
          simpa using abs_sub_le (∫ omega, f omega ∂coefficient.positive) 0
            (∫ omega, f omega ∂coefficient.negative)
    _ ≤ (∫ omega, |f omega| ∂coefficient.positive) +
          ∫ omega, |f omega| ∂coefficient.negative := by
          apply add_le_add
          · simpa only [Real.norm_eq_abs] using
              (MeasureTheory.norm_integral_le_integral_norm (μ := coefficient.positive) f)
          · simpa only [Real.norm_eq_abs] using
              (MeasureTheory.norm_integral_le_integral_norm (μ := coefficient.negative) f)
    _ ≤ (∫ _omega, bound ∂coefficient.positive) +
          ∫ _omega, bound ∂coefficient.negative := by
          apply add_le_add
          · apply MeasureTheory.integral_mono hpositiveIntegrable.norm
              (MeasureTheory.integrable_const bound)
            intro omega
            simpa only [Real.norm_eq_abs] using hpoint omega
          · apply MeasureTheory.integral_mono hnegativeIntegrable.norm
              (MeasureTheory.integrable_const bound)
            intro omega
            simpa only [Real.norm_eq_abs] using hpoint omega
    _ = bound *
        (coefficient.positive.real Set.univ + coefficient.negative.real Set.univ) := by
          rw [MeasureTheory.integral_const, MeasureTheory.integral_const]
          simp only [smul_eq_mul]
          ring

/-- Differences of signed coefficient integrals are represented by the
signed integral of the pointwise difference. -/
theorem signedMeasureCoefficientPairIntegral_sub
    {Ω : Type*} [MeasurableSpace Ω]
    (coefficient : SignedMeasureCoefficientPair Ω) (f g : Ω → ℝ)
    (hpositiveF : MeasureTheory.Integrable f coefficient.positive)
    (hpositiveG : MeasureTheory.Integrable g coefficient.positive)
    (hnegativeF : MeasureTheory.Integrable f coefficient.negative)
    (hnegativeG : MeasureTheory.Integrable g coefficient.negative) :
    signedMeasureCoefficientPairIntegral coefficient f -
      signedMeasureCoefficientPairIntegral coefficient g =
        signedMeasureCoefficientPairIntegral coefficient (fun omega => f omega - g omega) := by
  unfold signedMeasureCoefficientPairIntegral
  rw [MeasureTheory.integral_sub hpositiveF hpositiveG,
    MeasureTheory.integral_sub hnegativeF hnegativeG]
  ring

/-- A uniform pointwise difference bound transfers through a finite signed
coefficient pair. -/
theorem abs_signedMeasureCoefficientPairIntegral_sub_le_of_forall_abs_sub_le
    {Ω : Type*} [MeasurableSpace Ω]
    (coefficient : SignedMeasureCoefficientPair Ω) (f g : Ω → ℝ) (bound : ℝ)
    (hpositiveF : MeasureTheory.Integrable f coefficient.positive)
    (hpositiveG : MeasureTheory.Integrable g coefficient.positive)
    (hnegativeF : MeasureTheory.Integrable f coefficient.negative)
    (hnegativeG : MeasureTheory.Integrable g coefficient.negative)
    (hpoint : ∀ omega, |f omega - g omega| ≤ bound) :
    |signedMeasureCoefficientPairIntegral coefficient f -
      signedMeasureCoefficientPairIntegral coefficient g| ≤
        bound * signedMeasureCoefficientPairMass coefficient := by
  rw [signedMeasureCoefficientPairIntegral_sub coefficient f g hpositiveF hpositiveG
    hnegativeF hnegativeG]
  exact abs_signedMeasureCoefficientPairIntegral_le_of_forall_abs_le coefficient
    (fun omega => f omega - g omega) bound (hpositiveF.sub hpositiveG)
    (hnegativeF.sub hnegativeG) hpoint

/-- A class is measure-spanned by an indexed coordinate family when every
target admits an integrable signed-measure representation with controlled
total variation and uniform error.  The signed coefficient is represented by
its finite positive and negative parts so that Lean's ordinary Bochner
integral has no hidden signed-integral convention. -/
def IsMeasureSpanned {Γ Ω : Type*} [MeasurableSpace Ω]
    (target : Set (Γ → ℝ)) (basis : Ω → Γ → ℝ)
    (epsilon coefficientNorm : ℝ) : Prop :=
  ∀ targetFunction ∈ target, ∃ coefficient : SignedMeasureCoefficientPair Ω,
    signedMeasureCoefficientPairMass coefficient ≤ coefficientNorm ∧
      (∀ point, MeasureTheory.Integrable (fun omega => basis omega point)
        coefficient.positive) ∧
      (∀ point, MeasureTheory.Integrable (fun omega => basis omega point)
        coefficient.negative) ∧
      ∀ point, |targetFunction point -
        signedMeasureCoefficientPairIntegral coefficient (fun omega => basis omega point)| ≤ epsilon

/-- Integrability of all coordinate values gives integrability of their
finite-horizon residual correlation. -/
theorem integrable_multiaccuracyCorrelation_of_integrableCoordinates
    {X Ω : Type*} {horizon : ℕ} [MeasurableSpace Ω]
    (basis : Ω → X → ℝ) (forecasts : ForecastSequence X horizon)
    (contexts : Fin horizon → X) (outcomes : Fin horizon → Bool)
    (measure : MeasureTheory.Measure Ω)
    (hintegrable : ∀ point,
      MeasureTheory.Integrable (fun omega => basis omega point) measure) :
    MeasureTheory.Integrable
      (fun omega => multiaccuracyCorrelation (basis omega) forecasts contexts outcomes) measure := by
  unfold multiaccuracyCorrelation
  apply MeasureTheory.integrable_finset_sum
  intro round _
  exact (hintegrable _).mul_const _

/-- Residual correlation commutes with an integrable signed coefficient
representation of a feature family. -/
theorem multiaccuracyCorrelation_signedMeasureCoefficientPairIntegral
    {X Ω : Type*} {horizon : ℕ} [MeasurableSpace Ω]
    (coefficient : SignedMeasureCoefficientPair Ω) (basis : Ω → X → ℝ)
    (forecasts : ForecastSequence X horizon)
    (contexts : Fin horizon → X) (outcomes : Fin horizon → Bool)
    (hpositive : ∀ point,
      MeasureTheory.Integrable (fun omega => basis omega point) coefficient.positive)
    (hnegative : ∀ point,
      MeasureTheory.Integrable (fun omega => basis omega point) coefficient.negative) :
    multiaccuracyCorrelation
      (fun point => signedMeasureCoefficientPairIntegral coefficient
        (fun omega => basis omega point)) forecasts contexts outcomes =
      signedMeasureCoefficientPairIntegral coefficient
        (fun omega => multiaccuracyCorrelation (basis omega) forecasts contexts outcomes) := by
  unfold multiaccuracyCorrelation signedMeasureCoefficientPairIntegral
  have hpositiveSum :
      (∫ omega, ∑ round,
          basis omega (contexts round) *
            forecastResidual forecasts contexts outcomes round
          ∂coefficient.positive) =
        ∑ round, (∫ omega, basis omega (contexts round) ∂coefficient.positive) *
          forecastResidual forecasts contexts outcomes round := by
        rw [MeasureTheory.integral_finset_sum]
        · apply Finset.sum_congr rfl
          intro round _
          rw [MeasureTheory.integral_mul_const]
        · intro round _
          exact (hpositive _).mul_const _
  have hnegativeSum :
      (∫ omega, ∑ round,
          basis omega (contexts round) *
            forecastResidual forecasts contexts outcomes round
          ∂coefficient.negative) =
        ∑ round, (∫ omega, basis omega (contexts round) ∂coefficient.negative) *
          forecastResidual forecasts contexts outcomes round := by
        rw [MeasureTheory.integral_finset_sum]
        · apply Finset.sum_congr rfl
          intro round _
          rw [MeasureTheory.integral_mul_const]
        · intro round _
          exact (hnegative _).mul_const _
  rw [hpositiveSum, hnegativeSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro round _
  ring

/-- A pointwise approximation transfers to a finite-horizon residual
correlation. -/
theorem abs_multiaccuracyCorrelation_sub_le_of_forall_abs_sub_le
    {X : Type*} {horizon : ℕ} (left right : X → ℝ)
    (forecasts : ForecastSequence X horizon) (contexts : Fin horizon → X)
    (outcomes : Fin horizon → Bool) (epsilon : ℝ)
    (hpoint : ∀ point, |left point - right point| ≤ epsilon)
    (hresidual : ∀ round, |forecastResidual forecasts contexts outcomes round| ≤ 1)
    (hepsilon : 0 ≤ epsilon) :
    |multiaccuracyCorrelation left forecasts contexts outcomes -
      multiaccuracyCorrelation right forecasts contexts outcomes| ≤ epsilon * horizon := by
  unfold multiaccuracyCorrelation
  calc
    |(∑ round, left (contexts round) * forecastResidual forecasts contexts outcomes round) -
        ∑ round, right (contexts round) * forecastResidual forecasts contexts outcomes round| =
        |∑ round, (left (contexts round) - right (contexts round)) *
          forecastResidual forecasts contexts outcomes round| := by
          congr 1
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro round _
          ring
    _ ≤ ∑ round, |(left (contexts round) - right (contexts round)) *
        forecastResidual forecasts contexts outcomes round| :=
      Finset.abs_sum_le_sum_abs _ Finset.univ
    _ ≤ ∑ _round : Fin horizon, epsilon := by
      apply Finset.sum_le_sum
      intro round _
      rw [abs_mul]
      calc
        |left (contexts round) - right (contexts round)| *
            |forecastResidual forecasts contexts outcomes round| ≤
            epsilon * |forecastResidual forecasts contexts outcomes round| :=
          mul_le_mul_of_nonneg_right (hpoint _) (abs_nonneg _)
        _ ≤ epsilon * 1 :=
          mul_le_mul_of_nonneg_left (hresidual round) hepsilon
        _ = epsilon := by ring
    _ = epsilon * horizon := by
      simp [nsmul_eq_mul]
      ring

/-- Measure-spanned feature classes inherit a uniform residual-correlation
bound from their coordinate family.  This is the finite-horizon half of
OKK25 Lemma 4.13. -/
theorem abs_multiaccuracyCorrelation_le_of_isMeasureSpanned
    {X Ω : Type*} {horizon : ℕ} [MeasurableSpace Ω]
    {targetClass : Set (X → ℝ)} {basis : Ω → X → ℝ}
    {forecasts : ForecastSequence X horizon} {contexts : Fin horizon → X}
    {outcomes : Fin horizon → Bool} {target : X → ℝ}
    {epsilon coefficientNorm bound : ℝ}
    (hspanned : IsMeasureSpanned targetClass basis epsilon coefficientNorm)
    (htarget : target ∈ targetClass)
    (hresidual : ∀ round, |forecastResidual forecasts contexts outcomes round| ≤ 1)
    (hbasis : ∀ omega,
      |multiaccuracyCorrelation (basis omega) forecasts contexts outcomes| ≤ bound)
    (hepsilon : 0 ≤ epsilon) (hbound : 0 ≤ bound) :
    |multiaccuracyCorrelation target forecasts contexts outcomes| ≤
      coefficientNorm * bound + epsilon * horizon := by
  rcases hspanned target htarget with ⟨coefficient, hmass, hpositive, hnegative, happrox⟩
  let approximation : X → ℝ := fun point =>
    signedMeasureCoefficientPairIntegral coefficient (fun omega => basis omega point)
  have hpositiveCorrelation := integrable_multiaccuracyCorrelation_of_integrableCoordinates
    basis forecasts contexts outcomes coefficient.positive hpositive
  have hnegativeCorrelation := integrable_multiaccuracyCorrelation_of_integrableCoordinates
    basis forecasts contexts outcomes coefficient.negative hnegative
  have happroximation : ∀ point, |target point - approximation point| ≤ epsilon := happrox
  have happroximationCorrelation :=
    abs_multiaccuracyCorrelation_sub_le_of_forall_abs_sub_le target approximation forecasts
      contexts outcomes epsilon happroximation hresidual hepsilon
  have hcoordinateCorrelation :
      multiaccuracyCorrelation approximation forecasts contexts outcomes =
        signedMeasureCoefficientPairIntegral coefficient
          (fun omega => multiaccuracyCorrelation (basis omega) forecasts contexts outcomes) := by
    exact multiaccuracyCorrelation_signedMeasureCoefficientPairIntegral coefficient basis
      forecasts contexts outcomes hpositive hnegative
  have hcombination :
      |multiaccuracyCorrelation approximation forecasts contexts outcomes| ≤
        coefficientNorm * bound := by
    rw [hcoordinateCorrelation]
    calc
      |signedMeasureCoefficientPairIntegral coefficient
          (fun omega => multiaccuracyCorrelation (basis omega) forecasts contexts outcomes)| ≤
          bound * signedMeasureCoefficientPairMass coefficient :=
        abs_signedMeasureCoefficientPairIntegral_le_of_forall_abs_le coefficient
          (fun omega => multiaccuracyCorrelation (basis omega) forecasts contexts outcomes)
          bound hpositiveCorrelation hnegativeCorrelation hbasis
      _ = signedMeasureCoefficientPairMass coefficient * bound := by ring
      _ ≤ coefficientNorm * bound := mul_le_mul_of_nonneg_right hmass hbound
  calc
    |multiaccuracyCorrelation target forecasts contexts outcomes| ≤
        |multiaccuracyCorrelation target forecasts contexts outcomes -
          multiaccuracyCorrelation approximation forecasts contexts outcomes| +
        |multiaccuracyCorrelation approximation forecasts contexts outcomes| :=
      by
        simpa using abs_sub_le
          (multiaccuracyCorrelation target forecasts contexts outcomes)
          (multiaccuracyCorrelation approximation forecasts contexts outcomes) 0
    _ ≤ epsilon * horizon + coefficientNorm * bound :=
      add_le_add happroximationCorrelation hcombination
    _ = coefficientNorm * bound + epsilon * horizon := by ring

/-- A pointwise finite linear combination of real-valued functions. -/
def finiteLinearCombination {Γ : Type*} {n : ℕ}
    (coefficient : Fin n → ℝ) (basis : Fin n → Γ → ℝ) : Γ → ℝ :=
  fun x => ∑ i, coefficient i * basis i x

/-- `basis` is an `ε`-approximate basis for `target`, with at most `sparsity`
terms and `ℓ₁` coefficient norm at most `coefficientNorm`.  The individual
coefficient bound is included because it is part of the source definition,
although the transfer theorem below only needs the `ℓ₁` bound. -/
def IsFiniteApproximateBasis {Γ : Type*}
    (target basisClass : Set (Γ → ℝ)) (epsilon : ℝ)
    (sparsity : ℕ) (coefficientNorm : ℝ) : Prop :=
  ∀ targetFunction ∈ target, ∃ (n : ℕ) (basis : Fin n → Γ → ℝ)
    (coefficient : Fin n → ℝ), n ≤ sparsity ∧
      (∀ i, basis i ∈ basisClass) ∧
      (∀ i, |coefficient i| ≤ 1) ∧
      (∑ i, |coefficient i|) ≤ coefficientNorm ∧
      ∀ x, |targetFunction x - finiteLinearCombination coefficient basis x| ≤ epsilon

/-- A finite approximate basis with a separately controlled affine intercept.
Unlike `IsFixedFiniteAffineApproximateBasis`, the finite coordinate family may
depend on the target function.  This is the natural interface after a
report-side coordinate family is composed with an arbitrary hypothesis class:
the selected hypothesis fixes the coordinates used for that approximation. -/
def IsFiniteAffineApproximateBasis {Γ : Type*}
    (target basisClass : Set (Γ → ℝ)) (epsilon : ℝ)
    (sparsity : ℕ) (interceptNorm coefficientNorm : ℝ) : Prop :=
  ∀ targetFunction ∈ target, ∃ (n : ℕ) (basis : Fin n → Γ → ℝ)
    (intercept : ℝ) (coefficient : Fin n → ℝ), n ≤ sparsity ∧
      (∀ i, basis i ∈ basisClass) ∧
      |intercept| ≤ interceptNorm ∧
      (∀ i, |coefficient i| ≤ 1) ∧
      (∑ i, |coefficient i|) ≤ coefficientNorm ∧
      ∀ x, |targetFunction x -
        (intercept + finiteLinearCombination coefficient basis x)| ≤ epsilon

/-- Affine approximate-basis guarantees are preserved when the target class
is restricted and the permitted nonconstant coordinate class is enlarged. -/
theorem IsFiniteAffineApproximateBasis.mono
    {Γ : Type*} {target target' basisClass basisClass' : Set (Γ → ℝ)}
    {epsilon interceptNorm coefficientNorm : ℝ} {sparsity : ℕ}
    (happrox : IsFiniteAffineApproximateBasis
      target basisClass epsilon sparsity interceptNorm coefficientNorm)
    (htarget : target' ⊆ target) (hbasis : basisClass ⊆ basisClass') :
    IsFiniteAffineApproximateBasis
      target' basisClass' epsilon sparsity interceptNorm coefficientNorm := by
  intro targetFunction htargetFunction
  rcases happrox targetFunction (htarget htargetFunction) with
    ⟨n, basis, intercept, coefficient, hsparsity, hbasisMembership, hintercept,
      hcoefficient, hnorm, herror⟩
  exact ⟨n, basis, intercept, coefficient, hsparsity,
    fun index => hbasis (hbasisMembership index), hintercept, hcoefficient, hnorm, herror⟩

/-- Approximate-basis guarantees are preserved when the target class is
restricted and the permitted basis class is enlarged. -/
theorem IsFiniteApproximateBasis.mono
    {Γ : Type*} {target target' basisClass basisClass' : Set (Γ → ℝ)}
    {epsilon coefficientNorm : ℝ} {sparsity : ℕ}
    (happrox : IsFiniteApproximateBasis target basisClass epsilon sparsity coefficientNorm)
    (htarget : target' ⊆ target) (hbasis : basisClass ⊆ basisClass') :
    IsFiniteApproximateBasis target' basisClass' epsilon sparsity coefficientNorm := by
  intro targetFunction htargetFunction
  rcases happrox targetFunction (htarget htargetFunction) with
    ⟨n, basis, coefficient, hsparsity, hbasisMembership, hcoefficient, hnorm, herror⟩
  exact ⟨n, basis, coefficient, hsparsity,
    fun index => hbasis (hbasisMembership index), hcoefficient,
    hnorm, herror⟩

/-- Postcompose a real-valued function class with a class of maps. -/
def functionClassPostcompose {Γ₀ Γ₁ : Type*}
    (functions : Set (Γ₁ → ℝ)) (maps : Set (Γ₀ → Γ₁)) : Set (Γ₀ → ℝ) :=
  { composite | ∃ function ∈ functions, ∃ map ∈ maps,
    composite = fun x => function (map x) }

/-- Pointwise differences of two functions from a common class. -/
def functionDifferenceClass {Γ : Type*} (functions : Set (Γ → ℝ)) : Set (Γ → ℝ) :=
  { difference | ∃ positive ∈ functions, ∃ negative ∈ functions,
    difference = fun point => positive point - negative point }

/-- Pointwise sums of functions from two classes.  This is the natural target
class when a multiscale approximation represents an interval as the sum of
its disjoint dyadic pieces. -/
def functionSumClass {Γ : Type*} (left right : Set (Γ → ℝ)) : Set (Γ → ℝ) :=
  { total | ∃ leftFunction ∈ left, ∃ rightFunction ∈ right,
    total = fun point => leftFunction point + rightFunction point }

/--
A fixed finite coordinate family is an approximate basis when every target has
one coefficient vector over those same coordinates.  This is stronger data
than `IsFiniteApproximateBasis`, whose finite support may depend on the
target.  It is the form used when a paper says that a finite set `G` itself is
the basis.
-/
def IsFixedFiniteApproximateBasis {Γ : Type*} {dimension : ℕ}
    (target : Set (Γ → ℝ)) (basis : Fin dimension → Γ → ℝ)
    (epsilon coefficientNorm : ℝ) : Prop :=
  ∀ function ∈ target, ∃ coefficient : Fin dimension → ℝ,
    (∀ index, |coefficient index| ≤ 1) ∧
    (∑ index, |coefficient index|) ≤ coefficientNorm ∧
    ∀ point, |function point -
      finiteLinearCombination coefficient basis point| ≤ epsilon

/-- The source-paper notion of a finite uniform approximate basis.  Unlike
`IsFixedFiniteApproximateBasis`, it imposes no coefficient or coefficient-mass
bound: it records precisely a common finite family of `[-1,1]` coordinates
whose unrestricted linear span uniformly approximates every target.  This is
the appropriate interface for approximate dimension; algorithms that charge
coefficient mass should use the stronger controlled interface above. -/
def IsFixedFiniteUniformApproximateBasis {Γ : Type*} {dimension : ℕ}
    (target : Set (Γ → ℝ)) (basis : Fin dimension → Γ → ℝ) (epsilon : ℝ) : Prop :=
  (∀ index point, |basis index point| ≤ 1) ∧
  ∀ function ∈ target, ∃ coefficient : Fin dimension → ℝ,
    ∀ point, |function point - finiteLinearCombination coefficient basis point| ≤ epsilon

/-- The affine form of the source-paper uniform approximate-basis notion.
The intercept is intentionally unrestricted, matching definitions that write
`r₀ + Σᵢ rᵢ sᵢ` separately from the bounded coordinate family. -/
def IsFixedFiniteAffineUniformApproximateBasis {Γ : Type*} {dimension : ℕ}
    (target : Set (Γ → ℝ)) (basis : Fin dimension → Γ → ℝ) (epsilon : ℝ) : Prop :=
  (∀ index point, |basis index point| ≤ 1) ∧
  ∀ function ∈ target, ∃ intercept : ℝ, ∃ coefficient : Fin dimension → ℝ,
    ∀ point, |function point -
      (intercept + finiteLinearCombination coefficient basis point)| ≤ epsilon

/-- A homogeneous uniform approximate basis is an affine one with zero
intercept. -/
theorem IsFixedFiniteUniformApproximateBasis.toAffine
    {Γ : Type*} {dimension : ℕ} {target : Set (Γ → ℝ)}
    {basis : Fin dimension → Γ → ℝ} {epsilon : ℝ}
    (happrox : IsFixedFiniteUniformApproximateBasis target basis epsilon) :
    IsFixedFiniteAffineUniformApproximateBasis target basis epsilon := by
  rcases happrox with ⟨hbounded, hspan⟩
  refine ⟨hbounded, ?_⟩
  intro function hfunction
  rcases hspan function hfunction with ⟨coefficient, herror⟩
  exact ⟨0, coefficient, by simpa using herror⟩

/--
An affine variant of a fixed finite approximate basis.  Some approximation
results state a free constant intercept separately from the listed basis
coordinates.  Keeping it explicit prevents an accidental use of such a
result as a homogeneous basis theorem when the source basis functions all
vanish at a common point.

When the intercept has magnitude at most one, a later theorem adds the
constant-one function as one ordinary coordinate and returns the paper's
homogeneous `IsFixedFiniteApproximateBasis` interface.
-/
def IsFixedFiniteAffineApproximateBasis {Γ : Type*} {dimension : ℕ}
    (target : Set (Γ → ℝ)) (basis : Fin dimension → Γ → ℝ)
    (epsilon interceptNorm coefficientNorm : ℝ) : Prop :=
  ∀ function ∈ target, ∃ (intercept : ℝ) (coefficient : Fin dimension → ℝ),
    |intercept| ≤ interceptNorm ∧
      (∀ index, |coefficient index| ≤ 1) ∧
      (∑ index, |coefficient index|) ≤ coefficientNorm ∧
      ∀ point, |function point -
        (intercept + finiteLinearCombination coefficient basis point)| ≤ epsilon

/-- A fixed affine approximation whose intercept is genuinely free, but whose
nonconstant coefficients have a uniform `ℓ₁` budget.  This is the natural
interface for source results that write an unrestricted affine offset
separately from a controlled linear expansion. -/
def IsFixedFiniteAffineL1ApproximateBasis {Γ : Type*} {dimension : ℕ}
    (target : Set (Γ → ℝ)) (basis : Fin dimension → Γ → ℝ)
    (epsilon coefficientNorm : ℝ) : Prop :=
  ∀ function ∈ target, ∃ (intercept : ℝ) (coefficient : Fin dimension → ℝ),
    (∑ index, |coefficient index|) ≤ coefficientNorm ∧
      ∀ point, |function point -
        (intercept + finiteLinearCombination coefficient basis point)| ≤ epsilon

/-- Forgetting the individual-coordinate and intercept bounds retains the
free-intercept `ℓ₁` approximation data. -/
theorem IsFixedFiniteAffineApproximateBasis.toL1
    {Γ : Type*} {dimension : ℕ} {target : Set (Γ → ℝ)}
    {basis : Fin dimension → Γ → ℝ} {epsilon interceptNorm coefficientNorm : ℝ}
    (happrox : IsFixedFiniteAffineApproximateBasis
      target basis epsilon interceptNorm coefficientNorm) :
    IsFixedFiniteAffineL1ApproximateBasis target basis epsilon coefficientNorm := by
  intro function hfunction
  rcases happrox function hfunction with
    ⟨intercept, coefficient, _hintercept, _hcoordinate, hnorm, herror⟩
  exact ⟨intercept, coefficient, hnorm, herror⟩

/-- A free-intercept, coefficient-controlled affine approximation may be composed with a
common uniform approximation of each of its coordinates.  The inner basis
uses unrestricted coefficients, while the outer `ℓ₁` budget controls how its
coordinatewise errors accumulate.  This is the standard bridge from an
approximate ReLU family to an affine Taylor expansion of convex functions. -/
theorem isFixedFiniteAffineL1ApproximateBasis_compose_isFixedFiniteUniformApproximateBasis
    {Γ : Type*} {outerDimension innerDimension : ℕ}
    (target : Set (Γ → ℝ))
    (outerBasis : Fin outerDimension → Γ → ℝ)
    (innerBasis : Fin innerDimension → Γ → ℝ)
    (outerError coefficientNorm innerError : ℝ)
    (houter : IsFixedFiniteAffineL1ApproximateBasis
      target outerBasis outerError coefficientNorm)
    (hinner : IsFixedFiniteUniformApproximateBasis
      (Set.range outerBasis) innerBasis innerError)
    (hinnerNonnegative : 0 ≤ innerError) :
    IsFixedFiniteAffineUniformApproximateBasis target innerBasis
      (outerError + coefficientNorm * innerError) := by
  classical
  rcases hinner with ⟨hinnerBounded, hinnerSpan⟩
  refine ⟨hinnerBounded, ?_⟩
  intro targetFunction htargetFunction
  rcases houter targetFunction htargetFunction with
    ⟨intercept, outerCoefficient, houterNorm, houterApproximation⟩
  have hcoordinateApproximation : ∀ outerCoordinate,
      ∃ innerCoefficient : Fin innerDimension → ℝ, ∀ point,
        |outerBasis outerCoordinate point -
          finiteLinearCombination innerCoefficient innerBasis point| ≤ innerError := by
    intro outerCoordinate
    exact hinnerSpan (outerBasis outerCoordinate) (Set.mem_range_self outerCoordinate)
  choose innerCoefficient hinnerApproximation using hcoordinateApproximation
  refine ⟨intercept, fun innerCoordinate =>
    ∑ outerCoordinate, outerCoefficient outerCoordinate *
      innerCoefficient outerCoordinate innerCoordinate, ?_⟩
  intro point
  have hcombination :
      finiteLinearCombination
          (fun innerCoordinate => ∑ outerCoordinate,
            outerCoefficient outerCoordinate *
              innerCoefficient outerCoordinate innerCoordinate)
          innerBasis point =
        ∑ outerCoordinate, outerCoefficient outerCoordinate *
          finiteLinearCombination (innerCoefficient outerCoordinate) innerBasis point := by
    unfold finiteLinearCombination
    calc
      (∑ innerCoordinate,
          (∑ outerCoordinate,
            outerCoefficient outerCoordinate *
              innerCoefficient outerCoordinate innerCoordinate) *
            innerBasis innerCoordinate point) =
          ∑ innerCoordinate, ∑ outerCoordinate,
            (outerCoefficient outerCoordinate *
              innerCoefficient outerCoordinate innerCoordinate) *
              innerBasis innerCoordinate point := by
            apply Finset.sum_congr rfl
            intro innerCoordinate _
            rw [Finset.sum_mul]
      _ = ∑ outerCoordinate, ∑ innerCoordinate,
          (outerCoefficient outerCoordinate *
            innerCoefficient outerCoordinate innerCoordinate) *
            innerBasis innerCoordinate point := by
          rw [Finset.sum_comm]
      _ = ∑ outerCoordinate, outerCoefficient outerCoordinate *
          finiteLinearCombination (innerCoefficient outerCoordinate) innerBasis point := by
          apply Finset.sum_congr rfl
          intro outerCoordinate _
          unfold finiteLinearCombination
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro innerCoordinate _
          ring
  rw [hcombination]
  have hcoordinateError :
      |(∑ outerCoordinate,
          outerCoefficient outerCoordinate * outerBasis outerCoordinate point) -
          ∑ outerCoordinate, outerCoefficient outerCoordinate *
            finiteLinearCombination (innerCoefficient outerCoordinate) innerBasis point| ≤
        coefficientNorm * innerError := by
    calc
      |(∑ outerCoordinate,
          outerCoefficient outerCoordinate * outerBasis outerCoordinate point) -
          ∑ outerCoordinate, outerCoefficient outerCoordinate *
            finiteLinearCombination (innerCoefficient outerCoordinate) innerBasis point| =
          |∑ outerCoordinate, outerCoefficient outerCoordinate *
            (outerBasis outerCoordinate point -
              finiteLinearCombination (innerCoefficient outerCoordinate) innerBasis point)| := by
            congr 1
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro outerCoordinate _
            ring
      _ ≤ ∑ outerCoordinate,
          |outerCoefficient outerCoordinate| *
            |outerBasis outerCoordinate point -
              finiteLinearCombination (innerCoefficient outerCoordinate) innerBasis point| := by
            calc
              _ ≤ ∑ outerCoordinate,
                |outerCoefficient outerCoordinate *
                  (outerBasis outerCoordinate point -
                    finiteLinearCombination (innerCoefficient outerCoordinate) innerBasis point)| :=
                Finset.abs_sum_le_sum_abs _ Finset.univ
              _ = _ := by
                apply Finset.sum_congr rfl
                intro outerCoordinate _
                rw [abs_mul]
      _ ≤ ∑ outerCoordinate, |outerCoefficient outerCoordinate| * innerError := by
        apply Finset.sum_le_sum
        intro outerCoordinate _
        exact mul_le_mul_of_nonneg_left
          (hinnerApproximation outerCoordinate point)
          (abs_nonneg _)
      _ = (∑ outerCoordinate, |outerCoefficient outerCoordinate|) * innerError := by
        rw [Finset.sum_mul]
      _ ≤ coefficientNorm * innerError :=
        mul_le_mul_of_nonneg_right houterNorm hinnerNonnegative
  have houterCombination :
      finiteLinearCombination outerCoefficient outerBasis point =
        ∑ outerCoordinate, outerCoefficient outerCoordinate * outerBasis outerCoordinate point := by
    rfl
  have houterApproximationAt := houterApproximation point
  rw [houterCombination] at houterApproximationAt
  calc
    |targetFunction point -
        (intercept + ∑ outerCoordinate, outerCoefficient outerCoordinate *
          finiteLinearCombination (innerCoefficient outerCoordinate) innerBasis point)| ≤
        |targetFunction point -
          (intercept + ∑ outerCoordinate, outerCoefficient outerCoordinate *
            outerBasis outerCoordinate point)| +
          |(intercept + ∑ outerCoordinate, outerCoefficient outerCoordinate *
            outerBasis outerCoordinate point) -
            (intercept + ∑ outerCoordinate, outerCoefficient outerCoordinate *
              finiteLinearCombination (innerCoefficient outerCoordinate) innerBasis point)| :=
      abs_sub_le _ _ _
    _ ≤ outerError + coefficientNorm * innerError := by
      apply add_le_add houterApproximationAt
      simpa only [add_sub_add_left_eq_sub] using hcoordinateError

/-- The bounded-intercept affine interface is a special case of the
free-intercept composition rule. -/
theorem isFixedFiniteAffineApproximateBasis_compose_isFixedFiniteUniformApproximateBasis
    {Γ : Type*} {outerDimension innerDimension : ℕ}
    (target : Set (Γ → ℝ))
    (outerBasis : Fin outerDimension → Γ → ℝ)
    (innerBasis : Fin innerDimension → Γ → ℝ)
    (outerError interceptNorm coefficientNorm innerError : ℝ)
    (houter : IsFixedFiniteAffineApproximateBasis
      target outerBasis outerError interceptNorm coefficientNorm)
    (hinner : IsFixedFiniteUniformApproximateBasis
      (Set.range outerBasis) innerBasis innerError)
    (hinnerNonnegative : 0 ≤ innerError) :
    IsFixedFiniteAffineUniformApproximateBasis target innerBasis
      (outerError + coefficientNorm * innerError) := by
  exact isFixedFiniteAffineL1ApproximateBasis_compose_isFixedFiniteUniformApproximateBasis
    target outerBasis innerBasis outerError coefficientNorm innerError houter.toL1 hinner
    hinnerNonnegative

/-- With one common coordinate family, errors add under pointwise sums while
the unrestricted source-paper coefficients simply add.  This is the
combination rule used after a dyadic interval decomposition; no coordinate
duplication or artificial coefficient bound is introduced. -/
theorem functionSumClass_isFixedFiniteUniformApproximateBasis_of_commonCoordinates
    {Γ : Type*} {dimension : ℕ}
    (leftFunctions rightFunctions : Set (Γ → ℝ))
    (basis : Fin dimension → Γ → ℝ) (leftError rightError : ℝ)
    (hleft : IsFixedFiniteUniformApproximateBasis leftFunctions basis leftError)
    (hright : IsFixedFiniteUniformApproximateBasis rightFunctions basis rightError) :
    IsFixedFiniteUniformApproximateBasis (functionSumClass leftFunctions rightFunctions)
      basis (leftError + rightError) := by
  rcases hleft with ⟨hbounded, hleft⟩
  rcases hright with ⟨_hrightBounded, hright⟩
  refine ⟨hbounded, ?_⟩
  intro total htotal
  rcases htotal with ⟨leftFunction, hleftFunction, rightFunction, hrightFunction, rfl⟩
  rcases hleft leftFunction hleftFunction with ⟨leftCoefficient, hleftError⟩
  rcases hright rightFunction hrightFunction with ⟨rightCoefficient, hrightError⟩
  refine ⟨leftCoefficient + rightCoefficient, ?_⟩
  intro point
  have hcombination : finiteLinearCombination (leftCoefficient + rightCoefficient) basis point =
      finiteLinearCombination leftCoefficient basis point +
        finiteLinearCombination rightCoefficient basis point := by
    unfold finiteLinearCombination
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [hcombination]
  calc
    |(leftFunction point + rightFunction point) -
        (finiteLinearCombination leftCoefficient basis point +
          finiteLinearCombination rightCoefficient basis point)| =
        |(leftFunction point - finiteLinearCombination leftCoefficient basis point) +
          (rightFunction point - finiteLinearCombination rightCoefficient basis point)| := by
        congr 1
        ring
    _ ≤ |leftFunction point - finiteLinearCombination leftCoefficient basis point| +
        |rightFunction point - finiteLinearCombination rightCoefficient basis point| :=
      abs_add_le _ _
    _ ≤ leftError + rightError := add_le_add (hleftError point) (hrightError point)

/-- A common uniform approximate basis also approximates any finite sum of
target functions.  This is the list form of the two-function combination
rule: the coordinate family stays fixed, its unrestricted coefficient vectors
add, and the pointwise errors add once per summand. -/
theorem exists_finiteLinearCombination_approximation_list_sum
    {Γ : Type*} {dimension : ℕ} {target : Set (Γ → ℝ)}
    {basis : Fin dimension → Γ → ℝ} {epsilon : ℝ}
    (happrox : IsFixedFiniteUniformApproximateBasis target basis epsilon)
    (functions : List (Γ → ℝ))
    (hmembership : ∀ function ∈ functions, function ∈ target) :
    ∃ coefficient : Fin dimension → ℝ, ∀ point,
      |(functions.map fun function => function point).sum -
        finiteLinearCombination coefficient basis point| ≤ functions.length * epsilon := by
  rcases happrox with ⟨_hbounded, hspan⟩
  induction functions with
  | nil =>
      refine ⟨fun _ => 0, ?_⟩
      intro point
      simp [finiteLinearCombination]
  | cons function functions ih =>
      rcases hspan function (hmembership function (by simp)) with
        ⟨functionCoefficient, hfunctionApproximation⟩
      have htailMembership : ∀ remaining ∈ functions, remaining ∈ target := by
        intro remaining hremaining
        exact hmembership remaining (by simp [hremaining])
      rcases ih htailMembership with ⟨tailCoefficient, htailApproximation⟩
      refine ⟨functionCoefficient + tailCoefficient, ?_⟩
      intro point
      have hcombination :
          finiteLinearCombination (functionCoefficient + tailCoefficient) basis point =
            finiteLinearCombination functionCoefficient basis point +
              finiteLinearCombination tailCoefficient basis point := by
        unfold finiteLinearCombination
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      rw [hcombination]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        |(function point + (functions.map fun remaining => remaining point).sum) -
            (finiteLinearCombination functionCoefficient basis point +
              finiteLinearCombination tailCoefficient basis point)| =
            |(function point - finiteLinearCombination functionCoefficient basis point) +
              ((functions.map fun remaining => remaining point).sum -
                finiteLinearCombination tailCoefficient basis point)| := by
              congr 1
              ring
        _ ≤ |function point - finiteLinearCombination functionCoefficient basis point| +
            |(functions.map fun remaining => remaining point).sum -
              finiteLinearCombination tailCoefficient basis point| :=
          abs_add_le _ _
        _ ≤ epsilon + functions.length * epsilon :=
          add_le_add (hfunctionApproximation point) (htailApproximation point)
        _ = ((functions.length : ℝ) + 1) * epsilon := by
          ring
        _ = ((↑(functions.length + 1) : ℝ) * epsilon) := by
          rw [Nat.cast_add, Nat.cast_one]

/-- A tagged union of two finite coordinate families uniformly approximates
the union of their target classes.  This is the dimension-preserving step for
adjoining sparse coordinates to a multiscale approximate basis. -/
theorem union_isFixedFiniteUniformApproximateBasis
    {Γ : Type*} {leftDimension rightDimension : ℕ}
    (leftFunctions rightFunctions : Set (Γ → ℝ))
    (leftBasis : Fin leftDimension → Γ → ℝ)
    (rightBasis : Fin rightDimension → Γ → ℝ)
    (leftError rightError : ℝ)
    (hleft : IsFixedFiniteUniformApproximateBasis leftFunctions leftBasis leftError)
    (hright : IsFixedFiniteUniformApproximateBasis rightFunctions rightBasis rightError) :
    IsFixedFiniteUniformApproximateBasis (leftFunctions ∪ rightFunctions)
      (Fin.addCases leftBasis rightBasis) (max leftError rightError) := by
  rcases hleft with ⟨hleftBounded, hleft⟩
  rcases hright with ⟨hrightBounded, hright⟩
  refine ⟨?_, ?_⟩
  · intro index point
    refine Fin.addCases (fun coordinate => ?_) (fun coordinate => ?_) index
    · change |Fin.addCases (motive := fun _ => Γ → ℝ) leftBasis rightBasis
        (Fin.castAdd rightDimension coordinate) point| ≤ 1
      rw [Fin.addCases_left]
      exact hleftBounded coordinate point
    · change |Fin.addCases (motive := fun _ => Γ → ℝ) leftBasis rightBasis
        (Fin.natAdd leftDimension coordinate) point| ≤ 1
      rw [Fin.addCases_right]
      exact hrightBounded coordinate point
  · intro function hfunction
    rcases hfunction with hfunction | hfunction
    · rcases hleft function hfunction with ⟨coefficient, herror⟩
      refine ⟨Fin.addCases coefficient (fun _ => 0), ?_⟩
      intro point
      have hcombination : finiteLinearCombination
          (Fin.addCases coefficient (fun _ => 0))
          (Fin.addCases leftBasis rightBasis) point =
          finiteLinearCombination coefficient leftBasis point := by
        unfold finiteLinearCombination
        rw [Fin.sum_univ_add]
        simp
      rw [hcombination]
      exact (herror point).trans (le_max_left _ _)
    · rcases hright function hfunction with ⟨coefficient, herror⟩
      refine ⟨Fin.addCases (fun _ => 0) coefficient, ?_⟩
      intro point
      have hcombination : finiteLinearCombination
          (Fin.addCases (fun _ => 0) coefficient)
          (Fin.addCases leftBasis rightBasis) point =
          finiteLinearCombination coefficient rightBasis point := by
        unfold finiteLinearCombination
        rw [Fin.sum_univ_add]
        simp
      rw [hcombination]
      exact (herror point).trans (le_max_right _ _)

/-- Combining two fixed coordinate families approximates pointwise sums of
their target classes.  The tagged `Fin.addCases` coordinates preserve the
individual coefficient bound while their error and coefficient mass add. -/
theorem functionSumClass_isFixedFiniteApproximateBasis
    {Γ : Type*} {leftDimension rightDimension : ℕ}
    (leftFunctions rightFunctions : Set (Γ → ℝ))
    (leftBasis : Fin leftDimension → Γ → ℝ)
    (rightBasis : Fin rightDimension → Γ → ℝ)
    (leftError rightError leftCoefficientNorm rightCoefficientNorm : ℝ)
    (hleft : IsFixedFiniteApproximateBasis
      leftFunctions leftBasis leftError leftCoefficientNorm)
    (hright : IsFixedFiniteApproximateBasis
      rightFunctions rightBasis rightError rightCoefficientNorm) :
    IsFixedFiniteApproximateBasis (functionSumClass leftFunctions rightFunctions)
      (Fin.addCases leftBasis rightBasis)
      (leftError + rightError) (leftCoefficientNorm + rightCoefficientNorm) := by
  intro total htotal
  rcases htotal with ⟨leftFunction, hleftFunction, rightFunction, hrightFunction, rfl⟩
  rcases hleft leftFunction hleftFunction with
    ⟨leftCoefficient, hleftCoefficient, hleftNorm, hleftApproximation⟩
  rcases hright rightFunction hrightFunction with
    ⟨rightCoefficient, hrightCoefficient, hrightNorm, hrightApproximation⟩
  refine ⟨Fin.addCases leftCoefficient rightCoefficient, ?_, ?_, ?_⟩
  · intro index
    refine Fin.addCases (fun coordinate => ?_) (fun coordinate => ?_) index
    · change |Fin.addCases (motive := fun _ => ℝ) leftCoefficient rightCoefficient
        (Fin.castAdd rightDimension coordinate)| ≤ 1
      rw [Fin.addCases_left]
      exact hleftCoefficient coordinate
    · change |Fin.addCases (motive := fun _ => ℝ) leftCoefficient rightCoefficient
        (Fin.natAdd leftDimension coordinate)| ≤ 1
      rw [Fin.addCases_right]
      exact hrightCoefficient coordinate
  · rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    exact add_le_add hleftNorm hrightNorm
  · intro point
    have hcombination : finiteLinearCombination
        (Fin.addCases leftCoefficient rightCoefficient)
        (Fin.addCases leftBasis rightBasis) point =
        finiteLinearCombination leftCoefficient leftBasis point +
          finiteLinearCombination rightCoefficient rightBasis point := by
      unfold finiteLinearCombination
      rw [Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right]
    rw [hcombination]
    calc
      |(leftFunction point + rightFunction point) -
          (finiteLinearCombination leftCoefficient leftBasis point +
            finiteLinearCombination rightCoefficient rightBasis point)| =
          |(leftFunction point - finiteLinearCombination leftCoefficient leftBasis point) +
            (rightFunction point - finiteLinearCombination rightCoefficient rightBasis point)| := by
          congr 1
          ring
      _ ≤ |leftFunction point - finiteLinearCombination leftCoefficient leftBasis point| +
          |rightFunction point - finiteLinearCombination rightCoefficient rightBasis point| :=
        abs_add_le _ _
      _ ≤ leftError + rightError :=
        add_le_add (hleftApproximation point) (hrightApproximation point)

/-- Forgetting that a fixed coordinate family is shared by all target
functions yields the ordinary finite approximate-basis interface. -/
theorem IsFixedFiniteApproximateBasis.toFinite
    {Γ : Type*} {dimension : ℕ} {target : Set (Γ → ℝ)}
    {basis : Fin dimension → Γ → ℝ} {epsilon coefficientNorm : ℝ}
    (happrox : IsFixedFiniteApproximateBasis target basis epsilon coefficientNorm) :
    IsFiniteApproximateBasis target (Set.range basis) epsilon dimension coefficientNorm := by
  intro function hfunction
  rcases happrox function hfunction with ⟨coefficient, hcoefficient, hnorm, herror⟩
  refine ⟨dimension, basis, coefficient, le_rfl, ?_, hcoefficient, hnorm, herror⟩
  intro index
  exact Set.mem_range_self index

/-- Forgetting that an affine coordinate family is shared by every target
yields the variable-finite affine interface. -/
theorem IsFixedFiniteAffineApproximateBasis.toFiniteAffine
    {Γ : Type*} {dimension : ℕ} {target : Set (Γ → ℝ)}
    {basis : Fin dimension → Γ → ℝ} {epsilon interceptNorm coefficientNorm : ℝ}
    (happrox : IsFixedFiniteAffineApproximateBasis
      target basis epsilon interceptNorm coefficientNorm) :
    IsFiniteAffineApproximateBasis target (Set.range basis)
      epsilon dimension interceptNorm coefficientNorm := by
  intro function hfunction
  rcases happrox function hfunction with
    ⟨intercept, coefficient, hintercept, hcoefficient, hnorm, herror⟩
  exact ⟨dimension, basis, intercept, coefficient, le_rfl,
    fun index => Set.mem_range_self index, hintercept, hcoefficient, hnorm, herror⟩

/-- An affine fixed basis with a unit-bounded intercept becomes a homogeneous
fixed basis after adjoining the constant-one coordinate. -/
theorem isFixedFiniteApproximateBasis_of_affine
    {Γ : Type*} {dimension : ℕ} (target : Set (Γ → ℝ))
    (basis : Fin dimension → Γ → ℝ) (epsilon interceptNorm coefficientNorm : ℝ)
    (hinterceptNorm : interceptNorm ≤ 1)
    (happrox : IsFixedFiniteAffineApproximateBasis target basis epsilon interceptNorm coefficientNorm) :
    IsFixedFiniteApproximateBasis target
      (Fin.cons (fun _ : Γ => 1) basis) epsilon (interceptNorm + coefficientNorm) := by
  intro function hfunction
  rcases happrox function hfunction with
    ⟨intercept, coefficient, hintercept, hcoefficient, hnorm, herror⟩
  refine ⟨Fin.cons intercept coefficient, ?_, ?_, ?_⟩
  · intro index
    refine Fin.cases ?_ (fun coordinate => ?_) index
    · simpa using hintercept.trans hinterceptNorm
    · simpa using hcoefficient coordinate
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    exact add_le_add hintercept hnorm
  · intro point
    have hcombination : finiteLinearCombination (Fin.cons intercept coefficient)
        (Fin.cons (fun _ : Γ => 1) basis) point =
        intercept + finiteLinearCombination coefficient basis point := by
      unfold finiteLinearCombination
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring
    rw [hcombination]
    exact herror point

/-- A report-independent bounded loss whose discrete derivative is the
constant-one calibration weight.  It is proper because every report has the
same Bernoulli risk. -/
noncomputable def constantOneDerivativeProperLoss : BinaryLoss :=
  fun _ outcome => if outcome then (1 / 2 : ℝ) else -(1 / 2 : ℝ)

theorem constantOneDerivativeProperLoss_isProper :
    IsProperBinaryLoss constantOneDerivativeProperLoss := by
  intro truth report htruth hreport
  unfold bernoulliRisk constantOneDerivativeProperLoss
  simp

theorem constantOneDerivativeProperLoss_isUnitBounded :
    IsUnitBoundedBinaryLoss constantOneDerivativeProperLoss := by
  intro report hreport outcome
  constructor
  · cases outcome <;> norm_num [constantOneDerivativeProperLoss]
  · cases outcome <;> norm_num [constantOneDerivativeProperLoss]

theorem discreteDerivative_constantOneDerivativeProperLoss (report : ℝ) :
    discreteDerivative constantOneDerivativeProperLoss report = 1 := by
  simp [discreteDerivative, constantOneDerivativeProperLoss]
  norm_num

/-- The constant-one weight is one of the bounded proper-calibration tests. -/
theorem constantOne_mem_properDerivativeClass :
    (fun _ : ℝ => 1) ∈ properDerivativeClass := by
  refine ⟨constantOneDerivativeProperLoss, constantOneDerivativeProperLoss_isProper,
    constantOneDerivativeProperLoss_isUnitBounded, ?_⟩
  funext report
  exact (discreteDerivative_constantOneDerivativeProperLoss report).symm

/-- Proper calibration controls the constant-one feature without any OWAL
call.  This is useful when a cited affine approximation theorem has a free
intercept and the algorithm learns only the nonconstant coordinates. -/
theorem multiaccuracyCorrelation_constantOne_abs_le_of_calibration
    {X : Type*} {horizon : ℕ} (forecasts : ForecastSequence X horizon)
    (contexts : Fin horizon → X) (outcomes : Fin horizon → Bool) (bound : ℝ)
    (hcalibration : CalibrationBound properDerivativeClass forecasts contexts outcomes bound) :
    |multiaccuracyCorrelation (fun _ : X => 1) forecasts contexts outcomes| ≤ bound := by
  simpa only [multiaccuracyCorrelation, calibrationCorrelation] using
    hcalibration (fun _ : ℝ => 1) constantOne_mem_properDerivativeClass

/-- Adjoining the constant-one feature preserves a common multiaccuracy bound
when that feature is already controlled by proper calibration. -/
theorem multiaccuracyBound_finCons_constantOne_of_calibration
    {X : Type*} {horizon dimension : ℕ} (basis : Fin dimension → X → ℝ)
    (forecasts : ForecastSequence X horizon) (contexts : Fin horizon → X)
    (outcomes : Fin horizon → Bool) (bound : ℝ)
    (hcalibration : CalibrationBound properDerivativeClass forecasts contexts outcomes bound)
    (hbasis : MultiaccuracyBound (Set.range basis) forecasts contexts outcomes bound) :
    MultiaccuracyBound (Set.range (Fin.cons (fun _ : X => 1) basis))
      forecasts contexts outcomes bound := by
  intro test htest
  rcases htest with ⟨index, rfl⟩
  refine Fin.cases ?_ (fun coordinate => ?_) index
  · exact multiaccuracyCorrelation_constantOne_abs_le_of_calibration
      forecasts contexts outcomes bound hcalibration
  · exact hbasis (basis coordinate) (Set.mem_range_self coordinate)

/-- Two tagged copies of an affine coordinate family approximate the
difference class while retaining individual coefficient bounds.  The affine
intercept remains explicit, so its norm doubles separately. -/
theorem functionDifferenceClass_isFixedFiniteAffineApproximateBasis_of_commonCoordinates
    {Γ : Type*} {dimension : ℕ} (functions : Set (Γ → ℝ))
    (basis : Fin dimension → Γ → ℝ) (epsilon interceptNorm coefficientNorm : ℝ)
    (happrox : IsFixedFiniteAffineApproximateBasis
      functions basis epsilon interceptNorm coefficientNorm) :
    IsFixedFiniteAffineApproximateBasis (functionDifferenceClass functions)
      (Fin.addCases basis basis) (2 * epsilon) (2 * interceptNorm) (2 * coefficientNorm) := by
  intro difference hdifference
  rcases hdifference with ⟨positive, hpositive, negative, hnegative, rfl⟩
  rcases happrox positive hpositive with
    ⟨positiveIntercept, positiveCoefficient, hpositiveIntercept,
      hpositiveCoefficient, hpositiveNorm, hpositiveError⟩
  rcases happrox negative hnegative with
    ⟨negativeIntercept, negativeCoefficient, hnegativeIntercept,
      hnegativeCoefficient, hnegativeNorm, hnegativeError⟩
  refine ⟨positiveIntercept - negativeIntercept,
    Fin.addCases positiveCoefficient (fun coordinate => -negativeCoefficient coordinate), ?_, ?_, ?_, ?_⟩
  · calc
      |positiveIntercept - negativeIntercept| ≤
          |positiveIntercept - 0| + |0 - negativeIntercept| := abs_sub_le _ _ _
      _ = |positiveIntercept| + |negativeIntercept| := by
        rw [sub_zero, zero_sub, abs_neg]
      _ ≤ interceptNorm + interceptNorm := add_le_add hpositiveIntercept hnegativeIntercept
      _ = 2 * interceptNorm := by ring
  · intro index
    refine Fin.addCases (fun coordinate => ?_) (fun coordinate => ?_) index
    · change |Fin.addCases (motive := fun _ => ℝ) positiveCoefficient
        (fun coordinate => -negativeCoefficient coordinate)
        (Fin.castAdd dimension coordinate)| ≤ 1
      rw [Fin.addCases_left]
      exact hpositiveCoefficient coordinate
    · change |Fin.addCases (motive := fun _ => ℝ) positiveCoefficient
        (fun coordinate => -negativeCoefficient coordinate)
        (Fin.natAdd dimension coordinate)| ≤ 1
      rw [Fin.addCases_right]
      simpa using hnegativeCoefficient coordinate
  · rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, abs_neg]
    calc
      (∑ index, |positiveCoefficient index|) +
          ∑ index, |negativeCoefficient index| ≤ coefficientNorm + coefficientNorm :=
        add_le_add hpositiveNorm hnegativeNorm
      _ = 2 * coefficientNorm := by ring
  · intro point
    have hcombination : finiteLinearCombination
        (Fin.addCases positiveCoefficient (fun coordinate => -negativeCoefficient coordinate))
        (Fin.addCases basis basis) point =
        finiteLinearCombination positiveCoefficient basis point -
          finiteLinearCombination negativeCoefficient basis point := by
      unfold finiteLinearCombination
      rw [Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right, neg_mul,
        Finset.sum_neg_distrib]
      ring
    rw [hcombination]
    calc
      |(positive point - negative point) -
          ((positiveIntercept - negativeIntercept) +
            (finiteLinearCombination positiveCoefficient basis point -
              finiteLinearCombination negativeCoefficient basis point))| =
          |(positive point - (positiveIntercept +
              finiteLinearCombination positiveCoefficient basis point)) -
            (negative point - (negativeIntercept +
              finiteLinearCombination negativeCoefficient basis point))| := by
            congr 1
            ring
      _ ≤ |(positive point - (positiveIntercept +
          finiteLinearCombination positiveCoefficient basis point)) - 0| +
          |0 - (negative point - (negativeIntercept +
            finiteLinearCombination negativeCoefficient basis point))| := abs_sub_le _ _ _
      _ = |positive point - (positiveIntercept +
          finiteLinearCombination positiveCoefficient basis point)| +
          |negative point - (negativeIntercept +
            finiteLinearCombination negativeCoefficient basis point)| := by
        rw [sub_zero, zero_sub, abs_neg]
      _ ≤ epsilon + epsilon := add_le_add (hpositiveError point) (hnegativeError point)
      _ = 2 * epsilon := by ring

/--
If one fixed finite coordinate family approximates a class, then two copies of
that family approximate its pointwise difference class.  The duplication is
necessary to preserve the standard individual coefficient bound `|cᵢ| ≤ 1`:
subtracting two admissible coefficients can otherwise have magnitude two.
-/
theorem functionDifferenceClass_isFiniteApproximateBasis_of_commonCoordinates
    {Γ : Type*} {dimension : ℕ} (functions : Set (Γ → ℝ))
    (basis : Fin dimension → Γ → ℝ) (epsilon coefficientNorm : ℝ)
    (happrox : IsFixedFiniteApproximateBasis functions basis epsilon coefficientNorm) :
    IsFiniteApproximateBasis (functionDifferenceClass functions) (Set.range basis)
      (2 * epsilon) (dimension + dimension) (2 * coefficientNorm) := by
  intro difference hdifference
  rcases hdifference with ⟨positive, hpositive, negative, hnegative, rfl⟩
  rcases happrox positive hpositive with
    ⟨positiveCoefficient, hpositiveCoefficient, hpositiveNorm, hpositiveError⟩
  rcases happrox negative hnegative with
    ⟨negativeCoefficient, hnegativeCoefficient, hnegativeNorm, hnegativeError⟩
  refine ⟨dimension + dimension,
    Fin.addCases basis basis,
    Fin.addCases positiveCoefficient (fun index => -negativeCoefficient index),
    le_rfl, ?_, ?_, ?_, ?_⟩
  · intro index
    refine Fin.addCases (fun coordinate => ?_) (fun coordinate => ?_) index
    · change Fin.addCases basis basis (Fin.castAdd dimension coordinate) ∈ Set.range basis
      rw [Fin.addCases_left]
      exact Set.mem_range_self coordinate
    · change Fin.addCases basis basis (Fin.natAdd dimension coordinate) ∈ Set.range basis
      rw [Fin.addCases_right]
      exact Set.mem_range_self coordinate
  · intro index
    refine Fin.addCases (fun coordinate => ?_) (fun coordinate => ?_) index
    · change |Fin.addCases (motive := fun _ => ℝ) positiveCoefficient
        (fun coordinate => -negativeCoefficient coordinate)
        (Fin.castAdd dimension coordinate)| ≤ 1
      rw [Fin.addCases_left]
      exact hpositiveCoefficient coordinate
    · change |Fin.addCases (motive := fun _ => ℝ) positiveCoefficient
        (fun coordinate => -negativeCoefficient coordinate)
        (Fin.natAdd dimension coordinate)| ≤ 1
      rw [Fin.addCases_right]
      simpa using hnegativeCoefficient coordinate
  · rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, abs_neg]
    calc
      (∑ index, |positiveCoefficient index|) +
          ∑ index, |negativeCoefficient index| ≤
          coefficientNorm + coefficientNorm :=
        add_le_add hpositiveNorm hnegativeNorm
      _ = 2 * coefficientNorm := by ring
  · intro point
    have hcombination :
        finiteLinearCombination
          (Fin.addCases positiveCoefficient (fun index => -negativeCoefficient index))
          (Fin.addCases basis basis) point =
          finiteLinearCombination positiveCoefficient basis point -
            finiteLinearCombination negativeCoefficient basis point := by
      unfold finiteLinearCombination
      rw [Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right, neg_mul,
        Finset.sum_neg_distrib]
      ring
    rw [hcombination]
    calc
      |(positive point - negative point) -
          (finiteLinearCombination positiveCoefficient basis point -
            finiteLinearCombination negativeCoefficient basis point)| =
          |(positive point - finiteLinearCombination positiveCoefficient basis point) -
            (negative point - finiteLinearCombination negativeCoefficient basis point)| := by
            congr 1
            ring
      _ ≤ |positive point - finiteLinearCombination positiveCoefficient basis point| +
          |negative point - finiteLinearCombination negativeCoefficient basis point| :=
            by
              calc
                _ ≤ |(positive point - finiteLinearCombination positiveCoefficient basis point) - 0| +
                    |0 - (negative point - finiteLinearCombination negativeCoefficient basis point)| :=
                  abs_sub_le _ _ _
                _ = |positive point - finiteLinearCombination positiveCoefficient basis point| +
                    |negative point - finiteLinearCombination negativeCoefficient basis point| := by
                      rw [sub_zero, zero_sub, abs_neg]
      _ ≤ epsilon + epsilon :=
        add_le_add (hpositiveError point) (hnegativeError point)
      _ = 2 * epsilon := by ring

/-- Finite approximate bases are preserved when both the target and basis
functions are postcomposed with the same map class (OKK25 Lemma 4.10). -/
theorem finiteApproximateBasis_postcompose
    {Γ₀ Γ₁ : Type*} {target basisClass : Set (Γ₁ → ℝ)}
    {maps : Set (Γ₀ → Γ₁)} {epsilon coefficientNorm : ℝ} {sparsity : ℕ}
    (happrox : IsFiniteApproximateBasis target basisClass epsilon sparsity coefficientNorm) :
    IsFiniteApproximateBasis (functionClassPostcompose target maps)
      (functionClassPostcompose basisClass maps) epsilon sparsity coefficientNorm := by
  intro targetFunction htarget
  rcases htarget with ⟨function, hfunction, map, hmap, rfl⟩
  rcases happrox function hfunction with
    ⟨n, basis, coefficient, hn, hbasis, hcoefficient, hnorm, herror⟩
  refine ⟨n, fun i x => basis i (map x), coefficient, hn, ?_, hcoefficient, hnorm, ?_⟩
  · intro i
    exact ⟨basis i, hbasis i, map, hmap, rfl⟩
  · intro x
    simpa [finiteLinearCombination] using herror (map x)

/-- Affine finite approximate bases are preserved when target and coordinate
functions are postcomposed with a common map class.  The affine intercept is
unchanged, while the chosen map determines the finite coordinate family. -/
theorem finiteAffineApproximateBasis_postcompose
    {Γ₀ Γ₁ : Type*} {target basisClass : Set (Γ₁ → ℝ)}
    {maps : Set (Γ₀ → Γ₁)} {epsilon interceptNorm coefficientNorm : ℝ}
    {sparsity : ℕ}
    (happrox : IsFiniteAffineApproximateBasis
      target basisClass epsilon sparsity interceptNorm coefficientNorm) :
    IsFiniteAffineApproximateBasis
      (functionClassPostcompose target maps)
      (functionClassPostcompose basisClass maps)
      epsilon sparsity interceptNorm coefficientNorm := by
  intro targetFunction htarget
  rcases htarget with ⟨function, hfunction, map, hmap, rfl⟩
  rcases happrox function hfunction with
    ⟨n, basis, intercept, coefficient, hn, hbasis, hintercept,
      hcoefficient, hnorm, herror⟩
  refine ⟨n, fun index point => basis index (map point), intercept, coefficient,
    hn, ?_, hintercept, hcoefficient, hnorm, ?_⟩
  · intro index
    exact ⟨basis index, hbasis index, map, hmap, rfl⟩
  · intro point
    simpa [finiteLinearCombination] using herror (map point)

/-- Residual correlation is linear in a finite combination of feature tests. -/
theorem multiaccuracyCorrelation_finiteLinearCombination
    {X : Type*} {horizon n : ℕ} (coefficient : Fin n → ℝ)
    (basis : Fin n → X → ℝ) (forecasts : ForecastSequence X horizon)
    (contexts : Fin horizon → X) (outcomes : Fin horizon → Bool) :
    multiaccuracyCorrelation (finiteLinearCombination coefficient basis)
      forecasts contexts outcomes =
      ∑ i, coefficient i * multiaccuracyCorrelation (basis i) forecasts contexts outcomes := by
  unfold multiaccuracyCorrelation finiteLinearCombination
  calc
    (∑ round, (∑ i, coefficient i * basis i (contexts round)) *
        forecastResidual forecasts contexts outcomes round) =
        ∑ round, ∑ i, (coefficient i * basis i (contexts round)) *
          forecastResidual forecasts contexts outcomes round := by
      apply Finset.sum_congr rfl
      intro round _
      rw [Finset.sum_mul]
    _ = ∑ i, ∑ round, (coefficient i * basis i (contexts round)) *
          forecastResidual forecasts contexts outcomes round := Finset.sum_comm
    _ = ∑ i, coefficient i * ∑ round, basis i (contexts round) *
          forecastResidual forecasts contexts outcomes round := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro round _
      ring

/-- The correlation of an approximated test decomposes into the correlation of
its finite linear approximation plus its pointwise residual. -/
theorem multiaccuracyCorrelation_eq_linearCombination_add_error
    {X : Type*} {horizon n : ℕ} (target : X → ℝ)
    (coefficient : Fin n → ℝ) (basis : Fin n → X → ℝ)
    (forecasts : ForecastSequence X horizon) (contexts : Fin horizon → X)
    (outcomes : Fin horizon → Bool) :
    multiaccuracyCorrelation target forecasts contexts outcomes =
      (∑ i, coefficient i * multiaccuracyCorrelation (basis i) forecasts contexts outcomes) +
        ∑ round, (target (contexts round) -
          finiteLinearCombination coefficient basis (contexts round)) *
          forecastResidual forecasts contexts outcomes round := by
  let approximation := finiteLinearCombination coefficient basis
  have hsplit :
      multiaccuracyCorrelation target forecasts contexts outcomes =
        multiaccuracyCorrelation approximation forecasts contexts outcomes +
          ∑ round, (target (contexts round) - approximation (contexts round)) *
            forecastResidual forecasts contexts outcomes round := by
    unfold multiaccuracyCorrelation
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro round _
    dsimp [approximation]
    ring
  rw [hsplit, multiaccuracyCorrelation_finiteLinearCombination]

/-- Transfer a multiaccuracy bound through one finite approximate-basis
representation.  This is the finite-horizon algebra of OKK25 Lemma 4.11;
the theorem is stated pointwise so it remains useful for arbitrary function
classes. -/
theorem abs_multiaccuracyCorrelation_le_of_finiteApproximation
    {X : Type*} {horizon n : ℕ} {target : X → ℝ}
    {coefficient : Fin n → ℝ} {basis : Fin n → X → ℝ}
    {forecasts : ForecastSequence X horizon} {contexts : Fin horizon → X}
    {outcomes : Fin horizon → Bool} {epsilon coefficientNorm bound : ℝ}
    (hcoefficientNorm : (∑ i, |coefficient i|) ≤ coefficientNorm)
    (happroximation : ∀ x,
      |target x - finiteLinearCombination coefficient basis x| ≤ epsilon)
    (hresidual : ∀ round, |forecastResidual forecasts contexts outcomes round| ≤ 1)
    (hbasis : ∀ i,
      |multiaccuracyCorrelation (basis i) forecasts contexts outcomes| ≤ bound)
    (hepsilon : 0 ≤ epsilon) (hbound : 0 ≤ bound) :
    |multiaccuracyCorrelation target forecasts contexts outcomes| ≤
      coefficientNorm * bound + epsilon * horizon := by
  rw [multiaccuracyCorrelation_eq_linearCombination_add_error]
  calc
    |(∑ i, coefficient i * multiaccuracyCorrelation (basis i) forecasts contexts outcomes) +
        ∑ round, (target (contexts round) -
          finiteLinearCombination coefficient basis (contexts round)) *
          forecastResidual forecasts contexts outcomes round| ≤
        |∑ i, coefficient i * multiaccuracyCorrelation (basis i) forecasts contexts outcomes| +
          |∑ round, (target (contexts round) -
            finiteLinearCombination coefficient basis (contexts round)) *
            forecastResidual forecasts contexts outcomes round| := abs_add_le _ _
    _ ≤ (∑ i, |coefficient i| *
          |multiaccuracyCorrelation (basis i) forecasts contexts outcomes|) +
        ∑ round, |(target (contexts round) -
          finiteLinearCombination coefficient basis (contexts round)) *
          forecastResidual forecasts contexts outcomes round| := by
      gcongr
      · simpa using Finset.abs_sum_le_sum_abs
          (fun i : Fin n => coefficient i *
            multiaccuracyCorrelation (basis i) forecasts contexts outcomes) Finset.univ
      · simpa using Finset.abs_sum_le_sum_abs
          (fun round : Fin horizon =>
            (target (contexts round) - finiteLinearCombination coefficient basis (contexts round)) *
              forecastResidual forecasts contexts outcomes round) Finset.univ
    _ ≤ (∑ i, |coefficient i| * bound) + ∑ _round : Fin horizon, epsilon := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hbasis i) (abs_nonneg _)
      · apply Finset.sum_le_sum
        intro round _
        rw [abs_mul]
        calc
          |target (contexts round) - finiteLinearCombination coefficient basis (contexts round)| *
              |forecastResidual forecasts contexts outcomes round| ≤
              epsilon * |forecastResidual forecasts contexts outcomes round| :=
            mul_le_mul_of_nonneg_right (happroximation (contexts round)) (abs_nonneg _)
          _ ≤ epsilon * 1 :=
            mul_le_mul_of_nonneg_left (hresidual round) hepsilon
          _ = epsilon := by ring
    _ ≤ coefficientNorm * bound + epsilon * horizon := by
      have hlinear : (∑ i, |coefficient i| * bound) =
          (∑ i, |coefficient i|) * bound := by
        rw [Finset.sum_mul]
      rw [hlinear]
      have hcoeffBound : (∑ i, |coefficient i|) * bound ≤ coefficientNorm * bound :=
        mul_le_mul_of_nonneg_right hcoefficientNorm hbound
      have hsumEpsilon : (∑ _round : Fin horizon, epsilon) = epsilon * horizon := by
        simp [nsmul_eq_mul]
        ring
      rw [hsumEpsilon]
      exact add_le_add hcoeffBound le_rfl

/-- Multiaccuracy transfers through a fixed affine approximation when the
constant coordinate and every nonconstant coordinate share one correlation
bound.  Unlike a homogeneous approximate basis, no individual bound on the
affine intercept is needed for this analytic transfer. -/
theorem abs_multiaccuracyCorrelation_le_of_fixedAffineApproximation
    {X : Type*} {horizon dimension : ℕ} {targetClass : Set (X → ℝ)}
    {basis : Fin dimension → X → ℝ} {forecasts : ForecastSequence X horizon}
    {contexts : Fin horizon → X} {outcomes : Fin horizon → Bool}
    {target : X → ℝ} {epsilon interceptNorm coefficientNorm bound : ℝ}
    (happrox : IsFixedFiniteAffineApproximateBasis
      targetClass basis epsilon interceptNorm coefficientNorm)
    (htarget : target ∈ targetClass)
    (hresidual : ∀ round, |forecastResidual forecasts contexts outcomes round| ≤ 1)
    (hconstant : |multiaccuracyCorrelation (fun _ : X => 1) forecasts contexts outcomes| ≤ bound)
    (hbasis : ∀ index,
      |multiaccuracyCorrelation (basis index) forecasts contexts outcomes| ≤ bound)
    (hepsilon : 0 ≤ epsilon) (hbound : 0 ≤ bound) :
    |multiaccuracyCorrelation target forecasts contexts outcomes| ≤
      (interceptNorm + coefficientNorm) * bound + epsilon * horizon := by
  rcases happrox target htarget with
    ⟨intercept, coefficient, hintercept, _hcoefficient, hcoefficientNorm, hrepresentation⟩
  have haugmentedNorm : (∑ index, |Fin.cons intercept coefficient index|) ≤
      interceptNorm + coefficientNorm := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    exact add_le_add hintercept hcoefficientNorm
  have haugmentedRepresentation : ∀ point,
      |target point - finiteLinearCombination (Fin.cons intercept coefficient)
        (Fin.cons (fun _ : X => 1) basis) point| ≤ epsilon := by
    intro point
    have hcombination : finiteLinearCombination (Fin.cons intercept coefficient)
        (Fin.cons (fun _ : X => 1) basis) point =
        intercept + finiteLinearCombination coefficient basis point := by
      unfold finiteLinearCombination
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring
    rw [hcombination]
    exact hrepresentation point
  have haugmentedBasis : ∀ index,
      |multiaccuracyCorrelation
          ((Fin.cons (α := fun _ => X → ℝ) (fun _ => 1) basis) index)
          forecasts contexts outcomes| ≤ bound := by
    intro index
    refine Fin.cases ?_ (fun coordinate => ?_) index
    · simpa using hconstant
    · simpa using hbasis coordinate
  exact abs_multiaccuracyCorrelation_le_of_finiteApproximation haugmentedNorm
    haugmentedRepresentation hresidual haugmentedBasis hepsilon hbound

/-- Multiaccuracy transfers through a variable finite affine approximation.
The constant term is controlled by calibration, while every selected
nonconstant coordinate is controlled by the supplied coordinate class. -/
theorem abs_multiaccuracyCorrelation_le_of_finiteAffineApproximation
    {X : Type*} {horizon sparsity : ℕ} {targetClass basisClass : Set (X → ℝ)}
    {forecasts : ForecastSequence X horizon} {contexts : Fin horizon → X}
    {outcomes : Fin horizon → Bool} {target : X → ℝ}
    {epsilon interceptNorm coefficientNorm bound : ℝ}
    (happrox : IsFiniteAffineApproximateBasis
      targetClass basisClass epsilon sparsity interceptNorm coefficientNorm)
    (htarget : target ∈ targetClass)
    (hresidual : ∀ round, |forecastResidual forecasts contexts outcomes round| ≤ 1)
    (hconstant : |multiaccuracyCorrelation (fun _ : X => 1) forecasts contexts outcomes| ≤ bound)
    (hbasis : MultiaccuracyBound basisClass forecasts contexts outcomes bound)
    (hepsilon : 0 ≤ epsilon) (hbound : 0 ≤ bound) :
    |multiaccuracyCorrelation target forecasts contexts outcomes| ≤
      (interceptNorm + coefficientNorm) * bound + epsilon * horizon := by
  rcases happrox target htarget with
    ⟨n, basis, intercept, coefficient, _hn, hbasisMembership, hintercept,
      _hcoefficient, hcoefficientNorm, hrepresentation⟩
  have haugmentedNorm : (∑ index, |Fin.cons intercept coefficient index|) ≤
      interceptNorm + coefficientNorm := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    exact add_le_add hintercept hcoefficientNorm
  have haugmentedRepresentation : ∀ point,
      |target point - finiteLinearCombination (Fin.cons intercept coefficient)
        (Fin.cons (fun _ : X => 1) basis) point| ≤ epsilon := by
    intro point
    have hcombination : finiteLinearCombination (Fin.cons intercept coefficient)
        (Fin.cons (fun _ : X => 1) basis) point =
        intercept + finiteLinearCombination coefficient basis point := by
      unfold finiteLinearCombination
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring
    rw [hcombination]
    exact hrepresentation point
  have haugmentedBasis : ∀ index,
      |multiaccuracyCorrelation
          ((Fin.cons (α := fun _ => X → ℝ) (fun _ => 1) basis) index)
          forecasts contexts outcomes| ≤ bound := by
    intro index
    refine Fin.cases ?_ (fun coordinate => ?_) index
    · simpa using hconstant
    · simpa using hbasis (basis coordinate) (hbasisMembership coordinate)
  exact abs_multiaccuracyCorrelation_le_of_finiteApproximation haugmentedNorm
    haugmentedRepresentation hresidual haugmentedBasis hepsilon hbound

/-- Multiaccuracy transfers from a finite approximate basis to its target
class, with the source's `coefficientNorm * basisError + epsilon * T` loss.
This is the pointwise conclusion of OKK25 Lemma 4.11. -/
theorem abs_multiaccuracyCorrelation_le_of_finiteApproximateBasis
    {X : Type*} {horizon sparsity : ℕ} {targetClass basisClass : Set (X → ℝ)}
    {forecasts : ForecastSequence X horizon} {contexts : Fin horizon → X}
    {outcomes : Fin horizon → Bool} {target : X → ℝ}
    {epsilon coefficientNorm bound : ℝ}
    (happrox : IsFiniteApproximateBasis targetClass basisClass epsilon sparsity coefficientNorm)
    (htarget : target ∈ targetClass)
    (hresidual : ∀ round, |forecastResidual forecasts contexts outcomes round| ≤ 1)
    (hbasis : MultiaccuracyBound basisClass forecasts contexts outcomes bound)
    (hepsilon : 0 ≤ epsilon) (hbound : 0 ≤ bound) :
    |multiaccuracyCorrelation target forecasts contexts outcomes| ≤
      coefficientNorm * bound + epsilon * horizon := by
  rcases happrox target htarget with
    ⟨n, basis, coefficient, _hn, hbasisMembership, _hcoefficient, hcoefficientNorm,
      hrepresentation⟩
  exact abs_multiaccuracyCorrelation_le_of_finiteApproximation hcoefficientNorm
    hrepresentation hresidual
    (fun i => hbasis (basis i) (hbasisMembership i)) hepsilon hbound

/-- Combine proper calibration with multiaccuracy transferred through a
finite approximate basis.  This is the reusable finite-basis omniprediction
reduction: the basis contributes exactly `coefficientNorm * basisError +
epsilon * horizon` to the pairwise regret bound. -/
theorem omniPairRegret_le_calibration_add_finiteApproximateBasis
    {X : Type*} {horizon sparsity : ℕ} (losses : Set BinaryLoss)
    (postprocess : BinaryLoss → ℝ → ℝ) (hypotheses : Set (X → ℝ))
    (basisClass : Set (X → ℝ))
    (forecasts : ForecastSequence X horizon) (contexts : Fin horizon → X)
    (outcomes : Fin horizon → Bool) (calibrationBound epsilon coefficientNorm basisError : ℝ)
    (happrox : IsFiniteApproximateBasis
      (derivativeHypothesisClass losses hypotheses) basisClass epsilon sparsity coefficientNorm)
    (hbayes : ∀ loss ∈ losses, IsBayesPostprocessor loss (postprocess loss))
    (hbounded : ∀ loss ∈ losses, IsUnitBoundedBinaryLoss loss)
    (hforecasts : ForecastsInUnitInterval forecasts contexts)
    (hhypotheses : ∀ hypothesis ∈ hypotheses, HypothesisInUnitInterval hypothesis)
    (hcalibration : CalibrationBound properDerivativeClass
      forecasts contexts outcomes calibrationBound)
    (hbasis : MultiaccuracyBound basisClass forecasts contexts outcomes basisError)
    (hepsilon : 0 ≤ epsilon) (hbasisError : 0 ≤ basisError)
    {loss : BinaryLoss} (hloss : loss ∈ losses)
    {hypothesis : X → ℝ} (hhypothesis : hypothesis ∈ hypotheses) :
    omniPairRegret loss (postprocess loss) hypothesis forecasts contexts outcomes ≤
      calibrationBound + coefficientNorm * basisError + epsilon * horizon := by
  have hmultiaccuracy : MultiaccuracyBound (derivativeHypothesisClass losses hypotheses)
      forecasts contexts outcomes (coefficientNorm * basisError + epsilon * horizon) := by
    intro target htarget
    exact abs_multiaccuracyCorrelation_le_of_finiteApproximateBasis happrox htarget
      (forecastResidual_abs_le_one forecasts contexts outcomes hforecasts)
      hbasis hepsilon hbasisError
  have hpostprocessedCalibration : CalibrationBound
      (postprocessedDerivativeClass losses postprocess) forecasts contexts outcomes calibrationBound := by
    intro weight hweight
    rcases hweight with ⟨sourceLoss, hsourceLoss, rfl⟩
    apply hcalibration
    exact ⟨postprocessedLoss sourceLoss (postprocess sourceLoss),
      postprocessedLoss_isProper (hbayes sourceLoss hsourceLoss),
      postprocessedLoss_isUnitBounded (hbounded sourceLoss hsourceLoss)
        (hbayes sourceLoss hsourceLoss), rfl⟩
  exact (omniPairRegret_le_calibration_add_multiaccuracy hloss hhypothesis
    (hbayes loss hloss) hforecasts (hhypotheses hypothesis hhypothesis)
    hpostprocessedCalibration hmultiaccuracy).trans_eq (by ring)

/-- Exact finite-grid threshold basis for a function with source-scale range
and total variation at most two.  The constant threshold is duplicated so
that every coefficient obeys the source's individual `[-1,1]` restriction;
the resulting coefficient norm is at most three.  This is the discrete core
of the repaired bounded-variation threshold construction. -/
theorem finiteGrid_isFiniteApproximateBasis_of_range_and_variation
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ)
    (hbounded : ∀ level, |values level| ≤ 2)
    (hvariation :
      (∑ level : Fin gridSize, |values level.succ - values level.castSucc|) ≤ 2) :
    IsFiniteApproximateBasis ({values} : Set (Fin (gridSize + 1) → ℝ))
      (Set.range (duplicatedZeroFiniteThresholdBasis (gridSize := gridSize)))
      0 (gridSize + 2) 3 := by
  intro target htarget
  rw [Set.mem_singleton_iff] at htarget
  subst target
  refine ⟨gridSize + 2, duplicatedZeroFiniteThresholdBasis,
    duplicatedZeroFiniteThresholdBasisCoefficients values, le_rfl, ?_, ?_, ?_, ?_⟩
  · intro coordinate
    exact ⟨coordinate, rfl⟩
  · intro coordinate
    exact abs_duplicatedZeroFiniteThresholdBasisCoefficients_le_one values
      hbounded hvariation coordinate
  · exact sum_abs_duplicatedZeroFiniteThresholdBasisCoefficients_le_three values
      hbounded hvariation
  · intro report
    have hrepresentation := duplicatedZeroFiniteThresholdBasis_evaluation_eq values
    have hevaluation : finiteLinearCombination
        (duplicatedZeroFiniteThresholdBasisCoefficients values)
        duplicatedZeroFiniteThresholdBasis = finiteThresholdBasisEvaluation values := by
      simpa only [finiteLinearCombination] using hrepresentation
    rw [hevaluation, finiteThresholdBasisEvaluation_eq]
    simp

/-- A pointwise rounding map turns the corrected finite-grid threshold basis
into an approximate basis on any domain.  This isolates the only analytic
step in a Lipschitz or bounded-variation threshold construction: exhibiting
a grid value within the desired pointwise error. -/
theorem roundedFiniteGrid_isFiniteApproximateBasis_of_range_and_variation
    {Γ : Type*} {gridSize : ℕ} (target : Γ → ℝ)
    (round : Γ → Fin (gridSize + 1)) (values : Fin (gridSize + 1) → ℝ)
    (epsilon : ℝ)
    (hrounding : ∀ point, |target point - values (round point)| ≤ epsilon)
    (hbounded : ∀ level, |values level| ≤ 2)
    (hvariation :
      (∑ level : Fin gridSize, |values level.succ - values level.castSucc|) ≤ 2) :
    IsFiniteApproximateBasis ({target} : Set (Γ → ℝ))
      (Set.range (fun coordinate point =>
        duplicatedZeroFiniteThresholdBasis coordinate (round point)))
      epsilon (gridSize + 2) 3 := by
  intro function hfunction
  rw [Set.mem_singleton_iff] at hfunction
  subst function
  let basis : Fin (gridSize + 2) → Γ → ℝ := fun coordinate point =>
    duplicatedZeroFiniteThresholdBasis coordinate (round point)
  refine ⟨gridSize + 2, basis, duplicatedZeroFiniteThresholdBasisCoefficients values,
    le_rfl, ?_, ?_, ?_, ?_⟩
  · intro coordinate
    exact ⟨coordinate, rfl⟩
  · intro coordinate
    exact abs_duplicatedZeroFiniteThresholdBasisCoefficients_le_one values
      hbounded hvariation coordinate
  · exact sum_abs_duplicatedZeroFiniteThresholdBasisCoefficients_le_three values
      hbounded hvariation
  · intro point
    have hrepresentation := duplicatedZeroFiniteThresholdBasis_evaluation_eq values
    have hevaluation : finiteLinearCombination
        (duplicatedZeroFiniteThresholdBasisCoefficients values)
        duplicatedZeroFiniteThresholdBasis = finiteThresholdBasisEvaluation values := by
      simpa only [finiteLinearCombination] using hrepresentation
    have hrounded : finiteLinearCombination
        (duplicatedZeroFiniteThresholdBasisCoefficients values) basis point =
        values (round point) := by
      rw [show finiteLinearCombination
          (duplicatedZeroFiniteThresholdBasisCoefficients values) basis point =
          finiteLinearCombination
            (duplicatedZeroFiniteThresholdBasisCoefficients values)
            duplicatedZeroFiniteThresholdBasis (round point) by
              rfl]
      rw [hevaluation, finiteThresholdBasisEvaluation_eq]
    rw [hrounded]
    exact hrounding point

/-- Passing from losses to discrete derivatives doubles a uniform
approximation error, while retaining the same finite combination and
coefficient norm.  This is the corrected form of the transformation used in
OKK25's online-to-batch proof. -/
theorem finiteApproximateBasis_uncurriedDiscreteDerivative
    {losses basisLosses : Set BinaryLoss} {epsilon coefficientNorm : ℝ}
    {sparsity : ℕ}
    (happrox : IsFiniteApproximateBasis (uncurriedBinaryLossClass losses)
      (uncurriedBinaryLossClass basisLosses) epsilon sparsity coefficientNorm) :
    IsFiniteApproximateBasis
      (uncurriedDerivativeClass (uncurriedBinaryLossClass losses))
      (uncurriedDerivativeClass (uncurriedBinaryLossClass basisLosses))
      (2 * epsilon) sparsity coefficientNorm := by
  intro target htarget
  rcases htarget with ⟨loss, ⟨sourceLoss, hsourceLoss, hloss⟩, rfl⟩
  subst loss
  rcases happrox (uncurryBinaryLoss sourceLoss) ⟨sourceLoss, hsourceLoss, rfl⟩ with
    ⟨n, basis, coefficient, hn, hbasis, hcoefficient, hcoefficientNorm, herror⟩
  let derivativeBasis : Fin n → ℝ → ℝ :=
    fun index => uncurriedDiscreteDerivative (basis index)
  refine ⟨n, derivativeBasis, coefficient, hn, ?_, hcoefficient, hcoefficientNorm, ?_⟩
  · intro index
    rcases hbasis index with ⟨basisLoss, hbasisLoss, hbasisEq⟩
    refine ⟨uncurryBinaryLoss basisLoss, ⟨basisLoss, hbasisLoss, rfl⟩, ?_⟩
    simp [derivativeBasis, hbasisEq]
  · intro report
    have htrue := herror (report, true)
    have hfalse := herror (report, false)
    have hlinearCombination :
        finiteLinearCombination coefficient derivativeBasis report =
          finiteLinearCombination coefficient basis (report, true) -
            finiteLinearCombination coefficient basis (report, false) := by
      simp only [finiteLinearCombination, derivativeBasis, uncurriedDiscreteDerivative]
      calc
        (∑ index, coefficient index *
            (basis index (report, true) - basis index (report, false))) =
            ∑ index, (coefficient index * basis index (report, true) -
              coefficient index * basis index (report, false)) := by
              apply Finset.sum_congr rfl
              intro index _
              ring
        _ = (∑ index, coefficient index * basis index (report, true)) -
            (∑ index, coefficient index * basis index (report, false)) := by
            rw [Finset.sum_sub_distrib]
    rw [hlinearCombination]
    calc
      |uncurriedDiscreteDerivative (uncurryBinaryLoss sourceLoss) report -
          (finiteLinearCombination coefficient basis (report, true) -
            finiteLinearCombination coefficient basis (report, false))| =
          |(uncurryBinaryLoss sourceLoss (report, true) -
              finiteLinearCombination coefficient basis (report, true)) -
            (uncurryBinaryLoss sourceLoss (report, false) -
              finiteLinearCombination coefficient basis (report, false))| := by
            simp [uncurriedDiscreteDerivative, uncurryBinaryLoss]
            ring_nf
      _ ≤ |uncurryBinaryLoss sourceLoss (report, true) -
            finiteLinearCombination coefficient basis (report, true)| +
          |uncurryBinaryLoss sourceLoss (report, false) -
            finiteLinearCombination coefficient basis (report, false)| :=
          by simpa only [sub_zero, zero_sub, abs_neg] using (_root_.abs_sub_le
            (uncurryBinaryLoss sourceLoss (report, true) -
              finiteLinearCombination coefficient basis (report, true))
            0
            (uncurryBinaryLoss sourceLoss (report, false) -
              finiteLinearCombination coefficient basis (report, false)))
      _ ≤ epsilon + epsilon := add_le_add htrue hfalse
      _ = 2 * epsilon := by ring

end AppliedModelingLib.Learning.Prediction
