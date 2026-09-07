import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Multitask incentives and crowding out

Reusable shape results for settings where an incentive target raises effort on
a measurable task and therefore crowds out a second task.  The agent index can
represent a type, a normalized quantile within an admitted population, or any
other heterogeneous response coordinate.

The main theorem says that if each agent's measurable-task effort is
nondecreasing and convex in the target, while residual-task production is
increasing and concave, then aggregate residual-task utility is nonincreasing
and concave in the target.  This is the primitive-to-frontier bridge used by
linear scalarization arguments in strategic ranking and multitask mechanism
design.
-/

namespace AppliedModelingLib

open MeasureTheory

/--
An alternative policy Pareto-dominates a baseline for two utility objectives
when it weakly raises both utilities and strictly raises at least one.
-/
def TwoUtilityParetoDominates {Policy : Type*}
    (firstUtility secondUtility : Policy → ℝ)
    (alternative baseline : Policy) : Prop :=
  firstUtility baseline ≤ firstUtility alternative ∧
    secondUtility baseline ≤ secondUtility alternative ∧
    (firstUtility baseline < firstUtility alternative ∨
      secondUtility baseline < secondUtility alternative)

/--
A feasible policy is Pareto efficient for two utility objectives if no other
feasible policy Pareto-dominates it.
-/
def IsTwoUtilityParetoEfficientOn {Policy : Type*}
    (domain : Set Policy) (firstUtility secondUtility : Policy → ℝ)
    (policy : Policy) : Prop :=
  policy ∈ domain ∧
    ¬ ∃ alternative ∈ domain,
      TwoUtilityParetoDominates firstUtility secondUtility alternative policy

/--
Every point of a strictly opposed one-dimensional utility tradeoff is Pareto
efficient.  This conclusion needs no concavity or supporting-hyperplane
assumption: moving in either direction strictly lowers one of the utilities.
-/
theorem isTwoUtilityParetoEfficientOn_of_strictTradeoff
    {Policy : Type*} [LinearOrder Policy]
    {domain : Set Policy} {firstUtility secondUtility : Policy → ℝ}
    (hfirst : StrictMonoOn firstUtility domain)
    (hsecond : StrictAntiOn secondUtility domain)
    {policy : Policy} (hpolicy : policy ∈ domain) :
    IsTwoUtilityParetoEfficientOn domain firstUtility secondUtility policy := by
  refine ⟨hpolicy, ?_⟩
  rintro ⟨alternative, halternative,
    hfirst_weak, hsecond_weak, hstrict⟩
  rcases lt_trichotomy alternative policy with hleft | heq | hright
  · have hfirst_strict : firstUtility alternative < firstUtility policy :=
      hfirst halternative hpolicy hleft
    exact (not_lt_of_ge hfirst_weak) hfirst_strict
  · subst alternative
    rcases hstrict with hfirst_strict | hsecond_strict
    · exact (lt_irrefl _) hfirst_strict
    · exact (lt_irrefl _) hsecond_strict
  · have hsecond_strict : secondUtility alternative < secondUtility policy :=
      hsecond hpolicy halternative hright
    exact (not_lt_of_ge hsecond_weak) hsecond_strict

/--
Aggregate utility from a residual task after a target-dependent measurable-task
effort response.  `weight` allows the residual skill or productivity of an
agent type to enter multiplicatively.
-/
noncomputable def aggregateCrowdOutUtility
    {Agent : Type*} [MeasurableSpace Agent]
    (μ : Measure Agent)
    (weight : Agent → ℝ)
    (production : ℝ → ℝ)
    (budget : ℝ)
    (effortResponse : Agent → ℝ → ℝ)
    (target : ℝ) : ℝ :=
  ∫ agent, weight agent * production (budget - effortResponse agent target) ∂μ

/-!
## From technology primitives to convex effort response

The strategic-ranking application naturally specifies a concave increasing
score technology and a score requirement, while the aggregation theorems below
use the induced effort response.  The next lemmas close that seam without
assuming an unexplained shape for the inverse technology.
-/

/--
A right inverse of a strictly increasing technology is nondecreasing on the
target range.  The statement is domain-local: neither the technology nor its
inverse needs a global order property.

Upstream credit: the proof directly uses Mathlib's
`StrictMonoOn.le_iff_le` from
[`Order/Monotone/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Order/Monotone/Basic.lean),
at the pinned Apache-2.0 Mathlib revision.  No external code is copied or
ported.
-/
theorem rightInverseOn_monotoneOn_of_strictMonoOn
    {sourceDomain targetDomain : Set ℝ}
    {technology technologyInv : ℝ → ℝ}
    (htechnology_strictMono : StrictMonoOn technology sourceDomain)
    (hinverse_maps : Set.MapsTo technologyInv targetDomain sourceDomain)
    (hinverse : Set.RightInvOn technologyInv technology targetDomain) :
    MonotoneOn technologyInv targetDomain := by
  intro first hfirst second hsecond horder
  apply (htechnology_strictMono.le_iff_le
    (hinverse_maps hfirst) (hinverse_maps hsecond)).mp
  simpa [hinverse hfirst, hinverse hsecond] using horder

/--
A right inverse of a strictly increasing concave technology is convex on its
target range.  This is the domain-local inverse-shape fact needed for
nonnegative effort technologies such as those in strategic ranking.

Upstream credit: the order-reflection step directly uses Mathlib's
`StrictMonoOn.le_iff_le` from
[`Order/Monotone/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Order/Monotone/Basic.lean),
at the pinned Apache-2.0 Mathlib revision.  No external code is copied or
ported.
-/
theorem rightInverseOn_convexOn_of_strictMonoOn_concaveOn
    {sourceDomain targetDomain : Set ℝ}
    {technology technologyInv : ℝ → ℝ}
    (hsource_convex : Convex ℝ sourceDomain)
    (htarget_convex : Convex ℝ targetDomain)
    (htechnology_concave : ConcaveOn ℝ sourceDomain technology)
    (htechnology_strictMono : StrictMonoOn technology sourceDomain)
    (hinverse_maps : Set.MapsTo technologyInv targetDomain sourceDomain)
    (hinverse : Set.RightInvOn technologyInv technology targetDomain) :
    ConvexOn ℝ targetDomain technologyInv := by
  refine ⟨htarget_convex, ?_⟩
  intro first hfirst second hsecond firstWeight secondWeight
    hfirstWeight hsecondWeight hweightSum
  have htarget_average :
      firstWeight • first + secondWeight • second ∈ targetDomain :=
    htarget_convex hfirst hsecond hfirstWeight hsecondWeight hweightSum
  have hsource_average :
      firstWeight • technologyInv first +
          secondWeight • technologyInv second ∈ sourceDomain :=
    hsource_convex (hinverse_maps hfirst) (hinverse_maps hsecond)
      hfirstWeight hsecondWeight hweightSum
  apply (htechnology_strictMono.le_iff_le
    (hinverse_maps htarget_average) hsource_average).mp
  calc
    technology
        (technologyInv (firstWeight • first + secondWeight • second)) =
        firstWeight • first + secondWeight • second :=
      hinverse htarget_average
    _ = firstWeight • technology (technologyInv first) +
          secondWeight • technology (technologyInv second) := by
      rw [hinverse hfirst, hinverse hsecond]
    _ ≤ technology
        (firstWeight • technologyInv first +
          secondWeight • technologyInv second) :=
      htechnology_concave.2 (hinverse_maps hfirst) (hinverse_maps hsecond)
        hfirstWeight hsecondWeight hweightSum

/--
If the required effective score is nondecreasing and convex in a policy
target, applying the inverse of a strictly increasing concave technology gives
a nondecreasing convex effort response.  The range hypotheses expose exactly
the feasibility work needed by a concrete economic model.
-/
theorem rightInverseOn_comp_convexOn_and_monotoneOn
    {policyDomain sourceDomain targetDomain : Set ℝ}
    {technology technologyInv effectiveInput : ℝ → ℝ}
    (hsource_convex : Convex ℝ sourceDomain)
    (htarget_convex : Convex ℝ targetDomain)
    (htechnology_concave : ConcaveOn ℝ sourceDomain technology)
    (htechnology_strictMono : StrictMonoOn technology sourceDomain)
    (hinverse_maps : Set.MapsTo technologyInv targetDomain sourceDomain)
    (hinverse : Set.RightInvOn technologyInv technology targetDomain)
    (heffective_maps : Set.MapsTo effectiveInput policyDomain targetDomain)
    (heffective_convex : ConvexOn ℝ policyDomain effectiveInput)
    (heffective_mono : MonotoneOn effectiveInput policyDomain) :
    ConvexOn ℝ policyDomain (fun target => technologyInv (effectiveInput target)) ∧
      MonotoneOn (fun target => technologyInv (effectiveInput target)) policyDomain := by
  have hinverse_convex :=
    rightInverseOn_convexOn_of_strictMonoOn_concaveOn
      hsource_convex htarget_convex htechnology_concave
      htechnology_strictMono hinverse_maps hinverse
  have hinverse_mono :=
    rightInverseOn_monotoneOn_of_strictMonoOn
      htechnology_strictMono hinverse_maps hinverse
  constructor
  · refine ⟨heffective_convex.1, ?_⟩
    intro first hfirst second hsecond firstWeight secondWeight
      hfirstWeight hsecondWeight hweightSum
    have hpolicy_average :=
      heffective_convex.1 hfirst hsecond
        hfirstWeight hsecondWeight hweightSum
    have heffective_order :=
      heffective_convex.2 hfirst hsecond
        hfirstWeight hsecondWeight hweightSum
    have heffective_average_mem :
        firstWeight • effectiveInput first +
            secondWeight • effectiveInput second ∈ targetDomain :=
      htarget_convex (heffective_maps hfirst) (heffective_maps hsecond)
        hfirstWeight hsecondWeight hweightSum
    calc
      technologyInv
          (effectiveInput
            (firstWeight • first + secondWeight • second)) ≤
          technologyInv
            (firstWeight • effectiveInput first +
              secondWeight • effectiveInput second) :=
        hinverse_mono (heffective_maps hpolicy_average)
          heffective_average_mem heffective_order
      _ ≤ firstWeight • technologyInv (effectiveInput first) +
            secondWeight • technologyInv (effectiveInput second) :=
        hinverse_convex.2 (heffective_maps hfirst) (heffective_maps hsecond)
          hfirstWeight hsecondWeight hweightSum
  · simpa only [Function.comp_apply] using
      hinverse_mono.comp heffective_mono heffective_maps

/--
An elasticity criterion for the effective score requirement `m / F(m)`.

Here `F` is the skill multiplier faced by an admitted type when the common
measurable-output target is `m`, and `elasticity = m * F' / F`.  The conditions
`elasticity ≤ 1` and
`elasticity^2 - elasticity - m * elasticity' ≥ 0` are exactly the first- and
second-derivative tests making the effective input nondecreasing and convex.
They are therefore a direct, dimensionless bridge from a model's skill and
cutoff primitives to the convex-effective-input hypothesis used in multitask
crowd-out results.
-/
theorem effectiveInput_convexOn_and_monotoneOn_of_elasticity
    {lo hi : ℝ} {skill elasticity elasticityDeriv : ℝ → ℝ}
    (hlo : 0 < lo)
    (hskill_pos : ∀ target ∈ Set.Icc lo hi, 0 < skill target)
    (hskill_deriv : ∀ target ∈ Set.Icc lo hi,
      HasDerivAt skill (elasticity target * skill target / target) target)
    (helasticity_deriv : ∀ target ∈ Set.Icc lo hi,
      HasDerivAt elasticity (elasticityDeriv target) target)
    (helasticity_le_one : ∀ target ∈ Set.Icc lo hi, elasticity target ≤ 1)
    (hcurvature : ∀ target ∈ Set.Icc lo hi,
      0 ≤ elasticity target ^ 2 - elasticity target - target * elasticityDeriv target) :
    ConvexOn ℝ (Set.Icc lo hi) (fun target => target / skill target) ∧
      MonotoneOn (fun target => target / skill target) (Set.Icc lo hi) := by
  let domain : Set ℝ := Set.Icc lo hi
  have hdomain_convex : Convex ℝ domain := by
    exact convex_Icc lo hi
  have hskill_continuous : ContinuousOn skill domain := by
    intro target htarget
    exact (hskill_deriv target htarget).continuousAt.continuousWithinAt
  have hinput_continuous : ContinuousOn (fun target => target / skill target) domain := by
    exact continuousOn_id.div hskill_continuous (fun target htarget =>
      (hskill_pos target htarget).ne')
  have htarget_pos : ∀ target ∈ domain, 0 < target := by
    intro target htarget
    exact lt_of_lt_of_le hlo htarget.1
  have hinput_deriv : ∀ target ∈ domain,
      HasDerivAt (fun value => value / skill value)
        ((1 - elasticity target) / skill target) target := by
    intro target htarget
    have htarget_ne : target ≠ 0 := (htarget_pos target htarget).ne'
    have hskill_ne : skill target ≠ 0 := (hskill_pos target htarget).ne'
    have hquotient := (hasDerivAt_id target).div
      (hskill_deriv target htarget) hskill_ne
    convert hquotient using 1
    simp only [id_eq]
    field_simp [htarget_ne, hskill_ne]
  have hinput_deriv2 : ∀ target ∈ domain,
      HasDerivAt (fun value => (1 - elasticity value) / skill value)
        ((elasticity target ^ 2 - elasticity target -
            target * elasticityDeriv target) / (target * skill target)) target := by
    intro target htarget
    have htarget_ne : target ≠ 0 := (htarget_pos target htarget).ne'
    have hskill_ne : skill target ≠ 0 := (hskill_pos target htarget).ne'
    have hnumerator :
        HasDerivAt (fun value => 1 - elasticity value)
          (-elasticityDeriv target) target := by
      simpa using (hasDerivAt_const target (1 : ℝ)).sub
        (helasticity_deriv target htarget)
    have hquotient := hnumerator.div (hskill_deriv target htarget) hskill_ne
    convert hquotient using 1
    field_simp [htarget_ne, hskill_ne]
    ring
  have hinput_convex : ConvexOn ℝ domain (fun target => target / skill target) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg hdomain_convex hinput_continuous
    · intro target htarget
      exact (hinput_deriv target (interior_subset htarget)).hasDerivWithinAt
    · intro target htarget
      exact (hinput_deriv2 target (interior_subset htarget)).hasDerivWithinAt
    · intro target htarget
      exact div_nonneg
        (hcurvature target (interior_subset htarget))
        (le_of_lt (mul_pos (htarget_pos target (interior_subset htarget))
          (hskill_pos target (interior_subset htarget))))
  have hinput_mono : MonotoneOn (fun target => target / skill target) domain := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg hdomain_convex hinput_continuous
    · intro target htarget
      exact (hinput_deriv target (interior_subset htarget)).hasDerivWithinAt
    · intro target htarget
      exact div_nonneg
        (sub_nonneg.mpr (helasticity_le_one target (interior_subset htarget)))
        (le_of_lt (hskill_pos target (interior_subset htarget)))
  exact ⟨hinput_convex, hinput_mono⟩

/--
An elasticity criterion for the square-root production technology.

When production is `e ↦ sqrt e`, an effective score requirement `m / F(m)`
induces effort `(m / F(m))^2`.  This effort path is nondecreasing and convex
under the weaker conditions `elasticity ≤ 1 / 2` and `elasticity' ≤ 0`, where
`elasticity = m * F' / F`.  Thus concavity of the production technology can
repair curvature which is not present at the effective-input level itself.
-/
theorem squaredEffectiveInput_convexOn_and_monotoneOn_of_elasticity
    {lo hi : ℝ} {skill elasticity elasticityDeriv : ℝ → ℝ}
    (hlo : 0 < lo)
    (hskill_pos : ∀ target ∈ Set.Icc lo hi, 0 < skill target)
    (hskill_deriv : ∀ target ∈ Set.Icc lo hi,
      HasDerivAt skill (elasticity target * skill target / target) target)
    (helasticity_deriv : ∀ target ∈ Set.Icc lo hi,
      HasDerivAt elasticity (elasticityDeriv target) target)
    (helasticity_le_half : ∀ target ∈ Set.Icc lo hi, elasticity target ≤ 1 / 2)
    (helasticityDeriv_nonpos : ∀ target ∈ Set.Icc lo hi, elasticityDeriv target ≤ 0) :
    ConvexOn ℝ (Set.Icc lo hi) (fun target => (target / skill target) ^ 2) ∧
      MonotoneOn (fun target => (target / skill target) ^ 2) (Set.Icc lo hi) := by
  let domain : Set ℝ := Set.Icc lo hi
  have hdomain_convex : Convex ℝ domain := by
    exact convex_Icc lo hi
  have hskill_continuous : ContinuousOn skill domain := by
    intro target htarget
    exact (hskill_deriv target htarget).continuousAt.continuousWithinAt
  have hinput_continuous : ContinuousOn (fun target => target / skill target) domain := by
    exact continuousOn_id.div hskill_continuous (fun target htarget =>
      (hskill_pos target htarget).ne')
  have heffort_continuous :
      ContinuousOn (fun target => (target / skill target) ^ 2) domain := by
    exact hinput_continuous.pow 2
  have htarget_pos : ∀ target ∈ domain, 0 < target := by
    intro target htarget
    exact lt_of_lt_of_le hlo htarget.1
  have hinput_deriv : ∀ target ∈ domain,
      HasDerivAt (fun value => value / skill value)
        ((1 - elasticity target) / skill target) target := by
    intro target htarget
    have htarget_ne : target ≠ 0 := (htarget_pos target htarget).ne'
    have hskill_ne : skill target ≠ 0 := (hskill_pos target htarget).ne'
    have hquotient := (hasDerivAt_id target).div
      (hskill_deriv target htarget) hskill_ne
    convert hquotient using 1
    simp only [id_eq]
    field_simp [htarget_ne, hskill_ne]
  have hinput_deriv2 : ∀ target ∈ domain,
      HasDerivAt (fun value => (1 - elasticity value) / skill value)
        ((elasticity target ^ 2 - elasticity target -
            target * elasticityDeriv target) / (target * skill target)) target := by
    intro target htarget
    have htarget_ne : target ≠ 0 := (htarget_pos target htarget).ne'
    have hskill_ne : skill target ≠ 0 := (hskill_pos target htarget).ne'
    have hnumerator :
        HasDerivAt (fun value => 1 - elasticity value)
          (-elasticityDeriv target) target := by
      simpa using (hasDerivAt_const target (1 : ℝ)).sub
        (helasticity_deriv target htarget)
    have hquotient := hnumerator.div (hskill_deriv target htarget) hskill_ne
    convert hquotient using 1
    field_simp [htarget_ne, hskill_ne]
    ring
  have heffort_deriv : ∀ target ∈ domain,
      HasDerivAt (fun value => (value / skill value) ^ 2)
        (2 * (target / skill target) * ((1 - elasticity target) / skill target)) target := by
    intro target htarget
    have hproduct := (hinput_deriv target htarget).mul (hinput_deriv target htarget)
    convert hproduct using 1
    · ext value
      simp only [Pi.mul_apply, pow_two]
    · ring
  have heffort_deriv2 : ∀ target ∈ domain,
      HasDerivAt
        (fun value =>
          2 * (value / skill value) * ((1 - elasticity value) / skill value))
        (2 * ((1 - elasticity target) * (1 - 2 * elasticity target) -
          target * elasticityDeriv target) / (skill target) ^ 2) target := by
    intro target htarget
    have htarget_ne : target ≠ 0 := (htarget_pos target htarget).ne'
    have hskill_ne : skill target ≠ 0 := (hskill_pos target htarget).ne'
    have hproduct := ((hasDerivAt_const target (2 : ℝ)).mul
      (hinput_deriv target htarget)).mul (hinput_deriv2 target htarget)
    simp only [Pi.mul_apply] at hproduct
    convert hproduct using 1
    field_simp [htarget_ne, hskill_ne]
    ring
  have heffort_convex :
      ConvexOn ℝ domain (fun target => (target / skill target) ^ 2) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg hdomain_convex heffort_continuous
    · intro target htarget
      exact (heffort_deriv target (interior_subset htarget)).hasDerivWithinAt
    · intro target htarget
      exact (heffort_deriv2 target (interior_subset htarget)).hasDerivWithinAt
    · intro target htarget
      have hhalf := helasticity_le_half target (interior_subset htarget)
      have hderiv_nonpos := helasticityDeriv_nonpos target (interior_subset htarget)
      have hfirst_nonneg : 0 ≤ 1 - elasticity target := by linarith
      have hsecond_nonneg : 0 ≤ 1 - 2 * elasticity target := by linarith
      have hcurvature_nonneg :
          0 ≤ (1 - elasticity target) * (1 - 2 * elasticity target) -
            target * elasticityDeriv target := by
        have hproduct_nonneg := mul_nonneg hfirst_nonneg hsecond_nonneg
        have hderivative_term_nonpos : target * elasticityDeriv target ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos
            (htarget_pos target (interior_subset htarget)).le hderiv_nonpos
        linarith
      exact div_nonneg
        (mul_nonneg (by norm_num) hcurvature_nonneg)
        (sq_nonneg _)
  have heffort_mono :
      MonotoneOn (fun target => (target / skill target) ^ 2) domain := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg hdomain_convex heffort_continuous
    · intro target htarget
      exact (heffort_deriv target (interior_subset htarget)).hasDerivWithinAt
    · intro target htarget
      have hhalf := helasticity_le_half target (interior_subset htarget)
      have hinput_nonneg : 0 ≤ target / skill target := by
        exact div_nonneg (htarget_pos target (interior_subset htarget)).le
          (hskill_pos target (interior_subset htarget)).le
      have hfactor_nonneg : 0 ≤ (1 - elasticity target) / skill target := by
        exact div_nonneg (by linarith) (hskill_pos target (interior_subset htarget)).le
      exact mul_nonneg (mul_nonneg (by norm_num) hinput_nonneg) hfactor_nonneg
  exact ⟨heffort_convex, heffort_mono⟩

/--
The measurable-skill multiplier induced by a log-affine quantile along a
normalized admitted tail.  Here `cutoff` is the inverse common-output path and
`tailPosition` is the fixed normalized tail rank.
-/
noncomputable def exponentialTailMultiplier
    (scale logSlope tailPosition : ℝ) (cutoff : ℝ → ℝ) (output : ℝ) : ℝ :=
  scale * Real.exp (logSlope *
    (tailPosition + (1 - tailPosition) * cutoff output))

/--
The elasticity of `exponentialTailMultiplier` when the common-output inverse
has the power/exponential cutoff derivative used below.
-/
noncomputable def exponentialTailElasticity
    (logSlope cutoffCurvature tailPosition : ℝ) (cutoff : ℝ → ℝ) (output : ℝ) : ℝ :=
  logSlope * (1 - tailPosition) /
    (logSlope + cutoffCurvature / (1 - cutoff output))

/--
The derivative of `exponentialTailElasticity` along the same cutoff path.
-/
noncomputable def exponentialTailElasticityDeriv
    (logSlope cutoffCurvature tailPosition : ℝ) (cutoff : ℝ → ℝ) (output : ℝ) : ℝ :=
  -(logSlope * (1 - tailPosition) * cutoffCurvature) /
    (output * (1 - cutoff output) ^ 2 *
      (logSlope + cutoffCurvature / (1 - cutoff output)) ^ 3)

/--
The common measurable-output path induced by the power/exponential source
family, up to its positive capacity and skill scale.  The exponent
`cutoffCurvature` is `alpha / gamma` for
`g(e)=e^alpha` and `p(e)=e^gamma`.
-/
noncomputable def powerExponentialOutput
    (scale logSlope cutoffCurvature : ℝ) (cutoff : ℝ) : ℝ :=
  scale * Real.exp (logSlope * cutoff) * (1 - cutoff) ^ (-cutoffCurvature)

/--
The power/exponential common-output path has logarithmic derivative
`delta + kappa / (1-c)`.  This provides the source-side derivative which an
inverse cutoff map must invert before applying the multiplier-elasticity
criterion.
-/
theorem powerExponentialOutput_hasDerivAt
    {scale logSlope cutoffCurvature cutoff : ℝ}
    (hcutoff_lt_one : cutoff < 1) :
    HasDerivAt
      (powerExponentialOutput scale logSlope cutoffCurvature)
      (powerExponentialOutput scale logSlope cutoffCurvature cutoff *
        (logSlope + cutoffCurvature / (1 - cutoff))) cutoff := by
  have hcutoff_gap_pos : 0 < 1 - cutoff := by linarith
  have hcutoff_gap_ne : 1 - cutoff ≠ 0 := hcutoff_gap_pos.ne'
  have hgap_deriv :
      HasDerivAt (fun value => 1 - value) (-1) cutoff := by
    simpa using (hasDerivAt_const cutoff (1 : ℝ)).sub (hasDerivAt_id cutoff)
  have hpower_deriv :
      HasDerivAt (fun value => (1 - value) ^ (-cutoffCurvature))
        ((-1) * (-cutoffCurvature) *
          (1 - cutoff) ^ (-cutoffCurvature - 1)) cutoff := by
    exact hgap_deriv.rpow_const (Or.inl hcutoff_gap_ne)
  have hexponential_deriv :
      HasDerivAt (fun value => Real.exp (logSlope * value))
        (Real.exp (logSlope * cutoff) * logSlope) cutoff := by
    have hargument_raw :=
      (hasDerivAt_const cutoff logSlope).mul (hasDerivAt_id cutoff)
    have hargument :
        HasDerivAt (fun value => logSlope * value) logSlope cutoff := by
      convert hargument_raw using 1
      ring
    exact hargument.exp
  have hproduct :=
    ((hasDerivAt_const cutoff scale).mul hexponential_deriv).mul hpower_deriv
  simp only [Pi.mul_apply] at hproduct
  convert hproduct using 1
  simp only [powerExponentialOutput]
  rw [Real.rpow_sub_one hcutoff_gap_ne (-cutoffCurvature)]
  field_simp [hcutoff_gap_ne]
  ring

/--
Differentiate a locally defined inverse of `powerExponentialOutput`.  This is
the cutoff-inverse step connecting the source family's common-output formula
to `exponentialTailMultiplier_elasticity_conditions`; it requires neither a
global closed form for the inverse nor a stronger global invertibility claim.
-/
theorem powerExponentialOutput_localInverse_hasDerivAt
    {scale logSlope cutoffCurvature output : ℝ}
    {cutoff : ℝ → ℝ}
    (hlogSlope : 0 < logSlope)
    (hcurvature : 0 < cutoffCurvature)
    (houtput : 0 < output)
    (hcutoff_lt_one : cutoff output < 1)
    (hcutoff_continuous : ContinuousAt cutoff output)
    (hlocal_right_inverse :
      ∀ᶠ nearbyOutput in nhds output,
        powerExponentialOutput scale logSlope cutoffCurvature
          (cutoff nearbyOutput) = nearbyOutput) :
    HasDerivAt cutoff
      (1 / (output *
        (logSlope + cutoffCurvature / (1 - cutoff output)))) output := by
  have hcutoff_gap_pos : 0 < 1 - cutoff output := by linarith
  have hdenominator_pos :
      0 < logSlope + cutoffCurvature / (1 - cutoff output) := by
    exact add_pos hlogSlope (div_pos hcurvature hcutoff_gap_pos)
  have hvalue :
      powerExponentialOutput scale logSlope cutoffCurvature
        (cutoff output) = output :=
    hlocal_right_inverse.self_of_nhds
  have hpath_deriv :=
    powerExponentialOutput_hasDerivAt
      (scale := scale) (logSlope := logSlope)
      (cutoffCurvature := cutoffCurvature) hcutoff_lt_one
  have hpath_deriv_ne :
      powerExponentialOutput scale logSlope cutoffCurvature (cutoff output) *
          (logSlope + cutoffCurvature / (1 - cutoff output)) ≠ 0 := by
    rw [hvalue]
    exact mul_ne_zero houtput.ne' hdenominator_pos.ne'
  have hinverse := hpath_deriv.of_local_left_inverse hcutoff_continuous
    hpath_deriv_ne hlocal_right_inverse
  convert hinverse using 1
  rw [hvalue]
  field_simp [houtput.ne', hdenominator_pos.ne']

/--
The direct multiplier calculation for the power/exponential source family.
If the common-output inverse has derivative
`1 / (m (delta + kappa / (1 - C(m))))`, then an exponential measurable-skill
quantile has exactly the displayed elasticity and elasticity derivative.
The assumptions `0 ≤ C(m) < 1`, `0 ≤ s ≤ 1`, and `0 < delta ≤ kappa` imply
that elasticity is at most one half and is nonincreasing.  The specialization
`kappa = 1 / 4` is the paper's `g(e)=sqrt e`, `p(e)=e^2` power pair.
-/
theorem exponentialTailMultiplier_elasticity_conditions
    {scale logSlope cutoffCurvature tailPosition output : ℝ}
    {cutoff : ℝ → ℝ}
    (hscale : 0 < scale)
    (hlogSlope : 0 < logSlope)
    (hcurvature : logSlope ≤ cutoffCurvature)
    (htail_nonneg : 0 ≤ tailPosition)
    (htail_le_one : tailPosition ≤ 1)
    (houtput : 0 < output)
    (hcutoff_nonneg : 0 ≤ cutoff output)
    (hcutoff_lt_one : cutoff output < 1)
    (hcutoff_deriv :
      HasDerivAt cutoff
        (1 / (output *
          (logSlope + cutoffCurvature / (1 - cutoff output)))) output) :
    0 < exponentialTailMultiplier scale logSlope tailPosition cutoff output ∧
      HasDerivAt
        (exponentialTailMultiplier scale logSlope tailPosition cutoff)
        (exponentialTailElasticity logSlope cutoffCurvature tailPosition cutoff output *
          exponentialTailMultiplier scale logSlope tailPosition cutoff output / output)
        output ∧
      HasDerivAt
        (exponentialTailElasticity logSlope cutoffCurvature tailPosition cutoff)
        (exponentialTailElasticityDeriv
          logSlope cutoffCurvature tailPosition cutoff output) output ∧
      exponentialTailElasticity logSlope cutoffCurvature tailPosition cutoff output ≤ 1 / 2 ∧
      exponentialTailElasticityDeriv
        logSlope cutoffCurvature tailPosition cutoff output ≤ 0 := by
  have htail_gap_nonneg : 0 ≤ 1 - tailPosition := by linarith
  have htail_gap_le_one : 1 - tailPosition ≤ 1 := by linarith
  have hcurvature_pos : 0 < cutoffCurvature := hlogSlope.trans_le hcurvature
  have hcutoff_gap_pos : 0 < 1 - cutoff output := by linarith
  have hcutoff_gap_ne : 1 - cutoff output ≠ 0 := hcutoff_gap_pos.ne'
  let denominator : ℝ :=
    logSlope + cutoffCurvature / (1 - cutoff output)
  have hdenominator_pos : 0 < denominator := by
    dsimp only [denominator]
    exact add_pos hlogSlope (div_pos hcurvature_pos hcutoff_gap_pos)
  have hdenominator_ne : denominator ≠ 0 := hdenominator_pos.ne'
  have hmultiplier_pos :
      0 < exponentialTailMultiplier scale logSlope tailPosition cutoff output := by
    exact mul_pos hscale (Real.exp_pos _)
  have htail_path_deriv :
      HasDerivAt
        (fun value => tailPosition + (1 - tailPosition) * cutoff value)
        ((1 - tailPosition) /
          (output * denominator)) output := by
    have hpath := (hasDerivAt_const output tailPosition).add
      ((hasDerivAt_const output (1 - tailPosition)).mul hcutoff_deriv)
    convert hpath using 1
    dsimp only [denominator]
    ring
  have hmultiplier_deriv :
      HasDerivAt
        (exponentialTailMultiplier scale logSlope tailPosition cutoff)
        (exponentialTailElasticity logSlope cutoffCurvature tailPosition cutoff output *
          exponentialTailMultiplier scale logSlope tailPosition cutoff output / output)
        output := by
    have hargument := (hasDerivAt_const output logSlope).mul htail_path_deriv
    have hexponential := hargument.exp
    have hmultiplier := (hasDerivAt_const output scale).mul hexponential
    simp only [Pi.mul_apply] at hmultiplier
    convert hmultiplier using 1
    simp only [exponentialTailMultiplier, exponentialTailElasticity]
    dsimp only [denominator] at htail_path_deriv hdenominator_pos ⊢
    field_simp [houtput.ne', hcutoff_gap_ne, hdenominator_pos.ne']
    ring
  have hcutoff_gap_deriv :
      HasDerivAt (fun value => 1 - cutoff value)
        (-(1 / (output * denominator))) output := by
    have hgap := (hasDerivAt_const output (1 : ℝ)).sub hcutoff_deriv
    convert hgap using 1
    dsimp only [denominator]
    ring
  have hinverse_gap_deriv :
      HasDerivAt (fun value => (1 - cutoff value)⁻¹)
        ((1 / (output * denominator)) / (1 - cutoff output) ^ 2) output := by
    have hinverse := hcutoff_gap_deriv.inv hcutoff_gap_ne
    convert hinverse using 1
    ring
  have hdenominator_deriv :
      HasDerivAt
        (fun value => logSlope + cutoffCurvature / (1 - cutoff value))
        (cutoffCurvature /
          (output * denominator * (1 - cutoff output) ^ 2)) output := by
    have hdenominator' := (hasDerivAt_const output logSlope).add
      ((hasDerivAt_const output cutoffCurvature).div hcutoff_gap_deriv hcutoff_gap_ne)
    convert hdenominator' using 1
    dsimp only [denominator]
    field_simp [houtput.ne', hcutoff_gap_ne, hdenominator_pos.ne']
    ring
  have helasticity_deriv :
      HasDerivAt
        (exponentialTailElasticity logSlope cutoffCurvature tailPosition cutoff)
        (exponentialTailElasticityDeriv
          logSlope cutoffCurvature tailPosition cutoff output) output := by
    have hquotient :=
      (hasDerivAt_const output (logSlope * (1 - tailPosition))).div
        hdenominator_deriv hdenominator_ne
    convert hquotient using 1
    simp only [exponentialTailElasticityDeriv]
    dsimp only [denominator]
    field_simp [houtput.ne', hcutoff_gap_ne, hdenominator_pos.ne']
    ring
  have hratio_ge_one : 1 ≤ (1 - cutoff output)⁻¹ := by
    apply (one_le_inv₀ hcutoff_gap_pos).2
    linarith
  have hcurvature_over_gap_ge : cutoffCurvature ≤
      cutoffCurvature / (1 - cutoff output) := by
    rw [div_eq_mul_inv]
    nlinarith [mul_le_mul_of_nonneg_left hratio_ge_one hcurvature_pos.le]
  have hdenominator_ge_two_slope : 2 * logSlope ≤ denominator := by
    dsimp only [denominator]
    linarith
  have hnumerator_nonneg : 0 ≤ logSlope * (1 - tailPosition) := by
    exact mul_nonneg hlogSlope.le htail_gap_nonneg
  have hnumerator_le_slope : logSlope * (1 - tailPosition) ≤ logSlope := by
    exact mul_le_of_le_one_right hlogSlope.le htail_gap_le_one
  have helasticity_le_half :
      exponentialTailElasticity logSlope cutoffCurvature tailPosition cutoff output ≤ 1 / 2 := by
    simp only [exponentialTailElasticity]
    rw [div_le_iff₀ hdenominator_pos]
    nlinarith
  have hderivative_denominator_pos :
      0 < output * (1 - cutoff output) ^ 2 * denominator ^ 3 := by
    positivity
  have helasticity_deriv_nonpos :
      exponentialTailElasticityDeriv
        logSlope cutoffCurvature tailPosition cutoff output ≤ 0 := by
    simp only [exponentialTailElasticityDeriv]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (mul_nonneg
        (mul_nonneg hlogSlope.le htail_gap_nonneg)
        hcurvature_pos.le))
      hderivative_denominator_pos.le
  exact ⟨hmultiplier_pos, hmultiplier_deriv, helasticity_deriv,
    helasticity_le_half, helasticity_deriv_nonpos⟩

/--
Pointwise convex measurable-task effort produces a concave residual-task value
when production is increasing and concave.  A nonnegative type weight preserves
the inequality.
-/
theorem crowdOutIntegrand_concaveOn
    {Agent : Type*}
    {weight : Agent → ℝ}
    {production : ℝ → ℝ}
    {budget : ℝ}
    {effortResponse : Agent → ℝ → ℝ}
    {targetDomain : Set ℝ}
    (hdomain : Convex ℝ targetDomain)
    (hproduction_concave : ConcaveOn ℝ Set.univ production)
    (hproduction_mono : Monotone production)
    {agent : Agent}
    (hweight_nonneg : 0 ≤ weight agent)
    (heffort_convex : ConvexOn ℝ targetDomain (effortResponse agent)) :
    ConcaveOn ℝ targetDomain
      (fun target =>
        weight agent * production (budget - effortResponse agent target)) := by
  have hresidual_concave :
      ConcaveOn ℝ targetDomain
        (fun target => production (budget - effortResponse agent target)) := by
    refine ⟨hdomain, ?_⟩
    intro first hfirst second hsecond firstWeight secondWeight
      hfirstWeight hsecondWeight hweightSum
    have heffort := heffort_convex.2 hfirst hsecond
      hfirstWeight hsecondWeight hweightSum
    have hresidual_order :
        firstWeight • (budget - effortResponse agent first) +
            secondWeight • (budget - effortResponse agent second) ≤
          budget - effortResponse agent
            (firstWeight • first + secondWeight • second) := by
      simp only [smul_eq_mul] at heffort ⊢
      calc
        firstWeight * (budget - effortResponse agent first) +
            secondWeight * (budget - effortResponse agent second) =
          (firstWeight + secondWeight) * budget -
            (firstWeight * effortResponse agent first +
              secondWeight * effortResponse agent second) := by ring
        _ = budget -
            (firstWeight * effortResponse agent first +
              secondWeight * effortResponse agent second) := by
          rw [hweightSum]
          ring
        _ ≤ budget - effortResponse agent
            (firstWeight * first + secondWeight * second) :=
          sub_le_sub_left heffort budget
    calc
      firstWeight • production (budget - effortResponse agent first) +
          secondWeight • production (budget - effortResponse agent second) ≤
        production
          (firstWeight • (budget - effortResponse agent first) +
            secondWeight • (budget - effortResponse agent second)) :=
          hproduction_concave.2 (by simp) (by simp)
            hfirstWeight hsecondWeight hweightSum
      _ ≤ production
          (budget - effortResponse agent
            (firstWeight • first + secondWeight • second)) :=
        hproduction_mono hresidual_order
  have hscaled := ConcaveOn.smul hweight_nonneg hresidual_concave
  simpa [smul_eq_mul] using hscaled

/--
Pointwise nondecreasing measurable-task effort produces a nonincreasing
residual-task value when production is increasing.  A nonnegative type weight
preserves the order.
-/
theorem crowdOutIntegrand_antitoneOn
    {Agent : Type*}
    {weight : Agent → ℝ}
    {production : ℝ → ℝ}
    {budget : ℝ}
    {effortResponse : Agent → ℝ → ℝ}
    {targetDomain : Set ℝ}
    (hproduction_mono : Monotone production)
    {agent : Agent}
    (hweight_nonneg : 0 ≤ weight agent)
    (heffort_mono : MonotoneOn (effortResponse agent) targetDomain) :
    AntitoneOn
      (fun target =>
        weight agent * production (budget - effortResponse agent target))
      targetDomain := by
  intro first hfirst second hsecond htarget
  have heffort := heffort_mono hfirst hsecond htarget
  exact mul_le_mul_of_nonneg_left
    (hproduction_mono (by linarith)) hweight_nonneg

/--
Aggregate crowd-out utility is concave when almost every type has a convex
effort response and residual-task production is increasing and concave.

Upstream credit: this theorem directly reuses Mathlib's
`integral_concaveOn_of_integrand_ae` from
[`MeasureTheory/Integral/Bochner/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean),
at the pinned Apache-2.0 Mathlib revision.  No external code is copied or
ported.
-/
theorem aggregateCrowdOutUtility_concaveOn
    {Agent : Type*} [MeasurableSpace Agent]
    (μ : Measure Agent)
    (weight : Agent → ℝ)
    (production : ℝ → ℝ)
    (budget : ℝ)
    (effortResponse : Agent → ℝ → ℝ)
    (targetDomain : Set ℝ)
    (hdomain : Convex ℝ targetDomain)
    (hproduction_concave : ConcaveOn ℝ Set.univ production)
    (hproduction_mono : Monotone production)
    (hweight_nonneg : ∀ᵐ agent ∂μ, 0 ≤ weight agent)
    (heffort_convex :
      ∀ᵐ agent ∂μ, ConvexOn ℝ targetDomain (effortResponse agent))
    (hintegrable : ∀ target ∈ targetDomain,
      Integrable
        (fun agent =>
          weight agent * production (budget - effortResponse agent target)) μ) :
    ConcaveOn ℝ targetDomain
      (aggregateCrowdOutUtility μ weight production budget effortResponse) := by
  apply integral_concaveOn_of_integrand_ae hdomain
  · filter_upwards [hweight_nonneg, heffort_convex] with agent hweight heffort
    exact crowdOutIntegrand_concaveOn hdomain hproduction_concave
      hproduction_mono hweight heffort
  · exact hintegrable

/--
Aggregate crowd-out utility is nonincreasing when almost every type's effort
response is nondecreasing in the measurable-task target.

Upstream credit: this theorem directly reuses Mathlib's
`integral_antitoneOn_of_integrand_ae` from
[`MeasureTheory/Integral/Bochner/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean),
at the pinned Apache-2.0 Mathlib revision.  No external code is copied or
ported.
-/
theorem aggregateCrowdOutUtility_antitoneOn
    {Agent : Type*} [MeasurableSpace Agent]
    (μ : Measure Agent)
    (weight : Agent → ℝ)
    (production : ℝ → ℝ)
    (budget : ℝ)
    (effortResponse : Agent → ℝ → ℝ)
    (targetDomain : Set ℝ)
    (hproduction_mono : Monotone production)
    (hweight_nonneg : ∀ᵐ agent ∂μ, 0 ≤ weight agent)
    (heffort_mono :
      ∀ᵐ agent ∂μ, MonotoneOn (effortResponse agent) targetDomain)
    (hintegrable : ∀ target ∈ targetDomain,
      Integrable
        (fun agent =>
          weight agent * production (budget - effortResponse agent target)) μ) :
    AntitoneOn
      (aggregateCrowdOutUtility μ weight production budget effortResponse)
      targetDomain := by
  apply integral_antitoneOn_of_integrand_ae
  · filter_upwards [hweight_nonneg, heffort_mono] with agent hweight heffort
    exact crowdOutIntegrand_antitoneOn hproduction_mono hweight heffort
  · exact hintegrable

/--
Aggregate crowd-out utility is concave and nonincreasing when those two shape
properties hold directly for almost every type's residual-task contribution.

This is weaker than requiring the measurable-task effort response itself to be
convex: curvature of residual-task production may compensate for a mildly
concave effort response.  It is the shortest type-level assumption that can be
averaged into the supported aggregate frontier used by scalarization results.

Upstream credit: the proof directly reuses Mathlib's
`integral_concaveOn_of_integrand_ae` and
`integral_antitoneOn_of_integrand_ae` from
[`MeasureTheory/Integral/Bochner/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean),
at the pinned Apache-2.0 Mathlib revision.  No external code is copied or
ported.
-/
theorem aggregateCrowdOutUtility_concaveOn_and_antitoneOn_of_residual_shape
    {Agent : Type*} [MeasurableSpace Agent]
    (μ : Measure Agent)
    (weight : Agent → ℝ)
    (production : ℝ → ℝ)
    (budget : ℝ)
    (effortResponse : Agent → ℝ → ℝ)
    (targetDomain : Set ℝ)
    (hdomain : Convex ℝ targetDomain)
    (hweight_nonneg : ∀ᵐ agent ∂μ, 0 ≤ weight agent)
    (hresidual_concave :
      ∀ᵐ agent ∂μ,
        ConcaveOn ℝ targetDomain
          (fun target => production (budget - effortResponse agent target)))
    (hresidual_antitone :
      ∀ᵐ agent ∂μ,
        AntitoneOn
          (fun target => production (budget - effortResponse agent target))
          targetDomain)
    (hintegrable : ∀ target ∈ targetDomain,
      Integrable
        (fun agent =>
          weight agent * production (budget - effortResponse agent target)) μ) :
    ConcaveOn ℝ targetDomain
        (aggregateCrowdOutUtility μ weight production budget effortResponse) ∧
      AntitoneOn
        (aggregateCrowdOutUtility μ weight production budget effortResponse)
        targetDomain := by
  have hweighted_concave :
      ∀ᵐ agent ∂μ,
        ConcaveOn ℝ targetDomain
          (fun target =>
            weight agent * production (budget - effortResponse agent target)) := by
    filter_upwards [hweight_nonneg, hresidual_concave] with agent hweight hshape
    simpa [smul_eq_mul] using ConcaveOn.smul hweight hshape
  have hweighted_antitone :
      ∀ᵐ agent ∂μ,
        AntitoneOn
          (fun target =>
            weight agent * production (budget - effortResponse agent target))
          targetDomain := by
    filter_upwards [hweight_nonneg, hresidual_antitone] with agent hweight hshape
    intro first hfirst second hsecond horder
    exact mul_le_mul_of_nonneg_left
      (hshape hfirst hsecond horder) hweight
  constructor
  · apply integral_concaveOn_of_integrand_ae hdomain hweighted_concave
    exact hintegrable
  · apply integral_antitoneOn_of_integrand_ae hweighted_antitone
    exact hintegrable

/--
Combined primitive-to-frontier bridge: convex, nondecreasing effort responses
make aggregate residual-task utility both concave and nonincreasing in the
measurable-task target.
-/
theorem aggregateCrowdOutUtility_concaveOn_and_antitoneOn
    {Agent : Type*} [MeasurableSpace Agent]
    (μ : Measure Agent)
    (weight : Agent → ℝ)
    (production : ℝ → ℝ)
    (budget : ℝ)
    (effortResponse : Agent → ℝ → ℝ)
    (targetDomain : Set ℝ)
    (hdomain : Convex ℝ targetDomain)
    (hproduction_concave : ConcaveOn ℝ Set.univ production)
    (hproduction_mono : Monotone production)
    (hweight_nonneg : ∀ᵐ agent ∂μ, 0 ≤ weight agent)
    (heffort_convex :
      ∀ᵐ agent ∂μ, ConvexOn ℝ targetDomain (effortResponse agent))
    (heffort_mono :
      ∀ᵐ agent ∂μ, MonotoneOn (effortResponse agent) targetDomain)
    (hintegrable : ∀ target ∈ targetDomain,
      Integrable
        (fun agent =>
          weight agent * production (budget - effortResponse agent target)) μ) :
    ConcaveOn ℝ targetDomain
        (aggregateCrowdOutUtility μ weight production budget effortResponse) ∧
      AntitoneOn
        (aggregateCrowdOutUtility μ weight production budget effortResponse)
        targetDomain :=
  ⟨aggregateCrowdOutUtility_concaveOn μ weight production budget
      effortResponse targetDomain hdomain hproduction_concave hproduction_mono
      hweight_nonneg heffort_convex hintegrable,
    aggregateCrowdOutUtility_antitoneOn μ weight production budget
      effortResponse targetDomain hproduction_mono hweight_nonneg
      heffort_mono hintegrable⟩

end AppliedModelingLib
