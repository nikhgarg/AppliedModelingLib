import AppliedModelingLib.Queueing.MM1.Stationary
import AppliedModelingLib.Foundations.Probability.PoissonProcess
import AppliedModelingLib.Foundations.Probability.PMFKernel
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Tactic

/-!
# Discrete uniformization of the M/M/1 birth--death chain

This module upgrades the generator-balance calculation to a genuinely
countable discrete Markov-kernel invariant distribution.  It proves detailed
balance and one-step invariance for the reflected Bernoulli jump chain at the
uniformized birth probability `rho / (1 + rho)`, including the rate-specialized
identity `lambda / (lambda + mu)`.

It does not construct a continuous-time chain, its independent Poisson clock,
or a stationary Palm queueing path.  Those are separate path-space results.
-/

open scoped ENNReal NNReal

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory

/-- A countable-state discrete Markov kernel represented by a row PMF. -/
abbrev CountableMarkovKernel (α : Type*) := PMFKernel α α

namespace CountableMarkovKernel

/-- The `n`-step transition PMF of a countable-state kernel.  This is the
ordinary Kleisli iterate of its one-step transition rows. -/
noncomputable def iterate {α : Type*} (kernel : CountableMarkovKernel α) : ℕ →
    CountableMarkovKernel α
  | 0 => fun state => PMF.pure state
  | steps + 1 => fun state => (kernel state).bind (iterate kernel steps)

@[simp]
theorem iterate_zero {α : Type*} (kernel : CountableMarkovKernel α) :
    iterate kernel 0 = fun state => PMF.pure state := rfl

@[simp]
theorem iterate_succ {α : Type*} (kernel : CountableMarkovKernel α) (steps : ℕ) :
    iterate kernel (steps + 1) =
      fun state => (kernel state).bind (iterate kernel steps) := rfl

@[simp]
theorem iterate_one {α : Type*} (kernel : CountableMarkovKernel α) :
    iterate kernel 1 = kernel := by
  funext state
  simp [iterate]

/-- Splitting a finite number of transitions into two successive blocks is
Kleisli composition of the corresponding iterated transition PMFs. -/
theorem iterate_add_apply {α : Type*} (kernel : CountableMarkovKernel α)
    (first second : ℕ) (state : α) :
    iterate kernel (first + second) state =
      (iterate kernel first state).bind (iterate kernel second) := by
  induction first generalizing state with
  | zero =>
      simp [iterate]
  | succ first ih =>
      rw [Nat.succ_add, iterate_succ, iterate_succ, PMF.bind_bind]
      have hiterate : iterate kernel (first + second) =
          fun nextState => (iterate kernel first nextState).bind
            (iterate kernel second) := by
        funext nextState
        exact ih nextState
      rw [hiterate]

/-- Translating a natural-valued PMF by a fixed natural amount has the
expected singleton preimage: below the translation it is zero, and otherwise
it is the PMF evaluated at the unique residual count. -/
theorem map_add_left_apply (distribution : PMF ℕ) (first total : ℕ) :
    (PMF.map (fun second : ℕ => first + second) distribution) total =
      if first ≤ total then distribution (total - first) else 0 := by
  by_cases hfirst : first ≤ total
  · rw [PMF.map_apply, tsum_eq_single (total - first)]
    · simp [hfirst, Nat.add_sub_of_le hfirst]
    · intro second hsecond
      by_cases htotal : total = first + second
      · exfalso
        apply hsecond
        omega
      · simp [htotal]
  · rw [PMF.map_apply]
    simp only [if_neg hfirst]
    apply ENNReal.tsum_eq_zero.mpr
    intro second
    have htotal : total ≠ first + second := by omega
    simp [htotal]

/-- Mix the iterated transition PMFs by a Poisson number of potential events.
For a uniformized chain this is the canonical candidate transition row at a
fixed clock exposure.  Path-process identification is proved separately. -/
noncomputable def poissonized {α : Type*} (kernel : CountableMarkovKernel α)
    (mean : ℝ≥0) : CountableMarkovKernel α :=
  fun state => (ProbabilityTheory.poissonMeasure mean).toPMF.bind
    (fun steps => iterate kernel steps state)

/-- Pointwise expansion of a Poissonized transition row. -/
theorem poissonized_apply {α : Type*} (kernel : CountableMarkovKernel α)
    (mean : ℝ≥0) (state nextState : α) :
    poissonized kernel mean state nextState =
      ∑' steps : ℕ, (ProbabilityTheory.poissonMeasure mean).toPMF steps *
        iterate kernel steps state nextState := by
  exact PMF.bind_apply _ _ _

/-- The PMF value of a Poisson measure is the nonnegative-real lift of the
standard Poisson count likelihood. -/
theorem poissonMeasure_toPMF_apply_eq_countLikelihood
    (mean : NNReal) (n : ℕ) :
    (ProbabilityTheory.poissonMeasure mean).toPMF n =
      ENNReal.ofReal (PoissonProcess.countLikelihood 1 (mean : ℝ) n) := by
  rw [Measure.toPMF_apply, ProbabilityTheory.poissonMeasure_singleton]
  simp only [PoissonProcess.countLikelihood]
  norm_num

/-- Independent Poisson count PMFs add to a Poisson count PMF with the sum
of their means. This is the count-level convolution used by uniformized
continuous-time transition semigroups. -/
theorem poissonMeasure_toPMF_bind_add (firstMean secondMean : NNReal) :
    (ProbabilityTheory.poissonMeasure firstMean).toPMF.bind (fun first =>
      PMF.map (fun second : ℕ => first + second)
        (ProbabilityTheory.poissonMeasure secondMean).toPMF) =
      (ProbabilityTheory.poissonMeasure (firstMean + secondMean)).toPMF := by
  apply PMF.ext
  intro total
  rw [PMF.bind_apply]
  simp_rw [map_add_left_apply]
  rw [tsum_eq_sum (s := Finset.range (total + 1))]
  · have hfinite :
        (∑ first ∈ Finset.range (total + 1),
          (ProbabilityTheory.poissonMeasure firstMean).toPMF first *
            if first ≤ total then
              (ProbabilityTheory.poissonMeasure secondMean).toPMF (total - first)
            else 0) =
          ∑ first ∈ Finset.range (total + 1),
            (ProbabilityTheory.poissonMeasure firstMean).toPMF first *
              (ProbabilityTheory.poissonMeasure secondMean).toPMF (total - first) := by
      apply Finset.sum_congr rfl
      intro first hfirst
      have hlt : first < total + 1 := Finset.mem_range.mp hfirst
      have hle : first ≤ total := by omega
      rw [if_pos hle]
    rw [hfinite]
    simp_rw [poissonMeasure_toPMF_apply_eq_countLikelihood]
    have hproducts :
        (∑ first ∈ Finset.range (total + 1),
          ENNReal.ofReal (PoissonProcess.countLikelihood 1 (firstMean : ℝ) first) *
            ENNReal.ofReal (PoissonProcess.countLikelihood 1 (secondMean : ℝ)
              (total - first))) =
          ∑ first ∈ Finset.range (total + 1),
            ENNReal.ofReal (PoissonProcess.countLikelihood 1 (firstMean : ℝ) first *
              PoissonProcess.countLikelihood 1 (secondMean : ℝ) (total - first)) := by
      apply Finset.sum_congr rfl
      intro first _
      rw [← ENNReal.ofReal_mul
        (PoissonProcess.countLikelihood_nonneg (by positivity) first)]
    rw [hproducts, ← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      simpa using
        (PoissonProcess.sum_countLikelihood_split_eq_countLikelihood_add
          1 (firstMean : ℝ) (secondMean : ℝ) total)
    · intro first _
      exact mul_nonneg
        (PoissonProcess.countLikelihood_nonneg (by positivity) first)
        (PoissonProcess.countLikelihood_nonneg (by positivity) (total - first))
  · intro first hfirst
    have hfirst : ¬ first ≤ total := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hfirst
    simp [hfirst]

/-- At zero exposure, the Poisson measure is the point mass at zero, also at
the PMF level used by countable-state uniformization. -/
theorem poissonMeasure_toPMF_zero :
    (ProbabilityTheory.poissonMeasure 0).toPMF = PMF.pure 0 := by
  apply PMF.ext
  intro n
  rw [Measure.toPMF_apply]
  rw [ProbabilityTheory.poissonMeasure]
  rw [Measure.sum_apply _ (measurableSet_singleton n)]
  rw [tsum_eq_single 0]
  · by_cases hn : n = 0
    · subst n
      simp
    · simp [hn]
  · intro b hb
    simp [zero_pow hb]

/-- A Poissonized transition row has the identity transition at zero clock
exposure. -/
theorem poissonized_zero {α : Type*} (kernel : CountableMarkovKernel α) :
    poissonized kernel 0 = fun state => PMF.pure state := by
  funext state
  rw [poissonized, poissonMeasure_toPMF_zero, PMF.pure_bind]
  exact iterate_zero kernel ▸ rfl

/-- Poisson mixing upgrades the finite-block composition law of a
countable-state kernel to the continuous-parameter Chapman--Kolmogorov law.
The two Poisson exposures are independent at this PMF level and their counts
add, while the corresponding iterated transition rows compose. -/
theorem poissonized_bind_poissonized {α : Type*} (kernel : CountableMarkovKernel α)
    (firstMean secondMean : NNReal) (state : α) :
    (poissonized kernel firstMean state).bind
      (poissonized kernel secondMean) =
      poissonized kernel (firstMean + secondMean) state := by
  rw [poissonized, PMF.bind_bind]
  calc
    (ProbabilityTheory.poissonMeasure firstMean).toPMF.bind
        (fun first =>
          (iterate kernel first state).bind (fun nextState =>
            (ProbabilityTheory.poissonMeasure secondMean).toPMF.bind
              (fun second => iterate kernel second nextState))) =
      (ProbabilityTheory.poissonMeasure firstMean).toPMF.bind
        (fun first =>
          (ProbabilityTheory.poissonMeasure secondMean).toPMF.bind
            (fun second => iterate kernel (first + second) state)) := by
          congr 1
          funext first
          rw [PMF.bind_comm]
          simp_rw [← iterate_add_apply]
    _ = (ProbabilityTheory.poissonMeasure firstMean).toPMF.bind
        (fun first =>
          (PMF.map (fun second : ℕ => first + second)
            (ProbabilityTheory.poissonMeasure secondMean).toPMF).bind
              (fun total => iterate kernel total state)) := by
          congr 1
          funext first
          symm
          simpa only [Function.comp_apply] using
            (PMF.bind_map (ProbabilityTheory.poissonMeasure secondMean).toPMF
              (fun second : ℕ => first + second)
              (fun total => iterate kernel total state))
    _ = ((ProbabilityTheory.poissonMeasure firstMean).toPMF.bind
        (fun first => PMF.map (fun second : ℕ => first + second)
          (ProbabilityTheory.poissonMeasure secondMean).toPMF)).bind
            (fun total => iterate kernel total state) := by
          rw [PMF.bind_bind]
    _ = poissonized kernel (firstMean + secondMean) state := by
          rw [poissonMeasure_toPMF_bind_add]
          rfl

end CountableMarkovKernel

/-- A PMF is invariant for a countable-state discrete Markov kernel. -/
def PMFStationary {α : Type*} (K : CountableMarkovKernel α) (π : PMF α) : Prop :=
  π.bind K = π

/-- Reversibility/detailed balance for a countable-state PMF kernel. -/
def PMFDetailedBalance {α : Type*} (K : CountableMarkovKernel α) (π : PMF α) : Prop :=
  ∀ x y, π x * K x y = π y * K y x

/-- Detailed balance directly implies one-step invariance, including on an
infinite countable state space. -/
theorem PMFDetailedBalance.stationary
    {α : Type*} {K : CountableMarkovKernel α} {π : PMF α}
    (hbalance : PMFDetailedBalance K π) :
    PMFStationary K π := by
  apply PMF.ext
  intro y
  rw [PMF.bind_apply]
  calc
    (∑' x : α, π x * K x y) = ∑' x : α, π y * K y x :=
      tsum_congr fun x => hbalance x y
    _ = π y * ∑' x : α, K y x := by
      rw [ENNReal.tsum_mul_left]
    _ = π y := by simp

/-- A reflected nearest-neighbor uniformized birth--death kernel: a `true`
Bernoulli draw is a birth, while a `false` draw is a service completion (which
is reflected at zero). -/
noncomputable def reflectedBirthDeathKernel (p : ℝ≥0) (hp : p ≤ 1) :
    CountableMarkovKernel ℕ :=
  fun n => (PMF.bernoulli p hp).map (fun b => if b then n + 1 else n - 1)

lemma hasSum_geoNN (rho : ℝ≥0) (hrho : rho < 1) :
    HasSum (fun n : ℕ => (1 - rho) * rho ^ n) 1 := by
  have hsum := (NNReal.hasSum_geometric hrho).mul_left (1 - rho)
  convert hsum using 1
  have hpos : (0 : ℝ≥0) < 1 - rho := tsub_pos_of_lt hrho
  have hne : (1 - rho : ℝ≥0) ≠ 0 := ne_of_gt hpos
  rw [← div_eq_mul_inv, div_self hne]

noncomputable def geoNNPMF (rho : ℝ≥0) (hrho : rho < 1) : PMF ℕ :=
  ⟨fun n => ↑((1 - rho) * rho ^ n), ENNReal.hasSum_coe.mpr (hasSum_geoNN rho hrho)⟩

@[simp] lemma geoNNPMF_apply (rho : ℝ≥0) (hrho : rho < 1) (n : ℕ) :
    geoNNPMF rho hrho n = ↑((1 - rho) * rho ^ n) := rfl

/-- The NNReal geometric PMF used by uniformization is exactly Mathlib's
real-parameter geometric PMF with success probability `1 - rho`. -/
theorem geoNNPMF_eq_geometricPMF
    (rho : ℝ≥0) (hrho : rho < 1) :
    geoNNPMF rho hrho =
      geometricPMF (p := 1 - (rho : ℝ))
        (sub_pos.mpr (by exact_mod_cast hrho))
        (sub_le_self 1 (by positivity : 0 ≤ (rho : ℝ))) := by
  apply PMF.ext
  intro n
  rw [geoNNPMF_apply]
  change ↑((1 - rho) * rho ^ n) =
    ENNReal.ofReal ((1 - (1 - (rho : ℝ))) ^ n * (1 - (rho : ℝ)))
  rw [show 1 - (1 - (rho : ℝ)) = (rho : ℝ) by ring]
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  change ((↑(1 - rho) : ℝ) * (↑rho : ℝ) ^ n) =
    (↑rho : ℝ) ^ n * (1 - (↑rho : ℝ))
  rw [NNReal.coe_sub (le_of_lt hrho)]
  norm_num
  ring

/-- Measure-level form of `geoNNPMF_eq_geometricPMF`. -/
theorem geoNNPMF_toMeasure_eq_geometricMeasure
    (rho : ℝ≥0) (hrho : rho < 1) :
    (geoNNPMF rho hrho).toMeasure =
      geometricMeasure (p := 1 - (rho : ℝ))
        (sub_pos.mpr (by exact_mod_cast hrho))
        (sub_le_self 1 (by positivity : 0 ≤ (rho : ℝ))) := by
  unfold geometricMeasure
  exact congrArg PMF.toMeasure (geoNNPMF_eq_geometricPMF rho hrho)

lemma reflectedBirthDeathKernel_apply
    (p : ℝ≥0) (hp : p ≤ 1) (n y : ℕ) :
    reflectedBirthDeathKernel p hp n y =
      if y = n + 1 then (p : ℝ≥0∞) else
        if y = n - 1 then ((1 - p : ℝ≥0) : ℝ≥0∞) else 0 := by
  rw [reflectedBirthDeathKernel, PMF.map_apply, tsum_bool]
  simp only [PMF.bernoulli_apply, Bool.cond_true, Bool.cond_false,
    ENNReal.coe_sub, ENNReal.coe_one, ↓reduceIte]
  by_cases hbirth : y = n + 1
  · subst y
    have hne : n + 1 ≠ n - 1 := by omega
    simp [hne]
  · by_cases hdeath : y = n - 1
    · subst y
      simp [hbirth]
    · simp [hbirth, hdeath]

theorem reflectedBirthDeathKernel_congr
    {p q : ℝ≥0} (hp : p ≤ 1) (hq : q ≤ 1) (h : p = q) :
    reflectedBirthDeathKernel p hp = reflectedBirthDeathKernel q hq := by
  subst q
  rfl

noncomputable def uniformizedBirthProbability (rho : ℝ≥0) : ℝ≥0 :=
  rho / (1 + rho)

/-- The signed drift of the birth-versus-potential-service mark is the
traffic-intensity gap divided by the total normalized rate. -/
theorem one_sub_two_mul_uniformizedBirthProbability (rho : ℝ≥0) :
    1 - 2 * (uniformizedBirthProbability rho : ℝ) =
      (1 - (rho : ℝ)) / (1 + (rho : ℝ)) := by
  have hdenom : 1 + (rho : ℝ) ≠ 0 := by positivity
  change 1 - 2 * ((rho : ℝ) / (1 + (rho : ℝ))) = _
  field_simp [hdenom]
  ring

/-- In the stable regime, the absolute drift of a uniformized arrival mark
is bounded by the traffic-intensity gap. -/
theorem one_sub_two_mul_uniformizedBirthProbability_nonneg_le_gap
    (rho : ℝ≥0) (hrho : rho ≤ 1) :
    0 ≤ 1 - 2 * (uniformizedBirthProbability rho : ℝ) ∧
      1 - 2 * (uniformizedBirthProbability rho : ℝ) ≤ 1 - (rho : ℝ) := by
  rw [one_sub_two_mul_uniformizedBirthProbability]
  have hrho_real : (rho : ℝ) ≤ 1 := by exact_mod_cast hrho
  have hgap : 0 ≤ 1 - (rho : ℝ) := sub_nonneg.mpr hrho_real
  have hdenom_pos : 0 < 1 + (rho : ℝ) := by positivity
  constructor
  · exact div_nonneg hgap hdenom_pos.le
  · rw [div_le_iff₀ hdenom_pos]
    nlinarith

lemma uniformizedBirthProbability_lt_one (rho : ℝ≥0) :
    uniformizedBirthProbability rho < 1 := by
  unfold uniformizedBirthProbability
  apply (div_lt_one₀ (by positivity)).mpr
  exact lt_add_of_pos_left rho zero_lt_one

lemma uniformizedBirthProbability_le_one (rho : ℝ≥0) :
    uniformizedBirthProbability rho ≤ 1 :=
  (uniformizedBirthProbability_lt_one rho).le

lemma uniformizedBirthDeath_sum (rho : ℝ≥0) :
    uniformizedBirthProbability rho + 1 / (1 + rho) = 1 := by
  unfold uniformizedBirthProbability
  apply NNReal.eq
  norm_cast
  field_simp
  ring

lemma uniformizedDeathProbability_eq (rho : ℝ≥0) :
    1 - uniformizedBirthProbability rho = 1 / (1 + rho) := by
  unfold uniformizedBirthProbability
  apply (tsub_eq_iff_eq_add_of_le (uniformizedBirthProbability_le_one rho)).mpr
  rw [add_comm]
  exact (uniformizedBirthDeath_sum rho).symm

lemma geo_mass_mul_birth_eq_succ_mul_death (rho : ℝ≥0) (n : ℕ) :
    ((1 - rho) * rho ^ n) * uniformizedBirthProbability rho =
      ((1 - rho) * rho ^ (n + 1)) * (1 / (1 + rho)) := by
  unfold uniformizedBirthProbability
  rw [pow_succ]
  simp only [div_eq_mul_inv]
  ring

lemma coe_geo_mass_mul_birth_eq_succ_mul_death (rho : ℝ≥0) (n : ℕ) :
    (↑((1 - rho) * rho ^ n) : ℝ≥0∞) * ↑(uniformizedBirthProbability rho) =
      ↑((1 - rho) * rho ^ (n + 1)) * ↑(1 / (1 + rho)) := by
  exact_mod_cast geo_mass_mul_birth_eq_succ_mul_death rho n

theorem geoNNPMF_detailedBalance
    (rho : ℝ≥0) (hrho : rho < 1) :
    PMFDetailedBalance
      (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho))
      (geoNNPMF rho hrho) := by
  intro x y
  rw [geoNNPMF_apply, geoNNPMF_apply,
    reflectedBirthDeathKernel_apply, reflectedBirthDeathKernel_apply]
  by_cases hbirth : y = x + 1
  · subst y
    have hne : x ≠ x + 1 + 1 := by omega
    simpa [hne, uniformizedDeathProbability_eq] using
      coe_geo_mass_mul_birth_eq_succ_mul_death rho x
  · by_cases hdeath : y = x - 1
    · cases x with
      | zero =>
          subst y
          simp [uniformizedDeathProbability_eq]
      | succ n =>
          subst y
          have hne : n ≠ n + 1 + 1 := by omega
          simpa [hne, uniformizedDeathProbability_eq] using
            (coe_geo_mass_mul_birth_eq_succ_mul_death rho n).symm
    · cases x with
      | zero =>
          have hyzero : y ≠ 0 := by simpa using hdeath
          have hreverseDeath : 0 ≠ y - 1 := by omega
          simp [hbirth, hyzero, hreverseDeath]
      | succ n =>
          have hy_ne_n : y ≠ n := by simpa using hdeath
          have hn_ne_y : n ≠ y := hy_ne_n.symm
          have hy_ne_nsuccsucc : y ≠ n + 1 + 1 := by simpa using hbirth
          have hreverseDeath : n + 1 ≠ y - 1 := by omega
          simp [hy_ne_n, hn_ne_y, hy_ne_nsuccsucc, hreverseDeath]

/-- The stable geometric law is invariant for the explicitly constructed
discrete-time uniformization of the reflected M/M/1 birth--death chain. -/
theorem geoNNPMF_uniformized_stationary
    (rho : ℝ≥0) (hrho : rho < 1) :
    PMFStationary
      (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho))
      (geoNNPMF rho hrho) :=
  (geoNNPMF_detailedBalance rho hrho).stationary

/-- Traffic intensity from nonnegative M/M/1 rates, kept in `ℝ≥0` for the
discrete PMF construction. -/
noncomputable def mm1TrafficIntensityNN
    (arrivalRate serviceRate : ℝ≥0) : ℝ≥0 :=
  arrivalRate / serviceRate

theorem mm1TrafficIntensityNN_lt_one
    {arrivalRate serviceRate : ℝ≥0} (hstable : arrivalRate < serviceRate) :
    mm1TrafficIntensityNN arrivalRate serviceRate < 1 := by
  unfold mm1TrafficIntensityNN
  have hservice_pos : 0 < serviceRate :=
    lt_of_le_of_lt (zero_le arrivalRate) hstable
  apply (div_lt_one₀ hservice_pos).mpr
  exact hstable

theorem coe_mm1TrafficIntensityNN_eq_mm1TrafficIntensity
    (arrivalRate serviceRate : ℝ≥0) :
    (mm1TrafficIntensityNN arrivalRate serviceRate : ℝ) =
      mm1TrafficIntensity (arrivalRate : ℝ) (serviceRate : ℝ) := by
  unfold mm1TrafficIntensityNN mm1TrafficIntensity
  norm_cast

theorem uniformizedBirthProbability_eq_rate_fraction
    {arrivalRate serviceRate : ℝ≥0} (hservice_pos : 0 < serviceRate) :
    uniformizedBirthProbability
      (mm1TrafficIntensityNN arrivalRate serviceRate) =
      arrivalRate / (arrivalRate + serviceRate) := by
  unfold uniformizedBirthProbability mm1TrafficIntensityNN
  apply NNReal.eq
  norm_cast
  field_simp [ne_of_gt hservice_pos]
  ring

theorem rate_fraction_le_one
    (arrivalRate serviceRate : ℝ≥0) :
    arrivalRate / (arrivalRate + serviceRate) ≤ 1 := by
  by_cases hsum : arrivalRate + serviceRate = 0
  · simp [hsum]
  · apply (div_le_one₀ (by positivity)).mpr
    exact le_add_right (le_refl arrivalRate)

/-- With stable nonnegative rates, the explicitly uniformized M/M/1 kernel
has birth probability `λ / (λ + μ)` and leaves the geometric queue law
invariant.  This is a discrete-time result only; it does not construct the
continuous-time Poisson-clock queue process. -/
theorem mm1_uniformized_geometric_stationary
    (arrivalRate serviceRate : ℝ≥0) (hstable : arrivalRate < serviceRate) :
    PMFStationary
      (reflectedBirthDeathKernel
        (arrivalRate / (arrivalRate + serviceRate))
        (rate_fraction_le_one arrivalRate serviceRate))
      (geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
        (mm1TrafficIntensityNN_lt_one hstable)) := by
  have hservice_pos : 0 < serviceRate :=
    lt_of_le_of_lt (zero_le arrivalRate) hstable
  have hp := uniformizedBirthProbability_eq_rate_fraction
    (arrivalRate := arrivalRate) (serviceRate := serviceRate) hservice_pos
  have hK :
      reflectedBirthDeathKernel
        (arrivalRate / (arrivalRate + serviceRate))
        (rate_fraction_le_one arrivalRate serviceRate) =
      reflectedBirthDeathKernel
        (uniformizedBirthProbability (mm1TrafficIntensityNN arrivalRate serviceRate))
        (uniformizedBirthProbability_le_one
          (mm1TrafficIntensityNN arrivalRate serviceRate)) := by
    exact reflectedBirthDeathKernel_congr _ _ hp.symm
  rw [hK]
  exact geoNNPMF_uniformized_stationary
    (mm1TrafficIntensityNN arrivalRate serviceRate)
    (mm1TrafficIntensityNN_lt_one hstable)

/-- Pointwise, the discrete PMF's real mass is the generator module's
geometric M/M/1 stationary mass. -/
theorem geoNNPMF_toReal_eq_mm1StationaryMass
    (rho : ℝ≥0) (hrho : rho < 1) (n : ℕ) :
    (geoNNPMF rho hrho n).toReal = mm1StationaryMass (rho : ℝ) n := by
  rw [geoNNPMF_apply]
  simp [mm1StationaryMass]
  rw [ENNReal.toReal_sub_of_le]
  · simp
    ring
  · exact_mod_cast (le_of_lt hrho)
  · simp

end AppliedModelingLib.Probability.Queueing
