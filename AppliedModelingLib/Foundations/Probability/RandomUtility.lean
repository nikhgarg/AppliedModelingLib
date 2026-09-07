import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Random-Utility Noise Kernels

Reusable pointwise inequalities for one-dimensional random-utility models. They
are intentionally paper-neutral. Caller-specific ranking maps, payoff
certificates, and theorem-number wrappers should stay in the paper folder until
another paper needs the same abstraction.

## Main declarations

- `StrictlyWellOrderedNoise`
- `WeaklyWellOrderedNoise`
- `gaussianNoiseKernel_strictlyWellOrdered`
- `laplacianNoiseKernel_weaklyWellOrdered`
- `laplacianNoiseKernel_not_strictlyWellOrdered`
- `laplacianNoiseKernel_strictlyWellOrdered_of_overlap`
- `rumContractScore`
- `rumContractScore_preserves_weak_order`
- `rumContractScore_value_le_of_raw_max_and_contract_max`
- `weaklyWellOrderedNoise_swap_middle_density_le`
- `weaklyWellOrderedNoise_swap12_density3_le`
-/

namespace AppliedModelingLib
namespace Probability

noncomputable section

/--
Strict well-ordering condition for one-dimensional additive noise kernels.

For `a > b` and `c > d`, assigning the larger realized value to the larger true
value is strictly more likely than the crossed assignment.
-/
def StrictlyWellOrderedNoise (f : ℝ → ℝ) : Prop :=
  ∀ ⦃a b c d : ℝ⦄, b < a → d < c →
    f (a - c) * f (b - d) > f (a - d) * f (b - c)

/--
Weak well-ordering condition for one-dimensional additive noise kernels.
This covers Laplacian kernels, where the strict inequality can be an equality
when the ordered intervals are separated.
-/
def WeaklyWellOrderedNoise (f : ℝ → ℝ) : Prop :=
  ∀ ⦃a b c d : ℝ⦄, b < a → d < c →
    f (a - d) * f (b - c) ≤ f (a - c) * f (b - d)

/-- The strict well-ordering condition immediately gives the weak comparison. -/
theorem StrictlyWellOrderedNoise.weak {f : ℝ → ℝ}
    (hf : StrictlyWellOrderedNoise f) :
    WeaklyWellOrderedNoise f := by
  intro a b c d hab hcd
  exact le_of_lt (hf hab hcd)

/--
Multiplication by a positive normalizing constant preserves strict
well-ordering. This lets paper proofs move between unnormalized kernels and
actual density functions.
-/
theorem StrictlyWellOrderedNoise.const_mul_pos {f : ℝ → ℝ} {c : ℝ}
    (hf : StrictlyWellOrderedNoise f) (hc : 0 < c) :
    StrictlyWellOrderedNoise (fun z => c * f z) := by
  intro a b x y hab hxy
  have h := hf hab hxy
  have hc2 : 0 < c * c := mul_pos hc hc
  have hscaled := mul_lt_mul_of_pos_left h hc2
  nlinarith

/--
Multiplication by a nonnegative normalizing constant preserves weak
well-ordering.
-/
theorem WeaklyWellOrderedNoise.const_mul_nonneg {f : ℝ → ℝ} {c : ℝ}
    (hf : WeaklyWellOrderedNoise f) (hc : 0 ≤ c) :
    WeaklyWellOrderedNoise (fun z => c * f z) := by
  intro a b x y hab hxy
  have h := hf hab hxy
  have hc2 : 0 ≤ c * c := mul_nonneg hc hc
  have hscaled := mul_le_mul_of_nonneg_left h hc2
  nlinarith

/-- Gaussian density kernel, omitting the positive normalizing constant. -/
def gaussianNoiseKernel (κ : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-κ * x ^ 2)

/-- Laplacian density kernel, omitting the positive normalizing constant. -/
def laplacianNoiseKernel (lam : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-lam * |x|)

theorem gaussianNoiseKernel_pos (κ x : ℝ) :
    0 < gaussianNoiseKernel κ x := by
  unfold gaussianNoiseKernel
  exact Real.exp_pos _

theorem gaussianNoiseKernel_nonneg (κ x : ℝ) :
    0 ≤ gaussianNoiseKernel κ x :=
  le_of_lt (gaussianNoiseKernel_pos κ x)

theorem laplacianNoiseKernel_pos (lam x : ℝ) :
    0 < laplacianNoiseKernel lam x := by
  unfold laplacianNoiseKernel
  exact Real.exp_pos _

theorem laplacianNoiseKernel_nonneg (lam x : ℝ) :
    0 ≤ laplacianNoiseKernel lam x :=
  le_of_lt (laplacianNoiseKernel_pos lam x)

/--
The algebraic core of the Gaussian well-ordering proof: swapping the larger
realized value to the larger true value improves the negative squared-error
exponent by `2κ(a-b)(c-d)`.
-/
theorem gaussian_exponent_cross_lt_ordered
    {κ a b c d : ℝ} (hκ : 0 < κ) (hab : b < a) (hcd : d < c) :
    -κ * (a - d) ^ 2 + -κ * (b - c) ^ 2 <
      -κ * (a - c) ^ 2 + -κ * (b - d) ^ 2 := by
  have hab_pos : 0 < a - b := sub_pos.mpr hab
  have hcd_pos : 0 < c - d := sub_pos.mpr hcd
  have hprod : 0 < 2 * κ * (a - b) * (c - d) := by
    have hκab : 0 < κ * (a - b) := mul_pos hκ hab_pos
    have h2κab : 0 < 2 * (κ * (a - b)) := mul_pos zero_lt_two hκab
    have hmain : 0 < (2 * (κ * (a - b))) * (c - d) := mul_pos h2κab hcd_pos
    simpa [mul_assoc] using hmain
  have hid :
      (-κ * (a - c) ^ 2 + -κ * (b - d) ^ 2) -
          (-κ * (a - d) ^ 2 + -κ * (b - c) ^ 2) =
        2 * κ * (a - b) * (c - d) := by
    ring
  have hdiff :
      0 <
        (-κ * (a - c) ^ 2 + -κ * (b - d) ^ 2) -
          (-κ * (a - d) ^ 2 + -κ * (b - c) ^ 2) := by
    rw [hid]
    exact hprod
  exact sub_pos.mp hdiff

/-- Gaussian kernels satisfy the strict well-ordering condition. -/
theorem gaussianNoiseKernel_strictlyWellOrdered
    {κ : ℝ} (hκ : 0 < κ) :
    StrictlyWellOrderedNoise (gaussianNoiseKernel κ) := by
  intro a b c d hab hcd
  unfold gaussianNoiseKernel
  rw [← Real.exp_add, ← Real.exp_add]
  exact Real.exp_lt_exp.mpr
    (gaussian_exponent_cross_lt_ordered hκ hab hcd)

/-- Four-point rearrangement inequality for absolute distance on the line. -/
theorem abs_ordered_cross_le_ordered
    {a b c d : ℝ} (hab : b ≤ a) (hcd : d ≤ c) :
    |a - c| + |b - d| ≤ |a - d| + |b - c| := by
  cases abs_cases (a - c) <;>
    cases abs_cases (b - d) <;>
    cases abs_cases (a - d) <;>
    cases abs_cases (b - c) <;>
    linarith

/--
Strict four-point rearrangement for absolute distance when the two ordered
intervals overlap (`b < c` and `d < a`).
-/
theorem abs_ordered_cross_lt_ordered_of_overlap
    {a b c d : ℝ} (hab : b < a) (hcd : d < c) (hbc : b < c) (hda : d < a) :
    |a - c| + |b - d| < |a - d| + |b - c| := by
  cases abs_cases (a - c) <;>
    cases abs_cases (b - d) <;>
    cases abs_cases (a - d) <;>
    cases abs_cases (b - c) <;>
    linarith

/-- Laplacian kernels satisfy the weak well-ordering inequality. -/
theorem laplacianNoiseKernel_weaklyWellOrdered
    {lam : ℝ} (hlam : 0 ≤ lam) :
    WeaklyWellOrderedNoise (laplacianNoiseKernel lam) := by
  intro a b c d hab hcd
  have habs := abs_ordered_cross_le_ordered
    (a := a) (b := b) (c := c) (d := d) (le_of_lt hab) (le_of_lt hcd)
  unfold laplacianNoiseKernel
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hmul :
      (-lam) * (|a - d| + |b - c|) ≤
        (-lam) * (|a - c| + |b - d|) := by
    exact mul_le_mul_of_nonpos_left habs (neg_nonpos.mpr hlam)
  linarith

/--
The strict well-ordering condition is not satisfied by the Laplacian kernel:
for separated ordered pairs, both assignments have the same total absolute
deviation.
-/
theorem laplacianNoiseKernel_not_strictlyWellOrdered (lam : ℝ) :
    ¬ StrictlyWellOrderedNoise (laplacianNoiseKernel lam) := by
  intro h
  have hbad := h (a := (10 : ℝ)) (b := 9) (c := 1) (d := 0)
    (by norm_num) (by norm_num)
  have heq :
      laplacianNoiseKernel lam ((10 : ℝ) - 1) *
          laplacianNoiseKernel lam (9 - 0) =
        laplacianNoiseKernel lam ((10 : ℝ) - 0) *
          laplacianNoiseKernel lam (9 - 1) := by
    unfold laplacianNoiseKernel
    norm_num
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hbad
  exact lt_irrefl _ hbad

/--
Laplacian kernels satisfy the strict well-ordering inequality on the overlap
region.  With `b < a` and `d < c`, the extra hypotheses `b < c` and `d < a`
say exactly that the open intervals `(b,a)` and `(d,c)` overlap.  This is the
pointwise strict case left after removing separated interval equality cases.
-/
theorem laplacianNoiseKernel_strictlyWellOrdered_of_overlap
    {lam a b c d : ℝ} (hlam : 0 < lam)
    (hab : b < a) (hcd : d < c) (hbc : b < c) (hda : d < a) :
    laplacianNoiseKernel lam (a - c) * laplacianNoiseKernel lam (b - d) >
      laplacianNoiseKernel lam (a - d) * laplacianNoiseKernel lam (b - c) := by
  have habs := abs_ordered_cross_lt_ordered_of_overlap hab hcd hbc hda
  unfold laplacianNoiseKernel
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_lt_exp.mpr
  have hmul :
      (-lam) * (|a - d| + |b - c|) <
      (-lam) * (|a - c| + |b - d|) := by
    exact mul_lt_mul_of_neg_left habs (by linarith)
  linarith

/-! ## Additive RUM contraction geometry -/

/--
One-coordinate contraction toward the true value:
`r' = x + t * (r - x)`.

For `0 ≤ t ≤ 1`, this is the usual additive-RUM interpolation between the true
score `x` and realized score `r`.
-/
def rumContractScore (t x r : ℝ) : ℝ :=
  x + t * (r - x)

theorem rumContractScore_eq_affine (t x r : ℝ) :
    rumContractScore t x r = (1 - t) * x + t * r := by
  unfold rumContractScore
  ring

theorem rumContractScore_sub
    (t xi xj ri rj : ℝ) :
    rumContractScore t xi ri - rumContractScore t xj rj =
      (1 - t) * (xi - xj) + t * (ri - rj) := by
  rw [rumContractScore_eq_affine, rumContractScore_eq_affine]
  ring

/--
Explicit finite score box forcing a top switch under contraction.

The box has the lower-valued raw top `low`, the higher-valued contracted top
`high`, and all other alternatives far below.  The caller supplies the two
margin inequalities at the box endpoints; a later paper proof can discharge
those margins from concrete choices of `eps` and `K`.
-/
theorem rumContractScore_topSwitch_openBox_of_parameters
    {ι : Type*} [DecidableEq ι]
    {t eps K : ℝ} {value : ι → ℝ} {low high : ι}
    (ht0 : 0 ≤ t) (hlowhigh : low ≠ high)
    (heps : 0 < eps) (hKpos : 0 < K)
    (hhigh_low :
      rumContractScore t (value low) eps <
        rumContractScore t (value high) (-(eps / 8)))
    (hhigh_other :
      ∀ d : ι, d ≠ low → d ≠ high →
        rumContractScore t (value d) (-K) <
          rumContractScore t (value high) (-(eps / 8))) :
    ∃ a b : ι → ℝ,
      (∀ i, a i < b i) ∧
      (∀ score ∈ Set.pi Set.univ (fun i => Set.Ioo (a i) (b i)),
        ∀ d : ι, d ≠ low → score d < score low) ∧
      (∀ score ∈ Set.pi Set.univ (fun i => Set.Ioo (a i) (b i)),
        ∀ d : ι, d ≠ high →
          rumContractScore t (value d) (score d) <
            rumContractScore t (value high) (score high)) := by
  classical
  let a : ι → ℝ := fun i =>
    if i = low then eps / 2 else if i = high then -(eps / 8) else -K - 1
  let b : ι → ℝ := fun i =>
    if i = low then eps else if i = high then eps / 8 else -K
  refine ⟨a, b, ?_, ?_, ?_⟩
  · intro i
    by_cases hilow : i = low
    · simp [a, b, hilow]
      linarith
    · by_cases hihigh : i = high
      · have hhighlow : high ≠ low := fun h => hlowhigh h.symm
        simp [a, b, hihigh, hhighlow]
        linarith
      · simp [a, b, hilow, hihigh]
  · intro score hscore d hdlow
    have hlow_mem : score low ∈ Set.Ioo (a low) (b low) :=
      hscore low (Set.mem_univ low)
    have hd_mem : score d ∈ Set.Ioo (a d) (b d) :=
      hscore d (Set.mem_univ d)
    by_cases hdhigh : d = high
    · subst d
      have hhighlow : high ≠ low := fun h => hlowhigh h.symm
      simp [a, b] at hlow_mem
      simp [a, b, hhighlow] at hd_mem
      linarith
    · simp [a, b, hdlow, hdhigh] at hd_mem
      simp [a, b] at hlow_mem
      have hneg : -K < eps / 2 := by
        nlinarith
      linarith
  · intro score hscore d hdhigh
    have hhigh_mem : score high ∈ Set.Ioo (a high) (b high) :=
      hscore high (Set.mem_univ high)
    have hd_mem : score d ∈ Set.Ioo (a d) (b d) :=
      hscore d (Set.mem_univ d)
    have hhigh_lower : -(eps / 8) < score high := by
      have hhighlow : high ≠ low := fun h => hlowhigh h.symm
      simp [a, b, hhighlow] at hhigh_mem
      exact hhigh_mem.1
    by_cases hdlow : d = low
    · subst d
      have hlow_upper : score low < eps := by
        simp [a, b] at hd_mem
        exact hd_mem.2
      have hleft_le :
          rumContractScore t (value low) (score low) ≤
            rumContractScore t (value low) eps := by
        rw [rumContractScore_eq_affine, rumContractScore_eq_affine]
        nlinarith
      have hright_le :
          rumContractScore t (value high) (-(eps / 8)) ≤
            rumContractScore t (value high) (score high) := by
        rw [rumContractScore_eq_affine, rumContractScore_eq_affine]
        nlinarith
      linarith
    · have hd_upper : score d < -K := by
        simp [a, b, hdlow, hdhigh] at hd_mem
        exact hd_mem.2
      have hleft_le :
          rumContractScore t (value d) (score d) ≤
            rumContractScore t (value d) (-K) := by
        rw [rumContractScore_eq_affine, rumContractScore_eq_affine]
        nlinarith
      have hright_le :
          rumContractScore t (value high) (-(eps / 8)) ≤
            rumContractScore t (value high) (score high) := by
        rw [rumContractScore_eq_affine, rumContractScore_eq_affine]
        nlinarith
      have hmargin := hhigh_other d hdlow hdhigh
      linarith

/--
The explicit top-switch margins used by
`rumContractScore_topSwitch_openBox_of_parameters` can always be chosen when
`0 < t < 1` and `high` has strictly larger true value than `low` over a finite
alternative set.
-/
theorem exists_rumContractScore_topSwitch_parameters
    {ι : Type*} [Fintype ι]
    {t : ℝ} {value : ι → ℝ} {low high : ι}
    (htpos : 0 < t) (htlt1 : t < 1)
    (hvalue : value low < value high) :
    ∃ eps K : ℝ,
      0 < eps ∧ 0 < K ∧
      rumContractScore t (value low) eps <
        rumContractScore t (value high) (-(eps / 8)) ∧
      ∀ d : ι, d ≠ low → d ≠ high →
        rumContractScore t (value d) (-K) <
          rumContractScore t (value high) (-(eps / 8)) := by
  classical
  let vals : Finset ℝ := Finset.univ.image value
  have hvals_nonempty : vals.Nonempty := by
    exact ⟨value high, by simp [vals]⟩
  let M : ℝ := vals.max' hvals_nonempty
  have hleM : ∀ d : ι, value d ≤ M := by
    intro d
    exact Finset.le_max' vals (value d) (by simp [vals])
  let gap : ℝ := value high - value low
  have hgap : 0 < gap := by
    dsimp [gap]
    exact sub_pos.mpr hvalue
  have h1t : 0 < 1 - t := sub_pos.mpr htlt1
  let eps : ℝ := ((1 - t) * gap) / (16 * t)
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  let K : ℝ := (((1 - t) * (M - value high) + t * (eps / 8) + 1) / t)
  have hM_high : value high ≤ M := hleM high
  have hKpos : 0 < K := by
    dsimp [K]
    have hnonneg_M : 0 ≤ M - value high := sub_nonneg.mpr hM_high
    have hnonneg_term : 0 ≤ (1 - t) * (M - value high) :=
      mul_nonneg (le_of_lt h1t) hnonneg_M
    have hnonneg_eps : 0 ≤ t * (eps / 8) := by positivity
    positivity
  refine ⟨eps, K, heps, hKpos, ?_, ?_⟩
  · rw [rumContractScore_eq_affine, rumContractScore_eq_affine]
    have htne : t ≠ 0 := ne_of_gt htpos
    dsimp [eps, gap]
    field_simp [htne]
    nlinarith [hgap, h1t]
  · intro d _hdlow _hdhigh
    rw [rumContractScore_eq_affine, rumContractScore_eq_affine]
    have hle : value d ≤ M := hleM d
    have htne : t ≠ 0 := ne_of_gt htpos
    dsimp [K]
    field_simp [htne]
    nlinarith [hle, h1t]

/-- Candidate `x₁` is weakly first among three realized scores. -/
def rum3TopFirstByScores (s1 s2 s3 : ℝ) : Prop :=
  s2 ≤ s1 ∧ s3 ≤ s1

/-- Candidate `x₂` strictly beats `x₁` and weakly beats `x₃`. -/
def rum3MiddleBeatsTopByScores (s1 s2 s3 : ℝ) : Prop :=
  s1 < s2 ∧ s3 ≤ s2

/-- Candidate `x₃` is weakly first among three realized scores. -/
def rum3BottomFirstByScores (s1 s2 s3 : ℝ) : Prop :=
  s1 ≤ s3 ∧ s2 ≤ s3

/--
Contraction cannot reverse an already-correct weak order between two
alternatives.
-/
theorem rumContractScore_preserves_weak_order
    {t xi xj ri rj : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : xj ≤ xi) (hr : rj ≤ ri) :
    rumContractScore t xj rj ≤ rumContractScore t xi ri := by
  have hx_nonneg : 0 ≤ xi - xj := sub_nonneg.mpr hx
  have hr_nonneg : 0 ≤ ri - rj := sub_nonneg.mpr hr
  have h1t : 0 ≤ 1 - t := by linarith
  have hdiff :
      0 ≤ rumContractScore t xi ri - rumContractScore t xj rj := by
    rw [rumContractScore_sub]
    nlinarith [mul_nonneg h1t hx_nonneg, mul_nonneg ht0 hr_nonneg]
  linarith

/--
Strict version of the contraction order lemma. If both true values and realized
scores put alternative `i` above alternative `j`, contraction keeps `i`
strictly above `j`.
-/
theorem rumContractScore_preserves_strict_order
    {t xi xj ri rj : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : xj < xi) (hr : rj < ri) :
    rumContractScore t xj rj < rumContractScore t xi ri := by
  have hx_pos : 0 < xi - xj := sub_pos.mpr hx
  have hr_pos : 0 < ri - rj := sub_pos.mpr hr
  have h1t : 0 ≤ 1 - t := by linarith
  have hdiff_pos :
      0 < rumContractScore t xi ri - rumContractScore t xj rj := by
    rw [rumContractScore_sub]
    by_cases htpos : 0 < t
    · have hterm2 : 0 < t * (ri - rj) := mul_pos htpos hr_pos
      have hterm1 : 0 ≤ (1 - t) * (xi - xj) :=
        mul_nonneg h1t (le_of_lt hx_pos)
      nlinarith
    · have ht_eq : t = 0 := le_antisymm (le_of_not_gt htpos) ht0
      nlinarith
  linarith

/--
If a raw-score winner is beaten after a genuine contraction, the contracted
winner must have weakly higher true value.

This is the two-alternative core of finite RUM monotonicity: with `t < 1`, a
lower true-value alternative cannot overtake a raw-score maximizer merely by
contracting scores toward true values.
-/
theorem rumContractScore_value_le_of_raw_le_and_contract_ge
    {t xi xj ri rj : ℝ}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hr : ri ≤ rj)
    (hc : rumContractScore t xj rj ≤ rumContractScore t xi ri) :
    xj ≤ xi := by
  by_contra hnot
  have hx : xi < xj := lt_of_not_ge hnot
  have h1t : 0 < 1 - t := by linarith
  have hx_pos : 0 < xj - xi := sub_pos.mpr hx
  have hr_nonneg : 0 ≤ rj - ri := sub_nonneg.mpr hr
  have hdiff :
      0 < rumContractScore t xj rj - rumContractScore t xi ri := by
    rw [rumContractScore_sub]
    nlinarith [mul_pos h1t hx_pos, mul_nonneg ht0 hr_nonneg]
  linarith

/--
Argmax form of `rumContractScore_value_le_of_raw_le_and_contract_ge`.

If `rawBest` maximizes raw realized scores and `contractBest` maximizes the
contracted scores, then the latter has weakly higher true value.  The statement
is deliberately independent of any particular finite argmax construction; users
can instantiate the two maximality hypotheses with rankings, finite search, or
explicit witnesses.
-/
theorem rumContractScore_value_le_of_raw_max_and_contract_max
    {ι : Type*} {t : ℝ} {value raw : ι → ℝ}
    {rawBest contractBest : ι}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hrawMax : ∀ i : ι, raw i ≤ raw rawBest)
    (hcontractMax : ∀ i : ι,
      rumContractScore t (value i) (raw i) ≤
        rumContractScore t (value contractBest) (raw contractBest)) :
    value rawBest ≤ value contractBest :=
  rumContractScore_value_le_of_raw_le_and_contract_ge
    (xi := value contractBest) (xj := value rawBest)
    (ri := raw contractBest) (rj := raw rawBest)
    ht0 htlt1 (hrawMax contractBest) (hcontractMax rawBest)

/--
Feasible-set form of `rumContractScore_value_le_of_raw_max_and_contract_max`.

The predicate `feasible` can be a remaining candidate set, a constrained choice
set, or any local comparison domain.  If `rawBest` maximizes raw scores on that
domain and `contractBest` maximizes contracted scores on the same domain, then
`contractBest` has weakly higher true value.
-/
theorem rumContractScore_value_le_of_raw_max_on_and_contract_max_on
    {ι : Type*} {t : ℝ} {value raw : ι → ℝ} {feasible : ι → Prop}
    {rawBest contractBest : ι}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hrawMem : feasible rawBest) (hcontractMem : feasible contractBest)
    (hrawMax : ∀ i : ι, feasible i → raw i ≤ raw rawBest)
    (hcontractMax : ∀ i : ι, feasible i →
      rumContractScore t (value i) (raw i) ≤
        rumContractScore t (value contractBest) (raw contractBest)) :
    value rawBest ≤ value contractBest :=
  rumContractScore_value_le_of_raw_le_and_contract_ge
    (xi := value contractBest) (xj := value rawBest)
    (ri := raw contractBest) (rj := raw rawBest)
    ht0 htlt1 (hrawMax contractBest hcontractMem)
    (hcontractMax rawBest hrawMem)

/--
Three-alternative top-first preservation: if `x₁` is first before contraction,
it is still first after contraction.
-/
theorem rum3_contract_top_first_of_original_top_first
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 ≤ x1) (hx13 : x3 ≤ x1)
    (hr12 : r2 ≤ r1) (hr13 : r3 ≤ r1) :
    rumContractScore t x2 r2 ≤ rumContractScore t x1 r1 ∧
      rumContractScore t x3 r3 ≤ rumContractScore t x1 r1 :=
  ⟨rumContractScore_preserves_weak_order ht0 ht1 hx12 hr12,
    rumContractScore_preserves_weak_order ht0 ht1 hx13 hr13⟩

/--
Three-alternative bottom-first reflection: if the lowest-value alternative is
first after contraction, then it was already first before contraction.
-/
theorem rum3_contract_bottom_first_imp_original_bottom_first
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx31 : x3 < x1) (hx32 : x3 < x2)
    (hc31 : rumContractScore t x1 r1 ≤ rumContractScore t x3 r3)
    (hc32 : rumContractScore t x2 r2 ≤ rumContractScore t x3 r3) :
    r1 ≤ r3 ∧ r2 ≤ r3 := by
  constructor
  · by_contra h
    have hr : r3 < r1 := lt_of_not_ge h
    have hc_lt :
        rumContractScore t x3 r3 < rumContractScore t x1 r1 :=
      rumContractScore_preserves_strict_order ht0 ht1 hx31 hr
    linarith
  · by_contra h
    have hr : r3 < r2 := lt_of_not_ge h
    have hc_lt :
        rumContractScore t x3 r3 < rumContractScore t x2 r2 :=
      rumContractScore_preserves_strict_order ht0 ht1 hx32 hr
    linarith

/--
Strict bottom-first reflection for a genuine contraction (`t < 1`).
-/
theorem rum3_contract_bottom_first_imp_original_bottom_first_strict_of_t_lt_one
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hx31 : x3 < x1) (hx32 : x3 < x2)
    (hc31 : rumContractScore t x1 r1 ≤ rumContractScore t x3 r3)
    (hc32 : rumContractScore t x2 r2 ≤ rumContractScore t x3 r3) :
    r1 < r3 ∧ r2 < r3 := by
  have h1t : 0 < 1 - t := by linarith
  constructor
  · by_contra hnot
    have hr31 : r3 ≤ r1 := le_of_not_gt hnot
    have hx_pos : 0 < x1 - x3 := sub_pos.mpr hx31
    have hr_nonneg : 0 ≤ r1 - r3 := sub_nonneg.mpr hr31
    have hdiff :
        0 < rumContractScore t x1 r1 - rumContractScore t x3 r3 := by
      rw [rumContractScore_sub]
      nlinarith [mul_pos h1t hx_pos, mul_nonneg ht0 hr_nonneg]
    linarith
  · by_contra hnot
    have hr32 : r3 ≤ r2 := le_of_not_gt hnot
    have hx_pos : 0 < x2 - x3 := sub_pos.mpr hx32
    have hr_nonneg : 0 ≤ r2 - r3 := sub_nonneg.mpr hr32
    have hdiff :
        0 < rumContractScore t x2 r2 - rumContractScore t x3 r3 := by
      rw [rumContractScore_sub]
      nlinarith [mul_pos h1t hx_pos, mul_nonneg ht0 hr_nonneg]
    linarith

/--
If a middle alternative beats a top alternative after contraction, then its
original realized score is strictly higher than the top alternative's score.
-/
theorem rum3_swap_middle_base_score_lt
    {t x1 x2 r1 r2 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1)
    (hc12 :
      rumContractScore t x1 r1 <
        rumContractScore t x2 r2) :
    r1 < r2 := by
  by_contra hnot
  have hr21 : r2 ≤ r1 := le_of_not_gt hnot
  have hcontract :
      rumContractScore t x2 r2 ≤ rumContractScore t x1 r1 :=
    rumContractScore_preserves_weak_order ht0 ht1 (le_of_lt hx12) hr21
  linarith

/--
The deterministic coordinate-swap geometry used by three-alternative RUM
proofs: a bottom-first realization whose contraction makes the middle
alternative beat the top can be sent, by swapping the top and middle realized
scores, to a bottom-first realization where the contracted top wins.
-/
theorem rum3_swap_middle_transition_geometry
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1)
    (hr13 : r1 ≤ r3) (hr23 : r2 ≤ r3)
    (hc12 : rumContractScore t x1 r1 < rumContractScore t x2 r2)
    (hc32 : rumContractScore t x3 r3 ≤ rumContractScore t x2 r2) :
    r2 ≤ r3 ∧ r1 ≤ r3 ∧
      rumContractScore t x2 r1 ≤ rumContractScore t x1 r2 ∧
      rumContractScore t x3 r3 ≤ rumContractScore t x1 r2 := by
  have hr12 : r1 < r2 := by
    by_contra hnot
    have hr21 : r2 ≤ r1 := le_of_not_gt hnot
    have hcontract :
        rumContractScore t x2 r2 ≤ rumContractScore t x1 r1 :=
      rumContractScore_preserves_weak_order ht0 ht1 (le_of_lt hx12) hr21
    linarith
  have hswap12 :
      rumContractScore t x2 r1 ≤ rumContractScore t x1 r2 :=
    le_of_lt (rumContractScore_preserves_strict_order ht0 ht1 hx12 hr12)
  have hsameRealization :
      rumContractScore t x2 r2 ≤ rumContractScore t x1 r2 :=
    rumContractScore_preserves_weak_order ht0 ht1 (le_of_lt hx12) le_rfl
  exact ⟨hr23, hr13, hswap12, le_trans hc32 hsameRealization⟩

/-! ## Additive RUM density-product comparisons -/

theorem weaklyWellOrderedNoise_swap_middle_density_le
    {f : ℝ → ℝ} (hf : WeaklyWellOrderedNoise f)
    {x1 x2 r1 r2 : ℝ} (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) ≤ f (r2 - x1) * f (r1 - x2) := by
  have h := hf (a := r2) (b := r1) (c := x1) (d := x2) hr12 hx12
  calc
    f (r1 - x1) * f (r2 - x2) =
        f (r2 - x2) * f (r1 - x1) := by ring
    _ ≤ f (r2 - x1) * f (r1 - x2) := h

theorem strictlyWellOrderedNoise_swap_middle_density_lt
    {f : ℝ → ℝ} (hf : StrictlyWellOrderedNoise f)
    {x1 x2 r1 r2 : ℝ} (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) < f (r2 - x1) * f (r1 - x2) := by
  have h := hf (a := r2) (b := r1) (c := x1) (d := x2) hr12 hx12
  calc
    f (r1 - x1) * f (r2 - x2) =
        f (r2 - x2) * f (r1 - x1) := by ring
    _ < f (r2 - x1) * f (r1 - x2) := h

/--
Pointwise three-coordinate density comparison for swapping top and middle
realized scores in a wrong `x₁`/`x₂` pairwise realization.
-/
theorem weaklyWellOrderedNoise_swap12_density3_le
    {f : ℝ → ℝ} (hf : WeaklyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 ≤ f (r3 - x3))
    (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) ≤
      f (r2 - x1) * f (r1 - x2) * f (r3 - x3) := by
  have hpair := weaklyWellOrderedNoise_swap_middle_density_le
    (f := f) hf hx12 hr12
  exact mul_le_mul_of_nonneg_right hpair hctx

/--
Strict three-coordinate density comparison for swapping top and middle realized
scores in a wrong `x₁`/`x₂` pairwise realization.
-/
theorem strictlyWellOrderedNoise_swap12_density3_lt
    {f : ℝ → ℝ} (hf : StrictlyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 < f (r3 - x3))
    (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) <
      f (r2 - x1) * f (r1 - x2) * f (r3 - x3) := by
  have hpair := strictlyWellOrderedNoise_swap_middle_density_lt
    (f := f) hf hx12 hr12
  exact mul_lt_mul_of_pos_right hpair hctx

/--
Pointwise three-coordinate density comparison for swapping middle and bottom
realized scores in a wrong `x₂`/`x₃` pairwise realization.
-/
theorem weaklyWellOrderedNoise_swap23_density3_le
    {f : ℝ → ℝ} (hf : WeaklyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 ≤ f (r1 - x1))
    (hx23 : x3 < x2) (hr23 : r2 < r3) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) ≤
      f (r1 - x1) * f (r3 - x2) * f (r2 - x3) := by
  have hpair := weaklyWellOrderedNoise_swap_middle_density_le
    (f := f) hf hx23 hr23
  calc
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) =
        f (r1 - x1) * (f (r2 - x2) * f (r3 - x3)) := by ring
    _ ≤ f (r1 - x1) * (f (r3 - x2) * f (r2 - x3)) := by
        exact mul_le_mul_of_nonneg_left hpair hctx
    _ = f (r1 - x1) * f (r3 - x2) * f (r2 - x3) := by ring

/--
Strict three-coordinate density comparison for swapping middle and bottom
realized scores in a wrong `x₂`/`x₃` pairwise realization.
-/
theorem strictlyWellOrderedNoise_swap23_density3_lt
    {f : ℝ → ℝ} (hf : StrictlyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 < f (r1 - x1))
    (hx23 : x3 < x2) (hr23 : r2 < r3) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) <
      f (r1 - x1) * f (r3 - x2) * f (r2 - x3) := by
  have hpair := strictlyWellOrderedNoise_swap_middle_density_lt
    (f := f) hf hx23 hr23
  calc
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) =
        f (r1 - x1) * (f (r2 - x2) * f (r3 - x3)) := by ring
    _ < f (r1 - x1) * (f (r3 - x2) * f (r2 - x3)) := by
        exact mul_lt_mul_of_pos_left hpair hctx
    _ = f (r1 - x1) * f (r3 - x2) * f (r2 - x3) := by ring

end

end Probability
end AppliedModelingLib
