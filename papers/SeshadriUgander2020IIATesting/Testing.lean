import SeshadriUgander2020IIATesting.MainTheorem
import SeshadriUgander2020IIATesting.AlternatingCycles

/-!
# Finite binary testing and Le Cam's inequality

The paper invokes Le Cam's method after replacing the separated alternative
by a finite uniform mixture.  This file gives the finite-support binary
testing inequality directly from the total-variation definition used by the
paper, so no measure-theoretic probability interface is hidden in the main
lower-bound reduction.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators

namespace FiniteDistribution

variable {α : Type} [Fintype α] [DecidableEq α]

/-- A deterministic binary test; `true` means reject the null. -/
abbrev Test (α : Type) := α → Bool

/-- The finite rejection event of a deterministic test. -/
def rejectionSet (φ : Test α) : Finset α := Finset.univ.filter (fun x => φ x = true)

theorem rejectionSet_not (φ : Test α) :
    rejectionSet (fun x => !φ x) = (rejectionSet φ)ᶜ := by
  ext x
  simp [rejectionSet]

/-- Equal-prior average Type-I/Type-II error for a binary finite test. -/
noncomputable def binaryError (p q : FiniteDistribution α) (φ : Test α) : ℝ :=
  (1 / 2 : ℝ) * ∑ x ∈ rejectionSet φ, p.mass x +
    (1 / 2 : ℝ) * ∑ x ∈ (rejectionSet φ)ᶜ, q.mass x

/-- Le Cam's lower bound for every deterministic finite binary test. -/
theorem lecam_binary (p q : FiniteDistribution α) (φ : Test α) :
    1 / 2 - (1 / 2 : ℝ) * totalVariation p q ≤ binaryError p q φ := by
  let A := rejectionSet φ
  have hq_part : (∑ x ∈ A, q.mass x) + ∑ x ∈ Aᶜ, q.mass x = 1 := by
    rw [A.sum_add_sum_compl]
    exact q.sum_one
  have hq_comp : (∑ x ∈ Aᶜ, q.mass x) = 1 - ∑ x ∈ A, q.mass x := by
    linarith
  have htv := abs_sum_sub_mass_le_totalVariation p q A
  have hdiff : (∑ x ∈ A, (p.mass x - q.mass x)) =
      (∑ x ∈ A, p.mass x) - ∑ x ∈ A, q.mass x := by
    rw [Finset.sum_sub_distrib]
  unfold binaryError
  change 1 / 2 - (1 / 2 : ℝ) * totalVariation p q ≤
    (1 / 2 : ℝ) * ∑ x ∈ A, p.mass x +
      (1 / 2 : ℝ) * ∑ x ∈ Aᶜ, q.mass x
  rw [hq_comp]
  rw [hdiff] at htv
  rw [abs_le] at htv
  linarith

/-- The binary error against a uniform finite mixture is the corresponding
uniform average of componentwise binary errors. -/
theorem binaryError_uniformMixture_eq_average {β : Type} (B : Finset β)
    (hB : B.Nonempty) (q : β → FiniteDistribution α) (p : FiniteDistribution α)
    (φ : Test α) :
    binaryError (uniformMixture B hB q) p φ =
      (∑ b ∈ B, binaryError (q b) p φ) / (B.card : ℝ) := by
  let A := rejectionSet φ
  have hreject :
      (∑ x ∈ A, (uniformMixture B hB q).mass x) =
        (∑ b ∈ B, ∑ x ∈ A, (q b).mass x) / (B.card : ℝ) := by
    simp_rw [uniformMixture_mass]
    rw [← Finset.sum_div, Finset.sum_comm]
  unfold binaryError
  change
    (1 / 2 : ℝ) * ∑ x ∈ A, (uniformMixture B hB q).mass x +
        (1 / 2 : ℝ) * ∑ x ∈ Aᶜ, p.mass x =
      (∑ b ∈ B, ((1 / 2 : ℝ) * ∑ x ∈ A, (q b).mass x +
        (1 / 2 : ℝ) * ∑ x ∈ Aᶜ, p.mass x)) / (B.card : ℝ)
  rw [hreject, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have hcard : (B.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hB
  field_simp

/-- Swapping the two hypotheses and complementing a test preserves its
equal-prior error. -/
theorem binaryError_swap_not (p q : FiniteDistribution α) (φ : Test α) :
    binaryError q p (fun x => !φ x) = binaryError p q φ := by
  unfold binaryError
  rw [rejectionSet_not]
  rw [compl_compl]
  ring

/-- Some component of a finite uniform mixture is at least as difficult for a
fixed binary test as the mixture itself. -/
theorem exists_component_binaryError_ge_uniformMixture {β : Type} (B : Finset β)
    (hB : B.Nonempty) (q : β → FiniteDistribution α) (p : FiniteDistribution α)
    (φ : Test α) :
    ∃ b ∈ B, binaryError (uniformMixture B hB q) p φ ≤ binaryError (q b) p φ := by
  by_contra h
  push Not at h
  have hsum_lt : (∑ b ∈ B, binaryError (q b) p φ) <
      ∑ b ∈ B, binaryError (uniformMixture B hB q) p φ := by
    refine Finset.sum_lt_sum (fun b hb => (h b hb).le) ?_
    obtain ⟨b, hb⟩ := hB
    exact ⟨b, hb, h b hb⟩
  rw [Finset.sum_const, nsmul_eq_mul] at hsum_lt
  have havg := binaryError_uniformMixture_eq_average B hB q p φ
  have hcard : (B.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hB
  field_simp [hcard] at havg
  linarith

/-- A lower bound for a mixture transfers to one of its components for each
test in the usual null-versus-alternative orientation. -/
theorem exists_component_standardError_ge_mixture {β : Type} (B : Finset β)
    (hB : B.Nonempty) (q : β → FiniteDistribution α) (p : FiniteDistribution α)
    (φ : Test α) (lower : ℝ)
    (hlower : lower ≤ binaryError (uniformMixture B hB q) p (fun x => !φ x)) :
    ∃ b ∈ B, lower ≤ binaryError p (q b) φ := by
  obtain ⟨b, hb, hcomponent⟩ :=
    exists_component_binaryError_ge_uniformMixture B hB q p (fun x => !φ x)
  refine ⟨b, hb, ?_⟩
  calc
    lower ≤ binaryError (uniformMixture B hB q) p (fun x => !φ x) := hlower
    _ ≤ binaryError (q b) p (fun x => !φ x) := hcomponent
    _ = binaryError p (q b) φ := binaryError_swap_not p (q b) φ

/-- Against a fixed test, some component of a finite mixture has at least the
standard null-versus-alternative error of the mixture.  This is the exact
comparison needed for the source phrase ``not statistically harder''. -/
theorem exists_component_standardError_ge_mixture_self {β : Type}
    (B : Finset β) (hB : B.Nonempty) (q : β → FiniteDistribution α)
    (p : FiniteDistribution α) (φ : Test α) :
    ∃ b ∈ B,
      binaryError p (uniformMixture B hB q) φ ≤ binaryError p (q b) φ := by
  apply exists_component_standardError_ge_mixture B hB q p φ
    (binaryError p (uniformMixture B hB q) φ)
  rw [binaryError_swap_not]

end FiniteDistribution

namespace ChoiceSystem

variable {F : ChoiceFrame}

/-- An operational finite-sample lower bound for the paper's IIA testing
problem. For every test, a separated alternative makes its equal-prior error
against the uniform IIA null at least `lower`. This directly implies the
source minimax lower bound, while avoiding an unnecessary encoding of real
infima/suprema. -/
def ProductTestingLowerBound (N : ℕ) (δ lower : ℝ) : Prop :=
  ∀ φ : FiniteDistribution.Test (Fin N → F.Observation),
    ∃ q : ChoiceSystem F, SeparatedFromIIA q δ ∧
      lower ≤ FiniteDistribution.binaryError
        (FiniteDistribution.product (asFiniteDistribution (uniform F)) N)
        (FiniteDistribution.product (asFiniteDistribution q) N) φ

/-- A fixed-error operational form of a minimax lower bound.  At the
conventional threshold `1 / 4`, every test has a `δ`-separated alternative
whose equal-prior error is strictly above that threshold.  This avoids
encoding an infimum over tests while still expressing exactly the obstruction
used to derive the paper's testing-radius and sample-complexity rates. -/
def QuarterRiskObstruction (N : ℕ) (δ : ℝ) : Prop :=
  ∀ φ : FiniteDistribution.Test (Fin N → F.Observation),
    ∃ q : ChoiceSystem F, SeparatedFromIIA q δ ∧
      (1 / 4 : ℝ) < FiniteDistribution.binaryError
        (FiniteDistribution.product (asFiniteDistribution (uniform F)) N)
        (FiniteDistribution.product (asFiniteDistribution q) N) φ

/-- A deterministic finite test whose equal-prior error is at most `1 / 4`
against every `δ`-separated alternative.  This is the finite operational
counterpart of the paper's phrase ``a test succeeds at separation `δ`''. -/
def HasQuarterAccurateTest (N : ℕ) (δ : ℝ) : Prop :=
  ∃ φ : FiniteDistribution.Test (Fin N → F.Observation),
    ∀ q : ChoiceSystem F, SeparatedFromIIA q δ →
      FiniteDistribution.binaryError
        (FiniteDistribution.product (asFiniteDistribution (uniform F)) N)
        (FiniteDistribution.product (asFiniteDistribution q) N) φ ≤ 1 / 4

/-- A chi-square exponent below `log 2` keeps the displayed Theorem-1 risk
lower bound strictly above the fixed error threshold `1 / 4`.  The constant
is now explicit, which makes the source's `\GtrSim` interpretation a genuine
mathematical statement rather than an unspecified prose convention. -/
theorem quarter_lt_riskLower_of_exponent_lt_log_two {exponent : ℝ}
    (hexponent : exponent < Real.log 2) :
    (1 / 4 : ℝ) < 1 / 2 - (1 / 4 : ℝ) *
      Real.sqrt (Real.exp exponent - 1) := by
  have hexp_lt : Real.exp exponent < 2 := by
    exact (Real.lt_log_iff_exp_lt (by norm_num)).mp hexponent
  have hsqrt_lt : Real.sqrt (Real.exp exponent - 1) < 1 := by
    apply (Real.sqrt_lt' (by norm_num)).mpr
    linarith
  linarith

/-- Turn a strict finite risk lower bound into the fixed-error operational
obstruction used below. -/
theorem quarterRiskObstruction_of_productTestingLowerBound
    {N : ℕ} {δ lower : ℝ}
    (hlower : ProductTestingLowerBound (F := F) N δ lower)
    (hquarter : (1 / 4 : ℝ) < lower) :
    QuarterRiskObstruction (F := F) N δ := by
  intro φ
  obtain ⟨q, hseparated, herror⟩ := hlower φ
  exact ⟨q, hseparated, hquarter.trans_le herror⟩

/-- The fixed-error obstruction rules out a uniformly accurate finite test. -/
theorem not_hasQuarterAccurateTest_of_quarterRiskObstruction
    {N : ℕ} {δ : ℝ}
    (hobstruction : QuarterRiskObstruction (F := F) N δ) :
    ¬ HasQuarterAccurateTest (F := F) N δ := by
  rintro ⟨φ, hφ⟩
  obtain ⟨q, hseparated, herror⟩ := hobstruction φ
  linarith [hφ q hseparated]

namespace CycleDecomposition

variable (D : CycleDecomposition F)

/-- The cycle-dispersion statistic of a nonempty concrete decomposition is
strictly positive.  This supplies the positive denominator needed when the
Theorem-1 exponent is rearranged into a sample-complexity rate. -/
private theorem cycleDispersion_pos :
    0 < CycleMixture.cycleDispersion F.incidenceCount D.length := by
  unfold CycleMixture.cycleDispersion
  refine mul_pos ?_ ?_
  · exact one_div_pos.mpr (by exact_mod_cast F.incidenceCount_pos)
  · refine Finset.sum_pos' (fun i _ => sq_nonneg _) ?_
    obtain ⟨i⟩ := D.cycle_nonempty
    refine ⟨i, Finset.mem_univ _, ?_⟩
    have hlength : 0 < (D.length i : ℝ) := by
      exact_mod_cast D.length_pos i
    exact sq_pos_of_pos hlength

/-- Lemmas 3--4 plus the now-proved finite Le Cam inequality, for every
binary test of the uniform null against the orientation mixture. -/
theorem binaryError_lower_oriented_cycles (ε : ℝ) (hε_nonneg : 0 ≤ ε)
    (hε_le_one : ε ≤ 1) (N : ℕ)
    (φ : FiniteDistribution.Test (Fin N → F.Observation)) :
    1 / 2 - (1 / 4 : ℝ) *
        Real.sqrt (Real.exp (((N : ℝ) ^ 2 * ε ^ 4 /
          (2 * (F.incidenceCount : ℝ))) *
          CycleMixture.cycleDispersion F.incidenceCount D.length) - 1) ≤
      FiniteDistribution.binaryError
        (FiniteDistribution.mixtureOfProducts (Finset.univ : Finset (D.Cycle → Bool))
          Finset.univ_nonempty
          (fun a => asFiniteDistribution
            (perturb (D.orientedSign a) ε hε_nonneg hε_le_one)) N)
        (FiniteDistribution.product
          (asFiniteDistribution (uniform F)) N) φ := by
  apply D.risk_lower_oriented_cycles ε hε_nonneg hε_le_one N
  exact FiniteDistribution.lecam_binary _ _ φ

/-- Source Lemma 2 as a finite testing reduction.  Under
`ε ≥ 2 μ(σ) δ`, every independently oriented perturbation is
`δ`-separated from IIA, and for every test some such component has error at
least that of the orientation mixture.  The latter conclusion is obtained by
finite-mixture averaging; it does not require the nonconvex separated class to
contain the mixture itself. -/
theorem lemma2_testing_reduction (W : D.AlternatingCycleWitness)
    (ε δ : ℝ) (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1)
    (hδ_nonneg : 0 ≤ δ) (hscale : 2 * D.cycleMean * δ ≤ ε) (N : ℕ) :
    (∀ a : D.Cycle → Bool,
      SeparatedFromIIA (perturb (D.orientedSign a) ε hε_nonneg hε_le_one) δ) ∧
    ∀ φ : FiniteDistribution.Test (Fin N → F.Observation),
      ∃ a : D.Cycle → Bool,
        FiniteDistribution.binaryError
            (FiniteDistribution.product (asFiniteDistribution (uniform F)) N)
            (FiniteDistribution.mixtureOfProducts
              (Finset.univ : Finset (D.Cycle → Bool)) Finset.univ_nonempty
              (fun orientation => asFiniteDistribution
                (perturb (D.orientedSign orientation) ε
                  hε_nonneg hε_le_one)) N) φ ≤
          FiniteDistribution.binaryError
            (FiniteDistribution.product (asFiniteDistribution (uniform F)) N)
            (FiniteDistribution.product
              (asFiniteDistribution
                (perturb (D.orientedSign a) ε hε_nonneg hε_le_one)) N) φ := by
  have hincidence : (0 : ℝ) < F.incidenceCount := by
    exact_mod_cast F.incidenceCount_pos
  have hcycles : (0 : ℝ) < Fintype.card D.Cycle := by
    exact_mod_cast D.cycle_card_pos
  have hscale_nonneg :
      0 ≤ (Fintype.card D.Cycle : ℝ) / (2 * F.incidenceCount) := by
    positivity
  have hradius :
      δ ≤ ε * (Fintype.card D.Cycle : ℝ) /
        (2 * (F.incidenceCount : ℝ)) := by
    calc
      δ = (2 * D.cycleMean * δ) *
          ((Fintype.card D.Cycle : ℝ) /
            (2 * (F.incidenceCount : ℝ))) := by
        unfold cycleMean
        field_simp
      _ ≤ ε * ((Fintype.card D.Cycle : ℝ) /
          (2 * (F.incidenceCount : ℝ))) :=
        mul_le_mul_of_nonneg_right hscale hscale_nonneg
      _ = ε * (Fintype.card D.Cycle : ℝ) /
          (2 * (F.incidenceCount : ℝ)) := by ring
  constructor
  · intro a p hp
    exact hradius.trans
      (AlternatingCycleWitness.orientedSign_separatedFromIIA
        (D := D) W a ε hε_nonneg hε_le_one p hp)
  · intro φ
    obtain ⟨a, _ha, herror⟩ :=
      FiniteDistribution.exists_component_standardError_ge_mixture_self
        (B := (Finset.univ : Finset (D.Cycle → Bool))) Finset.univ_nonempty
        (q := fun orientation => FiniteDistribution.product
          (asFiniteDistribution
            (perturb (D.orientedSign orientation) ε hε_nonneg hε_le_one)) N)
        (p := FiniteDistribution.product
          (asFiniteDistribution (uniform F)) N) φ
    exact ⟨a, by
      simpa only [FiniteDistribution.mixtureOfProducts] using herror⟩

/-- The mixture-to-component reduction applied to the cycle-orientation
family. Once Lemma 2 supplies the displayed separatedness premise, this is
the source's minimax testing reduction. -/
theorem productTestingLowerBound_of_oriented_separation (ε δ : ℝ)
    (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1) (N : ℕ)
    (hseparated : ∀ a : D.Cycle → Bool,
      SeparatedFromIIA (perturb (D.orientedSign a) ε hε_nonneg hε_le_one) δ) :
    ProductTestingLowerBound (F := F) N δ
      (1 / 2 - (1 / 4 : ℝ) *
        Real.sqrt (Real.exp (((N : ℝ) ^ 2 * ε ^ 4 /
          (2 * (F.incidenceCount : ℝ))) *
          CycleMixture.cycleDispersion F.incidenceCount D.length) - 1)) := by
  intro φ
  have hmixture := D.binaryError_lower_oriented_cycles ε hε_nonneg hε_le_one N
    (fun sample => !φ sample)
  obtain ⟨a, ha, herror⟩ :=
    FiniteDistribution.exists_component_standardError_ge_mixture
      (B := (Finset.univ : Finset (D.Cycle → Bool))) Finset.univ_nonempty
      (q := fun a => FiniteDistribution.product
        (asFiniteDistribution (perturb (D.orientedSign a) ε hε_nonneg hε_le_one)) N)
      (p := FiniteDistribution.product (asFiniteDistribution (uniform F)) N)
      φ
      (1 / 2 - (1 / 4 : ℝ) *
        Real.sqrt (Real.exp (((N : ℝ) ^ 2 * ε ^ 4 /
          (2 * (F.incidenceCount : ℝ))) *
          CycleMixture.cycleDispersion F.incidenceCount D.length) - 1))
      (by simpa only [FiniteDistribution.mixtureOfProducts] using hmixture)
  refine ⟨perturb (D.orientedSign a) ε hε_nonneg hε_le_one, hseparated a, ?_⟩
  exact herror

/-- Lemma 2's explicit alternating-cycle traversal now discharges the
separatedness premise in the mixture lower-bound theorem. This is the
finite-sample testing conclusion before the notation substitution
`ε = 2 μ(σ) δ`. -/
theorem productTestingLowerBound_alternating_cycles
    (W : D.AlternatingCycleWitness) (ε : ℝ)
    (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1) (N : ℕ) :
    ProductTestingLowerBound (F := F) N
      (ε * (Fintype.card D.Cycle : ℝ) / (2 * (F.incidenceCount : ℝ)))
      (1 / 2 - (1 / 4 : ℝ) *
        Real.sqrt (Real.exp (((N : ℝ) ^ 2 * ε ^ 4 /
          (2 * (F.incidenceCount : ℝ))) *
          CycleMixture.cycleDispersion F.incidenceCount D.length) - 1)) := by
  apply productTestingLowerBound_of_oriented_separation (D := D) ε
    (ε * (Fintype.card D.Cycle : ℝ) / (2 * (F.incidenceCount : ℝ)))
    hε_nonneg hε_le_one N
  intro a
  exact AlternatingCycleWitness.orientedSign_separatedFromIIA
    (D := D) W a ε hε_nonneg hε_le_one

/-- Theorem 1 in the paper's `μ(σ), α(σ), δ` notation. The explicit
small-separation premise is necessary because the source construction uses
`ε = 2 μ(σ) δ ∈ [0,1]`. -/
theorem theorem1_productTestingLowerBound (W : D.AlternatingCycleWitness)
    (δ : ℝ) (hδ_nonneg : 0 ≤ δ)
    (hsmall : 2 * D.cycleMean * δ ≤ 1) (N : ℕ) :
    ProductTestingLowerBound (F := F) N δ
      (1 / 2 - (1 / 4 : ℝ) *
        Real.sqrt (Real.exp
          ((8 * D.cycleMean ^ 4 * CycleMixture.cycleDispersion
              F.incidenceCount D.length * (N : ℝ) ^ 2 * δ ^ 4) /
            (F.incidenceCount : ℝ)) - 1)) := by
  let ε : ℝ := 2 * D.cycleMean * δ
  have hε_nonneg : 0 ≤ ε := by
    dsimp [ε]
    exact mul_nonneg (mul_nonneg (by norm_num) D.cycleMean_pos.le) hδ_nonneg
  have hε_le_one : ε ≤ 1 := by
    simpa [ε] using hsmall
  have hbase := productTestingLowerBound_alternating_cycles (D := D) W ε
    hε_nonneg hε_le_one N
  have hincidence : (F.incidenceCount : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt F.incidenceCount_pos
  have hcycles : (Fintype.card D.Cycle : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt D.cycle_card_pos
  have hradius :
      ε * (Fintype.card D.Cycle : ℝ) / (2 * (F.incidenceCount : ℝ)) = δ := by
    dsimp [ε]
    unfold cycleMean
    field_simp [hincidence, hcycles]
  have hexponent :
      (((N : ℝ) ^ 2 * ε ^ 4 / (2 * (F.incidenceCount : ℝ))) *
          CycleMixture.cycleDispersion F.incidenceCount D.length) =
        (8 * D.cycleMean ^ 4 * CycleMixture.cycleDispersion
            F.incidenceCount D.length * (N : ℝ) ^ 2 * δ ^ 4) /
          (F.incidenceCount : ℝ) := by
    dsimp [ε]
    exact source_exponent_after_epsilon_substitution (D := D) D.cycleMean δ N
  rw [hradius, hexponent] at hbase
  exact hbase

/-- Theorem 1's printed `\GtrSim` interpretation at a concrete error
threshold.  If its explicit exponent is below `log 2`, then no `N`-sample
test can attain equal-prior error at most `1 / 4` uniformly over the
`δ`-separated alternatives.  This is the precise finite obstruction from
which both displayed testing-radius and sample-complexity rates are obtained
by rearranging the exponent inequality. -/
theorem theorem1_quarterRiskObstruction (W : D.AlternatingCycleWitness)
    (δ : ℝ) (hδ_nonneg : 0 ≤ δ)
    (hsmall : 2 * D.cycleMean * δ ≤ 1) (N : ℕ)
    (hexponent :
      (8 * D.cycleMean ^ 4 * CycleMixture.cycleDispersion
          F.incidenceCount D.length * (N : ℝ) ^ 2 * δ ^ 4) /
          (F.incidenceCount : ℝ) < Real.log 2) :
    QuarterRiskObstruction (F := F) N δ := by
  apply quarterRiskObstruction_of_productTestingLowerBound
    (D.theorem1_productTestingLowerBound W δ hδ_nonneg hsmall N)
  exact quarter_lt_riskLower_of_exponent_lt_log_two hexponent

/-- Conversely, the existence of a uniformly quarter-accurate test forces
the Theorem-1 exponent to be at least `log 2`.  This is the exact
constant-bearing statement behind the paper's two `\GtrSim` displays. -/
theorem theorem1_log_two_le_exponent_of_hasQuarterAccurateTest
    (W : D.AlternatingCycleWitness)
    (δ : ℝ) (hδ_nonneg : 0 ≤ δ)
    (hsmall : 2 * D.cycleMean * δ ≤ 1) (N : ℕ)
    (haccurate : HasQuarterAccurateTest (F := F) N δ) :
    Real.log 2 ≤
      (8 * D.cycleMean ^ 4 * CycleMixture.cycleDispersion
          F.incidenceCount D.length * (N : ℝ) ^ 2 * δ ^ 4) /
          (F.incidenceCount : ℝ) := by
  by_contra hnot
  have hexponent :
      (8 * D.cycleMean ^ 4 * CycleMixture.cycleDispersion
          F.incidenceCount D.length * (N : ℝ) ^ 2 * δ ^ 4) /
          (F.incidenceCount : ℝ) < Real.log 2 := lt_of_not_ge hnot
  exact not_hasQuarterAccurateTest_of_quarterRiskObstruction
    (D.theorem1_quarterRiskObstruction W δ hδ_nonneg hsmall N hexponent) haccurate

/-- Exact sample-complexity form of Theorem 1 at error threshold `1 / 4`.
It is the source's `N_δ \GtrSim √d / (√(μ⁴ α) δ²)` statement with the
constant `√(log 2 / 8)` exposed and no asymptotic convention left implicit. -/
theorem theorem1_sampleLowerBound_of_hasQuarterAccurateTest
    (W : D.AlternatingCycleWitness)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (hsmall : 2 * D.cycleMean * δ ≤ 1) (N : ℕ)
    (haccurate : HasQuarterAccurateTest (F := F) N δ) :
    Real.sqrt
      (((F.incidenceCount : ℝ) * Real.log 2) /
        (8 * D.cycleMean ^ 4 *
          CycleMixture.cycleDispersion F.incidenceCount D.length * δ ^ 4)) ≤
      (N : ℝ) := by
  have hbase := D.theorem1_log_two_le_exponent_of_hasQuarterAccurateTest W δ
    hδ_pos.le hsmall N haccurate
  have hdpos : 0 < (F.incidenceCount : ℝ) := by
    exact_mod_cast F.incidenceCount_pos
  have hdisp : 0 < CycleMixture.cycleDispersion F.incidenceCount D.length :=
    D.cycleDispersion_pos
  have hdenpos : 0 < 8 * D.cycleMean ^ 4 *
      CycleMixture.cycleDispersion F.incidenceCount D.length * δ ^ 4 := by
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) (pow_pos D.cycleMean_pos 4)) hdisp)
      (pow_pos hδ_pos 4)
  have hsquared :
      ((F.incidenceCount : ℝ) * Real.log 2) /
        (8 * D.cycleMean ^ 4 *
          CycleMixture.cycleDispersion F.incidenceCount D.length * δ ^ 4) ≤
        (N : ℝ) ^ 2 := by
    rw [div_le_iff₀ hdenpos]
    have hmult := (le_div_iff₀ hdpos).mp hbase
    calc
      (F.incidenceCount : ℝ) * Real.log 2 =
          Real.log 2 * (F.incidenceCount : ℝ) := by ring
      _ ≤ 8 * D.cycleMean ^ 4 *
          CycleMixture.cycleDispersion F.incidenceCount D.length * (N : ℝ) ^ 2 * δ ^ 4 := hmult
      _ = (N : ℝ) ^ 2 *
          (8 * D.cycleMean ^ 4 *
            CycleMixture.cycleDispersion F.incidenceCount D.length * δ ^ 4) := by ring
  calc
    Real.sqrt
        (((F.incidenceCount : ℝ) * Real.log 2) /
          (8 * D.cycleMean ^ 4 *
            CycleMixture.cycleDispersion F.incidenceCount D.length * δ ^ 4)) ≤
        Real.sqrt ((N : ℝ) ^ 2) := Real.sqrt_le_sqrt hsquared
    _ = (N : ℝ) := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]; positivity

/-- Exact testing-radius form of Theorem 1 at error threshold `1 / 4`.
It exposes the constant in the source's
`δ_N \GtrSim d^(1/4) / (μ α^(1/4) √N)` display.  The two nested square
roots are the nonnegative real fourth root, avoiding an implicit convention
for fractional powers. -/
theorem theorem1_radiusLowerBound_of_hasQuarterAccurateTest
    (W : D.AlternatingCycleWitness)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (hsmall : 2 * D.cycleMean * δ ≤ 1) (N : ℕ) (hN_pos : 0 < N)
    (haccurate : HasQuarterAccurateTest (F := F) N δ) :
    Real.sqrt (Real.sqrt
      (((F.incidenceCount : ℝ) * Real.log 2) /
        (8 * D.cycleMean ^ 4 *
          CycleMixture.cycleDispersion F.incidenceCount D.length * (N : ℝ) ^ 2))) ≤
      δ := by
  have hbase := D.theorem1_log_two_le_exponent_of_hasQuarterAccurateTest W δ
    hδ_pos.le hsmall N haccurate
  have hdpos : 0 < (F.incidenceCount : ℝ) := by
    exact_mod_cast F.incidenceCount_pos
  have hdisp : 0 < CycleMixture.cycleDispersion F.incidenceCount D.length :=
    D.cycleDispersion_pos
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN_pos
  have hdenpos : 0 < 8 * D.cycleMean ^ 4 *
      CycleMixture.cycleDispersion F.incidenceCount D.length * (N : ℝ) ^ 2 := by
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) (pow_pos D.cycleMean_pos 4)) hdisp)
      (pow_pos hNreal 2)
  have hfourth :
      ((F.incidenceCount : ℝ) * Real.log 2) /
        (8 * D.cycleMean ^ 4 *
          CycleMixture.cycleDispersion F.incidenceCount D.length * (N : ℝ) ^ 2) ≤
        δ ^ 4 := by
    rw [div_le_iff₀ hdenpos]
    have hmult := (le_div_iff₀ hdpos).mp hbase
    calc
      (F.incidenceCount : ℝ) * Real.log 2 =
          Real.log 2 * (F.incidenceCount : ℝ) := by ring
      _ ≤ 8 * D.cycleMean ^ 4 *
          CycleMixture.cycleDispersion F.incidenceCount D.length * (N : ℝ) ^ 2 * δ ^ 4 := hmult
      _ = δ ^ 4 * (8 * D.cycleMean ^ 4 *
          CycleMixture.cycleDispersion F.incidenceCount D.length * (N : ℝ) ^ 2) := by ring
  calc
    Real.sqrt (Real.sqrt
        (((F.incidenceCount : ℝ) * Real.log 2) /
          (8 * D.cycleMean ^ 4 *
            CycleMixture.cycleDispersion F.incidenceCount D.length * (N : ℝ) ^ 2))) ≤
        Real.sqrt (Real.sqrt (δ ^ 4)) :=
      Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hfourth)
    _ = δ := by
      rw [show δ ^ 4 = (δ ^ 2) ^ 2 by ring, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (sq_nonneg δ), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hδ_pos.le]

private theorem riskLower_antitone_exponent {a b : ℝ} (hab : a ≤ b) :
    1 / 2 - (1 / 4 : ℝ) * Real.sqrt (Real.exp b - 1) ≤
      1 / 2 - (1 / 4 : ℝ) * Real.sqrt (Real.exp a - 1) := by
  have hexp : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
  have hsqrt : Real.sqrt (Real.exp a - 1) ≤ Real.sqrt (Real.exp b - 1) :=
    Real.sqrt_le_sqrt (by linarith)
  linarith

/-- A source-facing corollary of Theorem 1: any proved upper bounds on the
cycle mean and dispersion may be substituted into the finite testing bound.
The small-separation premise is stated at the substituted mean bound. -/
theorem productTestingLowerBound_of_cycleStatisticBounds
    (W : D.AlternatingCycleWitness) (meanBound dispersionBound : ℝ)
    (hmean : D.cycleMean ≤ meanBound)
    (hdispersion : CycleMixture.cycleDispersion F.incidenceCount D.length ≤ dispersionBound)
    (δ : ℝ) (hδ_nonneg : 0 ≤ δ) (hsmall : 2 * meanBound * δ ≤ 1) (N : ℕ) :
    ProductTestingLowerBound (F := F) N δ
      (1 / 2 - (1 / 4 : ℝ) *
        Real.sqrt (Real.exp
          ((8 * meanBound ^ 4 * dispersionBound * (N : ℝ) ^ 2 * δ ^ 4) /
            (F.incidenceCount : ℝ)) - 1)) := by
  have hsmallD : 2 * D.cycleMean * δ ≤ 1 := by
    calc
      2 * D.cycleMean * δ = D.cycleMean * (2 * δ) := by ring
      _ ≤ meanBound * (2 * δ) :=
        mul_le_mul_of_nonneg_right hmean (by positivity)
      _ = 2 * meanBound * δ := by ring
      _ ≤ 1 := hsmall
  have hbase := D.theorem1_productTestingLowerBound W δ hδ_nonneg hsmallD N
  let d : ℝ := (F.incidenceCount : ℝ)
  let a : ℝ :=
    (8 * D.cycleMean ^ 4 *
      CycleMixture.cycleDispersion F.incidenceCount D.length *
        (N : ℝ) ^ 2 * δ ^ 4) / d
  let b : ℝ := (8 * meanBound ^ 4 * dispersionBound * (N : ℝ) ^ 2 * δ ^ 4) / d
  have hdispersion_nonneg : 0 ≤ CycleMixture.cycleDispersion F.incidenceCount D.length := by
    unfold CycleMixture.cycleDispersion
    positivity
  have hmean_nonneg : 0 ≤ meanBound := D.cycleMean_pos.le.trans hmean
  have hmean_pow : D.cycleMean ^ 4 ≤ meanBound ^ 4 :=
    pow_le_pow_left₀ D.cycleMean_pos.le hmean 4
  have hproduct : D.cycleMean ^ 4 *
      CycleMixture.cycleDispersion F.incidenceCount D.length ≤
        meanBound ^ 4 * dispersionBound := by
    calc
      D.cycleMean ^ 4 * CycleMixture.cycleDispersion F.incidenceCount D.length ≤
          meanBound ^ 4 * CycleMixture.cycleDispersion F.incidenceCount D.length :=
        mul_le_mul_of_nonneg_right hmean_pow hdispersion_nonneg
      _ ≤ meanBound ^ 4 * dispersionBound :=
        mul_le_mul_of_nonneg_left hdispersion (pow_nonneg hmean_nonneg 4)
  have hfactor : 0 ≤ 8 * (N : ℝ) ^ 2 * δ ^ 4 := by positivity
  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast F.incidenceCount_pos
  have hab : a ≤ b := by
    dsimp [a, b]
    calc
      (8 * D.cycleMean ^ 4 * CycleMixture.cycleDispersion F.incidenceCount D.length *
          (N : ℝ) ^ 2 * δ ^ 4) / d =
          (D.cycleMean ^ 4 * CycleMixture.cycleDispersion F.incidenceCount D.length) *
            (8 * (N : ℝ) ^ 2 * δ ^ 4) / d := by ring
      _ ≤ (meanBound ^ 4 * dispersionBound) * (8 * (N : ℝ) ^ 2 * δ ^ 4) / d :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hproduct hfactor) hdpos.le
      _ = (8 * meanBound ^ 4 * dispersionBound * (N : ℝ) ^ 2 * δ ^ 4) / d := by ring
  have hlower :
      1 / 2 - (1 / 4 : ℝ) * Real.sqrt (Real.exp b - 1) ≤
        1 / 2 - (1 / 4 : ℝ) * Real.sqrt (Real.exp a - 1) :=
    riskLower_antitone_exponent hab
  intro φ
  obtain ⟨q, hseparated, herror⟩ := hbase φ
  refine ⟨q, hseparated, ?_⟩
  apply hlower.trans
  simpa [a, d] using herror

end CycleDecomposition

end ChoiceSystem

end SeshadriUgander2020IIATesting
