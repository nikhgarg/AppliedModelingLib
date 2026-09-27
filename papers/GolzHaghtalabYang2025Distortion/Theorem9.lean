import AppliedModelingLib.Learning.HumanFeedback.CorrelatedBradleyTerryFit
import AppliedModelingLib.Foundations.Probability.FiniteKLOptimization
import AppliedModelingLib.Foundations.Optimization.UniformArgmaxStability
import AppliedModelingLib.Foundations.Probability.FiniteIidUniformLaw
import AppliedModelingLib.Foundations.Probability.FiniteIidStrongLaw
import AppliedModelingLib.Learning.HumanFeedback.PairwiseReportFiniteConsistency
import GolzHaghtalabYang2025Distortion.Lemma15

/-!
# Theorem 9: correlated comparison sampling

This file develops the finite-prefix bridge in Appendix G.  The source first
uses the infinite three-user construction from Lemma 15, then puts almost all
comparison mass on adjacent pairs of a finite prefix.  The correlated
population-MLE objective is supplied by
`CorrelatedBradleyTerryFit`; the remaining paper-specific step is a backward
stability argument for its first-order equations when the off-path mass is
sufficiently small.
-/

namespace GolzHaghtalabYang2025Distortion

open scoped Topology

open AppliedModelingLib Learning HumanFeedback
open AppliedModelingLib.Learning.HumanFeedback.PairwiseCountDataset

/-- The `m`-alternative prefix of the Appendix-G three-user utility profile. -/
noncomputable def theorem9PrefixProfile (beta : ℝ) (m : ℕ) :
    AppliedModelingLib.Alignment.Welfare.FiniteUtilityProfile (Fin 3) (Fin m) :=
  fun user alternative => lemma15Utility beta alternative.val user

/-- The literal population Bradley--Terry preference model on a finite prefix
of the source sequence. -/
noncomputable def theorem9PrefixPreference (beta : ℝ) (m : ℕ) :
    PairwisePreference PUnit.{1} (Fin m) :=
  AppliedModelingLib.Alignment.Welfare.populationBradleyTerryPreference lemma15Population
    (theorem9PrefixProfile beta m) beta

/-- Lemma 15's interval invariant restricts directly to every finite prefix. -/
theorem theorem9_prefixProfile_unitInterval {beta : ℝ} (hbeta : 0 < beta) (m : ℕ) :
    AppliedModelingLib.Alignment.Welfare.UnitIntervalUtilityProfile
      (theorem9PrefixProfile beta m) := by
  intro user alternative
  exact ⟨(lemma15_utility_invariants hbeta alternative.val).1 user,
    (lemma15_utility_invariants hbeta alternative.val).2.1 user⟩

/-- Every finite-prefix human comparison is strictly interior, as required by
the correlated population-MLE existence theorem. -/
theorem theorem9_prefixPreference_prob_pos (beta : ℝ) (m : ℕ)
    (first second : Fin m) :
    0 < (theorem9PrefixPreference beta m).prob PUnit.unit.{1} first second := by
  exact AppliedModelingLib.Alignment.Welfare.populationBradleyTerryPreference_prob_pos
    lemma15Population (theorem9PrefixProfile beta m) beta first second

/-- The two ordered orientations of the `i`th adjacent source pair
`{aᵢ,aᵢ₊₁}`. -/
def theorem9PathOrientation {m : ℕ} (hm : 2 ≤ m)
    (edge : Fin (m - 1) × Bool) : Fin m × Fin m :=
  let lower : Fin m := ⟨edge.1.val, by omega⟩
  let upper : Fin m := ⟨edge.1.val + 1, by omega⟩
  if edge.2 then (lower, upper) else (upper, lower)

/-- Flipping the orientation bit reverses the selected ordered path pair. -/
def theorem9FlipPathOrientation {m : ℕ} (edge : Fin (m - 1) × Bool) :
    Fin (m - 1) × Bool := (edge.1, !edge.2)

theorem theorem9PathOrientation_flip {m : ℕ} (hm : 2 ≤ m)
    (edge : Fin (m - 1) × Bool) :
    theorem9PathOrientation hm (theorem9FlipPathOrientation edge) =
      (theorem9PathOrientation hm edge).swap := by
  cases edge with
  | mk edge orientation =>
    cases orientation <;> rfl

/-- The involutive relabeling of the path sampler's finite sample space that
reverses an edge orientation. -/
def theorem9PathFlipEquiv {m : ℕ} :
    (Fin (m - 1) × Bool) ≃ (Fin (m - 1) × Bool) :=
  { toFun := fun edge => theorem9FlipPathOrientation edge
    invFun := fun edge => theorem9FlipPathOrientation edge
    left_inv := by
      rintro ⟨edge, orientation⟩
      cases orientation <;> rfl
    right_inv := by
      rintro ⟨edge, orientation⟩
      cases orientation <;> rfl }

theorem theorem9PathFlipEquiv_apply {m : ℕ} (edge : Fin (m - 1) × Bool) :
    theorem9PathFlipEquiv edge = theorem9FlipPathOrientation edge := by
  rcases edge with ⟨edge, orientation⟩
  cases orientation <;> rfl

/-- Each edge/orientation choice identifies a different directed path pair. -/
theorem theorem9PathOrientation_injective {m : ℕ} (hm : 2 ≤ m) :
    Function.Injective (theorem9PathOrientation hm) := by
  rintro ⟨leftEdge, leftOrientation⟩ ⟨rightEdge, rightOrientation⟩ h
  cases leftOrientation <;> cases rightOrientation
  · apply Prod.ext
    · apply Fin.ext
      have hsecond := congrArg (fun pair : Fin m × Fin m => pair.2.val) h
      simpa [theorem9PathOrientation] using hsecond
    · rfl
  · exfalso
    have hfirst := congrArg (fun pair : Fin m × Fin m => pair.1.val) h
    have hsecond := congrArg (fun pair : Fin m × Fin m => pair.2.val) h
    simp [theorem9PathOrientation] at hfirst hsecond
    omega
  · exfalso
    have hfirst := congrArg (fun pair : Fin m × Fin m => pair.1.val) h
    have hsecond := congrArg (fun pair : Fin m × Fin m => pair.2.val) h
    simp [theorem9PathOrientation] at hfirst hsecond
    omega
  · apply Prod.ext
    · apply Fin.ext
      have hfirst := congrArg (fun pair : Fin m × Fin m => pair.1.val) h
      simpa [theorem9PathOrientation] using hfirst
    · rfl

/-- Every image of the path orientation map is an adjacent directed pair. -/
theorem theorem9PathOrientation_adjacent {m : ℕ} (hm : 2 ≤ m)
    (edge : Fin (m - 1) × Bool) :
    (theorem9PathOrientation hm edge).1.val + 1 =
        (theorem9PathOrientation hm edge).2.val ∨
      (theorem9PathOrientation hm edge).2.val + 1 =
        (theorem9PathOrientation hm edge).1.val := by
  rcases edge with ⟨index, orientation⟩
  cases orientation <;> simp [theorem9PathOrientation]

/-- The ordered representation of the source's uniform distribution over
adjacent unordered pairs: first select one path edge uniformly, then select
one of its two orientations uniformly. -/
noncomputable def theorem9PathSampling (m : ℕ) (hm : 2 ≤ m) :
    CorrelatedPairSampling (Fin m) := by
  letI : Nonempty (Fin (m - 1)) := ⟨0, by omega⟩
  exact PMF.map (theorem9PathOrientation hm) (AppliedModelingLib.uniformPMF (Fin (m - 1) × Bool))

/-- The ordered path component is symmetric because the uniform orientation
bit has an involution that reverses every selected comparison. -/
theorem theorem9PathSampling_isSymmetric {m : ℕ} (hm : 2 ≤ m) :
    (theorem9PathSampling m hm).IsSymmetric := by
  intro first second
  letI : Nonempty (Fin (m - 1)) := ⟨0, by omega⟩
  unfold theorem9PathSampling
  rw [AppliedModelingLib.pmf_map_apply_toReal_eq_pmfProb_preimage,
    AppliedModelingLib.pmf_map_apply_toReal_eq_pmfProb_preimage]
  apply AppliedModelingLib.pmfProb_uniformPMF_eq_of_comp_equiv theorem9PathFlipEquiv
  intro edge
  rw [theorem9PathFlipEquiv_apply, theorem9PathOrientation_flip]
  constructor <;> intro h
  · simpa using congrArg Prod.swap h
  · simpa using congrArg Prod.swap h

/-- Every oriented adjacent pair has the exact uniform mass of one path
edge-orientation draw. -/
theorem theorem9PathSampling_orientation_mass {m : ℕ} (hm : 2 ≤ m)
    (edge : Fin (m - 1) × Bool) :
    (theorem9PathSampling m hm (theorem9PathOrientation hm edge)).toReal =
      (Fintype.card (Fin (m - 1) × Bool) : ℝ)⁻¹ := by
  letI : Nonempty (Fin (m - 1)) := ⟨0, by omega⟩
  have hinjective := theorem9PathOrientation_injective hm
  have hmap :
      PMF.map (theorem9PathOrientation hm)
        (AppliedModelingLib.uniformPMF (Fin (m - 1) × Bool))
          (theorem9PathOrientation hm edge) =
        AppliedModelingLib.uniformPMF (Fin (m - 1) × Bool) edge := by
    rw [PMF.map_apply, tsum_fintype]
    rw [Finset.sum_eq_single edge]
    · simp
    · intro other _ hother
      have hne : theorem9PathOrientation hm edge ≠ theorem9PathOrientation hm other := by
        intro heq
        exact hother (hinjective heq).symm
      simp [hne]
    · simp
  unfold theorem9PathSampling
  rw [hmap, AppliedModelingLib.uniformPMF_apply_toReal]

/-- The path component gives zero mass to a nonadjacent directed pair. -/
theorem theorem9PathSampling_zero_of_not_adjacent {m : ℕ} (hm : 2 ≤ m)
    (first second : Fin m)
    (hnotAdjacent : ¬ (first.val + 1 = second.val ∨ second.val + 1 = first.val)) :
    (theorem9PathSampling m hm (first, second)).toReal = 0 := by
  classical
  letI : Nonempty (Fin (m - 1)) := ⟨0, by omega⟩
  unfold theorem9PathSampling
  have hnotSupport : (first, second) ∉
      (PMF.map (theorem9PathOrientation hm)
        (AppliedModelingLib.uniformPMF (Fin (m - 1) × Bool))).support := by
    rw [PMF.mem_support_map_iff]
    rintro ⟨edge, _, heq⟩
    apply hnotAdjacent
    have hadjacent := theorem9PathOrientation_adjacent hm edge
    rw [heq] at hadjacent
    exact hadjacent
  have hzero : PMF.map (theorem9PathOrientation hm)
      (AppliedModelingLib.uniformPMF (Fin (m - 1) × Bool)) (first, second) = 0 := by
    by_contra hnonzero
    apply hnotSupport
    rw [PMF.mem_support_iff]
    exact hnonzero
  rw [hzero]
  rfl

/-- The finite set of directed off-path pairs in a prefix. -/
def theorem9OffPathPairs (m : ℕ) : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun pair =>
    pair.1 ≠ pair.2 ∧ pair.1.val + 1 ≠ pair.2.val ∧ pair.2.val + 1 ≠ pair.1.val)

/-- Directed off-path pairs in a prefix.  The source samples their unordered
versions uniformly; representing both orientations here gives the same pair
mass and makes the likelihood's symmetry explicit. -/
def theorem9OffPathPair (m : ℕ) := {pair // pair ∈ theorem9OffPathPairs m}

/-- Reversing an off-path pair stays in the same finite off-path set. -/
def theorem9FlipOffPathPair {m : ℕ} (pair : theorem9OffPathPair m) :
    theorem9OffPathPair m :=
  ⟨pair.val.swap, by
    have hmem : pair.val ∈ theorem9OffPathPairs m := pair.property
    simp only [theorem9OffPathPairs, Finset.mem_filter, Finset.mem_univ,
      true_and] at hmem ⊢
    rcases hmem with ⟨hne, hforward, hbackward⟩
    exact ⟨hne.symm, hbackward, hforward⟩⟩

theorem theorem9FlipOffPathPair_involutive {m : ℕ}
    (pair : theorem9OffPathPair m) :
    theorem9FlipOffPathPair (theorem9FlipOffPathPair pair) = pair := by
  apply Subtype.ext
  simp [theorem9FlipOffPathPair]

/-- The involutive relabeling of directed off-path comparisons induced by
reversing their two alternatives. -/
def theorem9OffPathFlipEquiv (m : ℕ) :
    theorem9OffPathPair m ≃ theorem9OffPathPair m :=
  { toFun := theorem9FlipOffPathPair
    invFun := theorem9FlipOffPathPair
    left_inv := theorem9FlipOffPathPair_involutive
    right_inv := theorem9FlipOffPathPair_involutive }

/-- The uniform source off-path component, in the ordered-pair representation.
For `m ≥ 3`, `(a₁,a₃)` witnesses that this finite type is nonempty. -/
noncomputable def theorem9OffPathSampling (m : ℕ) (hm : 3 ≤ m) :
    CorrelatedPairSampling (Fin m) := by
  letI : Fintype (theorem9OffPathPair m) :=
    Fintype.ofFinset (theorem9OffPathPairs m) (by intro pair; rfl)
  letI : Nonempty (theorem9OffPathPair m) :=
    ⟨⟨(⟨0, by omega⟩, ⟨2, by omega⟩), by
      simp [theorem9OffPathPairs]⟩⟩
  exact PMF.map Subtype.val (AppliedModelingLib.uniformPMF (theorem9OffPathPair m))

/-- The ordered off-path component is symmetric under reversal of its directed
finite sample space. -/
theorem theorem9OffPathSampling_isSymmetric {m : ℕ} (hm : 3 ≤ m) :
    (theorem9OffPathSampling m hm).IsSymmetric := by
  classical
  intro first second
  letI : Fintype (theorem9OffPathPair m) :=
    Fintype.ofFinset (theorem9OffPathPairs m) (by intro pair; rfl)
  letI : Nonempty (theorem9OffPathPair m) :=
    ⟨⟨(⟨0, by omega⟩, ⟨2, by omega⟩), by simp [theorem9OffPathPairs]⟩⟩
  unfold theorem9OffPathSampling
  rw [AppliedModelingLib.pmf_map_apply_toReal_eq_pmfProb_preimage,
    AppliedModelingLib.pmf_map_apply_toReal_eq_pmfProb_preimage]
  apply AppliedModelingLib.pmfProb_uniformPMF_eq_of_comp_equiv (theorem9OffPathFlipEquiv m)
  intro pair
  change pair.val.swap = (first, second) ↔ pair.val = (second, first)
  constructor <;> intro h
  · simpa using congrArg Prod.swap h
  · simpa using congrArg Prod.swap h

/-- Every directed off-path pair has the exact uniform mass of its finite
off-path sample space. -/
theorem theorem9OffPathSampling_mass {m : ℕ} (hm : 3 ≤ m)
    (pair : theorem9OffPathPair m) :
    (theorem9OffPathSampling m hm pair.val).toReal =
      ((theorem9OffPathPairs m).card : ℝ)⁻¹ := by
  classical
  letI : Fintype (theorem9OffPathPair m) :=
    Fintype.ofFinset (theorem9OffPathPairs m) (by intro pair; rfl)
  letI : Nonempty (theorem9OffPathPair m) :=
    ⟨⟨(⟨0, by omega⟩, ⟨2, by omega⟩), by simp [theorem9OffPathPairs]⟩⟩
  have hmap :
      PMF.map Subtype.val (AppliedModelingLib.uniformPMF (theorem9OffPathPair m)) pair.val =
        AppliedModelingLib.uniformPMF (theorem9OffPathPair m) pair := by
    simp [PMF.map_apply]
    exact AppliedModelingLib.uniformPMF_apply pair
  have hcard : Fintype.card (theorem9OffPathPair m) =
      (theorem9OffPathPairs m).card := by
    exact Fintype.card_ofFinset (theorem9OffPathPairs m) (by intro candidate; rfl)
  unfold theorem9OffPathSampling
  rw [hmap, AppliedModelingLib.uniformPMF_apply_toReal, hcard]

/-- The off-path component gives zero mass to an adjacent pair (and, more
generally, to every pair outside its defining finite set). -/
theorem theorem9OffPathSampling_zero_of_not_mem {m : ℕ} (hm : 3 ≤ m)
    (pair : Fin m × Fin m) (hnotmem : pair ∉ theorem9OffPathPairs m) :
    (theorem9OffPathSampling m hm pair).toReal = 0 := by
  classical
  letI : Fintype (theorem9OffPathPair m) :=
    Fintype.ofFinset (theorem9OffPathPairs m) (by intro candidate; rfl)
  letI : Nonempty (theorem9OffPathPair m) :=
    ⟨⟨(⟨0, by omega⟩, ⟨2, by omega⟩), by simp [theorem9OffPathPairs]⟩⟩
  unfold theorem9OffPathSampling
  have hnotSupport : pair ∉
      (PMF.map Subtype.val (AppliedModelingLib.uniformPMF (theorem9OffPathPair m))).support := by
    rw [PMF.mem_support_map_iff]
    rintro ⟨source, _, heq⟩
    apply hnotmem
    rw [← heq]
    exact source.property
  have hzero : PMF.map Subtype.val
      (AppliedModelingLib.uniformPMF (theorem9OffPathPair m)) pair = 0 := by
    by_contra hnonzero
    apply hnotSupport
    rw [PMF.mem_support_iff]
    exact hnonzero
  rw [hzero]
  rfl

/-- A directed path pair is excluded from the source's off-path finite set. -/
theorem theorem9PathOrientation_not_mem_offPathPairs {m : ℕ} (hm : 3 ≤ m)
    (edge : Fin (m - 1) × Bool) :
    theorem9PathOrientation (by omega) edge ∉ theorem9OffPathPairs m := by
  simp only [theorem9OffPathPairs, Finset.mem_filter, Finset.mem_univ, true_and]
  intro hmembership
  rcases theorem9PathOrientation_adjacent (by omega) edge with hforward | hbackward
  · exact hmembership.2.1 hforward
  · exact hmembership.2.2 hbackward

/-- Appendix G's correlated comparison law on a prefix: mass `1 - ε` is
uniform on adjacent pairs and mass `ε` is uniform on all remaining unordered
pairs, represented with their two ordered orientations. -/
noncomputable def theorem9ComparisonSampling (m : ℕ) (hm : 3 ≤ m)
    (epsilon : NNReal) : CorrelatedPairSampling (Fin m) :=
  AppliedModelingLib.binaryMixturePMF (1 - epsilon) tsub_le_self
    (theorem9PathSampling m (by omega)) (theorem9OffPathSampling m hm)

/-- The path-component coordinate residual in the finite-prefix MLE equation. -/
noncomputable def theorem9PathResidual (beta : ℝ) (m : ℕ) (hm : 3 ≤ m)
    (reward : Fin m → ℝ) (response : Fin m) : ℝ :=
  ∑ opponent : Fin m,
    (theorem9PathSampling m (by omega) (response, opponent)).toReal *
      ((theorem9PrefixPreference beta m).prob PUnit.unit.{1} response opponent -
        Real.sigmoid (reward response - reward opponent))

/-- The off-path-component coordinate residual in the finite-prefix MLE equation. -/
noncomputable def theorem9OffPathResidual (beta : ℝ) (m : ℕ) (hm : 3 ≤ m)
    (reward : Fin m → ℝ) (response : Fin m) : ℝ :=
  ∑ opponent : Fin m,
    (theorem9OffPathSampling m hm (response, opponent)).toReal *
      ((theorem9PrefixPreference beta m).prob PUnit.unit.{1} response opponent -
        Real.sigmoid (reward response - reward opponent))

/-- The full Appendix-G comparison law retains the symmetric ordered-pair
presentation of each of its two uniform components. -/
theorem theorem9ComparisonSampling_isSymmetric {m : ℕ} (hm : 3 ≤ m)
    (epsilon : NNReal) :
    (theorem9ComparisonSampling m hm epsilon).IsSymmetric := by
  intro first second
  have hpath := theorem9PathSampling_isSymmetric (m := m) (by omega) first second
  have hoff := theorem9OffPathSampling_isSymmetric (m := m) hm first second
  rw [theorem9ComparisonSampling, AppliedModelingLib.binaryMixturePMF_apply_toReal,
    AppliedModelingLib.binaryMixturePMF_apply_toReal, hpath, hoff]

/-- Appendix G's comparison law never displays a diagonal pair, matching the
zero diagonal of the literal finite count likelihood. -/
theorem theorem9ComparisonSampling_zeroDiagonal {m : ℕ} (hm : 3 ≤ m)
    (epsilon : NNReal) :
    (theorem9ComparisonSampling m hm epsilon).HasZeroDiagonal := by
  intro alternative
  have hpath := theorem9PathSampling_zero_of_not_adjacent (m := m) (by omega)
    alternative alternative (by omega)
  have hoff := theorem9OffPathSampling_zero_of_not_mem hm
    (alternative, alternative) (by simp [theorem9OffPathPairs])
  rw [theorem9ComparisonSampling, AppliedModelingLib.binaryMixturePMF_apply_toReal,
    hpath, hoff]
  ring

/-- The exact mass of a directed adjacent comparison in the source mixture. -/
theorem theorem9ComparisonSampling_path_orientation_mass {m : ℕ} (hm : 3 ≤ m)
    (epsilon : NNReal) (edge : Fin (m - 1) × Bool) :
    (theorem9ComparisonSampling m hm epsilon
      (theorem9PathOrientation (by omega) edge)).toReal =
      ((1 - epsilon : NNReal) : ℝ) *
        (Fintype.card (Fin (m - 1) × Bool) : ℝ)⁻¹ := by
  have hoffzero := theorem9OffPathSampling_zero_of_not_mem hm
    (theorem9PathOrientation (by omega) edge)
    (theorem9PathOrientation_not_mem_offPathPairs hm edge)
  rw [theorem9ComparisonSampling, AppliedModelingLib.binaryMixturePMF_apply_toReal,
    hoffzero, theorem9PathSampling_orientation_mass]
  ring

/-- Each oriented adjacent pair has positive mass in the path component. -/
theorem theorem9_pathSampling_orientation_pos {m : ℕ} (hm : 2 ≤ m)
    (edge : Fin (m - 1) × Bool) :
    0 < (theorem9PathSampling m hm (theorem9PathOrientation hm edge)).toReal := by
  letI : Nonempty (Fin (m - 1)) := ⟨0, by omega⟩
  unfold theorem9PathSampling
  apply AppliedModelingLib.pmf_map_apply_toReal_pos_of_pos
  exact AppliedModelingLib.uniformPMF_apply_toReal_pos edge

/-- Each directed off-path pair has positive mass in the uniform off-path
component. -/
theorem theorem9_offPathSampling_pos {m : ℕ} (hm : 3 ≤ m)
    (pair : theorem9OffPathPair m) :
    0 < (theorem9OffPathSampling m hm pair.val).toReal := by
  letI : Fintype (theorem9OffPathPair m) :=
    Fintype.ofFinset (theorem9OffPathPairs m) (by intro pair; rfl)
  letI : Nonempty (theorem9OffPathPair m) :=
    ⟨⟨(⟨0, by omega⟩, ⟨2, by omega⟩), by simp [theorem9OffPathPairs]⟩⟩
  unfold theorem9OffPathSampling
  apply AppliedModelingLib.pmf_map_apply_toReal_pos_of_pos
  exact AppliedModelingLib.uniformPMF_apply_toReal_pos pair

/-- If `ε < 1`, the source mixture retains positive mass on every oriented
adjacent pair. -/
theorem theorem9_comparisonSampling_path_orientation_pos {m : ℕ} (hm : 3 ≤ m)
    (epsilon : NNReal) (hepsilon : epsilon < 1) (edge : Fin (m - 1) × Bool) :
    0 < (theorem9ComparisonSampling m hm epsilon
      (theorem9PathOrientation (by omega) edge)).toReal := by
  have hepsilon_real : (epsilon : ℝ) < 1 := by exact_mod_cast hepsilon
  have hshare : 0 < ((1 - epsilon : NNReal) : ℝ) := by
    rw [NNReal.coe_sub (le_of_lt hepsilon)]
    norm_num
    linarith
  rw [theorem9ComparisonSampling, AppliedModelingLib.binaryMixturePMF_apply_toReal]
  have hpath := theorem9_pathSampling_orientation_pos (m := m) (by omega) edge
  have hoff_nonneg : 0 ≤
      (theorem9OffPathSampling m hm (theorem9PathOrientation (by omega) edge)).toReal :=
    ENNReal.toReal_nonneg
  have hshare_le_one : ((1 - epsilon : NNReal) : ℝ) ≤ 1 := by
    exact_mod_cast tsub_le_self
  have hremaining_nonneg : 0 ≤ 1 - ((1 - epsilon : NNReal) : ℝ) :=
    sub_nonneg.mpr hshare_le_one
  have hpath_term := mul_pos hshare hpath
  have hoff_term := mul_nonneg hremaining_nonneg hoff_nonneg
  linarith

/-- If `0 < ε < 1`, the source mixture retains positive mass on every
off-path pair. -/
theorem theorem9_comparisonSampling_offPath_pos {m : ℕ} (hm : 3 ≤ m)
    (epsilon : NNReal) (hepsilon_pos : 0 < epsilon) (hepsilon_lt : epsilon < 1)
    (pair : theorem9OffPathPair m) :
    0 < (theorem9ComparisonSampling m hm epsilon pair.val).toReal := by
  have hepsilon_real : 0 < (epsilon : ℝ) := by exact_mod_cast hepsilon_pos
  have hremaining : 1 - ((1 - epsilon : NNReal) : ℝ) = (epsilon : ℝ) := by
    rw [NNReal.coe_sub (le_of_lt hepsilon_lt)]
    norm_num
  rw [theorem9ComparisonSampling, AppliedModelingLib.binaryMixturePMF_apply_toReal, hremaining]
  have hpath_nonneg : 0 ≤ (theorem9PathSampling m (by omega) pair.val).toReal :=
    ENNReal.toReal_nonneg
  have hoff := theorem9_offPathSampling_pos hm pair
  nlinarith [mul_pos hepsilon_real hoff]

/-- For `0 < ε < 1`, Appendix G's mixture assigns positive mass to every
distinct ordered pair: adjacent pairs come from the path component and every
other pair comes from the off-path component. -/
theorem theorem9ComparisonSampling_fullOffDiagonalSupport {m : ℕ} (hm : 3 ≤ m)
    (epsilon : NNReal) (hepsilon_pos : 0 < epsilon) (hepsilon_lt : epsilon < 1) :
    (theorem9ComparisonSampling m hm epsilon).HasFullOffDiagonalSupport := by
  intro first second hne
  by_cases hforward : first.val + 1 = second.val
  · let edge : Fin (m - 1) := ⟨first.val, by omega⟩
    have hfirst : (⟨edge.val, by omega⟩ : Fin m) = first := by
      apply Fin.ext
      rfl
    have hsecond : (⟨edge.val + 1, by omega⟩ : Fin m) = second := by
      apply Fin.ext
      exact hforward
    have horientation : theorem9PathOrientation (by omega) (edge, true) =
        (first, second) := by
      simp [theorem9PathOrientation, hfirst, hsecond]
    have hpos := theorem9_comparisonSampling_path_orientation_pos hm epsilon hepsilon_lt
      (edge, true)
    rwa [horientation] at hpos
  by_cases hbackward : second.val + 1 = first.val
  · let edge : Fin (m - 1) := ⟨second.val, by omega⟩
    have hfirst : (⟨edge.val + 1, by omega⟩ : Fin m) = first := by
      apply Fin.ext
      exact hbackward
    have hsecond : (⟨edge.val, by omega⟩ : Fin m) = second := by
      apply Fin.ext
      rfl
    have horientation : theorem9PathOrientation (by omega) (edge, false) =
        (first, second) := by
      simp [theorem9PathOrientation, hfirst, hsecond]
    have hpos := theorem9_comparisonSampling_path_orientation_pos hm epsilon hepsilon_lt
      (edge, false)
    rwa [horientation] at hpos
  let pair : theorem9OffPathPair m := ⟨(first, second), by
    simp only [theorem9OffPathPairs, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨hne, hforward, hbackward⟩⟩
  have hpos := theorem9_comparisonSampling_offPath_pos hm epsilon
    hepsilon_pos hepsilon_lt pair
  simpa [pair] using hpos

/-- The literal iid observation law used for the sampled-MLE step of
Appendix G: first draw one correlated ordered pair, then its Bradley--Terry
Boolean comparison outcome. -/
noncomputable def theorem9OneComparisonReportLaw (beta : ℝ) (m : ℕ) (hm : 3 ≤ m)
    (epsilon : NNReal) : PMF (BinaryPairwiseReport (Fin m)) :=
  correlatedOneComparisonReportLaw
    (theorem9ComparisonSampling m hm epsilon) (theorem9PrefixPreference beta m)

/-- Every directed winner report has positive probability in the literal
Appendix-G iid observation law. -/
theorem theorem9OneComparisonReportLaw_directTrue_pos {beta : ℝ} {m : ℕ}
    (hm : 3 ≤ m) (epsilon : NNReal) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt : epsilon < 1) (winner loser : Fin m) (hneq : winner ≠ loser) :
    0 < (theorem9OneComparisonReportLaw beta m hm epsilon
      (PairwiseCountDataset.directTrueBinaryReport winner loser)).toReal := by
  unfold theorem9OneComparisonReportLaw
  apply correlatedOneComparisonReportLaw_directTrue_pos
  · exact hneq
  · exact theorem9ComparisonSampling_fullOffDiagonalSupport hm epsilon
      hepsilon_pos hepsilon_lt
  · intro first second
    exact theorem9_prefixPreference_prob_pos beta m first second

/-- Hence, under the source's literal iid comparison law, the probability
that the finite fixed-reference logistic MLE is unattained converges to zero.
This is the finite-data existence component of Appendix G; the empirical
argmax-to-population-order step is developed separately below. -/
theorem theorem9_iidNoFiniteMLEProbability_tendsto_zero {beta : ℝ} {m : ℕ}
    (hm : 3 ≤ m) (epsilon : NNReal) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt : epsilon < 1) :
    Filter.Tendsto
      (PairwiseCountDataset.noPairwiseMLEProbability
        (theorem9OneComparisonReportLaw beta m hm epsilon)
        PairwiseCountDataset.sigmoidCDFLikePairwiseLink (⟨0, by omega⟩ : Fin m))
      Filter.atTop (𝓝 0) := by
  apply PairwiseCountDataset.noPairwiseMLEProbability_tendsto_zero
    (theorem9OneComparisonReportLaw beta m hm epsilon)
    PairwiseCountDataset.sigmoidCDFLikePairwiseLink (⟨0, by omega⟩ : Fin m)
  · exact PairwiseCountDataset.continuous_sigmoidCDFLikePairwiseLink
  · exact PairwiseCountDataset.strictMono_sigmoidCDFLikePairwiseLink
  · intro winner loser hneq
    exact theorem9OneComparisonReportLaw_directTrue_pos hm epsilon hepsilon_pos
      hepsilon_lt winner loser hneq

/-- The literal Appendix-G report likelihood has exactly twice the correlated
population fit objective.  This is the source-to-model identity needed for
the iid sampled-MLE step and does not replace correlated pairs by independent
candidate draws. -/
theorem theorem9_expectedRawLogLikelihood_eq_two_populationObjective
    {beta : ℝ} {m : ℕ} (hm : 3 ≤ m) (epsilon : NNReal)
    (score : PairwiseCountDataset.ScoreVector (Fin m)) :
    correlatedOneComparisonExpectedRawLogLikelihood
      (theorem9ComparisonSampling m hm epsilon) (theorem9PrefixPreference beta m) score =
      2 * correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
        (theorem9ComparisonSampling m hm epsilon) score := by
  calc
    correlatedOneComparisonExpectedRawLogLikelihood
        (theorem9ComparisonSampling m hm epsilon) (theorem9PrefixPreference beta m) score =
        2 * correlatedOneComparisonOffDiagonalFitObjective
          (theorem9ComparisonSampling m hm epsilon) (theorem9PrefixPreference beta m)
            score := by
          exact correlatedOneComparisonExpectedRawLogLikelihood_eq_two_offDiagonalFitObjective
            (theorem9ComparisonSampling m hm epsilon) (theorem9PrefixPreference beta m)
            (theorem9ComparisonSampling_isSymmetric hm epsilon) score
    _ = 2 * correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
        (theorem9ComparisonSampling m hm epsilon) score := by
          rw [correlatedBradleyTerryFitObjective_eq_offDiagonalFitObjective
            (theorem9ComparisonSampling m hm epsilon) (theorem9PrefixPreference beta m)
            (theorem9ComparisonSampling_zeroDiagonal hm epsilon)]

/-- The population objective that is literally the expectation of one
Appendix-G Boolean comparison report. -/
noncomputable def theorem9RawPopulationLogLikelihood (beta : ℝ) (m : ℕ)
    (hm : 3 ≤ m) (epsilon : NNReal)
    (score : ScoreVector (Fin m)) : ℝ :=
  correlatedOneComparisonExpectedRawLogLikelihood
    (theorem9ComparisonSampling m hm epsilon) (theorem9PrefixPreference beta m) score

/-- The literal one-report population likelihood is continuous in all finite
score coordinates. -/
theorem continuous_theorem9RawPopulationLogLikelihood (beta : ℝ) (m : ℕ)
    (hm : 3 ≤ m) (epsilon : NNReal) :
    Continuous (theorem9RawPopulationLogLikelihood beta m hm epsilon) := by
  unfold theorem9RawPopulationLogLikelihood
    correlatedOneComparisonExpectedRawLogLikelihood pmfExp
  apply continuous_finset_sum
  intro report _
  apply Continuous.const_mul
  exact continuous_binaryReportLogLikelihoodTerm_sigmoid report

/-- The literal raw population likelihood and the source correlated
Bradley--Terry objective have the same global maximizers. -/
theorem theorem9_rawPopulation_globalMax_iff_correlatedBradleyTerryFit_globalMax
    (beta : ℝ) (m : ℕ) (hm : 3 ≤ m) (epsilon : NNReal)
    (score : ScoreVector (Fin m)) :
    (∀ candidate,
      theorem9RawPopulationLogLikelihood beta m hm epsilon candidate ≤
        theorem9RawPopulationLogLikelihood beta m hm epsilon score) ↔
      (∀ candidate,
        correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
          (theorem9ComparisonSampling m hm epsilon) candidate ≤
        correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
          (theorem9ComparisonSampling m hm epsilon) score) := by
  constructor
  · intro h candidate
    have hraw := h candidate
    unfold theorem9RawPopulationLogLikelihood at hraw
    rw [theorem9_expectedRawLogLikelihood_eq_two_populationObjective hm epsilon,
      theorem9_expectedRawLogLikelihood_eq_two_populationObjective hm epsilon] at hraw
    nlinarith
  · intro h candidate
    have hpopulation := h candidate
    unfold theorem9RawPopulationLogLikelihood
    rw [theorem9_expectedRawLogLikelihood_eq_two_populationObjective hm epsilon,
      theorem9_expectedRawLogLikelihood_eq_two_populationObjective hm epsilon]
    nlinarith

/-- The finite family of literal direct-true reports in an Appendix-G prefix
has a common positive atom-frequency threshold. -/
theorem theorem9_exists_directTrueFrequencyThreshold {beta : ℝ} {m : ℕ}
    (hm : 3 ≤ m) (epsilon : NNReal) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt : epsilon < 1) :
    ∃ threshold : ℝ, 0 < threshold ∧ threshold < 1 ∧
      ∀ winner loser : Fin m, winner ≠ loser →
        threshold <
          (theorem9OneComparisonReportLaw beta m hm epsilon
            (directTrueBinaryReport winner loser)).toReal := by
  let reportLaw : PMF (BinaryPairwiseReport (Fin m)) :=
    theorem9OneComparisonReportLaw beta m hm epsilon
  let atoms : Finset (BinaryPairwiseReport (Fin m)) :=
    directedTrueBinaryReports (Fin m)
  let first : Fin m := ⟨0, by omega⟩
  let second : Fin m := ⟨1, by omega⟩
  have hneq : first ≠ second := by
    intro h
    have hval := congrArg Fin.val h
    simp [first, second] at hval
  have hatoms : atoms.Nonempty := by
    refine ⟨directTrueBinaryReport first second, ?_⟩
    exact directTrueBinaryReport_mem_directedTrueBinaryReports first second hneq
  have hmass : ∀ atom ∈ atoms, 0 < (reportLaw atom).toReal := by
    intro atom hatom
    rcases Finset.mem_image.mp hatom with ⟨pair, hpair, rfl⟩
    exact theorem9OneComparisonReportLaw_directTrue_pos hm epsilon hepsilon_pos
      hepsilon_lt pair.1 pair.2 (Finset.mem_filter.mp hpair).2
  obtain ⟨threshold, hthreshold_pos, hthreshold⟩ :=
    Probability.exists_pos_lt_atomMass_of_finite reportLaw atoms hatoms hmass
  refine ⟨threshold, hthreshold_pos, ?_, ?_⟩
  · have hmember : directTrueBinaryReport first second ∈ atoms := by
      exact directTrueBinaryReport_mem_directedTrueBinaryReports first second hneq
    exact lt_of_lt_of_le (hthreshold _ hmember)
      (pmf_apply_toReal_le_one reportLaw _)
  · intro winner loser hneq
    exact hthreshold _
      (directTrueBinaryReport_mem_directedTrueBinaryReports winner loser hneq)

/-- The exact finite-prefix correlated likelihood attains a global population
MLE once the source's positive off-path mass gives full pair support. -/
theorem theorem9_exists_populationMLE {beta : ℝ} {m : ℕ} (hm : 3 ≤ m)
    (epsilon : NNReal) (hepsilon_pos : 0 < epsilon) (hepsilon_lt : epsilon < 1) :
    ∃ reward : Fin m → ℝ, ∀ candidate : Fin m → ℝ,
      correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
        (theorem9ComparisonSampling m hm epsilon) candidate ≤
        correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
          (theorem9ComparisonSampling m hm epsilon) reward := by
  letI : Nonempty (Fin m) := ⟨0, by omega⟩
  apply exists_correlatedBradleyTerryFit_globalMax
  · exact theorem9ComparisonSampling_fullOffDiagonalSupport hm epsilon
      hepsilon_pos hepsilon_lt
  · intro first second _
    exact theorem9_prefixPreference_prob_pos beta m first second

/-- At every attained finite-prefix population MLE, the source's exact
weighted first-order equation holds at each alternative. -/
theorem theorem9_populationMLE_stationary {beta : ℝ} {m : ℕ} (hm : 3 ≤ m)
    (epsilon : NNReal) (reward : Fin m → ℝ)
    (hmax : ∀ candidate : Fin m → ℝ,
      correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
        (theorem9ComparisonSampling m hm epsilon) candidate ≤
        correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
          (theorem9ComparisonSampling m hm epsilon) reward)
    (response : Fin m) :
    (∑ opponent : Fin m,
      (theorem9ComparisonSampling m hm epsilon (response, opponent)).toReal *
        ((theorem9PrefixPreference beta m).prob () response opponent -
          Real.sigmoid (reward response - reward opponent))) = 0 := by
  apply correlatedBradleyTerryFit_stationary_sum_of_globalMax
  · exact theorem9ComparisonSampling_isSymmetric hm epsilon
  · exact hmax

/-- The source stationary equation decomposes exactly into its path residual
and an `ε`-scaled off-path residual. -/
theorem theorem9_populationMLE_path_off_decomposition {beta : ℝ} {m : ℕ}
    (hm : 3 ≤ m) (epsilon : NNReal) (hepsilon_lt : epsilon < 1)
    (reward : Fin m → ℝ)
    (hmax : ∀ candidate : Fin m → ℝ,
      correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
        (theorem9ComparisonSampling m hm epsilon) candidate ≤
        correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
          (theorem9ComparisonSampling m hm epsilon) reward)
    (response : Fin m) :
    ((1 - epsilon : NNReal) : ℝ) *
        theorem9PathResidual beta m hm reward response +
      (epsilon : ℝ) * theorem9OffPathResidual beta m hm reward response = 0 := by
  have hremaining : 1 - ((1 - epsilon : NNReal) : ℝ) = (epsilon : ℝ) := by
    rw [NNReal.coe_sub (le_of_lt hepsilon_lt)]
    norm_num
  have hstationary := theorem9_populationMLE_stationary hm epsilon reward hmax response
  unfold theorem9PathResidual theorem9OffPathResidual
  rw [theorem9ComparisonSampling] at hstationary
  simp_rw [AppliedModelingLib.binaryMixturePMF_apply_toReal] at hstationary
  rw [hremaining] at hstationary
  calc
    ((1 - epsilon : NNReal) : ℝ) *
        (∑ opponent : Fin m,
          (theorem9PathSampling m (by omega) (response, opponent)).toReal *
            ((theorem9PrefixPreference beta m).prob PUnit.unit.{1} response opponent -
              Real.sigmoid (reward response - reward opponent))) +
      (epsilon : ℝ) *
        (∑ opponent : Fin m,
          (theorem9OffPathSampling m hm (response, opponent)).toReal *
            ((theorem9PrefixPreference beta m).prob PUnit.unit.{1} response opponent -
              Real.sigmoid (reward response - reward opponent))) =
        ∑ opponent : Fin m,
          (((1 - epsilon : NNReal) : ℝ) *
            (theorem9PathSampling m (by omega) (response, opponent)).toReal +
            (epsilon : ℝ) *
              (theorem9OffPathSampling m hm (response, opponent)).toReal) *
            ((theorem9PrefixPreference beta m).prob PUnit.unit.{1} response opponent -
              Real.sigmoid (reward response - reward opponent)) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun opponent _ => ?_
          ring
    _ = 0 := hstationary

/-- The off-path component of the Appendix-G comparison law contributes at
most one in absolute value to a coordinate stationary equation. -/
theorem theorem9_offPathResidual_abs_le_one {beta : ℝ} {m : ℕ} (hm : 3 ≤ m)
    (reward : Fin m → ℝ) (response : Fin m) :
    |theorem9OffPathResidual beta m hm reward response| ≤ 1 := by
  exact correlatedBradleyTerryResidual_abs_le_one
    (theorem9PrefixPreference beta m) (theorem9OffPathSampling m hm) reward response

/-- At a finite-prefix population MLE, each path-component coordinate
residual is at most `ε / (1 - ε)`.  This is the quantitative replacement for
the source proof's informal statement that the off-path perturbation is small. -/
theorem theorem9_populationMLE_pathResidual_abs_le {beta : ℝ} {m : ℕ}
    (hm : 3 ≤ m) (epsilon : NNReal) (hepsilon_lt : epsilon < 1)
    (reward : Fin m → ℝ)
    (hmax : ∀ candidate : Fin m → ℝ,
      correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
        (theorem9ComparisonSampling m hm epsilon) candidate ≤
        correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
          (theorem9ComparisonSampling m hm epsilon) reward)
    (response : Fin m) :
    |theorem9PathResidual beta m hm reward response| ≤
      (epsilon : ℝ) / ((1 - epsilon : NNReal) : ℝ) := by
  have hepsilon_lt_real : (epsilon : ℝ) < 1 := by
    exact_mod_cast hepsilon_lt
  have hshare : 0 < ((1 - epsilon : NNReal) : ℝ) := by
    rw [NNReal.coe_sub (le_of_lt hepsilon_lt)]
    exact sub_pos.mpr hepsilon_lt_real
  have hstationary := theorem9_populationMLE_path_off_decomposition hm epsilon
    hepsilon_lt reward hmax response
  have hoff := theorem9_offPathResidual_abs_le_one (beta := beta) hm reward response
  have hproduct :
      ((1 - epsilon : NNReal) : ℝ) *
          theorem9PathResidual beta m hm reward response =
        -(epsilon : ℝ) * theorem9OffPathResidual beta m hm reward response := by
    linarith
  have habs :
      ((1 - epsilon : NNReal) : ℝ) *
          |theorem9PathResidual beta m hm reward response| =
        (epsilon : ℝ) * |theorem9OffPathResidual beta m hm reward response| := by
    calc
      ((1 - epsilon : NNReal) : ℝ) *
          |theorem9PathResidual beta m hm reward response| =
          |((1 - epsilon : NNReal) : ℝ) *
            theorem9PathResidual beta m hm reward response| := by
            rw [abs_mul, abs_of_pos hshare]
      _ = |-(epsilon : ℝ) * theorem9OffPathResidual beta m hm reward response| := by
            rw [hproduct]
      _ = (epsilon : ℝ) * |theorem9OffPathResidual beta m hm reward response| := by
            rw [abs_mul, abs_neg, abs_of_nonneg (by exact_mod_cast epsilon.property)]
  apply (le_div_iff₀ hshare).mpr
  calc
    |theorem9PathResidual beta m hm reward response| *
        ((1 - epsilon : NNReal) : ℝ) =
        ((1 - epsilon : NNReal) : ℝ) *
          |theorem9PathResidual beta m hm reward response| := by ring
    _ = (epsilon : ℝ) * |theorem9OffPathResidual beta m hm reward response| := habs
    _ ≤ (epsilon : ℝ) * 1 := by
      exact mul_le_mul_of_nonneg_left hoff (by exact_mod_cast epsilon.property)
    _ = (epsilon : ℝ) := by ring

/-- At the last prefix alternative, the path residual consists of its unique
adjacent comparison. -/
theorem theorem9PathResidual_last {beta : ℝ} {m : ℕ} (hm : 3 ≤ m)
    (reward : Fin m → ℝ) :
    theorem9PathResidual beta m hm reward ⟨m - 1, by omega⟩ =
      (Fintype.card (Fin (m - 1) × Bool) : ℝ)⁻¹ *
        ((theorem9PrefixPreference beta m).prob PUnit.unit.{1}
            ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩ -
          Real.sigmoid (reward ⟨m - 1, by omega⟩ - reward ⟨m - 2, by omega⟩)) := by
  unfold theorem9PathResidual
  rw [Finset.sum_eq_single ⟨m - 2, by omega⟩]
  · have hpair :
        ((⟨m - 1, by omega⟩ : Fin m), (⟨m - 2, by omega⟩ : Fin m)) =
          theorem9PathOrientation (by omega) (⟨m - 2, by omega⟩, false) := by
          change
            ((⟨m - 1, by omega⟩ : Fin m), (⟨m - 2, by omega⟩ : Fin m)) =
              ((⟨m - 2 + 1, by omega⟩ : Fin m), (⟨m - 2, by omega⟩ : Fin m))
          apply Prod.ext
          · apply Fin.ext
            change m - 1 = m - 2 + 1
            omega
          · rfl
    rw [hpair, theorem9PathSampling_orientation_mass]
  · intro opponent _ hnotlast
    have hzero := theorem9PathSampling_zero_of_not_adjacent (m := m) (by omega)
      ⟨m - 1, by omega⟩ opponent (by
        rintro (hforward | hbackward)
        · change m - 1 + 1 = opponent.val at hforward
          have hmone : m - 1 + 1 = m := by omega
          omega
        · change opponent.val + 1 = m - 1 at hbackward
          have hmtwo : m - 2 + 1 = m - 1 := by omega
          have hopponent : opponent.val = m - 2 := by omega
          apply hnotlast
          exact Fin.ext hopponent)
    rw [hzero]
    ring
  · simp

/-- The successor index inside a nonempty finite prefix. -/
def theorem9Succ {m : ℕ} (index : Fin (m - 1)) : Fin m :=
  ⟨index.val + 1, by omega⟩

/-- The lower endpoint of a finite-prefix path edge. -/
def theorem9EdgeLower {m : ℕ} (edge : Fin (m - 1)) : Fin m :=
  ⟨edge.val, by
    have hedge : edge.val < m - 1 := edge.isLt
    omega⟩

/-- The edge at an interior index of a finite prefix. -/
def theorem9InteriorEdge {m : ℕ} (index : Fin (m - 2)) : Fin (m - 1) :=
  ⟨index.val, by
    have hindex : index.val < m - 2 := index.isLt
    omega⟩

/-- The next path edge after an interior index. -/
def theorem9NextEdge {m : ℕ} (index : Fin (m - 2)) : Fin (m - 1) :=
  ⟨index.val + 1, by
    have hindex : index.val < m - 2 := index.isLt
    omega⟩

/-- The directed Bradley--Terry fitting residual on one oriented path edge. -/
noncomputable def theorem9AdjacentResidual (beta : ℝ) (m : ℕ)
    (reward : Fin m → ℝ) (edge : Fin (m - 1)) : ℝ :=
  (theorem9PrefixPreference beta m).prob PUnit.unit.{1}
      (theorem9Succ edge) (theorem9EdgeLower edge) -
    Real.sigmoid (reward (theorem9Succ edge) - reward (theorem9EdgeLower edge))

/-- At an interior prefix alternative, the path residual is the common
oriented-edge mass times the difference of the two adjacent edge residuals.
This is the finite recurrence used by Appendix G's backward argument. -/
theorem theorem9PathResidual_interior {beta : ℝ} {m : ℕ} (hm : 3 ≤ m)
    (reward : Fin m → ℝ) (index : Fin (m - 2)) :
    theorem9PathResidual beta m hm reward
        (theorem9Succ (theorem9InteriorEdge index)) =
      (Fintype.card (Fin (m - 1) × Bool) : ℝ)⁻¹ *
        (theorem9AdjacentResidual beta m reward (theorem9InteriorEdge index) -
          theorem9AdjacentResidual beta m reward (theorem9NextEdge index)) := by
  let edge := theorem9InteriorEdge index
  let next := theorem9NextEdge index
  let lower := theorem9EdgeLower edge
  let center := theorem9Succ edge
  let upper := theorem9Succ next
  let term : Fin m → ℝ := fun opponent =>
    (theorem9PathSampling m (by omega) (center, opponent)).toReal *
      ((theorem9PrefixPreference beta m).prob PUnit.unit.{1} center opponent -
        Real.sigmoid (reward center - reward opponent))
  change (∑ opponent : Fin m, term opponent) =
    (Fintype.card (Fin (m - 1) × Bool) : ℝ)⁻¹ *
      ((theorem9PrefixPreference beta m).prob PUnit.unit.{1} center lower -
        Real.sigmoid (reward center - reward lower) -
        ((theorem9PrefixPreference beta m).prob PUnit.unit.{1} upper center -
          Real.sigmoid (reward upper - reward center)))
  have hsum : (∑ opponent : Fin m, term opponent) = term lower + term upper := by
    rw [Finset.sum_eq_add_sum_diff_singleton lower]
    · rw [Finset.sum_eq_single upper]
      · intro opponent hmem hnotupper
        have hnotlower : opponent ≠ lower := by
          simpa using (Finset.mem_sdiff.mp hmem).2
        have hzero := theorem9PathSampling_zero_of_not_adjacent (m := m) (by omega)
          center opponent (by
            rintro (hforward | hbackward)
            · change index.val + 1 + 1 = opponent.val at hforward
              have hopponent : opponent = upper := by
                apply Fin.ext
                change opponent.val = index.val + 1 + 1
                omega
              exact hnotupper hopponent
            · change opponent.val + 1 = index.val + 1 at hbackward
              have hopponent : opponent = lower := by
                apply Fin.ext
                change opponent.val = index.val
                omega
              exact hnotlower hopponent)
        dsimp [term]
        rw [hzero]
        ring
      · intro huppernotmem
        exfalso
        apply huppernotmem
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton]
        intro hupperlower
        have hvalue := congrArg Fin.val hupperlower
        change index.val + 1 + 1 = index.val at hvalue
        omega
    · simp
  have hleft : (center, lower) = theorem9PathOrientation (by omega) (edge, false) := by
    dsimp [center, lower, edge, theorem9InteriorEdge, theorem9EdgeLower, theorem9Succ]
    rfl
  have hright : (center, upper) = theorem9PathOrientation (by omega) (next, true) := by
    dsimp [center, upper, edge, next, theorem9InteriorEdge, theorem9NextEdge, theorem9Succ]
    rfl
  have hleft_mass := theorem9PathSampling_orientation_mass (m := m) (by omega)
    (edge, false)
  rw [← hleft] at hleft_mass
  have hright_mass := theorem9PathSampling_orientation_mass (m := m) (by omega)
    (next, true)
  rw [← hright] at hright_mass
  have hprobability :
      (theorem9PrefixPreference beta m).prob PUnit.unit.{1} center upper =
        1 - (theorem9PrefixPreference beta m).prob PUnit.unit.{1} upper center := by
    have hcomplementary := (theorem9PrefixPreference beta m).complementary
      PUnit.unit.{1} center upper
    linarith
  have hsigmoid : Real.sigmoid (reward center - reward upper) =
      1 - Real.sigmoid (reward upper - reward center) := by
    have hneg : reward center - reward upper = -(reward upper - reward center) := by
      ring
    rw [hneg, Real.sigmoid_neg]
  rw [hsum]
  dsimp [term]
  rw [hleft_mass, hright_mass, hprobability, hsigmoid]
  ring

/-- A finite chain whose terminal residual and successive residual changes are
bounded by `B` has every residual bounded by its remaining chain length times
`B`. -/
theorem finiteChain_abs_le_of_terminal_and_successive {n : ℕ}
    (residual : Fin (n + 1) → ℝ) (bound : ℝ)
    (hlast : |residual (Fin.last n)| ≤ bound)
    (hsuccessive : ∀ index : Fin n,
      |residual index.castSucc - residual index.succ| ≤ bound)
    (index : Fin (n + 1)) :
    |residual index| ≤ ((n + 1 - index.val : ℕ) : ℝ) * bound := by
  induction index using Fin.reverseInduction with
  | last => simpa using hlast
  | cast index ih =>
      have htriangle : |residual index.castSucc| ≤
          |residual index.castSucc - residual index.succ| + |residual index.succ| := by
        calc
          |residual index.castSucc| =
              |(residual index.castSucc - residual index.succ) + residual index.succ| := by
              congr 1
              ring
          _ ≤ |residual index.castSucc - residual index.succ| + |residual index.succ| :=
              abs_add_le _ _
      have hcount : n + 1 - index.val = 1 + (n + 1 - (index.val + 1)) := by
        have hindex : index.val < n := index.isLt
        omega
      calc
        |residual index.castSucc| ≤
            |residual index.castSucc - residual index.succ| + |residual index.succ| := htriangle
        _ ≤ bound + ((n + 1 - (index.val + 1) : ℕ) : ℝ) * bound := by
            exact add_le_add (hsuccessive index) ih
        _ = ((n + 1 - index.val : ℕ) : ℝ) * bound := by
            rw [hcount]
            push_cast
            ring

/-- The same finite-chain estimate stated directly on `Fin n`, with its last
index and predecessor/successor pairs written in the prefix notation used by
the Appendix-G construction. -/
theorem finiteChain_abs_le_of_terminal_and_successive_fin {n : ℕ}
    (hn : 0 < n) (residual : Fin n → ℝ) (bound : ℝ)
    (hlast : |residual ⟨n - 1, by omega⟩| ≤ bound)
    (hsuccessive : ∀ index : Fin (n - 1),
      |residual ⟨index.val, by omega⟩ - residual ⟨index.val + 1, by omega⟩| ≤ bound)
    (index : Fin n) :
    |residual index| ≤ ((n - index.val : ℕ) : ℝ) * bound := by
  cases n with
  | zero => omega
  | succ n =>
      simpa using finiteChain_abs_le_of_terminal_and_successive residual bound
        hlast hsuccessive index

/-- Every positive real threshold admits a strictly positive mixture weight
below one whose odds ratio is smaller than that threshold. -/
theorem exists_nnreal_pos_lt_one_ratio_lt (threshold : ℝ) (hthreshold : 0 < threshold) :
    ∃ epsilon : NNReal, 0 < epsilon ∧ epsilon < 1 ∧
      (epsilon : ℝ) / ((1 - epsilon : NNReal) : ℝ) < threshold := by
  let raw : ℝ := threshold / (2 + threshold)
  have hdenominator : 0 < 2 + threshold := by linarith
  have hraw_pos : 0 < raw := by
    dsimp [raw]
    exact div_pos hthreshold hdenominator
  have hraw_lt_one : raw < 1 := by
    dsimp [raw]
    apply (div_lt_iff₀ hdenominator).mpr
    linarith
  have hraw_ratio : raw / (1 - raw) < threshold := by
    have hsub : 1 - raw = 2 / (2 + threshold) := by
      dsimp [raw]
      field_simp
      ring
    calc
      raw / (1 - raw) = threshold / 2 := by
        dsimp [raw]
        rw [hsub]
        field_simp
      _ < threshold := by linarith
  let epsilon : NNReal := ⟨raw, hraw_pos.le⟩
  refine ⟨epsilon, ?_, ?_, ?_⟩
  · exact hraw_pos
  · exact hraw_lt_one
  · rw [NNReal.coe_sub (le_of_lt hraw_lt_one)]
    exact hraw_ratio

/-- The terminal path residual is the common path mass times the residual on
the last adjacent edge. -/
theorem theorem9PathResidual_last_eq_adjacentResidual {beta : ℝ} {m : ℕ}
    (hm : 3 ≤ m) (reward : Fin m → ℝ) :
    theorem9PathResidual beta m hm reward ⟨m - 1, by omega⟩ =
      (Fintype.card (Fin (m - 1) × Bool) : ℝ)⁻¹ *
        theorem9AdjacentResidual beta m reward (⟨m - 2, by omega⟩ : Fin (m - 1)) := by
  rw [theorem9PathResidual_last]
  have hsuccessor : theorem9Succ (⟨m - 2, by omega⟩ : Fin (m - 1)) =
      (⟨m - 1, by omega⟩ : Fin m) := by
    apply Fin.ext
    change m - 2 + 1 = m - 1
    omega
  have hlower : theorem9EdgeLower (⟨m - 2, by omega⟩ : Fin (m - 1)) =
      (⟨m - 2, by omega⟩ : Fin m) := by
    apply Fin.ext
    rfl
  rw [theorem9AdjacentResidual, hsuccessor, hlower]

/-- The Appendix-G stationary equations bound every adjacent fitting residual
by its remaining path length times the off-path perturbation. -/
theorem theorem9_populationMLE_adjacentResidual_abs_le {beta : ℝ} {m : ℕ}
    (hm : 3 ≤ m) (epsilon : NNReal) (hepsilon_lt : epsilon < 1)
    (reward : Fin m → ℝ)
    (hmax : ∀ candidate : Fin m → ℝ,
      correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
        (theorem9ComparisonSampling m hm epsilon) candidate ≤
        correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
          (theorem9ComparisonSampling m hm epsilon) reward)
    (edge : Fin (m - 1)) :
    |theorem9AdjacentResidual beta m reward edge| ≤
      ((m - 1 - edge.val : ℕ) : ℝ) *
        ((epsilon : ℝ) / ((1 - epsilon : NNReal) : ℝ) /
          (Fintype.card (Fin (m - 1) × Bool) : ℝ)⁻¹) := by
  let perturbation : ℝ := (epsilon : ℝ) / ((1 - epsilon : NNReal) : ℝ)
  let edgeMass : ℝ := (Fintype.card (Fin (m - 1) × Bool) : ℝ)⁻¹
  have hcard : 0 < Fintype.card (Fin (m - 1) × Bool) :=
    Fintype.card_pos_iff.mpr ⟨(⟨0, by omega⟩, false)⟩
  have hedgeMass : 0 < edgeMass := by
    dsimp [edgeMass]
    apply inv_pos.mpr
    exact_mod_cast hcard
  let lastEdge : Fin (m - 1) := ⟨m - 2, by omega⟩
  have hlast : |theorem9AdjacentResidual beta m reward lastEdge| ≤ perturbation / edgeMass := by
    have hpath := theorem9_populationMLE_pathResidual_abs_le hm epsilon hepsilon_lt
      reward hmax ⟨m - 1, by omega⟩
    rw [theorem9PathResidual_last_eq_adjacentResidual] at hpath
    change |edgeMass * theorem9AdjacentResidual beta m reward lastEdge| ≤ perturbation at hpath
    rw [abs_mul, abs_of_pos hedgeMass] at hpath
    apply (le_div_iff₀ hedgeMass).mpr
    simpa [mul_comm] using hpath
  have hsuccessive : ∀ index : Fin ((m - 1) - 1),
      |theorem9AdjacentResidual beta m reward ⟨index.val, by omega⟩ -
        theorem9AdjacentResidual beta m reward ⟨index.val + 1, by omega⟩| ≤
        perturbation / edgeMass := by
    intro index
    have hpath := theorem9_populationMLE_pathResidual_abs_le hm epsilon hepsilon_lt
      reward hmax (theorem9Succ (theorem9InteriorEdge index))
    rw [theorem9PathResidual_interior] at hpath
    change |edgeMass *
        (theorem9AdjacentResidual beta m reward (theorem9InteriorEdge index) -
          theorem9AdjacentResidual beta m reward (theorem9NextEdge index))| ≤ perturbation at hpath
    rw [abs_mul, abs_of_pos hedgeMass] at hpath
    have hdiff :
        |theorem9AdjacentResidual beta m reward (theorem9InteriorEdge index) -
          theorem9AdjacentResidual beta m reward (theorem9NextEdge index)| ≤
        perturbation / edgeMass := by
          apply (le_div_iff₀ hedgeMass).mpr
          simpa [mul_comm] using hpath
    simpa [theorem9InteriorEdge, theorem9NextEdge] using hdiff
  change |theorem9AdjacentResidual beta m reward edge| ≤
    ((m - 1 - edge.val : ℕ) : ℝ) * (perturbation / edgeMass)
  apply finiteChain_abs_le_of_terminal_and_successive_fin (n := m - 1) (by omega)
  · simpa [lastEdge] using hlast
  · exact hsuccessive

/-- Every adjacent pair in a prefix has the strict source majority used by the
backward MLE ordering argument. -/
theorem theorem9_prefix_adjacent_preference {beta : ℝ} (hbeta : 0 < beta)
    {m : ℕ} (hm : 2 ≤ m) (index : Fin (m - 1)) :
    (1 : ℝ) / 2 <
      (theorem9PrefixPreference beta m).prob PUnit.unit.{1}
        (theorem9Succ index) ⟨index.val, Nat.lt_trans index.isLt (by omega)⟩ := by
  change (1 : ℝ) / 2 <
    (AppliedModelingLib.Alignment.Welfare.populationBradleyTerryPreference lemma15Population
      (lemma15Profile beta) beta).prob PUnit.unit.{1} (index.val + 1) index.val
  exact lemma15_population_adjacent_preference hbeta index.val

/-- An adjacent prefix edge is ordered correctly whenever its source majority
margin exceeds the accumulated bound on its fitted residual. -/
theorem theorem9_populationMLE_adjacent_order {beta : ℝ} (hbeta : 0 < beta)
    {m : ℕ} (hm : 3 ≤ m) (epsilon : NNReal) (hepsilon_lt : epsilon < 1)
    (reward : Fin m → ℝ)
    (hmax : ∀ candidate : Fin m → ℝ,
      correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
        (theorem9ComparisonSampling m hm epsilon) candidate ≤
        correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
          (theorem9ComparisonSampling m hm epsilon) reward)
    (edge : Fin (m - 1))
    (hsmall : ((m - 1 - edge.val : ℕ) : ℝ) *
        ((epsilon : ℝ) / ((1 - epsilon : NNReal) : ℝ) /
          (Fintype.card (Fin (m - 1) × Bool) : ℝ)⁻¹) <
      (theorem9PrefixPreference beta m).prob PUnit.unit.{1}
          (theorem9Succ edge) (theorem9EdgeLower edge) - (1 : ℝ) / 2) :
    reward (theorem9EdgeLower edge) < reward (theorem9Succ edge) := by
  have hpreference := theorem9_prefix_adjacent_preference hbeta (m := m)
    (by omega) edge
  have hq : (1 : ℝ) / 2 <
      (theorem9PrefixPreference beta m).prob PUnit.unit.{1}
        (theorem9Succ edge) (theorem9EdgeLower edge) := by
    simpa [theorem9EdgeLower] using hpreference
  have hresidual := theorem9_populationMLE_adjacentResidual_abs_le hm epsilon
    hepsilon_lt reward hmax edge
  change |(theorem9PrefixPreference beta m).prob PUnit.unit.{1}
      (theorem9Succ edge) (theorem9EdgeLower edge) -
      Real.sigmoid (reward (theorem9Succ edge) - reward (theorem9EdgeLower edge))| ≤
      ((m - 1 - edge.val : ℕ) : ℝ) *
        ((epsilon : ℝ) / ((1 - epsilon : NNReal) : ℝ) /
          (Fintype.card (Fin (m - 1) × Bool) : ℝ)⁻¹) at hresidual
  have hgap : 0 < reward (theorem9Succ edge) - reward (theorem9EdgeLower edge) := by
    by_contra hnotgap
    have hgap_nonpos : reward (theorem9Succ edge) - reward (theorem9EdgeLower edge) ≤ 0 :=
      le_of_not_gt hnotgap
    have hfitted : Real.sigmoid
        (reward (theorem9Succ edge) - reward (theorem9EdgeLower edge)) ≤ (1 : ℝ) / 2 := by
      calc
        Real.sigmoid (reward (theorem9Succ edge) - reward (theorem9EdgeLower edge)) ≤
            Real.sigmoid 0 := Real.sigmoid_le hgap_nonpos
        _ = (1 : ℝ) / 2 := by norm_num
    have hmargin_lower :
        (theorem9PrefixPreference beta m).prob PUnit.unit.{1}
            (theorem9Succ edge) (theorem9EdgeLower edge) - (1 : ℝ) / 2 ≤
          (theorem9PrefixPreference beta m).prob PUnit.unit.{1}
            (theorem9Succ edge) (theorem9EdgeLower edge) -
            Real.sigmoid (reward (theorem9Succ edge) - reward (theorem9EdgeLower edge)) := by
      linarith
    have habs_lower :
        (theorem9PrefixPreference beta m).prob PUnit.unit.{1}
            (theorem9Succ edge) (theorem9EdgeLower edge) -
            Real.sigmoid (reward (theorem9Succ edge) - reward (theorem9EdgeLower edge)) ≤
          |(theorem9PrefixPreference beta m).prob PUnit.unit.{1}
            (theorem9Succ edge) (theorem9EdgeLower edge) -
            Real.sigmoid (reward (theorem9Succ edge) - reward (theorem9EdgeLower edge))| := by
      exact le_abs_self _
    linarith
  linarith

/-- For every finite prefix, one strictly positive off-path mixture weight
makes every attained population MLE order all source-adjacent alternatives
correctly.  The chosen weight is obtained from the finite minimum of the
strict adjacent Bradley--Terry margins. -/
theorem theorem9_exists_epsilon_all_adjacent_order {beta : ℝ} (hbeta : 0 < beta)
    {m : ℕ} (hm : 3 ≤ m) :
    ∃ epsilon : NNReal, 0 < epsilon ∧ epsilon < 1 ∧
      ∀ reward : Fin m → ℝ,
        (∀ candidate : Fin m → ℝ,
          correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
            (theorem9ComparisonSampling m hm epsilon) candidate ≤
            correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
              (theorem9ComparisonSampling m hm epsilon) reward) →
          ∀ edge : Fin (m - 1),
            reward (theorem9EdgeLower edge) < reward (theorem9Succ edge) := by
  letI : Nonempty (Fin (m - 1)) := ⟨⟨0, by omega⟩⟩
  let margin : Fin (m - 1) → ℝ := fun edge =>
    (theorem9PrefixPreference beta m).prob PUnit.unit.{1}
      (theorem9Succ edge) (theorem9EdgeLower edge) - (1 : ℝ) / 2
  have hmargin_pos : ∀ edge, 0 < margin edge := by
    intro edge
    dsimp [margin]
    have hpreference := theorem9_prefix_adjacent_preference hbeta (m := m)
      (by omega) edge
    simpa [theorem9EdgeLower] using hpreference
  let minimum : ℝ := finiteMin margin
  have hminimum : 0 < minimum := finiteMin_pos margin hmargin_pos
  let edgeMass : ℝ := (Fintype.card (Fin (m - 1) × Bool) : ℝ)⁻¹
  have hcard : 0 < Fintype.card (Fin (m - 1) × Bool) :=
    Fintype.card_pos_iff.mpr ⟨(⟨0, by omega⟩, false)⟩
  have hedgeMass : 0 < edgeMass := by
    dsimp [edgeMass]
    apply inv_pos.mpr
    exact_mod_cast hcard
  have hlength : 0 < ((m - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < m - 1 by omega)
  let threshold : ℝ := edgeMass * minimum / ((m - 1 : ℕ) : ℝ)
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    exact div_pos (mul_pos hedgeMass hminimum) hlength
  obtain ⟨epsilon, hepsilon_pos, hepsilon_lt, hepsilon_ratio⟩ :=
    exists_nnreal_pos_lt_one_ratio_lt threshold hthreshold
  refine ⟨epsilon, hepsilon_pos, hepsilon_lt, ?_⟩
  intro reward hmax edge
  apply theorem9_populationMLE_adjacent_order hbeta hm epsilon hepsilon_lt reward hmax edge
  have hshare : 0 < ((1 - epsilon : NNReal) : ℝ) := by
    rw [NNReal.coe_sub (le_of_lt hepsilon_lt)]
    have hepsilon_lt_real : (epsilon : ℝ) < 1 := by exact_mod_cast hepsilon_lt
    exact sub_pos.mpr hepsilon_lt_real
  have hratio_pos : 0 < (epsilon : ℝ) / ((1 - epsilon : NNReal) : ℝ) := by
    apply div_pos
    · exact_mod_cast hepsilon_pos
    · exact hshare
  have hquotient_pos : 0 <
      ((epsilon : ℝ) / ((1 - epsilon : NNReal) : ℝ)) / edgeMass :=
    div_pos hratio_pos hedgeMass
  have hquotient :
      ((epsilon : ℝ) / ((1 - epsilon : NNReal) : ℝ)) / edgeMass <
        minimum / ((m - 1 : ℕ) : ℝ) := by
    apply (div_lt_iff₀ hedgeMass).mpr
    calc
      (epsilon : ℝ) / ((1 - epsilon : NNReal) : ℝ) < threshold := hepsilon_ratio
      _ = (minimum / ((m - 1 : ℕ) : ℝ)) * edgeMass := by
        dsimp [threshold]
        ring
  have hremaining : ((m - 1 - edge.val : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_le (m - 1) edge.val)
  have hscaled : ((m - 1 - edge.val : ℕ) : ℝ) *
      (((epsilon : ℝ) / ((1 - epsilon : NNReal) : ℝ)) / edgeMass) < minimum := by
    calc
      ((m - 1 - edge.val : ℕ) : ℝ) *
          (((epsilon : ℝ) / ((1 - epsilon : NNReal) : ℝ)) / edgeMass) ≤
          ((m - 1 : ℕ) : ℝ) *
            (((epsilon : ℝ) / ((1 - epsilon : NNReal) : ℝ)) / edgeMass) :=
              mul_le_mul_of_nonneg_right hremaining hquotient_pos.le
      _ < ((m - 1 : ℕ) : ℝ) * (minimum / ((m - 1 : ℕ) : ℝ)) :=
              mul_lt_mul_of_pos_left hquotient hlength
      _ = minimum := by field_simp
  change ((m - 1 - edge.val : ℕ) : ℝ) *
      (((epsilon : ℝ) / ((1 - epsilon : NNReal) : ℝ)) / edgeMass) < margin edge
  exact hscaled.trans_le (finiteMin_le margin edge)

/-- Every finite prefix has a full-support correlated comparison law with an
attained population MLE that strictly ranks each source successor above its
predecessor. -/
theorem theorem9_exists_ordered_populationMLE {beta : ℝ} (hbeta : 0 < beta)
    {m : ℕ} (hm : 3 ≤ m) :
    ∃ epsilon : NNReal, 0 < epsilon ∧ epsilon < 1 ∧
      ∃ reward : Fin m → ℝ,
        (∀ candidate : Fin m → ℝ,
          correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
            (theorem9ComparisonSampling m hm epsilon) candidate ≤
            correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
              (theorem9ComparisonSampling m hm epsilon) reward) ∧
          ∀ edge : Fin (m - 1),
            reward (theorem9EdgeLower edge) < reward (theorem9Succ edge) := by
  obtain ⟨epsilon, hepsilon_pos, hepsilon_lt, hordered⟩ :=
    theorem9_exists_epsilon_all_adjacent_order hbeta hm
  obtain ⟨reward, hmax⟩ := theorem9_exists_populationMLE hm epsilon
    hepsilon_pos hepsilon_lt
  exact ⟨epsilon, hepsilon_pos, hepsilon_lt, reward, hmax, hordered reward hmax⟩

/-- The last edge is ordered correctly at any population MLE once the
off-path perturbation is smaller than the strict adjacent-comparison margin.
This is the base case of Appendix G's backward stability argument. -/
theorem theorem9_populationMLE_last_order {beta : ℝ} (hbeta : 0 < beta)
    {m : ℕ} (hm : 3 ≤ m) (epsilon : NNReal) (hepsilon_lt : epsilon < 1)
    (reward : Fin m → ℝ)
    (hmax : ∀ candidate : Fin m → ℝ,
      correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
        (theorem9ComparisonSampling m hm epsilon) candidate ≤
        correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
          (theorem9ComparisonSampling m hm epsilon) reward)
    (hsmall : (epsilon : ℝ) / ((1 - epsilon : NNReal) : ℝ) <
      (Fintype.card (Fin (m - 1) × Bool) : ℝ)⁻¹ *
        ((theorem9PrefixPreference beta m).prob PUnit.unit.{1}
            ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩ - (1 : ℝ) / 2)) :
    reward ⟨m - 2, by omega⟩ < reward ⟨m - 1, by omega⟩ := by
  have hcard : 0 < Fintype.card (Fin (m - 1) × Bool) :=
    Fintype.card_pos_iff.mpr ⟨(⟨0, by omega⟩, false)⟩
  have hweight : 0 < (Fintype.card (Fin (m - 1) × Bool) : ℝ)⁻¹ := by
    apply inv_pos.mpr
    exact_mod_cast hcard
  have hpreference := theorem9_prefix_adjacent_preference hbeta (m := m)
    (by omega) (⟨m - 2, by omega⟩ : Fin (m - 1))
  have hq : (1 : ℝ) / 2 <
      (theorem9PrefixPreference beta m).prob PUnit.unit.{1}
        ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩ := by
    have hsuccessor : theorem9Succ (⟨m - 2, by omega⟩ : Fin (m - 1)) =
        (⟨m - 1, by omega⟩ : Fin m) := by
      apply Fin.ext
      change m - 2 + 1 = m - 1
      omega
    rw [hsuccessor] at hpreference
    exact hpreference
  have hresidual := theorem9_populationMLE_pathResidual_abs_le hm epsilon
    hepsilon_lt reward hmax ⟨m - 1, by omega⟩
  rw [theorem9PathResidual_last] at hresidual
  have hgap : 0 < reward ⟨m - 1, by omega⟩ - reward ⟨m - 2, by omega⟩ := by
    by_contra hnotgap
    have hgap_nonpos : reward ⟨m - 1, by omega⟩ - reward ⟨m - 2, by omega⟩ ≤ 0 :=
      le_of_not_gt hnotgap
    have hfitted :
        Real.sigmoid (reward ⟨m - 1, by omega⟩ - reward ⟨m - 2, by omega⟩) ≤
          (1 : ℝ) / 2 := by
      calc
        Real.sigmoid (reward ⟨m - 1, by omega⟩ - reward ⟨m - 2, by omega⟩) ≤
            Real.sigmoid 0 := Real.sigmoid_le hgap_nonpos
        _ = (1 : ℝ) / 2 := by norm_num
    have hmargin_nonneg : 0 ≤
        (theorem9PrefixPreference beta m).prob PUnit.unit.{1}
          ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩ - (1 : ℝ) / 2 := by
      linarith
    have hgap_lower :
        (theorem9PrefixPreference beta m).prob PUnit.unit.{1}
            ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩ - (1 : ℝ) / 2 ≤
          (theorem9PrefixPreference beta m).prob PUnit.unit.{1}
            ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩ -
            Real.sigmoid (reward ⟨m - 1, by omega⟩ - reward ⟨m - 2, by omega⟩) := by
      linarith
    have hweighted_lower :
        (Fintype.card (Fin (m - 1) × Bool) : ℝ)⁻¹ *
            ((theorem9PrefixPreference beta m).prob PUnit.unit.{1}
              ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩ - (1 : ℝ) / 2) ≤
          (Fintype.card (Fin (m - 1) × Bool) : ℝ)⁻¹ *
            ((theorem9PrefixPreference beta m).prob PUnit.unit.{1}
              ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩ -
              Real.sigmoid (reward ⟨m - 1, by omega⟩ - reward ⟨m - 2, by omega⟩)) := by
      exact mul_le_mul_of_nonneg_left hgap_lower hweight.le
    have habs_lower :
        (Fintype.card (Fin (m - 1) × Bool) : ℝ)⁻¹ *
            ((theorem9PrefixPreference beta m).prob PUnit.unit.{1}
              ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩ -
              Real.sigmoid (reward ⟨m - 1, by omega⟩ - reward ⟨m - 2, by omega⟩)) ≤
          |(Fintype.card (Fin (m - 1) × Bool) : ℝ)⁻¹ *
            ((theorem9PrefixPreference beta m).prob PUnit.unit.{1}
              ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩ -
              Real.sigmoid (reward ⟨m - 1, by omega⟩ - reward ⟨m - 2, by omega⟩))| := by
      exact le_abs_self _
    linarith
  linarith

/-- Strict source-adjacent reward order makes the fitted score strictly
increasing across the whole finite prefix. -/
theorem theorem9_reward_strictMono_of_adjacent_order {m : ℕ} (hm : 2 ≤ m)
    (reward : Fin m → ℝ)
    (horder : ∀ edge : Fin (m - 1),
      reward (theorem9EdgeLower edge) < reward (theorem9Succ edge)) :
    StrictMono reward := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  apply Fin.strictMono_iff_lt_succ.mpr
  intro edge
  simpa [theorem9EdgeLower, theorem9Succ] using horder edge

/-- The final alternative has weakly maximal fitted reward on an ordered
finite prefix. -/
theorem theorem9_reward_le_last_of_adjacent_order {m : ℕ} (hm : 2 ≤ m)
    (reward : Fin m → ℝ)
    (horder : ∀ edge : Fin (m - 1),
      reward (theorem9EdgeLower edge) < reward (theorem9Succ edge))
    (alternative : Fin m) :
    reward alternative ≤ reward ⟨m - 1, by omega⟩ := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  change reward alternative ≤ reward (Fin.last n)
  exact (theorem9_reward_strictMono_of_adjacent_order (by omega) reward horder).monotone
    (Fin.le_last alternative)

/-- The final alternative has strictly maximal fitted reward except at itself. -/
theorem theorem9_reward_lt_last_of_adjacent_order {m : ℕ} (hm : 2 ≤ m)
    (reward : Fin m → ℝ)
    (horder : ∀ edge : Fin (m - 1),
      reward (theorem9EdgeLower edge) < reward (theorem9Succ edge))
    (alternative : Fin m) (halternative : alternative ≠ ⟨m - 1, by omega⟩) :
    reward alternative < reward ⟨m - 1, by omega⟩ := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  change reward alternative < reward (Fin.last n)
  apply theorem9_reward_strictMono_of_adjacent_order (by omega) reward horder
  exact lt_of_le_of_ne (Fin.le_last alternative) halternative

/-- The uniform reference policy used by the source at a nonempty finite
prefix.  The explicit size condition keeps the paper-facing type free of an
implementation-only nonemptiness instance. -/
noncomputable def theorem9UniformReference (m : ℕ) (hm : 1 ≤ m) : PMF (Fin m) := by
  letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  exact uniformPMF (Fin m)

/-- The Appendix-G uniform reference satisfies the paper's full-support
convention for reference policies. -/
theorem theorem9UniformReference_fullSupport (m : ℕ) (hm : 1 ≤ m) :
    PMFFullSupport (theorem9UniformReference m hm) := by
  letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  intro alternative
  change 0 < (uniformPMF (Fin m) alternative).toReal
  exact uniformPMF_apply_toReal_pos alternative

/-- At the source radius `log m` around a uniform reference, every finite
policy over an `m`-alternative prefix is KL-feasible. -/
theorem theorem9_every_policy_uniformKL_feasible {m : ℕ} (hm : 1 ≤ m)
    (policy : PMF (Fin m)) :
    finiteKLDivergence policy (theorem9UniformReference m hm) ≤ Real.log (m : ℝ) := by
  letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  change finiteKLDivergence policy (uniformPMF (Fin m)) ≤ Real.log (m : ℝ)
  simpa using (finiteKLDivergence_uniform_le_log_card policy)

/-- When the fitted reward is strictly ordered along the source prefix, the
pure final alternative maximizes its expected reward over the whole policy
simplex, and hence over the source KL ball. -/
theorem theorem9_pure_last_reward_maximizes_of_adjacent_order {m : ℕ} (hm : 2 ≤ m)
    (reward : Fin m → ℝ)
    (horder : ∀ edge : Fin (m - 1),
      reward (theorem9EdgeLower edge) < reward (theorem9Succ edge))
    (policy : PMF (Fin m)) :
    pmfExp policy reward ≤ pmfExp (PMF.pure (⟨m - 1, by omega⟩ : Fin m)) reward := by
  rw [pmfExp_pure]
  exact pmfExp_le_of_forall_le policy reward (reward ⟨m - 1, by omega⟩)
    (theorem9_reward_le_last_of_adjacent_order hm reward horder)

/-- The population welfare score on a finite Appendix-G prefix. -/
noncomputable def theorem9PrefixWelfare (beta : ℝ) (m : ℕ) : Fin m → ℝ :=
  fun alternative =>
    AppliedModelingLib.Alignment.Welfare.populationAverageUtility lemma15Population
      (theorem9PrefixProfile beta m) alternative

/-- The finite-prefix welfare score is the source's Lemma-15 average utility
at the corresponding natural-number index. -/
theorem theorem9_prefixWelfare_eq_source (beta : ℝ) (m : ℕ)
    (alternative : Fin m) :
    theorem9PrefixWelfare beta m alternative =
      lemma15AverageUtility beta alternative.val := by
  change AppliedModelingLib.Alignment.Welfare.populationAverageUtility lemma15Population
      (theorem9PrefixProfile beta m) alternative = _
  simpa [theorem9PrefixProfile, lemma15Profile] using
    (lemma15_population_average_eq beta alternative.val)

/-- The initial alternative in every nonempty prefix has source welfare
exactly one third. -/
theorem theorem9_prefixWelfare_first (beta : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    theorem9PrefixWelfare beta m ⟨0, by omega⟩ = (1 : ℝ) / 3 := by
  rw [theorem9_prefixWelfare_eq_source]
  exact lemma15_average_zero beta

/-- Every final prefix alternative has strictly positive source welfare. -/
theorem theorem9_prefixWelfare_last_pos {beta : ℝ} (hbeta : 0 < beta)
    {m : ℕ} (hm : 1 ≤ m) :
    0 < theorem9PrefixWelfare beta m ⟨m - 1, by omega⟩ := by
  rw [theorem9_prefixWelfare_eq_source]
  exact lemma15_average_pos hbeta _

/-- Lemma 15's monotone welfare descent makes the first alternative welfare
maximal on each finite prefix. -/
theorem theorem9_prefixWelfare_le_first {beta : ℝ} (hbeta : 0 < beta)
    {m : ℕ} (hm : 1 ≤ m) (alternative : Fin m) :
    theorem9PrefixWelfare beta m alternative ≤ theorem9PrefixWelfare beta m ⟨0, by omega⟩ := by
  rw [theorem9_prefixWelfare_eq_source, theorem9_prefixWelfare_eq_source]
  apply antitone_nat_of_succ_le
      (fun index => (lemma15_average_succ_lt hbeta index).le)
    (Nat.zero_le alternative.val)

/-- The pure first alternative maximizes welfare over every policy in a finite
Appendix-G prefix. -/
theorem theorem9_pure_first_welfare_maximizes {beta : ℝ} (hbeta : 0 < beta)
    {m : ℕ} (hm : 1 ≤ m) (policy : PMF (Fin m)) :
    pmfExp policy (theorem9PrefixWelfare beta m) ≤
      pmfExp (PMF.pure (⟨0, by omega⟩ : Fin m)) (theorem9PrefixWelfare beta m) := by
  rw [pmfExp_pure]
  exact pmfExp_le_of_forall_le policy (theorem9PrefixWelfare beta m)
    (theorem9PrefixWelfare beta m ⟨0, by omega⟩)
    (theorem9_prefixWelfare_le_first hbeta hm)

/-- The two pure policies selected by the source have exactly the displayed
finite-prefix welfare ratio. -/
theorem theorem9_pure_prefix_distortion_eq {beta : ℝ} (hbeta : 0 < beta)
    {m : ℕ} (hm : 1 ≤ m) :
    pmfExp (PMF.pure (⟨0, by omega⟩ : Fin m)) (theorem9PrefixWelfare beta m) /
        pmfExp (PMF.pure (⟨m - 1, by omega⟩ : Fin m))
          (theorem9PrefixWelfare beta m) =
      ((1 : ℝ) / 3) / lemma15AverageUtility beta (m - 1) := by
  rw [pmfExp_pure, pmfExp_pure, theorem9_prefixWelfare_eq_source,
    theorem9_prefixWelfare_eq_source, lemma15_average_zero]

/-- The complete finite-prefix policy endpoint in Appendix G.  The source's
uniform reference and radius `log m` make both pure policies feasible.  The
population MLE strictly orders the fitted rewards, so pure `a_m` is a
constrained reward maximizer while pure `a_1` is welfare-maximizing; their
welfare ratio is the source's displayed quantity. -/
theorem theorem9_exists_finitePrefix_RLHF_endpoint {beta : ℝ} (hbeta : 0 < beta)
    {m : ℕ} (hm : 3 ≤ m) :
    ∃ epsilon : NNReal, ∃ reward : Fin m → ℝ,
      ∃ rewardPolicy welfarePolicy : PMF (Fin m),
        0 < epsilon ∧ epsilon < 1 ∧
        (∀ candidate : Fin m → ℝ,
          correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
              (theorem9ComparisonSampling m hm epsilon) candidate ≤
            correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
              (theorem9ComparisonSampling m hm epsilon) reward) ∧
        (∀ edge : Fin (m - 1),
          reward (theorem9EdgeLower edge) < reward (theorem9Succ edge)) ∧
        finiteKLDivergence rewardPolicy (theorem9UniformReference m (by omega)) ≤
          Real.log (m : ℝ) ∧
        (∀ other : PMF (Fin m),
          finiteKLDivergence other (theorem9UniformReference m (by omega)) ≤
              Real.log (m : ℝ) →
            pmfExp other reward ≤ pmfExp rewardPolicy reward) ∧
        finiteKLDivergence welfarePolicy (theorem9UniformReference m (by omega)) ≤
          Real.log (m : ℝ) ∧
        (∀ other : PMF (Fin m),
          pmfExp other (theorem9PrefixWelfare beta m) ≤
            pmfExp welfarePolicy (theorem9PrefixWelfare beta m)) ∧
        0 < pmfExp rewardPolicy (theorem9PrefixWelfare beta m) ∧
        pmfExp welfarePolicy (theorem9PrefixWelfare beta m) /
            pmfExp rewardPolicy (theorem9PrefixWelfare beta m) =
          ((1 : ℝ) / 3) / lemma15AverageUtility beta (m - 1) := by
  obtain ⟨epsilon, hepsilon_pos, hepsilon_lt, reward, hmle, horder⟩ :=
    theorem9_exists_ordered_populationMLE hbeta hm
  let first : Fin m := ⟨0, by omega⟩
  let last : Fin m := ⟨m - 1, by omega⟩
  refine ⟨epsilon, reward, PMF.pure last, PMF.pure first, hepsilon_pos,
    hepsilon_lt, hmle, horder, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact theorem9_every_policy_uniformKL_feasible (by omega) (PMF.pure last)
  · intro other _
    exact theorem9_pure_last_reward_maximizes_of_adjacent_order (by omega) reward horder other
  · exact theorem9_every_policy_uniformKL_feasible (by omega) (PMF.pure first)
  · intro other
    exact theorem9_pure_first_welfare_maximizes hbeta (by omega) other
  · rw [pmfExp_pure]
    dsimp [last]
    exact theorem9_prefixWelfare_last_pos hbeta (by omega)
  · simpa [first, last] using theorem9_pure_prefix_distortion_eq hbeta (m := m) (by omega)

/-- Lemma 15's strictly positive welfare sequence tends to zero, so the
finite-prefix ratio in Appendix G tends to positive infinity. -/
theorem theorem9_prefix_distortion_tendsto_atTop {beta : ℝ} (hbeta : 0 < beta) :
    Filter.Tendsto (fun m : ℕ =>
      ((1 : ℝ) / 3) / lemma15AverageUtility beta m) Filter.atTop Filter.atTop := by
  have hpositive : ∀ᶠ m : ℕ in Filter.atTop,
      lemma15AverageUtility beta m ∈ Set.Ioi (0 : ℝ) :=
    Filter.Eventually.of_forall fun m => lemma15_average_pos hbeta m
  have hwithin : Filter.Tendsto (lemma15AverageUtility beta) Filter.atTop
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (lemma15_average_tendsto_zero hbeta) hpositive
  have hinverse : Filter.Tendsto (fun m : ℕ =>
      (lemma15AverageUtility beta m)⁻¹) Filter.atTop Filter.atTop :=
    hwithin.inv_tendsto_nhdsGT_zero
  simpa [div_eq_mul_inv] using
    hinverse.const_mul_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 3)

/-- The finite Appendix-G constructions have unbounded RLHF welfare
distortion: for every proposed finite bound, a sufficiently long prefix has
the source correlated comparison sampler and an attained constrained policy
pair whose welfare ratio exceeds that bound. -/
theorem theorem9_unbounded_finitePrefix_RLHF_distortion {beta : ℝ} (hbeta : 0 < beta)
    (bound : ℝ) :
    ∃ (m : ℕ) (hm : 3 ≤ m),
      ∃ epsilon : NNReal, ∃ reward : Fin m → ℝ,
        ∃ rewardPolicy welfarePolicy : PMF (Fin m),
          0 < epsilon ∧ epsilon < 1 ∧
          (∀ candidate : Fin m → ℝ,
            correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
                (theorem9ComparisonSampling m hm epsilon) candidate ≤
              correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
                (theorem9ComparisonSampling m hm epsilon) reward) ∧
          (∀ edge : Fin (m - 1),
            reward (theorem9EdgeLower edge) < reward (theorem9Succ edge)) ∧
          finiteKLDivergence rewardPolicy (theorem9UniformReference m (by omega)) ≤
            Real.log (m : ℝ) ∧
          (∀ other : PMF (Fin m),
            finiteKLDivergence other (theorem9UniformReference m (by omega)) ≤
                Real.log (m : ℝ) →
              pmfExp other reward ≤ pmfExp rewardPolicy reward) ∧
          finiteKLDivergence welfarePolicy (theorem9UniformReference m (by omega)) ≤
            Real.log (m : ℝ) ∧
          (∀ other : PMF (Fin m),
            pmfExp other (theorem9PrefixWelfare beta m) ≤
              pmfExp welfarePolicy (theorem9PrefixWelfare beta m)) ∧
          0 < pmfExp rewardPolicy (theorem9PrefixWelfare beta m) ∧
          bound < pmfExp welfarePolicy (theorem9PrefixWelfare beta m) /
            pmfExp rewardPolicy (theorem9PrefixWelfare beta m) := by
  obtain ⟨n, hbound, hn⟩ :=
    ((theorem9_prefix_distortion_tendsto_atTop hbeta).eventually_gt_atTop bound).and
      (Filter.eventually_ge_atTop 2) |>.exists
  obtain ⟨epsilon, reward, rewardPolicy, welfarePolicy, hepsilon_pos,
    hepsilon_lt, hmle, horder, hreward_feasible, hreward_max,
    hwelfare_feasible, hwelfare_max, hreward_welfare_pos, hratio⟩ :=
      theorem9_exists_finitePrefix_RLHF_endpoint hbeta (m := n + 1) (by omega)
  refine ⟨n + 1, (by omega), epsilon, reward, rewardPolicy, welfarePolicy, hepsilon_pos,
    hepsilon_lt, hmle, horder, hreward_feasible, hreward_max,
    hwelfare_feasible, hwelfare_max, hreward_welfare_pos, ?_⟩
  rw [hratio]
  simpa using hbound

/--
The source-facing form of Theorem 9.  The finite alternative set, population
utility model, correlated comparison distribution, reference policy, KL
budget, fitted reward, and two optimizing policies are existential source
objects.  The Appendix-G construction above supplies those witnesses; none of
its path-specific helper definitions occur in the theorem statement.
-/
theorem theorem9_unbounded_RLHF_distortion {beta : ℝ} (hbeta : 0 < beta)
    (bound : ℝ) :
    ∃ (m : ℕ) (hm : 3 ≤ m),
      ∃ (population : PMF (Fin 3))
        (utility : AppliedModelingLib.Alignment.Welfare.FiniteUtilityProfile (Fin 3) (Fin m))
        (comparisonSampling : CorrelatedPairSampling (Fin m))
        (reference : PMF (Fin m)) (klBudget : ℝ)
        (reward : Fin m → ℝ) (rewardPolicy welfarePolicy : PMF (Fin m)),
          AppliedModelingLib.Alignment.Welfare.UnitIntervalUtilityProfile utility ∧
          PMFFullSupport reference ∧
          comparisonSampling.IsSymmetric ∧
          comparisonSampling.HasZeroDiagonal ∧
          comparisonSampling.HasFullOffDiagonalSupport ∧
          0 ≤ klBudget ∧
          (∀ candidate : Fin m → ℝ,
            correlatedOneComparisonExpectedRawLogLikelihood comparisonSampling
                (AppliedModelingLib.Alignment.Welfare.populationBradleyTerryPreference
                  population utility beta) candidate ≤
              correlatedOneComparisonExpectedRawLogLikelihood comparisonSampling
                (AppliedModelingLib.Alignment.Welfare.populationBradleyTerryPreference
                  population utility beta) reward) ∧
          finiteKLDivergence rewardPolicy reference ≤ klBudget ∧
          (∀ other : PMF (Fin m),
            finiteKLDivergence other reference ≤ klBudget →
              pmfExp other reward ≤ pmfExp rewardPolicy reward) ∧
          finiteKLDivergence welfarePolicy reference ≤ klBudget ∧
          (∀ other : PMF (Fin m),
            finiteKLDivergence other reference ≤ klBudget →
              AppliedModelingLib.Alignment.Welfare.policyAverageUtility population utility other ≤
                AppliedModelingLib.Alignment.Welfare.policyAverageUtility
                  population utility welfarePolicy) ∧
          0 < AppliedModelingLib.Alignment.Welfare.policyAverageUtility
            population utility rewardPolicy ∧
          bound <
            AppliedModelingLib.Alignment.Welfare.policyAverageUtility
                population utility welfarePolicy /
              AppliedModelingLib.Alignment.Welfare.policyAverageUtility
                population utility rewardPolicy := by
  obtain ⟨m, hm, epsilon, reward, rewardPolicy, welfarePolicy, hepsilon_pos,
    hepsilon_lt, hmle, _horder, hreward_feasible, hreward_max,
    hwelfare_feasible, hwelfare_max, hreward_welfare_pos, hratio⟩ :=
      theorem9_unbounded_finitePrefix_RLHF_distortion hbeta bound
  refine ⟨m, hm, lemma15Population, theorem9PrefixProfile beta m,
    theorem9ComparisonSampling m hm epsilon,
    theorem9UniformReference m (by omega), Real.log (m : ℝ), reward,
    rewardPolicy, welfarePolicy, theorem9_prefixProfile_unitInterval hbeta m,
    theorem9UniformReference_fullSupport m (by omega),
    theorem9ComparisonSampling_isSymmetric hm epsilon,
    theorem9ComparisonSampling_zeroDiagonal hm epsilon,
    theorem9ComparisonSampling_fullOffDiagonalSupport hm epsilon hepsilon_pos hepsilon_lt,
    Real.log_nonneg ?_, ?_,
    hreward_feasible, hreward_max,
    hwelfare_feasible, ?_, ?_, ?_⟩
  · exact_mod_cast (show 1 ≤ m by omega)
  · simpa [theorem9RawPopulationLogLikelihood] using
      (theorem9_rawPopulation_globalMax_iff_correlatedBradleyTerryFit_globalMax
        beta m hm epsilon reward).2 hmle
  · intro other _
    simpa [AppliedModelingLib.Alignment.Welfare.policyAverageUtility,
      theorem9PrefixWelfare] using hwelfare_max other
  · simpa [AppliedModelingLib.Alignment.Welfare.policyAverageUtility,
      theorem9PrefixWelfare] using hreward_welfare_pos
  · simpa [AppliedModelingLib.Alignment.Welfare.policyAverageUtility,
      theorem9PrefixWelfare] using hratio

/-- The literal bad event for the sampled Appendix-G construction: an
attained fixed-reference finite logistic MLE fails at one adjacent reward
comparison. -/
def theorem9FiniteMLEBadOrderEvent (beta : ℝ) (m : ℕ) (hm : 3 ≤ m)
    (epsilon : NNReal) {horizon : ℕ}
    (sample : Fin horizon → BinaryPairwiseReport (Fin m)) : Prop :=
  ∃ score : ScoreVector (Fin m),
    isPairwiseMLE (ofBinaryReports sample) sigmoidCDFLikePairwiseLink
      (⟨0, by omega⟩ : Fin m) score ∧
      ∃ edge : Fin (m - 1), score (theorem9Succ edge) ≤ score (theorem9EdgeLower edge)

/-- The finite iid probability of an attained MLE with an adjacent-order
failure under the literal correlated source report law. -/
noncomputable def theorem9FiniteMLEBadOrderProbability (beta : ℝ) (m : ℕ)
    (hm : 3 ≤ m) (epsilon : NNReal) (horizon : ℕ) : ℝ := by
  classical
  let reportLaw : PMF (BinaryPairwiseReport (Fin m)) :=
    theorem9OneComparisonReportLaw beta m hm epsilon
  letI : DecidablePred
      (theorem9FiniteMLEBadOrderEvent beta m hm epsilon (horizon := horizon)) :=
    Classical.decPred _
  exact pmfProb (pmfProduct (Fin horizon) (BinaryPairwiseReport (Fin m)) reportLaw)
    (theorem9FiniteMLEBadOrderEvent beta m hm epsilon)

/-- Unfolding form of the literal Appendix-G finite-MLE bad-order
probability. -/
theorem theorem9FiniteMLEBadOrderProbability_eq (beta : ℝ) (m : ℕ)
    (hm : 3 ≤ m) (epsilon : NNReal) (horizon : ℕ) :
    theorem9FiniteMLEBadOrderProbability beta m hm epsilon horizon = by
      classical
      exact pmfProb
        (pmfProduct (Fin horizon) (BinaryPairwiseReport (Fin m))
          (theorem9OneComparisonReportLaw beta m hm epsilon))
        (theorem9FiniteMLEBadOrderEvent beta m hm epsilon) := by
  rfl

set_option maxHeartbeats 800000 in
-- The compact score-cube and uniform-argmax stability construction expands
-- several finite nested sums and needs a larger elaboration budget.
/-- For any Appendix-G prefix whose correlated population MLEs are all
strictly adjacent-ordered, the probability that an attained finite iid
logistic MLE violates an adjacent order converges to zero.  This is a literal
finite-alphabet uniform-law proof, not an assumed MLE consistency theorem. -/
theorem theorem9_iidFiniteMLEBadOrderProbability_tendsto_zero_of_populationOrder
    {beta : ℝ} (hbeta : 0 < beta) {m : ℕ} (hm : 3 ≤ m)
    (epsilon : NNReal) (hepsilon_pos : 0 < epsilon) (hepsilon_lt : epsilon < 1)
    (hordered : ∀ reward : Fin m → ℝ,
      (∀ candidate : Fin m → ℝ,
        correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
          (theorem9ComparisonSampling m hm epsilon) candidate ≤
          correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
            (theorem9ComparisonSampling m hm epsilon) reward) →
        ∀ edge : Fin (m - 1),
          reward (theorem9EdgeLower edge) < reward (theorem9Succ edge)) :
    Filter.Tendsto (theorem9FiniteMLEBadOrderProbability beta m hm epsilon)
      Filter.atTop (𝓝 0) := by
  classical
  let reportLaw : PMF (BinaryPairwiseReport (Fin m)) :=
    theorem9OneComparisonReportLaw beta m hm epsilon
  let raw : ScoreVector (Fin m) → ℝ :=
    theorem9RawPopulationLogLikelihood beta m hm epsilon
  let reference : Fin m := ⟨0, by omega⟩
  let next : Fin m := ⟨1, by omega⟩
  have hreference_next : reference ≠ next := by
    intro h
    have hval := congrArg Fin.val h
    simp [reference, next] at hval
  letI : Nonempty (BinaryPairwiseReport (Fin m)) := ⟨((reference, reference), true)⟩
  obtain ⟨threshold, hthreshold_pos, hthreshold_lt_one, hthreshold_mass⟩ :=
    theorem9_exists_directTrueFrequencyThreshold hm epsilon hepsilon_pos hepsilon_lt
  obtain ⟨bound, hbound_pos, htail_low, htail_high⟩ :=
    CDFLikePairwiseLink.exists_pos_tailBand sigmoidCDFLikePairwiseLink threshold
      hthreshold_pos hthreshold_lt_one
  obtain ⟨base, hbase_population⟩ :=
    theorem9_exists_populationMLE hm epsilon hepsilon_pos hepsilon_lt
  let cubeBound : ℝ :=
    max ((Fintype.card (Fin m) : ℝ) * bound) (scoreSupNorm reference base)
  let cube : Set (ScoreVector (Fin m)) :=
    Set.univ.pi (fun _ : Fin m => Set.Icc (-cubeBound) cubeBound)
  have hcube_compact : IsCompact cube := by
    dsimp [cube]
    exact isCompact_univ_pi fun _ : Fin m => isCompact_Icc
  have hbase_raw : ∀ candidate : ScoreVector (Fin m), raw candidate ≤ raw base := by
    dsimp [raw]
    exact
      (theorem9_rawPopulation_globalMax_iff_correlatedBradleyTerryFit_globalMax
        beta m hm epsilon base).mpr hbase_population
  have hbase_cube : base ∈ cube := by
    change ∀ alternative : Fin m, alternative ∈ Set.univ →
      -cubeBound ≤ base alternative ∧ base alternative ≤ cubeBound
    intro alternative _
    apply abs_le.mp
    exact (abs_score_le_scoreSupNorm reference alternative base).trans (le_max_right _ _)
  have hscore_cube : ∀ {horizon : ℕ}
      (horizon_pos : 0 < horizon)
      (sample : Fin horizon → BinaryPairwiseReport (Fin m))
      (hgood : ¬ ∃ atom,
        atom ∈ directedTrueBinaryReports (Fin m) ∧
        (Probability.empiricalCount sample atom : ℝ) ≤ (horizon : ℝ) * threshold)
      (score : ScoreVector (Fin m)),
      isPairwiseMLE (ofBinaryReports sample) sigmoidCDFLikePairwiseLink reference score →
        score ∈ cube := by
    intro horizon horizon_pos sample hgood score hmle
    have hscore_bound : scoreSupNorm reference score ≤
        (Fintype.card (Fin m) : ℝ) * bound := by
      apply scoreSupNorm_le_card_mul_bound_of_directTrueLowerFrequency
        sample sigmoidCDFLikePairwiseLink continuous_sigmoidCDFLikePairwiseLink
        strictMono_sigmoidCDFLikePairwiseLink reference score hmle threshold bound
        horizon_pos hthreshold_pos
      · intro winner loser hneq
        apply le_of_not_gt
        intro hlt
        apply hgood
        exact ⟨directTrueBinaryReport winner loser,
          directTrueBinaryReport_mem_directedTrueBinaryReports winner loser hneq, hlt.le⟩
      · exact hbound_pos
      · exact htail_low
      · exact htail_high
    change ∀ alternative : Fin m, alternative ∈ Set.univ →
      -cubeBound ≤ score alternative ∧ score alternative ≤ cubeBound
    intro alternative _
    apply abs_le.mp
    exact (abs_score_le_scoreSupNorm reference alternative score).trans
      (hscore_bound.trans (le_max_left _ _))
  let bad : Set (ScoreVector (Fin m)) :=
    {score | ∃ edge : Fin (m - 1),
      score (theorem9Succ edge) ≤ score (theorem9EdgeLower edge)}
  have hbad_closed : IsClosed bad := by
    dsimp [bad]
    simpa [Set.setOf_exists] using
      (isClosed_iUnion_of_finite (fun edge : Fin (m - 1) =>
        isClosed_le (continuous_apply (theorem9Succ edge))
          (continuous_apply (theorem9EdgeLower edge))))
  let compactBad : Set (ScoreVector (Fin m)) := cube ∩ bad
  have hcompactBad_compact : IsCompact compactBad := by
    dsimp [compactBad]
    exact hcube_compact.inter_right hbad_closed
  have hcompactBad_subset : compactBad ⊆ cube := by
    intro score hscore
    exact hscore.1
  have hraw_continuous : Continuous raw := by
    dsimp [raw]
    exact continuous_theorem9RawPopulationLogLikelihood beta m hm epsilon
  have hcompactBad_strict : ∀ score, score ∈ compactBad → raw score < raw base := by
    intro score hscore
    by_contra hnot
    have hbase_le : raw base ≤ raw score := le_of_not_gt hnot
    have hscore_raw_max : ∀ candidate : ScoreVector (Fin m), raw candidate ≤ raw score := by
      intro candidate
      exact (hbase_raw candidate).trans hbase_le
    have hscore_population_max : ∀ candidate : Fin m → ℝ,
        correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
          (theorem9ComparisonSampling m hm epsilon) candidate ≤
          correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
            (theorem9ComparisonSampling m hm epsilon) score := by
      apply
        (theorem9_rawPopulation_globalMax_iff_correlatedBradleyTerryFit_globalMax
          beta m hm epsilon score).mp
      simpa only [raw] using hscore_raw_max
    rcases hscore.2 with ⟨edge, hedge⟩
    have horder := hordered score hscore_population_max edge
    exact (not_lt_of_ge hedge) horder
  obtain ⟨tolerance, htolerance_pos, hstable⟩ :=
    AppliedModelingLib.Optimization.exists_pos_uniformArgmaxTolerance_not_mem_of_compact_of_strictSeparation
      hcompactBad_compact hcompactBad_subset hraw_continuous.continuousOn
      ⟨hbase_cube, fun candidate _ => hbase_raw candidate⟩ hcompactBad_strict
  let reportScore : ScoreVector (Fin m) → BinaryPairwiseReport (Fin m) → ℝ :=
    fun score report => binaryReportLogLikelihoodTerm Real.sigmoid score report
  have hreportScore_continuous : ∀ report,
      Continuous (fun score : ScoreVector (Fin m) => reportScore score report) := by
    intro report
    exact continuous_binaryReportLogLikelihoodTerm_sigmoid report
  have huniform : Filter.Tendsto
      (Probability.finiteIidUniformScoreDeviationFailure reportLaw reportScore cube tolerance)
      Filter.atTop (𝓝 0) := by
    apply Probability.finiteIidUniformScoreDeviationFailure_tendsto_zero
      reportLaw reportScore cube hcube_compact hreportScore_continuous tolerance htolerance_pos
  have hdirect : Filter.Tendsto
      (Probability.finiteIidFiniteSetLowerFrequencyFailure reportLaw
        (directedTrueBinaryReports (Fin m)) threshold)
      Filter.atTop (𝓝 0) := by
    apply Probability.finiteIidFiniteSetLowerFrequencyFailure_tendsto_zero
    intro atom hatom
    rcases Finset.mem_image.mp hatom with ⟨pair, hpair, rfl⟩
    exact hthreshold_mass pair.1 pair.2 (Finset.mem_filter.mp hpair).2
  have hprob : ∀ horizon,
      theorem9FiniteMLEBadOrderProbability beta m hm epsilon horizon ≤
        Probability.finiteIidFiniteSetLowerFrequencyFailure reportLaw
          (directedTrueBinaryReports (Fin m)) threshold horizon +
          Probability.finiteIidUniformScoreDeviationFailure reportLaw reportScore cube tolerance
            horizon := by
    intro horizon
    let product : PMF (Fin horizon → BinaryPairwiseReport (Fin m)) :=
      pmfProduct (Fin horizon) (BinaryPairwiseReport (Fin m)) reportLaw
    let directBad : (Fin horizon → BinaryPairwiseReport (Fin m)) → Prop :=
      Probability.finiteIidFiniteSetLowerFrequencyEvent
        (directedTrueBinaryReports (Fin m)) threshold
    let uniformBad : (Fin horizon → BinaryPairwiseReport (Fin m)) → Prop :=
      Probability.finiteIidUniformScoreDeviationEvent reportLaw reportScore cube tolerance
    let mleBad : (Fin horizon → BinaryPairwiseReport (Fin m)) → Prop :=
      theorem9FiniteMLEBadOrderEvent beta m hm epsilon
    letI : DecidablePred uniformBad := Classical.decPred _
    letI : DecidablePred mleBad := Classical.decPred _
    have hsubset : ∀ sample, mleBad sample → directBad sample ∨ uniformBad sample := by
      intro sample hmleBad
      unfold mleBad theorem9FiniteMLEBadOrderEvent at hmleBad
      rcases hmleBad with ⟨score, hmle, horder⟩
      by_cases horizon_zero : horizon = 0
      · left
        subst horizon
        unfold directBad Probability.finiteIidFiniteSetLowerFrequencyEvent
        refine ⟨directTrueBinaryReport reference next,
          directTrueBinaryReport_mem_directedTrueBinaryReports reference next hreference_next, ?_⟩
        simp [Probability.empiricalCount]
      by_cases hdirectBad : directBad sample
      · exact Or.inl hdirectBad
      · right
        by_contra huniformBad
        unfold uniformBad Probability.finiteIidUniformScoreDeviationEvent at huniformBad
        have horizon_pos : 0 < horizon := Nat.pos_of_ne_zero horizon_zero
        have horizon_real_pos : (0 : ℝ) < horizon := by exact_mod_cast horizon_pos
        have hscore_mem : score ∈ cube := by
          have hgood : ¬ ∃ atom,
              atom ∈ directedTrueBinaryReports (Fin m) ∧
              (Probability.empiricalCount sample atom : ℝ) ≤ (horizon : ℝ) * threshold := by
            unfold directBad Probability.finiteIidFiniteSetLowerFrequencyEvent at hdirectBad
            exact hdirectBad
          exact hscore_cube horizon_pos sample hgood score (by
            simpa [reference] using hmle)
        let empirical : ScoreVector (Fin m) → ℝ := fun candidate =>
          pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid candidate / (horizon : ℝ)
        have hempirical_uniform : ∀ candidate, candidate ∈ cube →
            |empirical candidate - raw candidate| ≤ tolerance := by
          intro candidate hcandidate
          have hraw_bound :
              |Probability.finiteIidScoreSum (reportScore candidate) sample -
                  (horizon : ℝ) * pmfExp reportLaw (reportScore candidate)| ≤
                (horizon : ℝ) * tolerance := by
              apply le_of_not_gt
              intro hgt
              apply huniformBad
              exact ⟨candidate, hcandidate, hgt⟩
          have hraw_bound' :
              |pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid candidate -
                  (horizon : ℝ) * raw candidate| ≤ (horizon : ℝ) * tolerance := by
              dsimp [reportScore, raw] at hraw_bound ⊢
              unfold Probability.finiteIidScoreSum at hraw_bound
              rw [← pairwiseLogLikelihood_ofBinaryReports_eq_sum
                sample Real.sigmoid candidate] at hraw_bound
              exact hraw_bound
          have hempirical_eq : empirical candidate - raw candidate =
              (pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid candidate -
                (horizon : ℝ) * raw candidate) / (horizon : ℝ) := by
            dsimp [empirical]
            field_simp
          rw [hempirical_eq, abs_div, abs_of_pos horizon_real_pos]
          exact (div_le_iff₀ horizon_real_pos).mpr (by simpa [mul_comm] using hraw_bound')
        have hempirical_max : IsMaxOn empirical cube score := by
          intro candidate _
          dsimp [empirical]
          apply (div_le_div_iff₀ horizon_real_pos horizon_real_pos).mpr
          exact mul_le_mul_of_nonneg_right
            (isPairwiseMLE_global_max (ofBinaryReports sample)
              sigmoidCDFLikePairwiseLink reference score (by simpa [reference] using hmle)
                candidate)
            horizon_real_pos.le
        have hnot_bad := hstable empirical score hempirical_uniform hscore_mem hempirical_max
        exact hnot_bad ⟨hscore_mem, horder⟩
    have hprob_or : pmfProb product mleBad ≤
        pmfProb product directBad + pmfProb product uniformBad := by
      calc
        pmfProb product mleBad ≤ pmfProb product (fun sample => directBad sample ∨ uniformBad sample) :=
          pmfProb_le_of_imp product mleBad (fun sample => directBad sample ∨ uniformBad sample) hsubset
        _ ≤ pmfProb product directBad + pmfProb product uniformBad := by
          rw [pmfProb_or_eq_add_sub_inter]
          exact sub_le_self _
            (pmfProb_nonneg product (fun sample => directBad sample ∧ uniformBad sample))
    have hmle_eq : theorem9FiniteMLEBadOrderProbability beta m hm epsilon horizon =
        pmfProb product mleBad := by
      simpa only [product, mleBad, reportLaw] using
        (theorem9FiniteMLEBadOrderProbability_eq beta m hm epsilon horizon)
    have hdirect_eq : Probability.finiteIidFiniteSetLowerFrequencyFailure reportLaw
        (directedTrueBinaryReports (Fin m)) threshold horizon = pmfProb product directBad := by
      unfold Probability.finiteIidFiniteSetLowerFrequencyFailure
      change pmfProb product
        (Probability.finiteIidFiniteSetLowerFrequencyEvent
          (directedTrueBinaryReports (Fin m)) threshold) = pmfProb product directBad
      apply pmfProb_congr
      intro sample
      rfl
    have huniform_eq : Probability.finiteIidUniformScoreDeviationFailure
        reportLaw reportScore cube tolerance horizon = pmfProb product uniformBad := by
      simpa only [product, uniformBad] using
        (Probability.finiteIidUniformScoreDeviationFailure_eq
          reportLaw reportScore cube tolerance horizon)
    calc
      theorem9FiniteMLEBadOrderProbability beta m hm epsilon horizon = pmfProb product mleBad :=
        hmle_eq
      _ ≤ pmfProb product directBad + pmfProb product uniformBad := hprob_or
      _ = Probability.finiteIidFiniteSetLowerFrequencyFailure reportLaw
          (directedTrueBinaryReports (Fin m)) threshold horizon +
          Probability.finiteIidUniformScoreDeviationFailure reportLaw reportScore cube tolerance
            horizon := by
          rw [← hdirect_eq, ← huniform_eq]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 0))
    (by simpa using hdirect.add huniform) ?_ hprob
  intro horizon
  unfold theorem9FiniteMLEBadOrderProbability
  exact pmfProb_nonneg _ _

/-- Appendix G's selected sufficiently small positive off-path mass has the
source's sampled-MLE conclusion: every adjacent reward order holds with
probability tending to one for literal iid comparison reports. -/
theorem theorem9_exists_iidFiniteMLEAdjacentOrder {beta : ℝ} (hbeta : 0 < beta)
    {m : ℕ} (hm : 3 ≤ m) :
    ∃ epsilon : NNReal, 0 < epsilon ∧ epsilon < 1 ∧
      Filter.Tendsto (theorem9FiniteMLEBadOrderProbability beta m hm epsilon)
        Filter.atTop (𝓝 0) := by
  obtain ⟨epsilon, hepsilon_pos, hepsilon_lt, hordered⟩ :=
    theorem9_exists_epsilon_all_adjacent_order hbeta hm
  exact ⟨epsilon, hepsilon_pos, hepsilon_lt,
    theorem9_iidFiniteMLEBadOrderProbability_tendsto_zero_of_populationOrder
      hbeta hm epsilon hepsilon_pos hepsilon_lt hordered⟩

set_option maxHeartbeats 800000 in
-- The pathwise proof repeats the compact stability bridge after constructing
-- canonical iid strong-law events, which expands the same finite score sums.
/-- The pathwise form of the finite-prefix bridge in Appendix G.  On the
canonical infinite iid product of the paper's literal correlated report law,
every sufficiently long prefix has no attained finite logistic MLE with an
adjacent reward-order reversal. -/
theorem theorem9_ae_eventually_noFiniteMLEBadOrder_of_populationOrder
    {beta : ℝ} (hbeta : 0 < beta) {m : ℕ} (hm : 3 ≤ m)
    (epsilon : NNReal) (hepsilon_pos : 0 < epsilon) (hepsilon_lt : epsilon < 1)
    (hordered : ∀ reward : Fin m → ℝ,
      (∀ candidate : Fin m → ℝ,
        correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
          (theorem9ComparisonSampling m hm epsilon) candidate ≤
          correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
            (theorem9ComparisonSampling m hm epsilon) reward) →
        ∀ edge : Fin (m - 1),
          reward (theorem9EdgeLower edge) < reward (theorem9Succ edge)) :
    letI : MeasurableSpace (BinaryPairwiseReport (Fin m)) := ⊤
    ∀ᵐ path ∂AppliedModelingLib.finitePMFIidPathMeasure
        (theorem9OneComparisonReportLaw beta m hm epsilon),
      ∀ᶠ horizon : ℕ in Filter.atTop,
        ¬ theorem9FiniteMLEBadOrderEvent beta m hm epsilon
          (AppliedModelingLib.finitePMFIidPathPrefix path horizon) := by
  classical
  letI : MeasurableSpace (BinaryPairwiseReport (Fin m)) := ⊤
  let reportLaw : PMF (BinaryPairwiseReport (Fin m)) :=
    theorem9OneComparisonReportLaw beta m hm epsilon
  let raw : ScoreVector (Fin m) → ℝ :=
    theorem9RawPopulationLogLikelihood beta m hm epsilon
  let reference : Fin m := ⟨0, by omega⟩
  let next : Fin m := ⟨1, by omega⟩
  have hreference_next : reference ≠ next := by
    intro h
    have hval := congrArg Fin.val h
    simp [reference, next] at hval
  letI : Nonempty (BinaryPairwiseReport (Fin m)) := ⟨((reference, reference), true)⟩
  obtain ⟨threshold, hthreshold_pos, hthreshold_lt_one, hthreshold_mass⟩ :=
    theorem9_exists_directTrueFrequencyThreshold hm epsilon hepsilon_pos hepsilon_lt
  obtain ⟨bound, hbound_pos, htail_low, htail_high⟩ :=
    CDFLikePairwiseLink.exists_pos_tailBand sigmoidCDFLikePairwiseLink threshold
      hthreshold_pos hthreshold_lt_one
  obtain ⟨base, hbase_population⟩ :=
    theorem9_exists_populationMLE hm epsilon hepsilon_pos hepsilon_lt
  let cubeBound : ℝ :=
    max ((Fintype.card (Fin m) : ℝ) * bound) (scoreSupNorm reference base)
  let cube : Set (ScoreVector (Fin m)) :=
    Set.univ.pi (fun _ : Fin m => Set.Icc (-cubeBound) cubeBound)
  have hcube_compact : IsCompact cube := by
    dsimp [cube]
    exact isCompact_univ_pi fun _ : Fin m => isCompact_Icc
  have hbase_raw : ∀ candidate : ScoreVector (Fin m), raw candidate ≤ raw base := by
    dsimp [raw]
    exact
      (theorem9_rawPopulation_globalMax_iff_correlatedBradleyTerryFit_globalMax
        beta m hm epsilon base).mpr hbase_population
  have hbase_cube : base ∈ cube := by
    change ∀ alternative : Fin m, alternative ∈ Set.univ →
      -cubeBound ≤ base alternative ∧ base alternative ≤ cubeBound
    intro alternative _
    apply abs_le.mp
    exact (abs_score_le_scoreSupNorm reference alternative base).trans (le_max_right _ _)
  have hscore_cube : ∀ {horizon : ℕ}
      (horizon_pos : 0 < horizon)
      (sample : Fin horizon → BinaryPairwiseReport (Fin m))
      (hgood : ¬ ∃ atom,
        atom ∈ directedTrueBinaryReports (Fin m) ∧
        (Probability.empiricalCount sample atom : ℝ) ≤ (horizon : ℝ) * threshold)
      (score : ScoreVector (Fin m)),
      isPairwiseMLE (ofBinaryReports sample) sigmoidCDFLikePairwiseLink reference score →
        score ∈ cube := by
    intro horizon horizon_pos sample hgood score hmle
    have hscore_bound : scoreSupNorm reference score ≤
        (Fintype.card (Fin m) : ℝ) * bound := by
      apply scoreSupNorm_le_card_mul_bound_of_directTrueLowerFrequency
        sample sigmoidCDFLikePairwiseLink continuous_sigmoidCDFLikePairwiseLink
        strictMono_sigmoidCDFLikePairwiseLink reference score hmle threshold bound
        horizon_pos hthreshold_pos
      · intro winner loser hneq
        apply le_of_not_gt
        intro hlt
        apply hgood
        exact ⟨directTrueBinaryReport winner loser,
          directTrueBinaryReport_mem_directedTrueBinaryReports winner loser hneq, hlt.le⟩
      · exact hbound_pos
      · exact htail_low
      · exact htail_high
    change ∀ alternative : Fin m, alternative ∈ Set.univ →
      -cubeBound ≤ score alternative ∧ score alternative ≤ cubeBound
    intro alternative _
    apply abs_le.mp
    exact (abs_score_le_scoreSupNorm reference alternative score).trans
      (hscore_bound.trans (le_max_left _ _))
  let bad : Set (ScoreVector (Fin m)) :=
    {score | ∃ edge : Fin (m - 1),
      score (theorem9Succ edge) ≤ score (theorem9EdgeLower edge)}
  have hbad_closed : IsClosed bad := by
    dsimp [bad]
    simpa [Set.setOf_exists] using
      (isClosed_iUnion_of_finite (fun edge : Fin (m - 1) =>
        isClosed_le (continuous_apply (theorem9Succ edge))
          (continuous_apply (theorem9EdgeLower edge))))
  let compactBad : Set (ScoreVector (Fin m)) := cube ∩ bad
  have hcompactBad_compact : IsCompact compactBad := by
    dsimp [compactBad]
    exact hcube_compact.inter_right hbad_closed
  have hcompactBad_subset : compactBad ⊆ cube := by
    intro score hscore
    exact hscore.1
  have hraw_continuous : Continuous raw := by
    dsimp [raw]
    exact continuous_theorem9RawPopulationLogLikelihood beta m hm epsilon
  have hcompactBad_strict : ∀ score, score ∈ compactBad → raw score < raw base := by
    intro score hscore
    by_contra hnot
    have hbase_le : raw base ≤ raw score := le_of_not_gt hnot
    have hscore_raw_max : ∀ candidate : ScoreVector (Fin m), raw candidate ≤ raw score := by
      intro candidate
      exact (hbase_raw candidate).trans hbase_le
    have hscore_population_max : ∀ candidate : Fin m → ℝ,
        correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
          (theorem9ComparisonSampling m hm epsilon) candidate ≤
          correlatedBradleyTerryFitObjective (theorem9PrefixPreference beta m)
            (theorem9ComparisonSampling m hm epsilon) score := by
      apply
        (theorem9_rawPopulation_globalMax_iff_correlatedBradleyTerryFit_globalMax
          beta m hm epsilon score).mp
      simpa only [raw] using hscore_raw_max
    rcases hscore.2 with ⟨edge, hedge⟩
    have horder := hordered score hscore_population_max edge
    exact (not_lt_of_ge hedge) horder
  obtain ⟨tolerance, htolerance_pos, hstable⟩ :=
    AppliedModelingLib.Optimization.exists_pos_uniformArgmaxTolerance_not_mem_of_compact_of_strictSeparation
      hcompactBad_compact hcompactBad_subset hraw_continuous.continuousOn
      ⟨hbase_cube, fun candidate _ => hbase_raw candidate⟩ hcompactBad_strict
  let reportScore : ScoreVector (Fin m) → BinaryPairwiseReport (Fin m) → ℝ :=
    fun score report => binaryReportLogLikelihoodTerm Real.sigmoid score report
  have hreportScore_continuous : ∀ report,
      Continuous (fun score : ScoreVector (Fin m) => reportScore score report) := by
    intro report
    exact continuous_binaryReportLogLikelihoodTerm_sigmoid report
  have hdirect :=
    AppliedModelingLib.ae_eventually_finitePMFIidPath_not_finiteIidFiniteSetLowerFrequencyEvent
      reportLaw (directedTrueBinaryReports (Fin m)) threshold (by
        intro atom hatom
        rcases Finset.mem_image.mp hatom with ⟨pair, hpair, rfl⟩
        exact hthreshold_mass pair.1 pair.2 (Finset.mem_filter.mp hpair).2)
  have huniform := AppliedModelingLib.ae_eventually_finitePMFIidPath_uniformScoreDeviation
    reportLaw reportScore cube hcube_compact hreportScore_continuous tolerance htolerance_pos
  filter_upwards [hdirect, huniform] with path pathDirect pathUniform
  filter_upwards [pathDirect, pathUniform, Filter.eventually_ge_atTop 1] with
      horizon hpathDirect hpathUniform hpositive
  intro hbadOrder
  rcases hbadOrder with ⟨score, hmle, horder⟩
  let sample : Fin horizon → BinaryPairwiseReport (Fin m) :=
    AppliedModelingLib.finitePMFIidPathPrefix path horizon
  have hscore_mem : score ∈ cube := by
    have hgood : ¬ ∃ atom,
        atom ∈ directedTrueBinaryReports (Fin m) ∧
      (Probability.empiricalCount sample atom : ℝ) ≤ (horizon : ℝ) * threshold := by
      exact hpathDirect
    exact hscore_cube hpositive sample hgood score (by
      simpa [sample, reference] using hmle)
  have horizon_real_pos : (0 : ℝ) < horizon := by exact_mod_cast hpositive
  let empirical : ScoreVector (Fin m) → ℝ := fun candidate =>
    pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid candidate / (horizon : ℝ)
  have hempirical_uniform : ∀ candidate, candidate ∈ cube →
      |empirical candidate - raw candidate| ≤ tolerance := by
    intro candidate hcandidate
    have hraw_bound :
        |Probability.finiteIidScoreSum (reportScore candidate) sample -
            (horizon : ℝ) * pmfExp reportLaw (reportScore candidate)| ≤
          (horizon : ℝ) * tolerance := by
      simpa [sample] using hpathUniform candidate hcandidate
    have hraw_bound' :
        |pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid candidate -
            (horizon : ℝ) * raw candidate| ≤ (horizon : ℝ) * tolerance := by
      dsimp [reportScore, raw] at hraw_bound ⊢
      unfold Probability.finiteIidScoreSum at hraw_bound
      rw [← pairwiseLogLikelihood_ofBinaryReports_eq_sum sample Real.sigmoid candidate] at hraw_bound
      exact hraw_bound
    have hempirical_eq : empirical candidate - raw candidate =
        (pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid candidate -
          (horizon : ℝ) * raw candidate) / (horizon : ℝ) := by
      dsimp [empirical]
      field_simp
    rw [hempirical_eq, abs_div, abs_of_pos horizon_real_pos]
    exact (div_le_iff₀ horizon_real_pos).mpr (by simpa [mul_comm] using hraw_bound')
  have hempirical_max : IsMaxOn empirical cube score := by
    intro candidate _
    dsimp [empirical]
    apply (div_le_div_iff₀ horizon_real_pos horizon_real_pos).mpr
    exact mul_le_mul_of_nonneg_right
      (isPairwiseMLE_global_max (ofBinaryReports sample)
        sigmoidCDFLikePairwiseLink reference score (by simpa [sample, reference] using hmle)
          candidate)
      horizon_real_pos.le
  have hnot_bad := hstable empirical score hempirical_uniform hscore_mem hempirical_max
  exact hnot_bad ⟨hscore_mem, horder⟩

/-- The selected small off-path mass in Appendix G has the source's
almost-sure sampled-MLE order conclusion on the literal iid correlated-report
experiment. -/
theorem theorem9_exists_ae_eventually_noFiniteMLEBadOrder {beta : ℝ} (hbeta : 0 < beta)
    {m : ℕ} (hm : 3 ≤ m) :
    ∃ epsilon : NNReal, 0 < epsilon ∧ epsilon < 1 ∧
      letI : MeasurableSpace (BinaryPairwiseReport (Fin m)) := ⊤
      ∀ᵐ path ∂AppliedModelingLib.finitePMFIidPathMeasure
          (theorem9OneComparisonReportLaw beta m hm epsilon),
        ∀ᶠ horizon : ℕ in Filter.atTop,
          ¬ theorem9FiniteMLEBadOrderEvent beta m hm epsilon
            (AppliedModelingLib.finitePMFIidPathPrefix path horizon) := by
  obtain ⟨epsilon, hepsilon_pos, hepsilon_lt, hordered⟩ :=
    theorem9_exists_epsilon_all_adjacent_order hbeta hm
  exact ⟨epsilon, hepsilon_pos, hepsilon_lt,
    theorem9_ae_eventually_noFiniteMLEBadOrder_of_populationOrder
      hbeta hm epsilon hepsilon_pos hepsilon_lt hordered⟩

/-- Source-facing unpacking of the Appendix-G strong-law conclusion: almost
every literal iid report path eventually orders every attained finite MLE in
the same strict adjacent order as the population construction. -/
theorem theorem9_exists_ae_eventually_allFiniteMLEAdjacentOrder
    {beta : ℝ} (hbeta : 0 < beta) {m : ℕ} (hm : 3 ≤ m) :
    ∃ epsilon : NNReal, 0 < epsilon ∧ epsilon < 1 ∧
      letI : MeasurableSpace (BinaryPairwiseReport (Fin m)) := ⊤
      ∀ᵐ path ∂AppliedModelingLib.finitePMFIidPathMeasure
          (theorem9OneComparisonReportLaw beta m hm epsilon),
        ∀ᶠ horizon : ℕ in Filter.atTop,
          ∀ score : ScoreVector (Fin m),
            isPairwiseMLE
              (ofBinaryReports (AppliedModelingLib.finitePMFIidPathPrefix path horizon))
              sigmoidCDFLikePairwiseLink (⟨0, by omega⟩ : Fin m) score →
              ∀ edge : Fin (m - 1),
                score (theorem9EdgeLower edge) < score (theorem9Succ edge) := by
  obtain ⟨epsilon, hepsilon_pos, hepsilon_lt, hpath⟩ :=
    theorem9_exists_ae_eventually_noFiniteMLEBadOrder hbeta hm
  refine ⟨epsilon, hepsilon_pos, hepsilon_lt, ?_⟩
  letI : MeasurableSpace (BinaryPairwiseReport (Fin m)) := ⊤
  filter_upwards [hpath] with path hpath
  filter_upwards [hpath] with horizon hbad
  intro score hmle edge
  by_contra hnot
  apply hbad
  exact ⟨score, hmle, edge, le_of_not_gt hnot⟩

/-- Positive empirical frequency of every direct report atom eventually gives
an attained finite logistic MLE on almost every Appendix-G iid path. -/
theorem theorem9_ae_eventually_existsFiniteMLE
    {beta : ℝ} {m : ℕ} (hm : 3 ≤ m)
    (epsilon : NNReal) (hepsilon_pos : 0 < epsilon) (hepsilon_lt : epsilon < 1) :
    letI : MeasurableSpace (BinaryPairwiseReport (Fin m)) := ⊤
    ∀ᵐ path ∂AppliedModelingLib.finitePMFIidPathMeasure
        (theorem9OneComparisonReportLaw beta m hm epsilon),
      ∀ᶠ horizon : ℕ in Filter.atTop,
        ∃ score : ScoreVector (Fin m),
          isPairwiseMLE
            (ofBinaryReports (AppliedModelingLib.finitePMFIidPathPrefix path horizon))
            sigmoidCDFLikePairwiseLink (⟨0, by omega⟩ : Fin m) score := by
  classical
  letI : MeasurableSpace (BinaryPairwiseReport (Fin m)) := ⊤
  let reportLaw : PMF (BinaryPairwiseReport (Fin m)) :=
    theorem9OneComparisonReportLaw beta m hm epsilon
  let reference : Fin m := ⟨0, by omega⟩
  letI : Nonempty (BinaryPairwiseReport (Fin m)) := ⟨((reference, reference), true)⟩
  obtain ⟨threshold, hthreshold_pos, hthreshold_lt_one, hthreshold_mass⟩ :=
    theorem9_exists_directTrueFrequencyThreshold hm epsilon hepsilon_pos hepsilon_lt
  have hdirect :=
    AppliedModelingLib.ae_eventually_finitePMFIidPath_not_finiteIidFiniteSetLowerFrequencyEvent
      reportLaw (directedTrueBinaryReports (Fin m)) threshold (by
        intro atom hatom
        rcases Finset.mem_image.mp hatom with ⟨pair, hpair, rfl⟩
        exact hthreshold_mass pair.1 pair.2 (Finset.mem_filter.mp hpair).2)
  filter_upwards [hdirect] with path hpath
  filter_upwards [hpath, Filter.eventually_ge_atTop 1] with horizon hdirect hpositive
  let sample : Fin horizon → BinaryPairwiseReport (Fin m) :=
    AppliedModelingLib.finitePMFIidPathPrefix path horizon
  apply exists_pairwiseMLE_of_allBinaryReportWins sample sigmoidCDFLikePairwiseLink reference
    continuous_sigmoidCDFLikePairwiseLink strictMono_sigmoidCDFLikePairwiseLink
  intro winner loser hneq
  have hpositiveH : (0 : ℝ) < horizon := by exact_mod_cast hpositive
  have hthresholdH : (0 : ℝ) < (horizon : ℝ) * threshold :=
    mul_pos hpositiveH hthreshold_pos
  have hnot_count_le :
      ¬ (Probability.empiricalCount sample (directTrueBinaryReport winner loser) : ℝ) ≤
          (horizon : ℝ) * threshold := by
    intro hcount
    apply hdirect
    exact ⟨directTrueBinaryReport winner loser,
      directTrueBinaryReport_mem_directedTrueBinaryReports winner loser hneq, hcount⟩
  have hcount_pos : 0 <
      (Probability.empiricalCount sample (directTrueBinaryReport winner loser) : ℝ) :=
    hthresholdH.trans (lt_of_not_ge hnot_count_le)
  have hcount_nat_pos : 0 <
      Probability.empiricalCount sample (directTrueBinaryReport winner loser) := by
    exact_mod_cast hcount_pos
  have hsuccess_pos : 0 <
      (successIndexSet (fun report : BinaryPairwiseReport (Fin m) =>
        report = directTrueBinaryReport winner loser) sample).card := by
    simpa [Probability.empiricalCount] using hcount_nat_pos
  obtain ⟨index, hindex⟩ := Finset.card_pos.mp hsuccess_pos
  have hreport : sample index = directTrueBinaryReport winner loser := by
    simpa [successIndexSet] using hindex
  refine ⟨index, ?_⟩
  simpa [hreport] using binaryReportWin_direct_true hneq

/-- Full source-facing Appendix-G conclusion: one sufficiently small
off-path mass yields literal correlated iid report paths on which finite MLEs
both exist and, eventually almost surely, satisfy every strict adjacent order.
-/
theorem theorem9_exists_ae_eventually_finiteMLEAdjacentOrder
    {beta : ℝ} (hbeta : 0 < beta) {m : ℕ} (hm : 3 ≤ m) :
    ∃ epsilon : NNReal, 0 < epsilon ∧ epsilon < 1 ∧
      letI : MeasurableSpace (BinaryPairwiseReport (Fin m)) := ⊤
      ∀ᵐ path ∂AppliedModelingLib.finitePMFIidPathMeasure
          (theorem9OneComparisonReportLaw beta m hm epsilon),
        ∀ᶠ horizon : ℕ in Filter.atTop,
          (∃ score : ScoreVector (Fin m),
            isPairwiseMLE
              (ofBinaryReports (AppliedModelingLib.finitePMFIidPathPrefix path horizon))
              sigmoidCDFLikePairwiseLink (⟨0, by omega⟩ : Fin m) score) ∧
          ∀ score : ScoreVector (Fin m),
            isPairwiseMLE
              (ofBinaryReports (AppliedModelingLib.finitePMFIidPathPrefix path horizon))
              sigmoidCDFLikePairwiseLink (⟨0, by omega⟩ : Fin m) score →
              ∀ edge : Fin (m - 1),
                score (theorem9EdgeLower edge) < score (theorem9Succ edge) := by
  obtain ⟨epsilon, hepsilon_pos, hepsilon_lt, horder⟩ :=
    theorem9_exists_ae_eventually_allFiniteMLEAdjacentOrder hbeta hm
  refine ⟨epsilon, hepsilon_pos, hepsilon_lt, ?_⟩
  letI : MeasurableSpace (BinaryPairwiseReport (Fin m)) := ⊤
  have hexists := theorem9_ae_eventually_existsFiniteMLE
    (beta := beta) hm epsilon hepsilon_pos hepsilon_lt
  filter_upwards [hexists, horder] with path hexists horder
  filter_upwards [hexists, horder] with horizon hMLE horder
  exact ⟨hMLE, horder⟩

end GolzHaghtalabYang2025Distortion
