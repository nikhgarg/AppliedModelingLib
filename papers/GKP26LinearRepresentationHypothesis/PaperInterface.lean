import GKP26LinearRepresentationHypothesis.MainTheorems
import GKP26LinearRepresentationHypothesis.Assumptions

/-!
# Human-Facing Paper Interface: Linear Representation Hypothesis Capacity

This file exposes the current source-shaped Lean surface for the paper.  The
LRH-specific linear compressed-sensing, geometry, threshold, and activation-bias
chains compile in finite quantitative form.  The recalled classical compressed
sensing theorem is derived from the reusable finite Rademacher construction,
and the threshold/activation endpoints prove the original printed asymptotic
regime by combining the paper's large-`m` proof route with a complementary
trace/Frobenius argument.
-/

namespace GKP26LinearRepresentationHypothesis

open AppliedModelingLib.Math.RankBounds
open AppliedModelingLib.Probability.RademacherMatrix

/--
Paper feature vector `z in R^m`.

Source status: exact source notation for finite feature coordinates.
-/
abbrev paper_feature_vector (m : ℕ) : Type :=
  FeatureVector m

/--
Paper representation/probe matrix, viewed by columns in `R^d`.

Source status: exact source notation for `A,B in R^{d x m}`, represented by
feature-indexed columns.
-/
abbrev paper_feature_matrix (m d : ℕ) : Type :=
  FeatureMatrix m d

/--
Paper nonlinear compressed-sensing measurement `Az`.

Source status: exact displayed finite-sum semantics for the recalled
compressed-sensing theorem.
-/
abbrev paper_compressed_sensing_measurement {m d : ℕ}
    (A : paper_feature_matrix m d) (z : paper_feature_vector m) :
    ColumnVector d :=
  compressedSensingMeasurement A z

/--
Paper support condition: `z` is `k`-sparse.

Source status: exact source convention, using nonzero support cardinality.
-/
abbrev paper_k_sparse {m : ℕ} (k : ℕ) (z : paper_feature_vector m) : Prop :=
  kSparse k z

/--
Paper basis-pursuit exact-recovery predicate.

Source status: exact theorem semantics for
`argmin_{z' : x = Az'} ||z'||_1` returning the original sparse vector, written
as uniqueness of any feasible vector whose `l1` value is no larger than the
original sparse vector's `l1` value.
-/
abbrev paper_basis_pursuit_exact_recovery {m d : ℕ}
    (A : paper_feature_matrix m d) (k : ℕ) : Prop :=
  basisPursuitExactRecovery A k

/--
Theorem `thm:compressed-sensing`, recalled classical compressed-sensing
result.

Source status: recalled classical result.  The Lean statement makes the hidden
asymptotic constant explicit and uses the standard compressed regime `2k <= m`
where the displayed `k log(m/k)` scale is meaningful.
-/
theorem paper_compressed_sensing_external_basis_pursuit :
    ∃ C : ℝ, 0 < C ∧
      ∀ m k : ℕ, 1 ≤ k → 2 * k ≤ m →
        ∃ d : ℕ, ∃ A : paper_feature_matrix m d,
          (d : ℝ) ≤ C * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) ∧
            paper_basis_pursuit_exact_recovery A k :=
  by
    rcases
      AppliedModelingLib.Probability.RademacherMatrix.exists_basisPursuitExactRecovery_dimension_bigO with
      ⟨C, hC, hmain⟩
    refine ⟨C, hC, ?_⟩
    intro m k hk hm
    rcases hmain m k hk hm with ⟨d, A, hd, hrecover⟩
    refine ⟨d, A, hd, ?_⟩
    intro z hz z' hmeasurement hl1
    exact hrecover z hz z'
      (by
        simpa [compressedSensingMeasurement,
          AppliedModelingLib.Math.LinearCompressedSensing.measurement, mul_comm] using hmeasurement)
      hl1

/--
Paper box condition: `z in [-1,1]^m`.

Source status: exact source convention, stated as `|z_i| <= 1`.
-/
abbrev paper_in_unit_box {m : ℕ} (z : paper_feature_vector m) : Prop :=
  inUnitBox z

/--
Coordinate `i` of the paper expression `B^T A z`.

Source status: exact displayed finite-sum semantics:
`(B^T A z)_i = sum_j z_j <b_i, a_j>`.
-/
abbrev paper_recovered_coordinate {m d : ℕ}
    (A B : paper_feature_matrix m d) (z : paper_feature_vector m)
    (i : Fin m) : ℝ :=
  recoveredCoordinate A B z i

/--
Linear recovery condition underlying the definition of `d(m,k,epsilon)`.

Source status: exact source statement, replacing the displayed `l_infty`
condition by coordinatewise absolute-error inequalities.
-/
theorem paper_linear_recovery_condition_iff {m d k : ℕ} {epsilon : ℝ}
    (A B : paper_feature_matrix m d) :
    linearRecoveryCondition A B k epsilon ↔
      ∀ z : paper_feature_vector m,
        paper_k_sparse k z → paper_in_unit_box z →
          ∀ i : Fin m,
            |paper_recovered_coordinate A B z i - z i| < epsilon := by
  rfl

/--
Feasibility predicate underlying the paper's `d(m,k,epsilon)`.

Source status: exact existential part of the source definition of
`d(m,k,epsilon)`.
-/
abbrev paper_linear_compressed_sensing_feasible
    (m k d : ℕ) (epsilon : ℝ) : Prop :=
  linearCompressedSensingFeasible m k d epsilon

/--
Exact "smallest `d`" predicate for the paper's `d(m,k,epsilon)`.

Source status: exact source definition of the dimension value.
-/
abbrev paper_linear_compressed_sensing_dimension_value
    (m k : ℕ) (epsilon : ℝ) (d : ℕ) : Prop :=
  linearCompressedSensingDimensionValue m k epsilon d

/--
Feasibility predicate for the binary threshold model in Theorem
`thm:threshold`.

Source status: exact existential part of the source threshold-separation
premise.
-/
abbrev paper_threshold_separation_feasible (m k d : ℕ) : Prop :=
  thresholdSeparationFeasible m k d

/--
Exact "smallest `d`" predicate for the binary threshold model.

Source status: source theorem's dimension lower bound, stated for the minimum
dimension admitting threshold separation.
-/
abbrev paper_threshold_separation_dimension_value (m k d : ℕ) : Prop :=
  thresholdSeparationDimensionValue m k d

/--
Feasibility predicate for the activation/bias separator model in Corollary
`cor:activation-bias`.

Source status: exact existential part of the source activation/bias premise,
including monotonicity of the activation function.
-/
abbrev paper_activation_separation_feasible (m k d : ℕ) : Prop :=
  activationSeparationFeasible m k d

/--
Exact "smallest `d`" predicate for the activation/bias separator model.

Source status: source corollary's dimension lower bound, stated for the
minimum dimension admitting activation/bias separation.
-/
abbrev paper_activation_separation_dimension_value (m k d : ℕ) : Prop :=
  activationSeparationDimensionValue m k d

/--
The paper's minimum dimension function `d(m,k,epsilon)`.

Source status: exact source definition when `0 < epsilon`; the companion
theorem below records that it satisfies the source "smallest d" predicate.
-/
noncomputable abbrev paper_linear_compressed_sensing_dimension
    (m k : ℕ) (epsilon : ℝ) : ℕ :=
  linearCompressedSensingDimension m k epsilon

/--
The paper's minimum dimension function satisfies the source "smallest d"
predicate for positive error.

Source status: exact source definition of `d(m,k,epsilon)`.
-/
theorem paper_linear_compressed_sensing_dimension_spec
    (m k : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    paper_linear_compressed_sensing_dimension_value m k epsilon
      (paper_linear_compressed_sensing_dimension m k epsilon) :=
  linearCompressedSensingDimension_spec m k hepsilon

/--
Concrete row dimension chosen in the Rademacher proof of the upper bound.

Source status: explicit finite witness for the paper's
`O_epsilon(k^2 log m)` upper bound.  It is the exact logarithmic
union-bound threshold with `mu = epsilon / (2k)`, rounded up by one.
-/
noncomputable abbrev paper_rademacher_upper_dimension
    (m k : ℕ) (epsilon : ℝ) : ℕ :=
  rademacherUpperDimension m k epsilon

/--
Concrete Rademacher dimension for producing a `mu`-incoherent family.

Source status: explicit finite witness behind Lemma `prop:incoherent`.
-/
noncomputable abbrev paper_rademacher_incoherent_dimension
    (m : ℕ) (mu : ℝ) : ℕ :=
  rademacherIncoherentDimension m mu

/--
Lemma `prop:incoherent`, explicit dimension envelope for the Rademacher
construction.

Source status: formal finite size estimate for the advertised
`O((log m) / mu^2)` row-dimension condition, with hidden constant made
explicit as `2`.
-/
theorem paper_rademacher_incoherent_dimension_real_bigO_envelope
    {m : ℕ} {mu : ℝ} (hm : 2 ≤ m) (hmu : 0 < mu) :
    (paper_rademacher_incoherent_dimension m mu : ℝ) ≤
      (2 / mu ^ 2) * Real.log (2 * (m : ℝ) ^ 2) + 2 :=
  rademacherIncoherentDimension_cast_le_bigO_envelope
    (m := m) (mu := mu) hm hmu

/--
The paper's minimum dimension `d(m,k,epsilon)` exists for positive error.

Source status: source definition support.  The witness is the exact identity
representation at dimension `m`; no asymptotic bound is claimed here.
-/
theorem paper_linear_compressed_sensing_dimension_value_exists
    (m k : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ d : ℕ, paper_linear_compressed_sensing_dimension_value m k epsilon d :=
  exists_linearCompressedSensingDimensionValue m k hepsilon

/--
Paper `mu`-incoherence condition.

Source status: source definition with non-strict off-diagonal inequality,
which is the closed form used by the deterministic recovery theorem.
-/
abbrev paper_mu_incoherent {m d : ℕ}
    (A : paper_feature_matrix m d) (mu : ℝ) : Prop :=
  muIncoherent A mu

/--
The source's strict `mu`-incoherence definition. The non-strict companion
above is the closed condition used by downstream deterministic estimates.
-/
abbrev paper_strict_mu_incoherent {m d : ℕ}
    (A : paper_feature_matrix m d) (mu : ℝ) : Prop :=
  (∀ i : Fin m,
      AppliedModelingLib.Math.LinearCompressedSensing.inner (A i) (A i) = 1) ∧
    ∀ ⦃i j : Fin m⦄, i ≠ j →
      |AppliedModelingLib.Math.LinearCompressedSensing.inner (A i) (A j)| < mu

/--
The existence consequence following Lemma `prop:incoherent`: a strict
`mu`-incoherent matrix exists in logarithmic row dimension.  The explicit
constant uses the Rademacher construction at `mu / 2`, so its non-strict
construction bound entails the source's strict off-diagonal definition.
-/
theorem paper_rademacher_strict_incoherent_exists_source_rate
    {m : ℕ} {mu : ℝ} (hm : 2 ≤ m) (hmu : 0 < mu) :
    ∃ d : ℕ, ∃ A : paper_feature_matrix m d,
      (d : ℝ) ≤ (8 / mu ^ 2) * Real.log (2 * (m : ℝ) ^ 2) + 2 ∧
        paper_strict_mu_incoherent A mu := by
  let nu : ℝ := mu / 2
  have hnu_pos : 0 < nu := by
    dsimp [nu]
    linarith
  rcases exists_muIncoherent_rademacherIncoherentDimension_of_two_le
    (m := m) (mu := nu) hm hnu_pos with ⟨A, hA⟩
  refine ⟨paper_rademacher_incoherent_dimension m nu, A, ?_, ?_⟩
  · have hdim :=
      paper_rademacher_incoherent_dimension_real_bigO_envelope
        (m := m) (mu := nu) hm hnu_pos
    have hmu_ne : mu ≠ 0 := ne_of_gt hmu
    have hcoef : 2 / (mu / 2) ^ 2 = 8 / mu ^ 2 := by
      field_simp [hmu_ne]
      norm_num
    simpa [nu, hcoef] using hdim
  · constructor
    · exact hA.self_inner
    · intro i j hij
      have hnu_lt_mu : nu < mu := by
        dsimp [nu]
        linarith
      exact lt_of_le_of_lt (hA.offdiag_abs_le hij) hnu_lt_mu

/--
Upper-bound proof core: an incoherent matrix gives a linear recovery witness
with `B = A`.

Source status: proved deterministic part of the proof of Theorem `thm:upper`;
the source-level asymptotic wrapper is
`paper_upper_bound_dimension_isBigO_k_sq_log_m`.
-/
theorem paper_upper_bound_incoherent_recovery_core
    {m d k : ℕ} {epsilon mu : ℝ} {A : paper_feature_matrix m d}
    (hmu_nonneg : 0 ≤ mu) (hA : paper_mu_incoherent A mu)
    (hbound : (k : ℝ) * mu < epsilon) :
    paper_linear_compressed_sensing_feasible m k d epsilon :=
  linearCompressedSensingFeasible_of_muIncoherent hmu_nonneg hA hbound

/--
Finite Rademacher upper-bound witness: if the explicit source-style union
bound over off-diagonal pairs is below one and `k * mu < epsilon`, then the
paper's linear compressed-sensing feasibility predicate holds.

Source status: finite, explicit-probability version of Lemma
`prop:incoherent` plus the deterministic proof core of Theorem `thm:upper`.
The source-level asymptotic wrapper is
`paper_upper_bound_dimension_isBigO_k_sq_log_m`.
-/
theorem paper_upper_bound_rademacher_source_tail_feasible
    {m d k : ℕ} {epsilon mu : ℝ}
    (hd : 0 < d) (hmu_nonneg : 0 ≤ mu)
    (hbad_lt_one :
      ((offdiagPairFinset (Feature := Fin m)).card : ℝ) *
          (2 * Real.exp (-((d : ℝ) * mu ^ 2) / 2)) < 1)
    (hbound : (k : ℝ) * mu < epsilon) :
    paper_linear_compressed_sensing_feasible m k d epsilon :=
  linearCompressedSensingFeasible_of_rademacher_source_tail_lt_one
    hd hmu_nonneg hbad_lt_one hbound

/--
Upper-bound proof core in logarithmic finite form: if the row dimension beats
the explicit log ordered-pair threshold and `k * mu < epsilon`, a linear
recovery witness exists.

Source status: finite logarithmic form of the proof of Theorem `thm:upper`.
The source-level asymptotic wrapper is
`paper_upper_bound_dimension_isBigO_k_sq_log_m`.
-/
theorem paper_upper_bound_rademacher_log_tail_feasible
    {m d k : ℕ} {epsilon mu : ℝ}
    (hd : 0 < d) (hmu_nonneg : 0 ≤ mu)
    (hpair_pos : 0 < ((offdiagPairFinset (Feature := Fin m)).card : ℝ))
    (hlog :
      Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) <
        ((Fintype.card (Fin d) : ℝ) * mu ^ 2) / 2)
    (hbound : (k : ℝ) * mu < epsilon) :
    paper_linear_compressed_sensing_feasible m k d epsilon :=
  linearCompressedSensingFeasible_of_rademacher_log_tail
    hd hmu_nonneg hpair_pos hlog hbound

/--
Upper-bound proof core with the source choice `mu = epsilon / (2k)`.

Source status: finite logarithmic form of the proof of Theorem `thm:upper`
after substituting the standard incoherence target. The source-level
asymptotic wrapper is `paper_upper_bound_dimension_isBigO_k_sq_log_m`.
-/
theorem paper_upper_bound_rademacher_log_tail_epsilon_over_two_k_feasible
    {m d k : ℕ} {epsilon : ℝ}
    (hd : 0 < d) (hk : 0 < k) (hepsilon : 0 < epsilon)
    (hpair_pos : 0 < ((offdiagPairFinset (Feature := Fin m)).card : ℝ))
    (hlog :
      Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) <
        ((Fintype.card (Fin d) : ℝ) *
          (epsilon / (2 * (k : ℝ))) ^ 2) / 2) :
    paper_linear_compressed_sensing_feasible m k d epsilon :=
  linearCompressedSensingFeasible_of_rademacher_log_tail_epsilon_over_two_k
    hd hk hepsilon hpair_pos hlog

/--
Finite upper-bound existence: for positive `epsilon` and `k`, once there is at
least one ordered off-diagonal pair, some finite row dimension satisfies the
Rademacher logarithmic tail condition and gives a recovery witness.

Source status: finite existential version of the upper-bound proof after
substituting `mu = epsilon / (2k)`. The source-level asymptotic wrapper is
`paper_upper_bound_dimension_isBigO_k_sq_log_m`.
-/
theorem paper_upper_bound_rademacher_exists_feasible_dimension
    {m k : ℕ} {epsilon : ℝ}
    (hk : 0 < k) (hepsilon : 0 < epsilon)
    (hpair_pos : 0 < ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) :
    ∃ d : ℕ, paper_linear_compressed_sensing_feasible m k d epsilon :=
  exists_linearCompressedSensingFeasible_of_rademacher_log_tail_epsilon_over_two_k
    hk hepsilon hpair_pos

/--
Theorem `thm:upper`, explicit finite upper-bound form: for at least two
features, positive sparsity, and positive error, the concrete Rademacher
dimension is feasible.

Source status: source theorem proved in an explicit rounded finite form.  This
is the quantitative witness behind `d(m,k,epsilon) =
O_epsilon(k^2 log m)`.
-/
theorem paper_upper_bound_rademacher_explicit_dimension_feasible
    {m k : ℕ} {epsilon : ℝ}
    (hm : 2 ≤ m) (hk : 0 < k) (hepsilon : 0 < epsilon) :
    paper_linear_compressed_sensing_feasible m k
      (paper_rademacher_upper_dimension m k epsilon) epsilon :=
  linearCompressedSensingFeasible_rademacherUpperDimension_of_two_le
    (m := m) (k := k) (epsilon := epsilon) hm hk hepsilon

/--
Theorem `thm:upper`, minimum-dimension form: the paper's smallest feasible
dimension `d(m,k,epsilon)` is at most the explicit Rademacher upper-bound
dimension.

Source status: source theorem proved in an explicit rounded finite form.  The
displayed asymptotic `O_epsilon(k^2 log m)` is represented by this concrete
dimension bound.
-/
theorem paper_upper_bound_dimension_value_le_explicit_rademacher_dimension
    (m k : ℕ) {epsilon : ℝ}
    (hm : 2 ≤ m) (hk : 0 < k) (hepsilon : 0 < epsilon) :
    ∃ d : ℕ,
      paper_linear_compressed_sensing_dimension_value m k epsilon d ∧
        d ≤ paper_rademacher_upper_dimension m k epsilon :=
  exists_linearCompressedSensingDimensionValue_le_rademacherUpperDimension_of_two_le
    m k hm hk hepsilon

/--
Theorem `thm:upper`, explicit logarithmic size estimate for the rounded
Rademacher witness.

Source status: formal finite size estimate behind the displayed
`O_epsilon(k^2 log m)` upper bound. The theorem keeps the exact ordered-pair
logarithmic term used in the proof.
-/
theorem paper_upper_bound_rademacher_dimension_real_size
    {m k : ℕ} {epsilon : ℝ}
    (hm : 2 ≤ m) (hk : 0 < k) (hepsilon : 0 < epsilon) :
    (paper_rademacher_upper_dimension m k epsilon : ℝ) ≤
      Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) /
          (((epsilon / (2 * (k : ℝ))) ^ 2) / 2) + 2 :=
  rademacherUpperDimension_cast_le_log_tail_add_two hm hk hepsilon

/--
Theorem `thm:upper`, readable logarithmic size estimate: the rounded
Rademacher witness is bounded using the elementary ordered-pair estimate
`|{(i,j): i != j}| <= m^2`.

Source status: formal finite estimate in the advertised
`k^2 log m` scale, up to the displayed constant and the harmless additive
rounding term.
-/
theorem paper_upper_bound_rademacher_dimension_real_size_m_sq
    {m k : ℕ} {epsilon : ℝ}
    (hm : 2 ≤ m) (hk : 0 < k) (hepsilon : 0 < epsilon) :
    (paper_rademacher_upper_dimension m k epsilon : ℝ) ≤
      Real.log (2 * (m : ℝ) ^ 2) /
          (((epsilon / (2 * (k : ℝ))) ^ 2) / 2) + 2 :=
  rademacherUpperDimension_cast_le_log_m_sq_tail_add_two hm hk hepsilon

/--
Theorem `thm:upper`, minimum-dimension logarithmic size estimate: the paper's
smallest feasible dimension is bounded by the same explicit `k^2 log m`
Rademacher envelope.

Source status: formal finite estimate for the advertised
`d(m,k,epsilon) = O_epsilon(k^2 log m)` upper bound.
-/
theorem paper_upper_bound_dimension_value_real_size_m_sq
    {m k : ℕ} {epsilon : ℝ}
    (hm : 2 ≤ m) (hk : 0 < k) (hepsilon : 0 < epsilon) :
    ∃ d : ℕ,
      paper_linear_compressed_sensing_dimension_value m k epsilon d ∧
        (d : ℝ) ≤
          Real.log (2 * (m : ℝ) ^ 2) /
              (((epsilon / (2 * (k : ℝ))) ^ 2) / 2) + 2 :=
  exists_linearCompressedSensingDimensionValue_real_le_log_m_sq_tail_add_two
    m k hm hk hepsilon

/--
Theorem `thm:upper`, explicit `O_epsilon(k^2 log m)` envelope: the paper's
smallest feasible dimension is bounded by a constant depending only on
`epsilon` times `k^2 log m`, plus the finite rounding term.

Source status: formal paper-facing upper bound with the hidden asymptotic
constant made explicit as `8 / epsilon^2`.
-/
theorem paper_upper_bound_dimension_value_real_bigO_envelope
    {m k : ℕ} {epsilon : ℝ}
    (hm : 2 ≤ m) (hk : 0 < k) (hepsilon : 0 < epsilon) :
    ∃ d : ℕ,
      paper_linear_compressed_sensing_dimension_value m k epsilon d ∧
        (d : ℝ) ≤
          (8 * (k : ℝ) ^ 2 / epsilon ^ 2) *
              Real.log (2 * (m : ℝ) ^ 2) + 2 :=
  exists_linearCompressedSensingDimensionValue_real_le_upper_bigO_envelope
    m k hm hk hepsilon

/--
Theorem `thm:upper`, source-readable explicit `O_epsilon(k^2 log m)` envelope:
the finite logarithmic tail and rounding term are absorbed into one constant
depending only on `epsilon`.

Source status: formal paper-facing upper bound with the hidden asymptotic
constant made explicit as `24 / epsilon^2 + 2 / log 2`.
-/
theorem paper_upper_bound_dimension_value_real_log_m_envelope
    {m k : ℕ} {epsilon : ℝ}
    (hm : 2 ≤ m) (hk : 0 < k) (hepsilon : 0 < epsilon) :
    ∃ d : ℕ,
      paper_linear_compressed_sensing_dimension_value m k epsilon d ∧
        (d : ℝ) ≤
          ((24 / epsilon ^ 2) + 2 / Real.log 2) *
            (k : ℝ) ^ 2 * Real.log (m : ℝ) :=
  exists_linearCompressedSensingDimensionValue_real_le_upper_log_m_envelope
    m k hm hk hepsilon

/--
Theorem `thm:upper`, paper-style asymptotic form: for fixed positive
`epsilon`, the minimum dimension `d(m,k,epsilon)` is
`O_epsilon(k^2 log m)` as `(m,k)` go to infinity.

Source status: exact Landau wrapper proved from the explicit finite
Rademacher envelope above.
-/
theorem paper_upper_bound_dimension_isBigO_k_sq_log_m
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Asymptotics.IsBigO (Filter.atTop : Filter (ℕ × ℕ))
      (fun p : ℕ × ℕ =>
        (paper_linear_compressed_sensing_dimension p.1 p.2 epsilon : ℝ))
      (fun p : ℕ × ℕ => (p.2 : ℝ) ^ 2 * Real.log (p.1 : ℝ)) :=
  linearCompressedSensingDimension_isBigO_upper_log_m hepsilon

/--
Lemma `prop:incoherent`, finite probability form: a scaled Rademacher matrix
has all off-diagonal column inner products below `mu` with probability at
least one minus the explicit union-bound tail.

Source status: proved finite source-tail statement. The remaining packaging is
the asymptotic dimension condition
`d = O((log m + log (1 / delta)) / mu^2)`.
-/
theorem paper_random_rademacher_strict_incoherence_probability
    {m d : ℕ} {mu : ℝ}
    (hd : 0 < d) (hmu_nonneg : 0 ≤ mu) :
    AppliedModelingLib.measureProb (rowsMeasure (Fin m) (Fin d))
        (fun ω =>
          ∀ ⦃i j : Fin m⦄, i ≠ j →
            |AppliedModelingLib.Math.LinearCompressedSensing.inner
              (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω i)
              (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω j)| < mu) ≥
      1 - ((offdiagPairFinset (Feature := Fin m)).card : ℝ) *
          (2 * Real.exp (-((d : ℝ) * mu ^ 2) / 2)) :=
  rademacher_strict_incoherence_probability_ge_one_sub_source_tail
    hd hmu_nonneg

/--
Lemma `prop:incoherent`, high-probability form: if the logarithmic dimension
condition beats the ordered-pair union bound with failure budget `delta`, a
scaled Rademacher matrix is `mu`-incoherent with probability at least
`1 - delta`.

Source status: formal finite high-probability packaging of the paper's
`d = O((log m + log(1 / delta)) / mu^2)` condition, stated with the explicit
ordered-pair logarithmic threshold.
-/
theorem paper_random_rademacher_strict_incoherence_probability_high_probability
    {m d : ℕ} {mu delta : ℝ}
    (hd : 0 < d) (hmu_nonneg : 0 ≤ mu)
    (hpair_pos : 0 < ((offdiagPairFinset (Feature := Fin m)).card : ℝ))
    (hdelta_pos : 0 < delta)
    (hlog :
      Real.log
          ((2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) / delta) ≤
        ((d : ℝ) * mu ^ 2) / 2) :
    AppliedModelingLib.measureProb (rowsMeasure (Fin m) (Fin d))
        (fun ω =>
          ∀ ⦃i j : Fin m⦄, i ≠ j →
            |AppliedModelingLib.Math.LinearCompressedSensing.inner
              (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω i)
              (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω j)| < mu) ≥
      1 - delta :=
  rademacher_strict_incoherence_probability_ge_one_sub_delta_of_log_div_le
    hd hmu_nonneg hpair_pos hdelta_pos hlog

/--
Lemma `prop:incoherent`, direct source-rate form.  For the standard
nondegenerate confidence regime, the explicit rounded dimension is bounded by
the source's logarithmic `m` and `delta` scale and gives the stated
high-probability incoherence conclusion.
-/
theorem paper_random_rademacher_strict_incoherence_source_rate
    {m : ℕ} {mu delta : ℝ}
    (hm : 2 ≤ m) (hmu : 0 < mu)
    (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1) :
    ∃ d : ℕ, 0 < d ∧
      (d : ℝ) ≤ Real.log (2 * (m : ℝ) ^ 2 / delta) / ((mu ^ 2) / 2) + 2 ∧
      (AppliedModelingLib.measureProb (rowsMeasure (Fin m) (Fin d))
          (fun ω =>
            ∀ ⦃i j : Fin m⦄, i ≠ j →
              |AppliedModelingLib.Math.LinearCompressedSensing.inner
                (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω i)
                (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω j)| < mu) ≥
        1 - delta) ∧
      (∀ (ω : Fin d → Fin m → Bool) (i : Fin m),
        AppliedModelingLib.Math.LinearCompressedSensing.inner
          (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω i)
          (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω i) = 1) :=
  exists_rademacher_strict_incoherence_at_explicit_logarithmic_dimension
    hm hmu hdelta hdelta_le_one

/--
Theorem `thm:lower`, finite proof spine: the symmetric-power rank obstruction
on each principal submatrix and the Turán counting inequality contradict linear
recovery.

Source status: finite source proof chain is proved with an explicit
polynomial-method replacement for the cited Alon rank step. The remaining
paper-facing work is the asymptotic `Omega_epsilon` packaging.
-/
theorem paper_lower_bound_finite_rank_turan_contradiction
    {m d s k power : ℕ} {gamma beta eta epsilon : ℝ}
    {A B : paper_feature_matrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hgamma_nonneg : 0 ≤ gamma) (hbeta_nonneg : 0 ≤ beta)
    (hdiag_lower : ∀ i : Fin m,
      gamma ≤ AppliedModelingLib.Math.LinearCompressedSensing.inner (B i) (A i))
    (hdiag_abs_upper : ∀ i : Fin m,
      |AppliedModelingLib.Math.LinearCompressedSensing.inner (B i) (A i)| ≤ beta)
    (heta : 0 ≤ eta)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      (Fintype.card (Sym (Sum (Fin d) (Fin d)) power) : ℝ) *
          ((Fintype.card {j // j ∈ t} : ℝ) * beta ^ (2 * power) +
            (Fintype.card {j // j ∈ t} : ℝ) *
              (Fintype.card {j // j ∈ t} : ℝ) * eta ^ (2 * power)) <
        (Fintype.card {j // j ∈ t} : ℝ) ^ 2 * gamma ^ (2 * power))
    (hk : 0 < k)
    (hepsilon_le : epsilon ≤ (k : ℝ) * eta)
    (hs : 0 < s)
    (havg :
      m * (2 * k) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) +
            (m % r).choose 2))) :
    False :=
  false_of_linearRecoveryCondition_and_symmetricPower_dimension_turan
    hrec hgamma_nonneg hbeta_nonneg hdiag_lower hdiag_abs_upper
    heta hdim hk hepsilon_le hs havg

/--
Theorem `thm:lower`, source-parameter finite proof spine: linear recovery
itself supplies diagonal entries above `1 - epsilon`, and the proof uses
`eta = epsilon / k` for the large-interference threshold.

Source status: finite source proof chain is proved after the paper's parameter
substitution. The remaining paper-facing work is the asymptotic
`Omega_epsilon` packaging. The symmetric-power coordinate count is written by
the factorial-normalized envelope
`(2d + power - 1)^power / power!`, and the aligned source subset size is
written directly as `s`.
-/
theorem paper_lower_bound_source_parameter_finite_contradiction
    {m d s k power : ℕ} {epsilon : ℝ}
    {A B : paper_feature_matrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hdim :
      ((((2 * d + power - 1) ^ power : ℕ) : ℝ) /
          (power.factorial : ℝ)) *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power))
    (hs : 0 < s)
    (havg :
      m * (2 * k) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) +
            (m % r).choose 2))) :
    False :=
  false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_factorial_card
    hrec hk hepsilon_nonneg hepsilon_lt_one hdim hs havg

/--
Theorem `thm:lower`, source-parameter finite proof spine using the source's
coarse Turán estimate `m^2/(2r)-m/2`.

Source status: finite source proof chain is proved after the paper's parameter
substitution and with the graph-counting step written in the paper's
source-readable coarse form. The remaining paper-facing work is the
asymptotic `Omega_epsilon` packaging and parameter selection.
-/
theorem paper_lower_bound_source_parameter_finite_contradiction_coarse_turan
    {m d s k power : ℕ} {epsilon : ℝ}
    {A B : paper_feature_matrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hdim :
      ((((2 * d + power - 1) ^ power : ℕ) : ℝ) /
          (power.factorial : ℝ)) *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power))
    (hs : 1 < s)
    (havg :
      (m : ℝ) * ((2 * k : ℕ) : ℝ) <
        (m : ℝ) ^ 2 / (2 * ((s - 1 : ℕ) : ℝ)) - (m : ℝ) / 2) :
    False :=
  false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_factorial_card_coarse_turan
    hrec hk hepsilon_nonneg hepsilon_lt_one hdim hs havg

/--
Theorem `thm:lower`, source-parameter finite proof spine using the
source-scale Stirling envelope and the paper's coarse Turán estimate.

Source status: finite source proof chain is proved after the paper's parameter
substitution with no factorial-normalized count or exact Turán expression in
the interface. The remaining paper-facing work is the asymptotic
`Omega_epsilon` packaging and parameter selection.
-/
theorem paper_lower_bound_source_parameter_finite_contradiction_exp_card_coarse_turan
    {m d s k power : ℕ} {epsilon : ℝ}
    {A B : paper_feature_matrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hpower : 0 < power)
    (hdim :
      (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power))
    (hs : 1 < s)
    (havg :
      (m : ℝ) * ((2 * k : ℕ) : ℝ) <
        (m : ℝ) ^ 2 / (2 * ((s - 1 : ℕ) : ℝ)) - (m : ℝ) / 2) :
    False :=
  false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_exp_card_coarse_turan
    hrec hk hepsilon_nonneg hepsilon_lt_one hpower hdim hs havg

/--
Theorem `thm:lower`, source-parameter finite proof spine using the
source-scale Stirling envelope and the source Turán parameter inequality
`(4k+1)(s-1) < m`.

Source status: finite source proof chain is proved after the paper's parameter
substitution. The remaining paper-facing work is the asymptotic
`Omega_epsilon` packaging and eventual parameter selection.
-/
theorem paper_lower_bound_source_parameter_finite_contradiction_exp_card_source_turan
    {m d s k power : ℕ} {epsilon : ℝ}
    {A B : paper_feature_matrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hpower : 0 < power)
    (hdim :
      (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power))
    (hs : 1 < s)
    (hm : 0 < m)
    (hturan : (((4 * k + 1 : ℕ) : ℝ) * ((s - 1 : ℕ) : ℝ)) < (m : ℝ)) :
    False :=
  false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_exp_card_source_turan
    hrec hk hepsilon_nonneg hepsilon_lt_one hpower hdim hs hm hturan

/--
Theorem `thm:lower`, finite minimum-dimension form: under the same explicit
symmetric-power and Turán arithmetic hypotheses, the paper's smallest feasible
dimension is strictly larger than the candidate dimension `D`.

Source status: finite source proof chain stated against the exact
`d(m,k,epsilon)` definition. The remaining paper-facing work is the
asymptotic `Omega_epsilon` packaging that chooses `s` and `power` from the
source growth regime. The symmetric-power coordinate count is written by
the factorial-normalized envelope
`(2D + power - 1)^power / power!`, and the aligned source subset size is
written directly as `s`.
-/
theorem paper_lower_bound_dimension_value_gt_of_symmetricPower_source_parameters
    {m D s k power : ℕ} {epsilon : ℝ}
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hdim :
      ((((2 * D + power - 1) ^ power : ℕ) : ℝ) /
          (power.factorial : ℝ)) *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power))
    (hs : 0 < s)
    (havg :
      m * (2 * k) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) +
            (m % r).choose 2)))
    {dmin : ℕ}
    (hvalue : paper_linear_compressed_sensing_dimension_value m k epsilon dmin) :
    D < dmin :=
  linearCompressedSensingDimensionValue_gt_of_symmetricPower_source_parameters_factorial_card
    hk hepsilon_nonneg hepsilon_lt_one hdim hs havg hvalue

/--
Theorem `thm:lower`, minimum-dimension form with source-scale symmetric-power
and source Turán parameter inequalities.

Source status: finite source proof chain stated against the exact
`d(m,k,epsilon)` definition. The remaining paper-facing work is the
asymptotic `Omega_epsilon` packaging and eventual parameter selection.
-/
theorem paper_lower_bound_dimension_value_gt_source_turan_exp_card
    {m D s k power : ℕ} {epsilon : ℝ}
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hpower : 0 < power)
    (hdim :
      (Real.exp 1 * ((2 * D + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power))
    (hs : 1 < s)
    (hm : 0 < m)
    (hturan : (((4 * k + 1 : ℕ) : ℝ) * ((s - 1 : ℕ) : ℝ)) < (m : ℝ))
    {dmin : ℕ}
    (hvalue : paper_linear_compressed_sensing_dimension_value m k epsilon dmin) :
    D < dmin :=
  linearCompressedSensingDimensionValue_gt_of_symmetricPower_source_parameters_exp_card_source_turan
    hk hepsilon_nonneg hepsilon_lt_one hpower hdim hs hm hturan hvalue

/--
Theorem `thm:lower`, minimum-dimension form with the source Turán parameter
selected as `s = floor(m/(4k+1))`.

Source status: finite source proof chain with the source Turán parameter
choice internalized. The remaining paper-facing work is the logarithmic
parameter selection for `power` and `D`.
-/
theorem paper_lower_bound_dimension_value_gt_floor_turan_exp_card
    {m D k power : ℕ} {epsilon : ℝ}
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hpower : 0 < power)
    (hdim :
      let s := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
      (Real.exp 1 * ((2 * D + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power))
    (hs :
      1 < Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)))
    (hm : 0 < m)
    {dmin : ℕ}
    (hvalue : paper_linear_compressed_sensing_dimension_value m k epsilon dmin) :
    D < dmin :=
  linearCompressedSensingDimensionValue_gt_of_symmetricPower_source_parameters_exp_card_floor_turan
    hk hepsilon_nonneg hepsilon_lt_one hpower hdim hs hm hvalue

/--
Theorem `thm:lower`, minimum-dimension form with the source Turán parameter
and the logarithmic floor-power selector internalized.

Source status: finite source proof chain with
`s = floor(m/(4k+1))` and
`power = floor(log s / (2 log k))`. The remaining paper-facing arithmetic is
the displayed source-scale base bound on the candidate dimension `D`; this is
the finite form from which the `Omega_epsilon((k^2/log k) log(m/k))` lower
bound is packaged.
-/
theorem paper_lower_bound_dimension_value_gt_floor_log_power_base_floor_turan
    {m D k : ℕ} {epsilon : ℝ}
    (hk_two : 2 ≤ k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hpower :
      let s := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
      0 < Nat.floor (Real.log (s : ℝ) / (2 * Real.log (k : ℝ))))
    (hbase :
      let s := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
      let power :=
        Nat.floor (Real.log (s : ℝ) / (2 * Real.log (k : ℝ)))
      Real.exp 1 * ((2 * D + power - 1 : ℕ) : ℝ) / (power : ℝ) ≤
        (1 / 4) * ((1 - epsilon) / (1 + epsilon)) ^ 2 *
          (k : ℝ) ^ 2)
    (hs :
      1 < Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)))
    (hm : 0 < m)
    {dmin : ℕ}
    (hvalue : paper_linear_compressed_sensing_dimension_value m k epsilon dmin) :
    D < dmin :=
  linearCompressedSensingDimensionValue_gt_of_floor_log_power_base_floor_turan
    hk_two hepsilon_nonneg hepsilon_lt_one hpower hbase hs hm hvalue

/--
Theorem `thm:lower`, selected finite lower-bound witness: any candidate
dimension below the displayed `epsilon`-dependent multiple of
`power * k^2` is strictly below the minimum feasible dimension.

Source status: finite source proof chain with source Turán and logarithmic
power selectors internalized. The remaining paper-facing packaging is to
derive the selector side conditions from the theorem's asymptotic source
regime and restate the result in Landau notation.
-/
theorem paper_lower_bound_dimension_value_gt_floor_log_power_candidate_floor_turan
    {m D k : ℕ} {epsilon : ℝ}
    (hk_two : 2 ≤ k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hpower :
      let s := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
      0 < Nat.floor (Real.log (s : ℝ) / (2 * Real.log (k : ℝ))))
    (hD :
      let s := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
      let power :=
        Nat.floor (Real.log (s : ℝ) / (2 * Real.log (k : ℝ)))
      (D : ℝ) ≤
        (((1 - epsilon) / (1 + epsilon)) ^ 2 /
          (16 * Real.exp 1)) * (power : ℝ) * (k : ℝ) ^ 2)
    (hk_large :
      Real.exp 1 ≤
        (1 / 8) * ((1 - epsilon) / (1 + epsilon)) ^ 2 *
          (k : ℝ) ^ 2)
    (hs :
      1 < Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)))
    (hm : 0 < m)
    {dmin : ℕ}
    (hvalue : paper_linear_compressed_sensing_dimension_value m k epsilon dmin) :
    D < dmin :=
  linearCompressedSensingDimensionValue_gt_of_floor_log_power_candidate_floor_turan
    hk_two hepsilon_nonneg hepsilon_lt_one hpower hD hk_large hs hm hvalue

/--
Theorem `thm:lower`, selected finite lower-bound witness with the source
epsilon regime deriving the Turán and logarithmic selector side conditions.

Source status: finite source proof chain with the paper's squared lower-bound
regime `5 k^3 < epsilon^2 m`. The remaining paper-facing packaging is the
Landau-notation restatement of this selected finite witness.
-/
theorem paper_lower_bound_dimension_value_gt_floor_log_power_candidate_source_regime
    {m D k : ℕ} {epsilon : ℝ}
    (hk_two : 2 ≤ k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hregime : 5 * (k : ℝ) ^ 3 < epsilon ^ 2 * (m : ℝ))
    (hD :
      let s := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
      let power :=
        Nat.floor (Real.log (s : ℝ) / (2 * Real.log (k : ℝ)))
      (D : ℝ) ≤
        (((1 - epsilon) / (1 + epsilon)) ^ 2 /
          (16 * Real.exp 1)) * (power : ℝ) * (k : ℝ) ^ 2)
    (hk_large :
      Real.exp 1 ≤
        (1 / 8) * ((1 - epsilon) / (1 + epsilon)) ^ 2 *
          (k : ℝ) ^ 2)
    {dmin : ℕ}
    (hvalue : paper_linear_compressed_sensing_dimension_value m k epsilon dmin) :
    D < dmin :=
  linearCompressedSensingDimensionValue_gt_of_floor_log_power_candidate_source_regime
    hk_two hepsilon_nonneg hepsilon_lt_one hregime hD hk_large hvalue

/--
Theorem `thm:lower`, logarithmic finite lower-bound envelope with source
selectors internalized: under the paper's squared lower-bound regime and the
large-`k` side condition used in the finite source proof, the minimum feasible
dimension exceeds an explicit constant times
`k^2 * log(floor(m/(4k+1))) / log k`.

Source status: Lean-checked finite logarithmic form of the lower-bound proof.
This is the source-selected finite witness behind the displayed
`Omega_epsilon((k^2/log k) log(m/k))` statement; the remaining difference is
the standard asymptotic replacement of `floor(m/(4k+1))` by `m/k`.
-/
theorem paper_lower_bound_dimension_value_real_gt_log_floor_selector_source_regime
    {m k dmin : ℕ} {epsilon : ℝ}
    (hk_two : 2 ≤ k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hregime : 5 * (k : ℝ) ^ 3 < epsilon ^ 2 * (m : ℝ))
    (hk_large :
      Real.exp 1 ≤
        (1 / 8) * ((1 - epsilon) / (1 + epsilon)) ^ 2 *
          (k : ℝ) ^ 2)
    {dmin : ℕ}
    (hvalue : paper_linear_compressed_sensing_dimension_value m k epsilon dmin) :
    ((((1 - epsilon) / (1 + epsilon)) ^ 2 /
        (64 * Real.exp 1)) *
      (k : ℝ) ^ 2 *
      (Real.log
          (Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)) : ℝ) /
        Real.log (k : ℝ))) < (dmin : ℝ) :=
  linearCompressedSensingDimensionValue_real_gt_log_floor_selector_source_regime
    hk_two hepsilon_nonneg hepsilon_lt_one hregime hk_large hvalue

/--
Theorem `thm:lower`, asymptotic lower-bound wrapper: for fixed
`0 < epsilon < 1`, along the source lower-bound regime the finite
rank/Turán floor-log scale
`k^2 * log(floor(m/(4k+1))) / log k` is Big-O of the minimum feasible
linear compressed-sensing dimension.  This is the formal `Omega_epsilon`
direction supplied by the proved finite lower-bound envelope.

Source status: Landau wrapper proved for the source-selected floor-log scale.
The validation report records the remaining source-level difference between
this checked scale and the printed `log(m/k)` display.
-/
theorem paper_lower_bound_dimension_isBigO_floor_log_source_regime
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) :
    Asymptotics.IsBigO
      (linearCompressedSensingLowerSourceFilter epsilon)
      linearCompressedSensingLowerFloorLogScale
      (fun p : ℕ × ℕ =>
        (paper_linear_compressed_sensing_dimension p.1 p.2 epsilon : ℝ)) :=
  linearCompressedSensingDimension_isBigO_lower_floor_log_source_regime
    hepsilon_pos hepsilon_lt_one

/--
Theorem `thm:lower`, printed source-scale asymptotic lower bound: for fixed
`0 < epsilon < 1`, along the source lower-bound regime the scale
`(k^2 / log k) * log(m/k)` is Big-O of the minimum feasible linear
compressed-sensing dimension.

Source status: Landau wrapper proved for the paper's displayed
`Omega_epsilon((k^2 / log k) log(m/k))` scale, using the checked finite
rank/Turán lower-bound envelope and the finite comparison from
`floor(m/(4k+1))` to `m/k`.
-/
theorem paper_lower_bound_dimension_isBigO_source_log_source_regime
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) :
    Asymptotics.IsBigO
      (linearCompressedSensingLowerSourceFilter epsilon)
      linearCompressedSensingLowerSourceLogScale
      (fun p : ℕ × ℕ =>
        (paper_linear_compressed_sensing_dimension p.1 p.2 epsilon : ℝ)) :=
  linearCompressedSensingDimension_isBigO_lower_source_log_source_regime
    hepsilon_pos hepsilon_lt_one

/--
Geometry Proposition 1, deterministic recovery core: given an incoherent
family of `m+2` columns, the source construction
`a_i = c_i + lambda a*`, `b_i = c_i + lambda b*` satisfies linear recovery
when the displayed diagonal and off-diagonal error budget is below `epsilon`.

Source status: proved finite deterministic construction core. The remaining
paper-facing Geometry Proposition 1 work is the asymptotic incoherent-matrix
existence and the normalized-correlation `delta + o(1)` / `1 - delta - o(1)`
packaging.
-/
theorem paper_geometry1_constructed_linear_recovery_core
    {m d k : ℕ} {epsilon lambda mu : ℝ}
    {C : Fin (m + 2) → ColumnVector d}
    (hlambda : 0 ≤ lambda) (hmu : 0 ≤ mu)
    (hC : muIncoherent C mu)
    (hbound :
      (2 * lambda + lambda ^ 2) * mu +
          (k : ℝ) * ((1 + 2 * lambda + lambda ^ 2) * mu) < epsilon) :
    linearRecoveryCondition
      (geometry1RepresentationMatrix C lambda)
      (geometry1ProbeMatrix C lambda) k epsilon :=
  geometry1_linearRecoveryCondition hlambda hmu hC hbound

/--
Geometry Proposition 1, explicit finite existential construction: at the
rounded Rademacher incoherent dimension for `m+2` auxiliary columns, there are
representation and probe matrices satisfying recovery plus the three displayed
finite correlation bounds.

Source status: finite source construction with the incoherent family produced
internally by the Rademacher lemma. The remaining paper-facing work is only
the asymptotic `O_{epsilon,delta}(k^2 log m)` and `o(1)` packaging.
-/
theorem paper_geometry1_exists_constructed_matrices_explicit_finite
    {m k : ℕ} {epsilon lambda mu : ℝ}
    (hlambda : 0 ≤ lambda) (hmu : 0 < mu)
    (hbound :
      (2 * lambda + lambda ^ 2) * mu +
          (k : ℝ) * ((1 + 2 * lambda + lambda ^ 2) * mu) < epsilon)
    (hs : 0 < 1 + lambda ^ 2 - 2 * lambda * mu)
    (hnum : 0 ≤ lambda ^ 2 - (1 + 2 * lambda) * mu) :
    ∃ A B : paper_feature_matrix m
        (paper_rademacher_incoherent_dimension (m + 2) mu),
      linearRecoveryCondition A B k epsilon ∧
        (∀ i : Fin m,
          |columnCorrelation (A i) (B i)| ≤
            (1 + (2 * lambda + lambda ^ 2) * mu) /
              (1 + lambda ^ 2 - 2 * lambda * mu)) ∧
        (∀ ⦃i j : Fin m⦄, i ≠ j →
          (lambda ^ 2 - (1 + 2 * lambda) * mu) /
              (1 + lambda ^ 2 + 2 * lambda * mu) ≤
            columnCorrelation (A i) (A j)) ∧
        (∀ ⦃i j : Fin m⦄, i ≠ j →
          (lambda ^ 2 - (1 + 2 * lambda) * mu) /
              (1 + lambda ^ 2 + 2 * lambda * mu) ≤
            columnCorrelation (B i) (B j)) :=
  exists_geometry1_constructed_matrices_rademacherIncoherentDimension
    hlambda hmu hbound hs hnum

/--
Geometry Proposition 1, finite construction with explicit row-dimension
envelope: the Rademacher construction gives matrices in a dimension bounded
by `O((log m) / mu^2)`, and the finite correlation/recovery guarantees hold
in that same dimension.

Source status: formal finite size-and-construction package behind the
paper's `O_{epsilon,delta}(k^2 log m)` construction. The theorem keeps the
source proof's explicit incoherence parameter `mu`; choosing `mu = Theta(1/k)`
gives the displayed `k^2 log m` scale.
-/
theorem paper_geometry1_exists_constructed_matrices_with_dimension_envelope
    {m k : ℕ} {epsilon lambda mu : ℝ}
    (hlambda : 0 ≤ lambda) (hmu : 0 < mu)
    (hbound :
      (2 * lambda + lambda ^ 2) * mu +
          (k : ℝ) * ((1 + 2 * lambda + lambda ^ 2) * mu) < epsilon)
    (hs : 0 < 1 + lambda ^ 2 - 2 * lambda * mu)
    (hnum : 0 ≤ lambda ^ 2 - (1 + 2 * lambda) * mu) :
    ∃ D : ℕ,
      (D : ℝ) ≤
          (2 / mu ^ 2) * Real.log (2 * ((m + 2 : ℕ) : ℝ) ^ 2) + 2 ∧
        ∃ A B : paper_feature_matrix m D,
          linearRecoveryCondition A B k epsilon ∧
            (∀ i : Fin m,
              |columnCorrelation (A i) (B i)| ≤
                (1 + (2 * lambda + lambda ^ 2) * mu) /
                  (1 + lambda ^ 2 - 2 * lambda * mu)) ∧
            (∀ ⦃i j : Fin m⦄, i ≠ j →
              (lambda ^ 2 - (1 + 2 * lambda) * mu) /
                  (1 + lambda ^ 2 + 2 * lambda * mu) ≤
                columnCorrelation (A i) (A j)) ∧
            (∀ ⦃i j : Fin m⦄, i ≠ j →
              (lambda ^ 2 - (1 + 2 * lambda) * mu) /
                  (1 + lambda ^ 2 + 2 * lambda * mu) ≤
                columnCorrelation (B i) (B j)) := by
  refine ⟨paper_rademacher_incoherent_dimension (m + 2) mu, ?_, ?_⟩
  · exact
      paper_rademacher_incoherent_dimension_real_bigO_envelope
        (m := m + 2) (mu := mu) (by omega) hmu
  · exact
      paper_geometry1_exists_constructed_matrices_explicit_finite
        (m := m) (k := k) (epsilon := epsilon)
        (lambda := lambda) (mu := mu)
        hlambda hmu hbound hs hnum

/--
Geometry Proposition 1 in its direct source-parameter form.  The construction
uses `lambda = sqrt(1 / delta - 1)` and an explicit conservative
`mu(epsilon, delta, k)` schedule.  Its finite row bound is the Rademacher
logarithmic envelope, while the two envelope errors tend to zero as `k` grows.
-/
theorem paper_geometry1_source_constructed_rate
    {epsilon delta : ℝ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) :
    AppliedModelingLib.Math.TendsToZero
      (fun k =>
        geometry1SelfCorrelationEnvelope
          (geometry1SourceLambda delta) (geometry1SourceMu epsilon delta k) - delta) ∧
      AppliedModelingLib.Math.TendsToZero
        (fun k =>
          (1 - delta) - geometry1OffdiagCorrelationEnvelope
            (geometry1SourceLambda delta) (geometry1SourceMu epsilon delta k)) ∧
      ∀ m k : ℕ, ∃ D : ℕ,
        (D : ℝ) ≤
            geometry1SourceDimensionCoefficient epsilon delta *
              ((k + 1 : ℕ) : ℝ) ^ 2 *
              Real.log (2 * ((m + 2 : ℕ) : ℝ) ^ 2) + 2 ∧
          ∃ A B : paper_feature_matrix m D,
            linearRecoveryCondition A B k epsilon ∧
              (∀ i : Fin m,
                |columnCorrelation (A i) (B i)| ≤
                  geometry1SelfCorrelationEnvelope
                    (geometry1SourceLambda delta) (geometry1SourceMu epsilon delta k)) ∧
              (∀ ⦃i j : Fin m⦄, i ≠ j →
                geometry1OffdiagCorrelationEnvelope
                  (geometry1SourceLambda delta) (geometry1SourceMu epsilon delta k) ≤
                  columnCorrelation (A i) (A j)) ∧
              (∀ ⦃i j : Fin m⦄, i ≠ j →
                geometry1OffdiagCorrelationEnvelope
                  (geometry1SourceLambda delta) (geometry1SourceMu epsilon delta k) ≤
                  columnCorrelation (B i) (B j)) := by
  rcases geometry1Source_correlation_errors_tendToZero hdelta_pos hdelta_lt_one with
    ⟨hself, hoff⟩
  refine ⟨hself, hoff, ?_⟩
  intro m k
  exact exists_geometry1_source_parameter_construction
    (m := m) (k := k) hepsilon_pos hepsilon_lt_one hdelta_pos hdelta_lt_one

/--
Geometry Proposition 1 limiting-error envelopes: as the incoherence parameter
used in the finite construction tends to zero, the same-feature upper envelope
converges to `1 / (1 + lambda^2)` and the different-feature lower envelope
converges to `lambda^2 / (1 + lambda^2)`.

Source status: formal `o(1)` packaging for the three finite Geometry
Proposition 1 correlation bounds.  With the source choice
`delta = 1 / (1 + lambda^2)`, these are exactly the displayed
`delta + o(1)` and `1 - delta - o(1)` limits.
-/
theorem paper_geometry1_correlation_envelope_errors_tend_to_zero
    {lambda : ℝ} {mu : ℕ → ℝ}
    (hmu : AppliedModelingLib.Math.TendsToZero mu) :
    AppliedModelingLib.Math.TendsToZero
        (fun n =>
          geometry1SelfCorrelationEnvelope lambda (mu n) -
            1 / (1 + lambda ^ 2)) ∧
      AppliedModelingLib.Math.TendsToZero
        (fun n =>
          lambda ^ 2 / (1 + lambda ^ 2) -
            geometry1OffdiagCorrelationEnvelope lambda (mu n)) :=
  ⟨geometry1SelfCorrelationError_tendsToZero_of_mu_tendsToZero hmu,
    geometry1OffdiagCorrelationError_tendsToZero_of_mu_tendsToZero hmu⟩

/--
Geometry Proposition 1(i), finite construction core: the normalized
representation/probe directions for the same feature have explicitly bounded
correlation.

Source status: proved finite bound from the source construction. The
`delta + o(1)` paper statement is packaged by
`paper_geometry1_correlation_envelope_errors_tend_to_zero` after using the
source relation `delta = 1 / (1 + lambda^2)`.
-/
theorem paper_geometry1_self_column_correlation_abs_bound
    {m d : ℕ} {lambda mu : ℝ}
    {C : Fin (m + 2) → ColumnVector d}
    (hlambda : 0 ≤ lambda) (hC : muIncoherent C mu)
    (hs : 0 < 1 + lambda ^ 2 - 2 * lambda * mu) (i : Fin m) :
    |columnCorrelation
        (geometry1RepresentationMatrix C lambda i)
        (geometry1ProbeMatrix C lambda i)| ≤
      (1 + (2 * lambda + lambda ^ 2) * mu) /
        (1 + lambda ^ 2 - 2 * lambda * mu) :=
  geometry1_self_columnCorrelation_abs_le hlambda hC hs i

/--
Geometry Proposition 1(ii), finite construction core: different constructed
representation directions have explicitly lower-bounded normalized correlation.

Source status: proved finite bound from the source construction. The
`1 - delta - o(1)` paper statement is packaged by
`paper_geometry1_correlation_envelope_errors_tend_to_zero` after using the
source relation `1 - delta = lambda^2 / (1 + lambda^2)`.
-/
theorem paper_geometry1_representation_column_correlation_lower_bound
    {m d : ℕ} {lambda mu : ℝ}
    {C : Fin (m + 2) → ColumnVector d}
    (hlambda : 0 ≤ lambda) (hmu : 0 ≤ mu) (hC : muIncoherent C mu)
    (hs : 0 < 1 + lambda ^ 2 - 2 * lambda * mu)
    (hnum : 0 ≤ lambda ^ 2 - (1 + 2 * lambda) * mu)
    {i j : Fin m} (hij : i ≠ j) :
    (lambda ^ 2 - (1 + 2 * lambda) * mu) /
        (1 + lambda ^ 2 + 2 * lambda * mu) ≤
      columnCorrelation
        (geometry1RepresentationMatrix C lambda i)
        (geometry1RepresentationMatrix C lambda j) :=
  geometry1_representation_columnCorrelation_lower
    hlambda hmu hC hs hnum hij

/--
Geometry Proposition 1(iii), finite construction core: different constructed
probe directions have explicitly lower-bounded normalized correlation.

Source status: proved finite bound from the source construction. The
`1 - delta - o(1)` paper statement is packaged by
`paper_geometry1_correlation_envelope_errors_tend_to_zero` after using the
source relation `1 - delta = lambda^2 / (1 + lambda^2)`.
-/
theorem paper_geometry1_probe_column_correlation_lower_bound
    {m d : ℕ} {lambda mu : ℝ}
    {C : Fin (m + 2) → ColumnVector d}
    (hlambda : 0 ≤ lambda) (hmu : 0 ≤ mu) (hC : muIncoherent C mu)
    (hs : 0 < 1 + lambda ^ 2 - 2 * lambda * mu)
    (hnum : 0 ≤ lambda ^ 2 - (1 + 2 * lambda) * mu)
    {i j : Fin m} (hij : i ≠ j) :
    (lambda ^ 2 - (1 + 2 * lambda) * mu) /
        (1 + lambda ^ 2 + 2 * lambda * mu) ≤
      columnCorrelation
        (geometry1ProbeMatrix C lambda i)
        (geometry1ProbeMatrix C lambda j) :=
  geometry1_probe_columnCorrelation_lower
    hlambda hmu hC hs hnum hij

/--
Euclidean norm of a representation/probe column.

Source status: exact source notation `||a_i||` and `||b_i||`.
-/
noncomputable abbrev paper_column_norm {d : ℕ}
    (x : ColumnVector d) : ℝ :=
  columnNorm x

/--
Correlation of unit-normalized representation/probe columns.

Source status: exact source notation
`<x / ||x||, y / ||y||>` with zero vectors normalized to zero. Under the
geometry proposition hypotheses the relevant columns are proved nonzero.
-/
noncomputable abbrev paper_column_correlation {d : ℕ}
    (x y : ColumnVector d) : ℝ :=
  columnCorrelation x y

/--
Geometry Proposition 2(i), finite deterministic form: bounded norms and
linear recovery force each feature's representation and probe directions to be
aligned.

Source status: proved finite source statement.
-/
theorem paper_geometry2_self_column_correlation_lower
    {m d k : ℕ} {epsilon gamma : ℝ} {A B : paper_feature_matrix m d}
    (hk : 1 ≤ k) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma_one : 1 ≤ gamma)
    (hrec : linearRecoveryCondition A B k epsilon)
    (hAnorm : ∀ i : Fin m, paper_column_norm (A i) ≤ gamma)
    (hBnorm : ∀ i : Fin m, paper_column_norm (B i) ≤ gamma)
    (i : Fin m) :
    (1 - epsilon) / gamma ^ 2 <
      paper_column_correlation (B i) (A i) :=
  geometry2_self_columnCorrelation_lower
    hk hepsilon_lt_one (by linarith) hrec hAnorm hBnorm i

/--
Geometry Proposition 2(ii), finite deterministic corrected form: bounded norms
and linear recovery upper-bound same-family representation correlations.

Source status: corrected finite statement. The printed proposition has
denominator `1 - epsilon` in the first term; the proof and norm hypotheses
yield `(1 - epsilon)^2`.
-/
theorem paper_geometry2_representation_column_correlation_upper_corrected
    {m d k : ℕ} {epsilon gamma : ℝ} {A B : paper_feature_matrix m d}
    (hk : 1 ≤ k) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma_one : 1 ≤ gamma)
    (hrec : linearRecoveryCondition A B k epsilon)
    (hAnorm : ∀ i : Fin m, paper_column_norm (A i) ≤ gamma)
    (hBnorm : ∀ i : Fin m, paper_column_norm (B i) ≤ gamma)
    {i j : Fin m} (hij : i ≠ j) :
    paper_column_correlation (A i) (A j) ≤
      epsilon * gamma ^ 2 / (1 - epsilon) ^ 2 +
        Real.sqrt (1 - ((1 - epsilon) / gamma ^ 2) ^ 2) :=
  geometry2_representation_columnCorrelation_le
    hk hepsilon_pos hepsilon_lt_one (by linarith) hrec hAnorm hBnorm hij

/--
Geometry Proposition 2(iii), finite deterministic corrected form: bounded
norms and linear recovery upper-bound same-family probe correlations.

Source status: corrected finite statement. The printed proposition has
denominator `1 - epsilon` in the first term; the proof and norm hypotheses
yield `(1 - epsilon)^2`.
-/
theorem paper_geometry2_probe_column_correlation_upper_corrected
    {m d k : ℕ} {epsilon gamma : ℝ} {A B : paper_feature_matrix m d}
    (hk : 1 ≤ k) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma_one : 1 ≤ gamma)
    (hrec : linearRecoveryCondition A B k epsilon)
    (hAnorm : ∀ i : Fin m, paper_column_norm (A i) ≤ gamma)
    (hBnorm : ∀ i : Fin m, paper_column_norm (B i) ≤ gamma)
    {i j : Fin m} (hij : i ≠ j) :
    paper_column_correlation (B i) (B j) ≤
      epsilon * gamma ^ 2 / (1 - epsilon) ^ 2 +
        Real.sqrt (1 - ((1 - epsilon) / gamma ^ 2) ^ 2) :=
  geometry2_probe_columnCorrelation_le
    hk hepsilon_pos hepsilon_lt_one (by linarith) hrec hAnorm hBnorm hij

/--
Theorem `thm:threshold`, finite proof spine: after the source diagonal
normalization step, the explicit symmetric-power obstruction and Turán
contradict Boolean threshold separation.

Source status: finite source proof chain is proved. The remaining paper-facing
work is the asymptotic `Omega` packaging.  The symmetric-power coordinate
count is written by the factorial-normalized envelope
`(2d + power - 1)^power / power!`, and the source subset size is written
directly in the displayed finite arithmetic.
-/
theorem paper_threshold_finite_rank_turan_contradiction
    {m d s k q power : ℕ} {eta : ℝ}
    {A B : paper_feature_matrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (heta : 0 ≤ eta) (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hsmall : (s : ℝ) * eta ^ (2 * power) ≤ 1)
    (hdim :
      2 * ((((2 * d + power - 1) ^ power : ℕ) : ℝ) /
        (power.factorial : ℝ)) < (s : ℝ))
    (hunit : 1 ≤ (q : ℝ) * eta)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) +
            (m % r).choose 2))) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_dimension_turan_normalized_factorial_card
    hk_one hsep heta hsmall hdim hq hqk hunit hs havg

/--
Theorem `thm:threshold`, source-threshold finite proof spine with
`eta = 1/q`.

Source status: finite source proof chain is proved after the paper's threshold
substitution. The remaining paper-facing work is the asymptotic `Omega`
packaging.  The symmetric-power coordinate count and source subset size are
written through the factorial-normalized envelope
`(2d + power - 1)^power / power!`.
-/
theorem paper_threshold_source_eta_finite_rank_turan_contradiction
    {m d s k q power : ℕ}
    {A B : paper_feature_matrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hsmall : (s : ℝ) * (1 / (q : ℝ)) ^ (2 * power) ≤ 1)
    (hdim :
      2 * ((((2 * d + power - 1) ^ power : ℕ) : ℝ) /
        (power.factorial : ℝ)) < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) +
            (m % r).choose 2))) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_factorial_card
    hk_one hsep hsmall hdim hq hqk hs havg

/--
Theorem `thm:threshold`, source-threshold finite proof spine with the
paper-readable smallness premise `s <= q^(2*power)`.

Source status: finite source proof chain after the paper's threshold
substitution. This removes the reciprocal-power normalization premise from the
interface; the remaining paper-facing work is the asymptotic `Omega`
packaging for the dimension/Turán arithmetic.
-/
theorem paper_threshold_source_eta_finite_rank_turan_contradiction_of_s_le_q_pow
    {m d s k q power : ℕ}
    {A B : paper_feature_matrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hs_le : (s : ℝ) ≤ (q : ℝ) ^ (2 * power))
    (hdim :
      2 * ((((2 * d + power - 1) ^ power : ℕ) : ℝ) /
        (power.factorial : ℝ)) < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) +
            (m % r).choose 2))) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_factorial_card_of_s_le_q_pow
    hk_one hsep hs_le hdim hq hqk hs havg

/--
Theorem `thm:threshold`, source-threshold finite proof spine with both the
paper-readable smallness premise `s <= q^(2*power)` and the Stirling-style
dimension envelope `2*(e*(2d+power-1)/power)^power < s`.

Source status: finite source proof chain after the paper's threshold
substitution. This removes the reciprocal-power and factorial-normalized
count premises from the interface; the remaining paper-facing work is the
asymptotic `Omega` packaging for the Turán arithmetic and parameter choices.
-/
theorem paper_threshold_source_eta_finite_rank_turan_contradiction_exp_card
    {m d s k q power : ℕ}
    {A B : paper_feature_matrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hs_le : (s : ℝ) ≤ (q : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) +
            (m % r).choose 2))) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_q_pow
    hk_one hsep hs_le hpower hdim hq hqk hs havg

/--
Theorem `thm:threshold`, source-threshold finite proof spine using the
source's coarse Turán estimate `m^2/(2r)-m/2`.

Source status: finite source proof chain after the paper's threshold
substitution. This row uses the source-readable smallness premise, the
Stirling-style symmetric-power count, and the paper's coarse Turán arithmetic.
The remaining paper-facing work is the asymptotic `Omega` packaging and
parameter selection.
-/
theorem paper_threshold_source_eta_finite_rank_turan_contradiction_exp_card_coarse_turan
    {m d s k q power : ℕ}
    {A B : paper_feature_matrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hs_le : (s : ℝ) ≤ (q : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 1 < s)
    (havg :
      (m : ℝ) * ((2 * q : ℕ) : ℝ) <
        (m : ℝ) ^ 2 / (2 * ((s - 1 : ℕ) : ℝ)) - (m : ℝ) / 2) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_q_pow_coarse_turan
    hk_one hsep hs_le hpower hdim hq hqk hs havg

/--
Theorem `thm:threshold`, source-threshold finite proof spine using the source
Turán parameter inequality `(4q+1)(s-1) < m`.

Source status: finite source proof chain after the paper's threshold
substitution. The remaining paper-facing work is the asymptotic `Omega`
packaging and eventual parameter selection.
-/
theorem paper_threshold_source_eta_finite_rank_turan_contradiction_exp_card_source_turan
    {m d s k q power : ℕ}
    {A B : paper_feature_matrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hs_le : (s : ℝ) ≤ (q : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 1 < s)
    (hm : 0 < m)
    (hturan : (((4 * q + 1 : ℕ) : ℝ) * ((s - 1 : ℕ) : ℝ)) < (m : ℝ)) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_q_pow_source_turan
    hk_one hsep hs_le hpower hdim hq hqk hs hm hturan

/--
Theorem `thm:threshold`, source-threshold finite proof spine with the
auxiliary denominator specialized to `k - 1`.

Source status: finite source proof chain with the non-source `q` parameter
removed from the theorem surface. The remaining paper-facing work is the
asymptotic `Omega` parameter selection for `s` and `power`.
-/
theorem paper_threshold_source_eta_finite_rank_turan_contradiction_exp_card_k_pred_source_turan
    {m d s k power : ℕ}
    {A B : paper_feature_matrix m d} {threshold : Fin m → ℝ}
    (hk_two : 2 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hs_le : (s : ℝ) ≤ ((k - 1 : ℕ) : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hs : 1 < s)
    (hm : 0 < m)
    (hturan :
      (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((s - 1 : ℕ) : ℝ)) < (m : ℝ)) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_k_pred_pow_source_turan
    hk_two hsep hs_le hpower hdim hs hm hturan

/--
Theorem `thm:threshold`, source-threshold finite proof spine with
`q = k - 1` and `s = floor(m/(4(k-1)+1))`.

Source status: finite source proof chain with both auxiliary counting
parameters internalized except for the logarithmic power choice. The remaining
paper-facing work is the asymptotic `Omega` dimension arithmetic.
-/
theorem paper_threshold_source_eta_finite_rank_turan_contradiction_exp_card_k_pred_floor_turan
    {m d k power : ℕ}
    {A B : paper_feature_matrix m d} {threshold : Fin m → ℝ}
    (hk_two : 2 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hs_le :
      let s := Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ))
      (s : ℝ) ≤ ((k - 1 : ℕ) : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      let s := Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ))
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hs :
      1 < Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ)))
    (hm : 0 < m) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_k_pred_pow_floor_turan
    hk_two hsep hs_le hpower hdim hs hm

/--
Theorem `thm:threshold`, finite proof spine with the source Turán subset
choice and the logarithmic power selector both internalized.

Source status: finite source proof chain with `s = floor(m/(4(k-1)+1))`
and `power = ceil(log s / (2 log(k-1)))`. The remaining paper-facing work is
the source-scale dimension arithmetic that makes the displayed `hdim`
inequality follow from an asymptotic lower bound on `d`.
-/
theorem paper_threshold_source_eta_finite_rank_turan_contradiction_exp_card_ceil_power_floor_turan
    {m d k : ℕ}
    {A B : paper_feature_matrix m d} {threshold : Fin m → ℝ}
    (hk_three : 3 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hdim :
      let s := Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ))
      let power :=
        Nat.ceil (Real.log (s : ℝ) /
          (2 * Real.log (((k - 1 : ℕ) : ℝ))))
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hs :
      1 < Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ)))
    (hm : 0 < m) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_ceil_power_floor_turan
    hk_three hsep hdim hs hm

/--
Theorem `thm:threshold`, selected finite lower-bound contradiction with the
source proof's finite size condition made explicit.

Source status: corrected finite source proof chain. The source proof takes
`r = m/(4k+1)` and applies the rank obstruction at threshold `1/k`, which
requires the selected Turán subset size to dominate `(k-1)^2`. Lean therefore
proves the finite theorem under `(4(k-1)+1)(k-1)^2 < m`, the condition used by
the proof and stronger than the printed `k < sqrt(m)` premise.
-/
theorem paper_threshold_source_eta_finite_rank_turan_contradiction_exp_card_floor_log_power_candidate_source_size
    {m d k : ℕ}
    {A B : paper_feature_matrix m d} {threshold : Fin m → ℝ}
    (hk_three : 3 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hsize :
      (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2) <
        (m : ℝ))
    (hD :
      let q := k - 1
      let s0 := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
      let power := Nat.floor (Real.log (s0 : ℝ) /
        (2 * Real.log ((q : ℝ))))
      (d : ℝ) ≤ (1 / (16 * Real.exp 1)) * (power : ℝ) * (q : ℝ) ^ 2)
    (hq_large :
      Real.exp 1 ≤ (1 / 8) * ((k - 1 : ℕ) : ℝ) ^ 2) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_floor_log_power_candidate_source_size
    hk_three hsep hsize hD hq_large

/--
Theorem `thm:threshold`, minimum-dimension finite lower-bound form under the
corrected finite size premise.

Source status: corrected finite source conclusion for the minimum threshold
separation dimension. The source proof's printed `k < sqrt(m)` condition is
replaced by the stronger finite condition actually needed by the rank/Turan
argument, `(4(k-1)+1)(k-1)^2 < m`.
-/
theorem paper_threshold_separation_dimension_value_real_gt_floor_log_power_candidate_source_size
    {m k dmin : ℕ}
    (hk_three : 3 ≤ k)
    (hsize :
      (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2) <
        (m : ℝ))
    (hq_large :
      Real.exp 1 ≤ (1 / 8) * ((k - 1 : ℕ) : ℝ) ^ 2)
    (hvalue : paper_threshold_separation_dimension_value m k dmin) :
    let q := k - 1
    let s0 := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
    let power := Nat.floor (Real.log (s0 : ℝ) /
      (2 * Real.log ((q : ℝ))))
    (1 / (16 * Real.exp 1)) * (power : ℝ) * (q : ℝ) ^ 2 <
      (dmin : ℝ) :=
  thresholdSeparationDimensionValue_real_gt_floor_log_power_candidate_source_size
    hk_three hsize hq_large hvalue

/--
Theorem `thm:threshold`, corrected-regime asymptotic form: along the finite
regime actually needed by the source rank/Turán proof, the floor-log
threshold scale is Big-O of the minimum threshold-separating dimension.

Source status: corrected finite source conclusion with Landau packaging.  This
keeps the documented finite size correction rather than the printed
`k < sqrt(m)` premise.
-/
theorem paper_threshold_separation_dimension_isBigO_lower_floor_log_corrected_regime :
    Asymptotics.IsBigO
      thresholdActivationCorrectedSourceFilter
      thresholdActivationLowerFloorLogScale
      (fun p : ℕ × ℕ =>
        (thresholdSeparationDimension p.1 p.2 : ℝ)) :=
  thresholdSeparationDimension_isBigO_lower_floor_log_corrected_regime

/--
Theorem `thm:threshold`, corrected-regime source-scale asymptotic form: along
the finite regime actually needed by the source rank/Turán proof, the printed
scale `(k^2 / log k) log(m/k)` is Big-O of the minimum
threshold-separating dimension.

Source status: corrected source-scale Landau conclusion.  This keeps the
documented finite size correction rather than the printed `k < sqrt(m)`
premise.
-/
theorem paper_threshold_separation_dimension_isBigO_lower_source_log_corrected_regime :
    Asymptotics.IsBigO
      thresholdActivationCorrectedSourceFilter
      thresholdActivationLowerSourceLogScale
      (fun p : ℕ × ℕ =>
        (thresholdSeparationDimension p.1 p.2 : ℝ)) :=
  thresholdSeparationDimension_isBigO_lower_source_log_corrected_regime

/--
Theorem `thm:threshold` in the original printed regime `k < sqrt(m)`: the
printed scale `(k^2 / log k) log(m/k)` is Big-O of the minimum
threshold-separating dimension.

Source status: exact source-scale Landau conclusion.  The proof combines the
paper's Alon--Turan branch with a complementary trace/Frobenius bound for the
intermediate finite range.
-/
theorem paper_threshold_separation_dimension_isBigO_lower_source_log_original_regime :
    Asymptotics.IsBigO
      thresholdActivationOriginalSourceFilter
      thresholdActivationLowerSourceLogScale
      (fun p : ℕ × ℕ =>
        (thresholdSeparationDimension p.1 p.2 : ℝ)) :=
  thresholdSeparationDimension_isBigO_lower_source_log_original_regime

/--
Corollary `cor:activation-bias`, finite proof spine: a monotone activation and
bias separator yields the threshold separator, so the finite threshold
rank/Turán contradiction applies.

Source status: finite source proof chain is proved. The remaining paper-facing
work is the asymptotic `Omega` packaging.  The symmetric-power coordinate
count is written by the factorial-normalized envelope
`(2d + power - 1)^power / power!`, and the source subset size is written
directly in the displayed finite arithmetic.
-/
theorem paper_activation_bias_finite_rank_turan_contradiction
    {m d s k q power : ℕ} {eta : ℝ}
    {A W : paper_feature_matrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (heta : 0 ≤ eta) (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hsmall : (s : ℝ) * eta ^ (2 * power) ≤ 1)
    (hdim :
      2 * ((((2 * d + power - 1) ^ power : ℕ) : ℝ) /
        (power.factorial : ℝ)) < (s : ℝ))
    (hunit : 1 ≤ (q : ℝ) * eta)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) +
            (m % r).choose 2))) :
    False :=
  false_of_activationSeparationCondition_and_symmetricPower_dimension_turan_factorial_card
    hk_one hmono hact heta hsmall hdim hq hqk hunit hs havg

/--
Corollary `cor:activation-bias`, source-threshold finite proof spine with
`eta = 1/q`.

Source status: finite source proof chain is proved after the paper's threshold
substitution. The remaining paper-facing work is the asymptotic `Omega`
packaging.  The symmetric-power coordinate count and source subset size are
written through the factorial-normalized envelope
`(2d + power - 1)^power / power!`.
-/
theorem paper_activation_bias_source_eta_finite_rank_turan_contradiction
    {m d s k q power : ℕ}
    {A W : paper_feature_matrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hsmall : (s : ℝ) * (1 / (q : ℝ)) ^ (2 * power) ≤ 1)
    (hdim :
      2 * ((((2 * d + power - 1) ^ power : ℕ) : ℝ) /
        (power.factorial : ℝ)) < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) +
            (m % r).choose 2))) :
    False :=
  false_of_activationSeparationCondition_and_symmetricPower_source_eta_factorial_card
    hk_one hmono hact hsmall hdim hq hqk hs havg

/--
Corollary `cor:activation-bias`, source-threshold finite proof spine with the
paper-readable smallness premise `s <= q^(2*power)`.

Source status: finite source proof chain after reducing monotone activation
separation to threshold separation. This removes the reciprocal-power
normalization premise from the interface; the remaining paper-facing work is
the asymptotic `Omega` packaging for the dimension/Turán arithmetic.
-/
theorem paper_activation_bias_source_eta_finite_rank_turan_contradiction_of_s_le_q_pow
    {m d s k q power : ℕ}
    {A W : paper_feature_matrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hs_le : (s : ℝ) ≤ (q : ℝ) ^ (2 * power))
    (hdim :
      2 * ((((2 * d + power - 1) ^ power : ℕ) : ℝ) /
        (power.factorial : ℝ)) < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) +
            (m % r).choose 2))) :
    False :=
  false_of_activationSeparationCondition_and_symmetricPower_source_eta_factorial_card_of_s_le_q_pow
    hk_one hmono hact hs_le hdim hq hqk hs havg

/--
Corollary `cor:activation-bias`, source-threshold finite proof spine with both
the paper-readable smallness premise `s <= q^(2*power)` and the
Stirling-style dimension envelope
`2*(e*(2d+power-1)/power)^power < s`.

Source status: finite source proof chain after reducing monotone activation
separation to threshold separation. This removes the reciprocal-power and
factorial-normalized count premises from the interface; the remaining
paper-facing work is the asymptotic `Omega` packaging for the Turán arithmetic
and parameter choices.
-/
theorem paper_activation_bias_source_eta_finite_rank_turan_contradiction_exp_card
    {m d s k q power : ℕ}
    {A W : paper_feature_matrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hs_le : (s : ℝ) ≤ (q : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) +
            (m % r).choose 2))) :
    False :=
  false_of_activationSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_q_pow
    hk_one hmono hact hs_le hpower hdim hq hqk hs havg

/--
Corollary `cor:activation-bias`, finite proof spine using the source's coarse
Turán estimate `m^2/(2r)-m/2`.

Source status: finite source proof chain after reducing monotone activation
separation to threshold separation. This row uses the source-readable
smallness premise, the Stirling-style symmetric-power count, and the paper's
coarse Turán arithmetic. The remaining paper-facing work is the asymptotic
`Omega` packaging and parameter selection.
-/
theorem paper_activation_bias_source_eta_finite_rank_turan_contradiction_exp_card_coarse_turan
    {m d s k q power : ℕ}
    {A W : paper_feature_matrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hs_le : (s : ℝ) ≤ (q : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 1 < s)
    (havg :
      (m : ℝ) * ((2 * q : ℕ) : ℝ) <
        (m : ℝ) ^ 2 / (2 * ((s - 1 : ℕ) : ℝ)) - (m : ℝ) / 2) :
    False :=
  false_of_activationSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_q_pow_coarse_turan
    hk_one hmono hact hs_le hpower hdim hq hqk hs havg

/--
Corollary `cor:activation-bias`, finite proof spine using the source Turán
parameter inequality `(4q+1)(s-1) < m`.

Source status: finite source proof chain after reducing monotone activation
separation to threshold separation. The remaining paper-facing work is the
asymptotic `Omega` packaging and eventual parameter selection.
-/
theorem paper_activation_bias_source_eta_finite_rank_turan_contradiction_exp_card_source_turan
    {m d s k q power : ℕ}
    {A W : paper_feature_matrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hs_le : (s : ℝ) ≤ (q : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 1 < s)
    (hm : 0 < m)
    (hturan : (((4 * q + 1 : ℕ) : ℝ) * ((s - 1 : ℕ) : ℝ)) < (m : ℝ)) :
    False :=
  false_of_activationSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_q_pow_source_turan
    hk_one hmono hact hs_le hpower hdim hq hqk hs hm hturan

/--
Corollary `cor:activation-bias`, finite proof spine with the auxiliary
denominator specialized to `k - 1`.

Source status: finite source proof chain after reducing monotone activation
separation to threshold separation, with the non-source `q` parameter removed
from the theorem surface. The remaining paper-facing work is the asymptotic
`Omega` parameter selection for `s` and `power`.
-/
theorem paper_activation_bias_source_eta_finite_rank_turan_contradiction_exp_card_k_pred_source_turan
    {m d s k power : ℕ}
    {A W : paper_feature_matrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_two : 2 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hs_le : (s : ℝ) ≤ ((k - 1 : ℕ) : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hs : 1 < s)
    (hm : 0 < m)
    (hturan :
      (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((s - 1 : ℕ) : ℝ)) < (m : ℝ)) :
    False :=
  false_of_activationSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_k_pred_pow_source_turan
    hk_two hmono hact hs_le hpower hdim hs hm hturan

/--
Corollary `cor:activation-bias`, finite proof spine with `q = k - 1` and
`s = floor(m/(4(k-1)+1))`.

Source status: finite source proof chain after reducing activation/bias
separation to threshold separation, with auxiliary counting parameters
internalized except for the logarithmic power choice. The remaining
paper-facing work is the asymptotic `Omega` dimension arithmetic.
-/
theorem paper_activation_bias_source_eta_finite_rank_turan_contradiction_exp_card_k_pred_floor_turan
    {m d k power : ℕ}
    {A W : paper_feature_matrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_two : 2 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hs_le :
      let s := Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ))
      (s : ℝ) ≤ ((k - 1 : ℕ) : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      let s := Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ))
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hs :
      1 < Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ)))
    (hm : 0 < m) :
    False :=
  false_of_activationSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_k_pred_pow_floor_turan
    hk_two hmono hact hs_le hpower hdim hs hm

/--
Corollary `cor:activation-bias`, finite proof spine with the same source
Turán subset and logarithmic power choices as the threshold theorem.

Source status: finite source proof chain after reducing activation/bias
separation to threshold separation. The remaining paper-facing work is the
same source-scale dimension arithmetic as in `thm:threshold`.
-/
theorem paper_activation_bias_source_eta_finite_rank_turan_contradiction_exp_card_ceil_power_floor_turan
    {m d k : ℕ}
    {A W : paper_feature_matrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_three : 3 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hdim :
      let s := Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ))
      let power :=
        Nat.ceil (Real.log (s : ℝ) /
          (2 * Real.log (((k - 1 : ℕ) : ℝ))))
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hs :
      1 < Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ)))
    (hm : 0 < m) :
    False :=
  false_of_activationSeparationCondition_and_symmetricPower_source_eta_exp_card_ceil_power_floor_turan
    hk_three hmono hact hdim hs hm

/--
Corollary `cor:activation-bias`, selected finite lower-bound contradiction
with the source proof's finite size condition made explicit.

Source status: corrected finite source proof chain, reducing monotone
activation separation to threshold separation. The same finite size correction
as Theorem `thm:threshold` is required by the source proof.
-/
theorem paper_activation_bias_source_eta_finite_rank_turan_contradiction_exp_card_floor_log_power_candidate_source_size
    {m d k : ℕ}
    {A W : paper_feature_matrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_three : 3 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hsize :
      (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2) <
        (m : ℝ))
    (hD :
      let q := k - 1
      let s0 := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
      let power := Nat.floor (Real.log (s0 : ℝ) /
        (2 * Real.log ((q : ℝ))))
      (d : ℝ) ≤ (1 / (16 * Real.exp 1)) * (power : ℝ) * (q : ℝ) ^ 2)
    (hq_large :
      Real.exp 1 ≤ (1 / 8) * ((k - 1 : ℕ) : ℝ) ^ 2) :
    False :=
  false_of_activationSeparationCondition_and_symmetricPower_source_eta_exp_card_floor_log_power_candidate_source_size
    hk_three hmono hact hsize hD hq_large

/--
Corollary `cor:activation-bias`, minimum-dimension finite lower-bound form
under the corrected finite size premise.

Source status: corrected finite source conclusion for the minimum
activation/bias separation dimension. It reduces monotone activation/bias
separation to threshold separation and inherits the same finite size correction
as Theorem `thm:threshold`.
-/
theorem paper_activation_separation_dimension_value_real_gt_floor_log_power_candidate_source_size
    {m k dmin : ℕ}
    (hk_three : 3 ≤ k)
    (hsize :
      (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2) <
        (m : ℝ))
    (hq_large :
      Real.exp 1 ≤ (1 / 8) * ((k - 1 : ℕ) : ℝ) ^ 2)
    (hvalue : paper_activation_separation_dimension_value m k dmin) :
    let q := k - 1
    let s0 := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
    let power := Nat.floor (Real.log (s0 : ℝ) /
      (2 * Real.log ((q : ℝ))))
    (1 / (16 * Real.exp 1)) * (power : ℝ) * (q : ℝ) ^ 2 <
      (dmin : ℝ) :=
  activationSeparationDimensionValue_real_gt_floor_log_power_candidate_source_size
    hk_three hsize hq_large hvalue

/--
Corollary `cor:activation-bias`, corrected-regime asymptotic form: along the
finite regime actually needed by the source rank/Turán proof, the floor-log
threshold scale is Big-O of the minimum activation/bias-separating dimension.

Source status: corrected finite source conclusion with Landau packaging,
inherited by reducing monotone activation/bias separation to threshold
separation.
-/
theorem paper_activation_separation_dimension_isBigO_lower_floor_log_corrected_regime :
    Asymptotics.IsBigO
      thresholdActivationCorrectedSourceFilter
      thresholdActivationLowerFloorLogScale
      (fun p : ℕ × ℕ =>
        (activationSeparationDimension p.1 p.2 : ℝ)) :=
  activationSeparationDimension_isBigO_lower_floor_log_corrected_regime

/--
Corollary `cor:activation-bias`, corrected-regime source-scale asymptotic
form: along the finite regime actually needed by the source rank/Turán proof,
the printed scale `(k^2 / log k) log(m/k)` is Big-O of the minimum
activation/bias-separating dimension.

Source status: corrected source-scale Landau conclusion, inherited by reducing
monotone activation/bias separation to threshold separation.
-/
theorem paper_activation_separation_dimension_isBigO_lower_source_log_corrected_regime :
    Asymptotics.IsBigO
      thresholdActivationCorrectedSourceFilter
      thresholdActivationLowerSourceLogScale
      (fun p : ℕ × ℕ =>
        (activationSeparationDimension p.1 p.2 : ℝ)) :=
  activationSeparationDimension_isBigO_lower_source_log_corrected_regime

/--
Corollary `cor:activation-bias` in the original printed regime and source
scale.

Source status: exact source-scale Landau conclusion, inherited through the
proved monotone activation-to-threshold reduction and the two-regime threshold
bound.
-/
theorem paper_activation_separation_dimension_isBigO_lower_source_log_original_regime :
    Asymptotics.IsBigO
      thresholdActivationOriginalSourceFilter
      thresholdActivationLowerSourceLogScale
      (fun p : ℕ × ℕ =>
        (activationSeparationDimension p.1 p.2 : ℝ)) :=
  activationSeparationDimension_isBigO_lower_source_log_original_regime

/-!
## Transparent source-review specifications

Each declaration below is the exact `Prop` reviewed against a pinned source
claim.  The accompanying proof endpoint is kept separate so that source
review never relies on a theorem name or an opaque proof wrapper.
-/

def paper_compressed_sensing_external_basis_pursuitSpec : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ m k : ℕ, 1 ≤ k → 2 * k ≤ m →
      ∃ d : ℕ, ∃ A : paper_feature_matrix m d,
        (d : ℝ) ≤ C * (k : ℝ) * Real.log ((m : ℝ) / (k : ℝ)) ∧
          paper_basis_pursuit_exact_recovery A k

theorem paper_compressed_sensing_external_basis_pursuitSpec_proof :
    paper_compressed_sensing_external_basis_pursuitSpec :=
  paper_compressed_sensing_external_basis_pursuit

/-- Source Lemma `lem:alon`, quoted from Alon (2003), Theorem 9.3. -/
def paper_alon_normalized_rank_bound_externalSpec : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (D : Matrix ι ι ℝ) {epsilon : ℝ},
      1 / Real.sqrt (Fintype.card ι : ℝ) < epsilon →
      epsilon < 1 / 2 →
      (∀ i, D i i = 1) →
      (∀ ⦃i j⦄, i ≠ j → |D i j| < epsilon) →
      alonNormalizedRankBound (Fintype.card ι) epsilon c ≤ (D.rank : ℝ)

theorem paper_alon_normalized_rank_bound_externalSpec_proof :
    paper_alon_normalized_rank_bound_externalSpec := by
  rcases assumption_alon_normalized_rank_bound with ⟨c, hc, hbound⟩
  refine ⟨c, hc, ?_⟩
  intro ι _ _ D epsilon hepsilon_low hepsilon_high hdiag hoff
  exact hbound D hepsilon_low hepsilon_high hdiag hoff

/-- Source Corollary `lem:rank`, obtained by row-normalizing Lemma `lem:alon`. -/
def paper_alon_scaled_rank_corollarySpec : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (C : Matrix ι ι ℝ) {gamma eta : ℝ},
      0 < gamma →
      gamma ≤ 1 →
      gamma / Real.sqrt (Fintype.card ι : ℝ) < eta →
      eta < gamma / 2 →
      (∀ i, gamma ≤ C i i) →
      (∀ ⦃i j⦄, i ≠ j → |C i j| < eta) →
      alonScaledRankBound (Fintype.card ι) gamma eta c ≤ (C.rank : ℝ)

theorem paper_alon_scaled_rank_corollarySpec_proof :
    paper_alon_scaled_rank_corollarySpec := by
  rcases assumption_alon_normalized_rank_bound with ⟨c, hc, hnormalized⟩
  refine ⟨c, hc, ?_⟩
  intro ι _ _ C gamma eta hgamma_pos hgamma_le_one heta_low heta_high hdiag hoff
  exact scaledRankBound_of_strict_normalizedRankBound
    (c := c)
    (fun D {epsilon} hepsilon_low hepsilon_high hDdiag hDoff =>
      hnormalized D hepsilon_low hepsilon_high hDdiag hDoff)
    C hgamma_pos heta_low heta_high hdiag hoff

def paper_rademacher_incoherent_dimension_real_bigO_envelopeSpec
    {m : ℕ} {mu : ℝ} (hm : 2 ≤ m) (hmu : 0 < mu) : Prop :=
  (paper_rademacher_incoherent_dimension m mu : ℝ) ≤
    (2 / mu ^ 2) * Real.log (2 * (m : ℝ) ^ 2) + 2

theorem paper_rademacher_incoherent_dimension_real_bigO_envelopeSpec_proof
    {m : ℕ} {mu : ℝ} (hm : 2 ≤ m) (hmu : 0 < mu) :
    paper_rademacher_incoherent_dimension_real_bigO_envelopeSpec hm hmu :=
  paper_rademacher_incoherent_dimension_real_bigO_envelope hm hmu

def paper_rademacher_strict_incoherent_exists_source_rateSpec
    {m : ℕ} {mu : ℝ} (hm : 2 ≤ m) (hmu : 0 < mu) : Prop :=
  ∃ d : ℕ, ∃ A : paper_feature_matrix m d,
    (d : ℝ) ≤ (8 / mu ^ 2) * Real.log (2 * (m : ℝ) ^ 2) + 2 ∧
      paper_strict_mu_incoherent A mu

theorem paper_rademacher_strict_incoherent_exists_source_rateSpec_proof
    {m : ℕ} {mu : ℝ} (hm : 2 ≤ m) (hmu : 0 < mu) :
    paper_rademacher_strict_incoherent_exists_source_rateSpec hm hmu :=
  paper_rademacher_strict_incoherent_exists_source_rate hm hmu

def paper_upper_bound_dimension_isBigO_k_sq_log_mSpec
    {epsilon : ℝ} (hepsilon : 0 < epsilon) : Prop :=
  Asymptotics.IsBigO (Filter.atTop : Filter (ℕ × ℕ))
    (fun p : ℕ × ℕ =>
      (paper_linear_compressed_sensing_dimension p.1 p.2 epsilon : ℝ))
    (fun p : ℕ × ℕ => (p.2 : ℝ) ^ 2 * Real.log (p.1 : ℝ))

theorem paper_upper_bound_dimension_isBigO_k_sq_log_mSpec_proof
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    paper_upper_bound_dimension_isBigO_k_sq_log_mSpec hepsilon :=
  paper_upper_bound_dimension_isBigO_k_sq_log_m hepsilon

def paper_random_rademacher_strict_incoherence_probability_high_probabilitySpec
    {m d : ℕ} {mu delta : ℝ}
    (hd : 0 < d) (hmu_nonneg : 0 ≤ mu)
    (hpair_pos : 0 < ((offdiagPairFinset (Feature := Fin m)).card : ℝ))
    (hdelta_pos : 0 < delta)
    (hlog :
      Real.log
          ((2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) / delta) ≤
        ((d : ℝ) * mu ^ 2) / 2) : Prop :=
  AppliedModelingLib.measureProb (rowsMeasure (Fin m) (Fin d))
      (fun ω =>
        ∀ ⦃i j : Fin m⦄, i ≠ j →
          |AppliedModelingLib.Math.LinearCompressedSensing.inner
            (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω i)
            (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω j)| < mu) ≥
    1 - delta

theorem paper_random_rademacher_strict_incoherence_probability_high_probabilitySpec_proof
    {m d : ℕ} {mu delta : ℝ}
    (hd : 0 < d) (hmu_nonneg : 0 ≤ mu)
    (hpair_pos : 0 < ((offdiagPairFinset (Feature := Fin m)).card : ℝ))
    (hdelta_pos : 0 < delta)
    (hlog :
      Real.log
          ((2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) / delta) ≤
        ((d : ℝ) * mu ^ 2) / 2) :
    paper_random_rademacher_strict_incoherence_probability_high_probabilitySpec
      hd hmu_nonneg hpair_pos hdelta_pos hlog :=
  paper_random_rademacher_strict_incoherence_probability_high_probability
    hd hmu_nonneg hpair_pos hdelta_pos hlog

/--
Transparent semantic target for the paper's named random-matrix lemma.  The
explicit dimension choice is retained so the source's `O((log m + log(1/delta))
/ mu^2)` claim is reviewed as a construction, not as an assumed side condition.
-/
def paper_random_rademacher_strict_incoherence_source_rateSpec
    {m : ℕ} {mu delta : ℝ}
    (hm : 2 ≤ m) (hmu : 0 < mu)
    (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1) : Prop :=
  ∃ d : ℕ, 0 < d ∧
    (d : ℝ) ≤ Real.log (2 * (m : ℝ) ^ 2 / delta) / ((mu ^ 2) / 2) + 2 ∧
    (AppliedModelingLib.measureProb (rowsMeasure (Fin m) (Fin d))
        (fun ω =>
          ∀ ⦃i j : Fin m⦄, i ≠ j →
            |AppliedModelingLib.Math.LinearCompressedSensing.inner
              (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω i)
              (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω j)| < mu) ≥
      1 - delta) ∧
    (∀ (ω : Fin d → Fin m → Bool) (i : Fin m),
      AppliedModelingLib.Math.LinearCompressedSensing.inner
        (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω i)
        (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω i) = 1)

theorem paper_random_rademacher_strict_incoherence_source_rateSpec_proof
    {m : ℕ} {mu delta : ℝ}
    (hm : 2 ≤ m) (hmu : 0 < mu)
    (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1) :
    paper_random_rademacher_strict_incoherence_source_rateSpec
      hm hmu hdelta hdelta_le_one :=
  paper_random_rademacher_strict_incoherence_source_rate
    hm hmu hdelta hdelta_le_one

def paper_lower_bound_dimension_isBigO_source_log_source_regimeSpec
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) : Prop :=
  Asymptotics.IsBigO
    (linearCompressedSensingLowerSourceFilter epsilon)
    linearCompressedSensingLowerSourceLogScale
    (fun p : ℕ × ℕ =>
      (paper_linear_compressed_sensing_dimension p.1 p.2 epsilon : ℝ))

theorem paper_lower_bound_dimension_isBigO_source_log_source_regimeSpec_proof
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) :
    paper_lower_bound_dimension_isBigO_source_log_source_regimeSpec
      hepsilon_pos hepsilon_lt_one :=
  paper_lower_bound_dimension_isBigO_source_log_source_regime
    hepsilon_pos hepsilon_lt_one

def paper_geometry1_source_constructed_rateSpec
    {epsilon delta : ℝ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) : Prop :=
  AppliedModelingLib.Math.TendsToZero
    (fun k =>
      geometry1SelfCorrelationEnvelope
        (geometry1SourceLambda delta) (geometry1SourceMu epsilon delta k) - delta) ∧
    AppliedModelingLib.Math.TendsToZero
      (fun k =>
        (1 - delta) - geometry1OffdiagCorrelationEnvelope
          (geometry1SourceLambda delta) (geometry1SourceMu epsilon delta k)) ∧
    ∀ m k : ℕ, ∃ D : ℕ,
      (D : ℝ) ≤
          geometry1SourceDimensionCoefficient epsilon delta *
            ((k + 1 : ℕ) : ℝ) ^ 2 *
            Real.log (2 * ((m + 2 : ℕ) : ℝ) ^ 2) + 2 ∧
        ∃ A B : paper_feature_matrix m D,
          linearRecoveryCondition A B k epsilon ∧
            (∀ i : Fin m,
              |columnCorrelation (A i) (B i)| ≤
                geometry1SelfCorrelationEnvelope
                  (geometry1SourceLambda delta) (geometry1SourceMu epsilon delta k)) ∧
            (∀ ⦃i j : Fin m⦄, i ≠ j →
              geometry1OffdiagCorrelationEnvelope
                (geometry1SourceLambda delta) (geometry1SourceMu epsilon delta k) ≤
                columnCorrelation (A i) (A j)) ∧
            (∀ ⦃i j : Fin m⦄, i ≠ j →
              geometry1OffdiagCorrelationEnvelope
                (geometry1SourceLambda delta) (geometry1SourceMu epsilon delta k) ≤
                columnCorrelation (B i) (B j))

theorem paper_geometry1_source_constructed_rateSpec_proof
    {epsilon delta : ℝ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) :
    paper_geometry1_source_constructed_rateSpec
      hepsilon_pos hepsilon_lt_one hdelta_pos hdelta_lt_one :=
  paper_geometry1_source_constructed_rate
    hepsilon_pos hepsilon_lt_one hdelta_pos hdelta_lt_one

def paper_geometry1_exists_constructed_matrices_with_dimension_envelopeSpec
    {m k : ℕ} {epsilon lambda mu : ℝ}
    (hlambda : 0 ≤ lambda) (hmu : 0 < mu)
    (hbound :
      (2 * lambda + lambda ^ 2) * mu +
          (k : ℝ) * ((1 + 2 * lambda + lambda ^ 2) * mu) < epsilon)
    (hs : 0 < 1 + lambda ^ 2 - 2 * lambda * mu)
    (hnum : 0 ≤ lambda ^ 2 - (1 + 2 * lambda) * mu) : Prop :=
  ∃ D : ℕ,
    (D : ℝ) ≤
        (2 / mu ^ 2) * Real.log (2 * ((m + 2 : ℕ) : ℝ) ^ 2) + 2 ∧
      ∃ A B : paper_feature_matrix m D,
        linearRecoveryCondition A B k epsilon ∧
          (∀ i : Fin m,
            |columnCorrelation (A i) (B i)| ≤
              (1 + (2 * lambda + lambda ^ 2) * mu) /
                (1 + lambda ^ 2 - 2 * lambda * mu)) ∧
          (∀ ⦃i j : Fin m⦄, i ≠ j →
            (lambda ^ 2 - (1 + 2 * lambda) * mu) /
                (1 + lambda ^ 2 + 2 * lambda * mu) ≤
              columnCorrelation (A i) (A j)) ∧
          (∀ ⦃i j : Fin m⦄, i ≠ j →
            (lambda ^ 2 - (1 + 2 * lambda) * mu) /
                (1 + lambda ^ 2 + 2 * lambda * mu) ≤
              columnCorrelation (B i) (B j))

theorem paper_geometry1_exists_constructed_matrices_with_dimension_envelopeSpec_proof
    {m k : ℕ} {epsilon lambda mu : ℝ}
    (hlambda : 0 ≤ lambda) (hmu : 0 < mu)
    (hbound :
      (2 * lambda + lambda ^ 2) * mu +
          (k : ℝ) * ((1 + 2 * lambda + lambda ^ 2) * mu) < epsilon)
    (hs : 0 < 1 + lambda ^ 2 - 2 * lambda * mu)
    (hnum : 0 ≤ lambda ^ 2 - (1 + 2 * lambda) * mu) :
    paper_geometry1_exists_constructed_matrices_with_dimension_envelopeSpec
      (m := m) hlambda hmu hbound hs hnum :=
  paper_geometry1_exists_constructed_matrices_with_dimension_envelope
    hlambda hmu hbound hs hnum

def paper_geometry1_correlation_envelope_errors_tend_to_zeroSpec
    {lambda : ℝ} {mu : ℕ → ℝ}
    (hmu : AppliedModelingLib.Math.TendsToZero mu) : Prop :=
  AppliedModelingLib.Math.TendsToZero
      (fun n =>
        geometry1SelfCorrelationEnvelope lambda (mu n) -
          1 / (1 + lambda ^ 2)) ∧
    AppliedModelingLib.Math.TendsToZero
      (fun n =>
        lambda ^ 2 / (1 + lambda ^ 2) -
          geometry1OffdiagCorrelationEnvelope lambda (mu n))

theorem paper_geometry1_correlation_envelope_errors_tend_to_zeroSpec_proof
    {lambda : ℝ} {mu : ℕ → ℝ}
    (hmu : AppliedModelingLib.Math.TendsToZero mu) :
    paper_geometry1_correlation_envelope_errors_tend_to_zeroSpec
      (lambda := lambda) hmu :=
  paper_geometry1_correlation_envelope_errors_tend_to_zero hmu

def paper_geometry2_self_column_correlation_lowerSpec
    {m d k : ℕ} {epsilon gamma : ℝ} {A B : paper_feature_matrix m d}
    (hk : 1 ≤ k) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma_one : 1 ≤ gamma)
    (hrec : linearRecoveryCondition A B k epsilon)
    (hAnorm : ∀ i : Fin m, paper_column_norm (A i) ≤ gamma)
    (hBnorm : ∀ i : Fin m, paper_column_norm (B i) ≤ gamma)
    (i : Fin m) : Prop :=
  (1 - epsilon) / gamma ^ 2 ≤
    paper_column_correlation (B i) (A i)

theorem paper_geometry2_self_column_correlation_lowerSpec_proof
    {m d k : ℕ} {epsilon gamma : ℝ} {A B : paper_feature_matrix m d}
    (hk : 1 ≤ k) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma_one : 1 ≤ gamma)
    (hrec : linearRecoveryCondition A B k epsilon)
    (hAnorm : ∀ i : Fin m, paper_column_norm (A i) ≤ gamma)
    (hBnorm : ∀ i : Fin m, paper_column_norm (B i) ≤ gamma)
    (i : Fin m) :
    paper_geometry2_self_column_correlation_lowerSpec
      hk hepsilon_pos hepsilon_lt_one hgamma_one hrec hAnorm hBnorm i :=
  le_of_lt (paper_geometry2_self_column_correlation_lower
    hk hepsilon_pos hepsilon_lt_one hgamma_one hrec hAnorm hBnorm i)

def paper_geometry2_representation_column_correlation_upper_correctedSpec
    {m d k : ℕ} {epsilon gamma : ℝ} {A B : paper_feature_matrix m d}
    (hk : 1 ≤ k) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma_one : 1 ≤ gamma)
    (hrec : linearRecoveryCondition A B k epsilon)
    (hAnorm : ∀ i : Fin m, paper_column_norm (A i) ≤ gamma)
    (hBnorm : ∀ i : Fin m, paper_column_norm (B i) ≤ gamma)
    {i j : Fin m} (hij : i ≠ j) : Prop :=
  paper_column_correlation (A i) (A j) ≤
    epsilon * gamma ^ 2 / (1 - epsilon) ^ 2 +
      Real.sqrt (1 - ((1 - epsilon) / gamma ^ 2) ^ 2)

theorem paper_geometry2_representation_column_correlation_upper_correctedSpec_proof
    {m d k : ℕ} {epsilon gamma : ℝ} {A B : paper_feature_matrix m d}
    (hk : 1 ≤ k) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma_one : 1 ≤ gamma)
    (hrec : linearRecoveryCondition A B k epsilon)
    (hAnorm : ∀ i : Fin m, paper_column_norm (A i) ≤ gamma)
    (hBnorm : ∀ i : Fin m, paper_column_norm (B i) ≤ gamma)
    {i j : Fin m} (hij : i ≠ j) :
    paper_geometry2_representation_column_correlation_upper_correctedSpec
      hk hepsilon_pos hepsilon_lt_one hgamma_one hrec hAnorm hBnorm hij :=
  paper_geometry2_representation_column_correlation_upper_corrected
    hk hepsilon_pos hepsilon_lt_one hgamma_one hrec hAnorm hBnorm hij

def paper_geometry2_probe_column_correlation_upper_correctedSpec
    {m d k : ℕ} {epsilon gamma : ℝ} {A B : paper_feature_matrix m d}
    (hk : 1 ≤ k) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma_one : 1 ≤ gamma)
    (hrec : linearRecoveryCondition A B k epsilon)
    (hAnorm : ∀ i : Fin m, paper_column_norm (A i) ≤ gamma)
    (hBnorm : ∀ i : Fin m, paper_column_norm (B i) ≤ gamma)
    {i j : Fin m} (hij : i ≠ j) : Prop :=
  paper_column_correlation (B i) (B j) ≤
    epsilon * gamma ^ 2 / (1 - epsilon) ^ 2 +
      Real.sqrt (1 - ((1 - epsilon) / gamma ^ 2) ^ 2)

theorem paper_geometry2_probe_column_correlation_upper_correctedSpec_proof
    {m d k : ℕ} {epsilon gamma : ℝ} {A B : paper_feature_matrix m d}
    (hk : 1 ≤ k) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma_one : 1 ≤ gamma)
    (hrec : linearRecoveryCondition A B k epsilon)
    (hAnorm : ∀ i : Fin m, paper_column_norm (A i) ≤ gamma)
    (hBnorm : ∀ i : Fin m, paper_column_norm (B i) ≤ gamma)
    {i j : Fin m} (hij : i ≠ j) :
    paper_geometry2_probe_column_correlation_upper_correctedSpec
      hk hepsilon_pos hepsilon_lt_one hgamma_one hrec hAnorm hBnorm hij :=
  paper_geometry2_probe_column_correlation_upper_corrected
    hk hepsilon_pos hepsilon_lt_one hgamma_one hrec hAnorm hBnorm hij

def paper_threshold_separation_dimension_isBigO_lower_source_log_original_regimeSpec : Prop :=
  Asymptotics.IsBigO
    thresholdActivationOriginalSourceFilter
    thresholdActivationLowerSourceLogScale
    (fun p : ℕ × ℕ => (thresholdSeparationDimension p.1 p.2 : ℝ))

theorem paper_threshold_separation_dimension_isBigO_lower_source_log_original_regimeSpec_proof :
    paper_threshold_separation_dimension_isBigO_lower_source_log_original_regimeSpec :=
  paper_threshold_separation_dimension_isBigO_lower_source_log_original_regime

def paper_activation_separation_dimension_isBigO_lower_source_log_original_regimeSpec : Prop :=
  Asymptotics.IsBigO
    thresholdActivationOriginalSourceFilter
    thresholdActivationLowerSourceLogScale
    (fun p : ℕ × ℕ => (activationSeparationDimension p.1 p.2 : ℝ))

theorem paper_activation_separation_dimension_isBigO_lower_source_log_original_regimeSpec_proof :
    paper_activation_separation_dimension_isBigO_lower_source_log_original_regimeSpec :=
  paper_activation_separation_dimension_isBigO_lower_source_log_original_regime

end GKP26LinearRepresentationHypothesis
