import GJ18InformativeRatingSystems.Assumptions

/-!
# Literal Source-Model Bridge: GJ18 Informative Rating Systems

This module turns the literal finite-ordinal source conditions into the
support-aware large-deviation certificate used by the finite i.i.d. horizon
model. It deliberately keeps the source's terminal-support gap visible:
strict decrease between displayed cutoffs supplies nonterminal atoms, while a
case split selects the low seller's actual support maximum.

The source does not state the positive-rate condition needed for an exponential
rate, nor does its state recurrence formally establish the i.i.d. joint law.
Those are kept outside `FiniteOrdinalSourceModel` as explicit corrected-model
obligations.
-/

namespace GJ18InformativeRatingSystems

noncomputable section

open AppliedModelingLib.Probability

/--
The author-approved corrected/source-shaped finite-ordinal package. The
above-bottom cross-type tail clause is a governing correction, not a literal
claim about the pinned archive's impossible bottom cutoff.
-/
structure FiniteOrdinalSourceModel
    {n m : Nat} (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real) : Prop where
  match_schedule : source_match_schedule_coherence sampleRate
  scores_in_unit_interval : source_rating_scores_in_unit_interval M.score
  scores_strictly_increasing : source_strictly_increasing_rating_scores M.score
  tails_strictly_decrease_at_displayed_cutoffs :
    source_strict_ordinal_cumulative_tail_decrease_at_displayed_cutoffs M
  quality_tails_strictly_increase_above_bottom :
    source_strict_ordinal_quality_tail_increase_above_bottom M

/-- The penultimate displayed rating, valid when there are at least three levels. -/
def sourceOrdinalPenultimate (m : Nat) : Fin (m + 1) :=
  ⟨m - 1, by omega⟩

theorem sourceOrdinalPenultimate_lt_last {m : Nat} (hm : 2 <= m) :
    sourceOrdinalPenultimate m < (Fin.last m : Fin (m + 1)) := by
  change m - 1 < m
  omega

theorem sourceOrdinalPenultimate_pos {m : Nat} (hm : 2 <= m) :
    0 < (sourceOrdinalPenultimate m).val := by
  change 0 < m - 1
  omega

theorem sourceOrdinal_nontrivial_rating_count {m : Nat} (hm : 2 <= m) :
    0 < m := by
  omega

theorem sourceOrdinal_bottom_mass_pos
    {Seller : Type*} {m : Nat}
    (M : FiniteRatingLDPModel Seller (Fin (m + 1)))
    (hwithin : source_strict_ordinal_cumulative_tail_decrease_at_displayed_cutoffs M)
    (hm : 2 <= m) (theta : Seller) :
    0 < (M.typeLaw theta 0).toReal := by
  let r : Fin m := ⟨0, sourceOrdinal_nontrivial_rating_count hm⟩
  have h :=
    mass_pos_of_source_strict_ordinal_cumulative_tail_decrease_at_displayed_cutoffs
      M hwithin theta r
  simpa [r] using h

theorem sourceOrdinal_penultimate_mass_pos
    {Seller : Type*} {m : Nat}
    (M : FiniteRatingLDPModel Seller (Fin (m + 1)))
    (hwithin : source_strict_ordinal_cumulative_tail_decrease_at_displayed_cutoffs M)
    (hm : 2 <= m) (theta : Seller) :
    0 < (M.typeLaw theta (sourceOrdinalPenultimate m)).toReal := by
  let r : Fin m := ⟨m - 1, by omega⟩
  have h :=
    mass_pos_of_source_strict_ordinal_cumulative_tail_decrease_at_displayed_cutoffs
      M hwithin theta r
  simpa [sourceOrdinalPenultimate, r] using h

theorem sourceOrdinal_support_le_penultimate_of_terminal_mass_zero
    {m : Nat} (hm : 2 <= m) {mu : PMF (Fin (m + 1))}
    (htop : ¬ (0 < (mu (Fin.last m)).toReal))
    (r : Fin (m + 1)) (hr : 0 < (mu r).toReal) :
    r <= sourceOrdinalPenultimate m := by
  let penultimate : Fin (m + 1) := sourceOrdinalPenultimate m
  by_cases hle : r <= penultimate
  · exact hle
  · have hpenultimate_lt_r : penultimate < r := lt_of_not_ge hle
    have hlast_le_r : Fin.last m <= r := by
      change m <= r.val
      change m - 1 < r.val at hpenultimate_lt_r
      omega
    have hr_last : r = Fin.last m := le_antisymm (Fin.le_last r) hlast_le_r
    subst r
    exact False.elim (htop hr)

/--
Literal ordinal-tail conditions yield a support-aware pairwise LDP certificate
whenever the rating scale has at least three displayed levels. The low seller's
terminal atom is selected only when it is actually positive; otherwise the
source-derived penultimate atom is its support maximum.
-/
noncomputable def ordinalSourcePairwiseLdpCertificate_at_least_three_levels
    {n m : Nat} [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 2 <= m) :
    PairwiseThresholdRateTopLdpCertificate M sampleRate
      finiteChainOrderedPairHi finiteChainOrderedPairLo := by
  have htail : assumption_ordinal_rating_tail_dominance M :=
    assumption_ordinal_rating_tail_dominance_of_source_strict_quality_tails M
      sourceModel.quality_tails_strictly_increase_above_bottom
  have hmean :
      forall p : finiteChainOrderedPair n,
        AppliedModelingLib.pmfExp (M.typeLaw (finiteChainOrderedPairLo p)) M.score <=
          AppliedModelingLib.pmfExp (M.typeLaw (finiteChainOrderedPairHi p)) M.score := by
    intro p
    exact AppliedModelingLib.pmfExp_le_pmfExp_of_fin_tail_prob_le
      (M.typeLaw (finiteChainOrderedPairLo p))
      (M.typeLaw (finiteChainOrderedPairHi p)) M.score
      sourceModel.scores_strictly_increasing.monotone (htail p)
  refine PairwiseThresholdRateTopLdpCertificate.of_expected_score_gap_and_support_extrema
    M sampleRate finiteChainOrderedPairHi finiteChainOrderedPairLo
    (fun p => hpositive_sample (finiteChainOrderedPairHi p))
    (fun p => hpositive_sample (finiteChainOrderedPairLo p))
    hmean
    (fun _ => 0) (fun _ => Fin.last m) (fun _ => 0)
    (fun p =>
      if 0 < (M.typeLaw (finiteChainOrderedPairLo p) (Fin.last m)).toReal then
        Fin.last m
      else sourceOrdinalPenultimate m)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro p
    exact sourceOrdinal_bottom_mass_pos M
      sourceModel.tails_strictly_decrease_at_displayed_cutoffs hm
      (finiteChainOrderedPairHi p)
  · intro p
    exact mass_pos_last_of_source_strict_ordinal_quality_tail_increase_above_bottom
      M sourceModel.quality_tails_strictly_increase_above_bottom p
      (sourceOrdinal_nontrivial_rating_count hm)
  · intro p
    exact sourceOrdinal_bottom_mass_pos M
      sourceModel.tails_strictly_decrease_at_displayed_cutoffs hm
      (finiteChainOrderedPairLo p)
  · intro p
    by_cases htop : 0 < (M.typeLaw (finiteChainOrderedPairLo p) (Fin.last m)).toReal
    · simpa [htop] using htop
    · simpa [htop] using sourceOrdinal_penultimate_mass_pos M
        sourceModel.tails_strictly_decrease_at_displayed_cutoffs hm
        (finiteChainOrderedPairLo p)
  · intro _ r _
    exact sourceModel.scores_strictly_increasing.monotone (Fin.zero_le r)
  · intro _ r _
    exact sourceModel.scores_strictly_increasing.monotone (Fin.le_last r)
  · intro _ r _
    exact sourceModel.scores_strictly_increasing.monotone (Fin.zero_le r)
  · intro p r hr
    by_cases htop : 0 < (M.typeLaw (finiteChainOrderedPairLo p) (Fin.last m)).toReal
    · simpa [htop] using
        sourceModel.scores_strictly_increasing.monotone (Fin.le_last r)
    · simp only [htop, ↓reduceIte]
      exact sourceModel.scores_strictly_increasing.monotone
        (sourceOrdinal_support_le_penultimate_of_terminal_mass_zero hm htop r hr)
  · intro _
    change M.score (0 : Fin (m + 1)) < M.score (Fin.last m)
    apply sourceModel.scores_strictly_increasing
    change 0 < m
    exact sourceOrdinal_nontrivial_rating_count hm
  · intro p
    by_cases htop : 0 < (M.typeLaw (finiteChainOrderedPairLo p) (Fin.last m)).toReal
    · simp only [htop, ↓reduceIte]
      apply sourceModel.scores_strictly_increasing
      change 0 < m
      exact sourceOrdinal_nontrivial_rating_count hm
    · simp only [htop, ↓reduceIte]
      apply sourceModel.scores_strictly_increasing
      change 0 < (sourceOrdinalPenultimate m).val
      exact sourceOrdinalPenultimate_pos hm
  · intro p
    by_cases htop : 0 < (M.typeLaw (finiteChainOrderedPairLo p) (Fin.last m)).toReal
    · simp only [htop, ↓reduceIte]
      apply sourceModel.scores_strictly_increasing
      change 0 < m
      exact sourceOrdinal_nontrivial_rating_count hm
    · simp only [htop, ↓reduceIte]
      apply sourceModel.scores_strictly_increasing
      change 0 < (sourceOrdinalPenultimate m).val
      exact sourceOrdinalPenultimate_pos hm

/--
The finite i.i.d. horizon completion of the source model has the paper's
extended exact rate under literal ordinal tails whenever there are at least
three displayed rating levels. Positive sample rates are an explicit
additional assumption: the source's displayed `g` condition alone permits a
zero-rate seller.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_ordinal_source_model_at_least_three_levels
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 2 <= m) :
    HasExtendedExponentialRate
      (fun k : Nat =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRateTop M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_pairwise_ldp_certificates
    M sampleRate
    (ordinalSourcePairwiseLdpCertificate_at_least_three_levels
      M sampleRate sourceModel hpositive_sample hm)

/-- Every displayed binary rating is either its bottom or its top level. -/
theorem sourceOrdinalBinaryRating_eq_bottom_or_top (r : Fin 2) :
    r = 0 ∨ r = Fin.last 1 := by
  fin_cases r <;> simp

/--
The binary source-model pair certificate.  If the low seller has terminal
mass, the ordinary support-extrema route applies.  If it has no terminal mass,
the proof instead uses the exact lower-endpoint calculation; the two branches
are semantic support cases, not function-name conventions.
-/
noncomputable def ordinalSourceSinglePairwiseLdpCertificate_binary
    {n : Nat}
    (M : FiniteRatingLDPModel (Fin n) (Fin 2))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (p : finiteChainOrderedPair n) :
    PairwiseThresholdRateTopLdpCertificate M sampleRate
      (fun _ : Unit => finiteChainOrderedPairHi p)
      (fun _ : Unit => finiteChainOrderedPairLo p) := by
  let hi := finiteChainOrderedPairHi p
  let lo := finiteChainOrderedPairLo p
  have htail : assumption_ordinal_rating_tail_dominance M :=
    assumption_ordinal_rating_tail_dominance_of_source_strict_quality_tails M
      sourceModel.quality_tails_strictly_increase_above_bottom
  have hmean :
      AppliedModelingLib.pmfExp (M.typeLaw lo) M.score <=
        AppliedModelingLib.pmfExp (M.typeLaw hi) M.score := by
    exact AppliedModelingLib.pmfExp_le_pmfExp_of_fin_tail_prob_le
      (M.typeLaw lo) (M.typeLaw hi) M.score
      sourceModel.scores_strictly_increasing.monotone (by
        simpa [hi, lo] using htail p)
  have hhi_bottom : 0 < (M.typeLaw hi (0 : Fin 2)).toReal := by
    let r : Fin 1 := 0
    have hmass :=
      mass_pos_of_source_strict_ordinal_cumulative_tail_decrease_at_displayed_cutoffs
        M sourceModel.tails_strictly_decrease_at_displayed_cutoffs hi r
    simpa [r] using hmass
  have hhi_top : 0 < (M.typeLaw hi (Fin.last 1)).toReal := by
    have hmass :=
      mass_pos_last_of_source_strict_ordinal_quality_tail_increase_above_bottom
        M sourceModel.quality_tails_strictly_increase_above_bottom p (by omega)
    simpa [hi] using hmass
  have hlo_bottom : 0 < (M.typeLaw lo (0 : Fin 2)).toReal := by
    let r : Fin 1 := 0
    have hmass :=
      mass_pos_of_source_strict_ordinal_cumulative_tail_decrease_at_displayed_cutoffs
        M sourceModel.tails_strictly_decrease_at_displayed_cutoffs lo r
    simpa [r] using hmass
  have hscore_lt : M.score (0 : Fin 2) < M.score (Fin.last 1) := by
    apply sourceModel.scores_strictly_increasing
    decide
  have hrating : forall r : Fin 2, r = 0 ∨ r = Fin.last 1 := by
    intro r
    exact sourceOrdinalBinaryRating_eq_bottom_or_top r
  by_cases hlo_top : 0 < (M.typeLaw lo (Fin.last 1)).toReal
  · exact
      PairwiseThresholdRateTopLdpCertificate.of_expected_score_gap_and_support_extrema
        M sampleRate (fun _ : Unit => hi) (fun _ : Unit => lo)
        (fun _ => hpositive_sample hi) (fun _ => hpositive_sample lo)
        (fun _ => hmean)
        (fun _ => 0) (fun _ => Fin.last 1) (fun _ => 0) (fun _ => Fin.last 1)
        (fun _ => hhi_bottom) (fun _ => hhi_top)
        (fun _ => hlo_bottom) (fun _ => hlo_top)
        (fun _ r _ => sourceModel.scores_strictly_increasing.monotone (Fin.zero_le r))
        (fun _ r _ => sourceModel.scores_strictly_increasing.monotone (Fin.le_last r))
        (fun _ r _ => sourceModel.scores_strictly_increasing.monotone (Fin.zero_le r))
        (fun _ r _ => sourceModel.scores_strictly_increasing.monotone (Fin.le_last r))
        (fun _ => hscore_lt) (fun _ => hscore_lt) (fun _ => hscore_lt)
  · have hlo_top_zero : (M.typeLaw lo (Fin.last 1)).toReal = 0 := by
      exact le_antisymm (le_of_not_gt hlo_top) ENNReal.toReal_nonneg
    let rate : Real := sampleRate hi *
      (-Real.log (AppliedModelingLib.pmfProb (M.typeLaw hi)
        (fun r => M.score r = M.score (0 : Fin 2))))
    refine
      { rate := fun _ => rate
        threshold_rate_top_eq := fun _ => ?_
        leftTail := fun _ => ?_ }
    · dsimp [rate]
      simpa [hi, lo] using
        pairwiseSellerThresholdRateTop_eq_binary_bottom_top_boundary
          M sampleRate hi lo (0 : Fin 2) (Fin.last 1)
          (hpositive_sample hi) (hpositive_sample lo) hrating hscore_lt
          hhi_bottom hlo_top_zero
    · dsimp [rate]
      simpa [hi, lo] using
        twoSampleFloorScoreGapLeftTail_exponentialRateCertificate_of_binary_bottom_top_boundary
          M sampleRate hi lo (0 : Fin 2) (Fin.last 1)
          (hpositive_sample hi) (hpositive_sample lo) hrating hscore_lt
          hhi_bottom hlo_top_zero

/--
Literal binary ordinal tails yield a pairwise LDP certificate without adding
terminal full support for the low seller.  The zero-terminal branch is handled
by its endpoint rate rather than by a fictitious finite stationary dual.
-/
noncomputable def ordinalSourcePairwiseLdpCertificate_binary
    {n : Nat} [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin 2))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta) :
    PairwiseThresholdRateTopLdpCertificate M sampleRate
      finiteChainOrderedPairHi finiteChainOrderedPairLo :=
  { rate := fun p =>
      (ordinalSourceSinglePairwiseLdpCertificate_binary
        M sampleRate sourceModel hpositive_sample p).rate ()
    threshold_rate_top_eq := fun p =>
      (ordinalSourceSinglePairwiseLdpCertificate_binary
        M sampleRate sourceModel hpositive_sample p).threshold_rate_top_eq ()
    leftTail := fun p =>
      (ordinalSourceSinglePairwiseLdpCertificate_binary
        M sampleRate sourceModel hpositive_sample p).leftTail () }

/--
Uniform pairwise certificate for every nontrivial finite ordinal scale.  The
case split is on the rating carrier itself, so callers cannot accidentally
recover the old terminal-full-support assumption through a wrapper.
-/
noncomputable def ordinalSourcePairwiseLdpCertificate
    {n m : Nat} [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 1 <= m) :
    PairwiseThresholdRateTopLdpCertificate M sampleRate
      finiteChainOrderedPairHi finiteChainOrderedPairLo := by
  classical
  if h : m = 1 then
    subst m
    exact
      ordinalSourcePairwiseLdpCertificate_binary
        M sampleRate sourceModel hpositive_sample
  else
    have hm2 : 2 <= m := by omega
    exact
      ordinalSourcePairwiseLdpCertificate_at_least_three_levels
        M sampleRate sourceModel hpositive_sample hm2

/--
The clarified finite ordinal assumptions do yield a finite real exponent for
each pair.  This is deliberately stated as a representative of the
support-safe rate rather than as the legacy unrestricted real `inf_a` wrapper,
which assigns a default real value outside the finite score hull.
-/
theorem source_pairwiseThresholdRateTop_has_finite_real_representative
    {n m : Nat} [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 1 <= m) (p : finiteChainOrderedPair n) :
    exists rate : Real,
      pairwiseSellerThresholdRateTop M sampleRate
          (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) =
        (rate : WithTop Real) := by
  let C := ordinalSourcePairwiseLdpCertificate
    M sampleRate sourceModel hpositive_sample hm
  exact ⟨C.rate p, C.threshold_rate_top_eq p⟩

/--
The finite adjacent-pair minimum of the support-safe source rate also has a
real representative. This is the appropriate real endpoint for the corrected
theorem: it does not identify the representative with the legacy unrestricted
real `inf_a` definition.
-/
theorem source_minFiniteChainAdjacentThresholdRateTop_has_finite_real_representative
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 1 <= m) :
    exists rate : Real,
      minFiniteChainAdjacentThresholdRateTop M sampleRate =
        (rate : WithTop Real) := by
  classical
  let C := ordinalSourcePairwiseLdpCertificate
    M sampleRate sourceModel hpositive_sample hm
  let adjacentRate : finiteChainAdjacentIndex n -> Real := fun i =>
    C.rate (finiteChainAdjacentPair i)
  obtain ⟨iMin, _hiMin, hmin_eq⟩ :=
    Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset (finiteChainAdjacentIndex n)))
      (H := Finset.univ_nonempty) (f := adjacentRate)
  refine ⟨adjacentRate iMin, ?_⟩
  apply minFiniteChainAdjacentThresholdRateTop_eq_coe_adjacent_rate_of_top_eq
    M sampleRate C.rate iMin
  · intro p
    simpa [finiteChainOrderedPairThresholdRateTop] using
      C.threshold_rate_top_eq p
  · intro i
    have hle :
        (Finset.univ : Finset (finiteChainAdjacentIndex n)).inf'
          Finset.univ_nonempty adjacentRate ≤ adjacentRate i :=
      Finset.inf'_le
        (s := (Finset.univ : Finset (finiteChainAdjacentIndex n)))
        (f := adjacentRate)
        (by simp : i ∈ (Finset.univ : Finset (finiteChainAdjacentIndex n)))
    calc
      adjacentRate iMin =
          (Finset.univ : Finset (finiteChainAdjacentIndex n)).inf'
            Finset.univ_nonempty adjacentRate := hmin_eq.symm
      _ ≤ adjacentRate i := hle

/--
The binary finite iid completion of the literal source model has the exact
support-safe extended rate.  This includes the low-terminal-zero boundary
that the prior full-support-only formalization omitted.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_ordinal_source_model_binary
    {n : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin 2))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta) :
    HasExtendedExponentialRate
      (fun k : Nat =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRateTop M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_pairwise_ldp_certificates
    M sampleRate
    (ordinalSourcePairwiseLdpCertificate_binary M sampleRate sourceModel hpositive_sample)

/--
For every nontrivial finite ordinal scale, the explicit iid completion of the
literal source model has the support-safe Theorem 1 rate.  The one-level scale
is excluded because the source strict-tail and strict-score conditions are
vacuous there; binary and larger scales are proved by their distinct support
arguments above.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_ordinal_source_model
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 1 <= m) :
    HasExtendedExponentialRate
      (fun k : Nat =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRateTop M sampleRate) := by
  have hcases : m = 1 ∨ 2 <= m := by omega
  rcases hcases with rfl | hm2
  · simpa using
      finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_ordinal_source_model_binary
        M sampleRate sourceModel hpositive_sample
  · exact
      finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_ordinal_source_model_at_least_three_levels
        M sampleRate sourceModel hpositive_sample hm2

end
end GJ18InformativeRatingSystems
