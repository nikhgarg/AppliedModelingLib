import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalFiniteTerminalDensity
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalUnboundedStopping
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCountMarginal

/-!
# Finite forward-Poisson arrival density for LBG

This paper-local surface exposes the actual arbitrary-finite arrival-density
theorem used by the Appendix B.2 campaign.  It concerns the canonical finite
gap event and deliberately does not identify an arbitrary endpoint policy with
a predictable stopping clock.
-/

namespace LBG24SpatialUnderreporting

open MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/--
The first `count` uninspected gaps after a discrete prefix stopping index,
separated from the following terminal gap.

This is deliberately a finite-block construction for `PrefixStoppingIndex`.
It does not identify a selected real-valued clock time with a prefix stop.
-/
def postStopSplitLastFiniteGaps (τ : PrefixStoppingIndex) (count : ℕ) :
    (ℕ → ℝ) → (Fin count → ℝ) × ℝ :=
  splitLastFiniteGaps count ∘ τ.postInterarrivalBlock (count + 1)

theorem measurable_postStopSplitLastFiniteGaps
    (τ : PrefixStoppingIndex) (count : ℕ) :
    Measurable (postStopSplitLastFiniteGaps τ count) := by
  exact (measurable_splitLastFiniteGaps count).comp
    (τ.measurable_postInterarrivalBlock (count + 1))

/--
The post-prefix finite gap block and its next terminal gap have the iid
exponential product law.
-/
theorem postStopSplitLastFiniteGaps_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (τ : PrefixStoppingIndex) (count : ℕ) :
    HasLaw (postStopSplitLastFiniteGaps τ count)
      ((Measure.pi (fun _ : Fin count => expMeasure rate)).prod (expMeasure rate))
      (exponentialInterarrivalMeasure rate) := by
  exact (splitLastFiniteGaps_hasLaw hrate count).comp
    (τ.postInterarrivalBlock_hasLaw hrate (count + 1))

/--
The event that exactly the displayed finite post-prefix gap block fits before
a deterministic relative horizon and its next gap survives beyond it.

As with `postStopSplitLastFiniteGaps`, this is a discrete-prefix event, not an
arbitrary real-time selected-start event.
-/
def postStopFiniteArrivalEvent
    (τ : PrefixStoppingIndex) (count : ℕ) (horizon : ℝ) : Set (ℕ → ℝ) :=
  postStopSplitLastFiniteGaps τ count ⁻¹'
    terminalSurvivalEvent (finiteGapPrefixTime count)
      (finiteGapPrefixCarrier count horizon) horizon

/--
After any total discrete prefix stopping index, a finite vector of cumulative
arrival epochs, restricted to `count` new arrivals before a deterministic
relative horizon, has the exact terminal-survival density.

This extends the one-arrival PrefixStoppingIndex result to arbitrary finite
blocks.  It uses only finite post-prefix iid regeneration and does **not**
assert a strong-Markov or density theorem at an arbitrary real-valued stopping
time.
-/
theorem postStop_cumulativeArrival_restrict_finiteTerminal_eq_withDensity
    {rate horizon : ℝ} (hrate : 0 < rate) (τ : PrefixStoppingIndex) (count : ℕ) :
    Measure.map (fun ω =>
      cumulativeArrivalVector count (postStopSplitLastFiniteGaps τ count ω).1)
      ((exponentialInterarrivalMeasure rate).restrict
        (postStopFiniteArrivalEvent τ count horizon)) =
      (volume : Measure (Fin count → ℝ)).withDensity
        (finiteArrivalTerminalDensity rate horizon count) := by
  let X := postStopSplitLastFiniteGaps τ count
  let S := terminalSurvivalEvent (finiteGapPrefixTime count)
    (finiteGapPrefixCarrier count horizon) horizon
  let F : (Fin count → ℝ) × ℝ → Fin count → ℝ :=
    fun p => cumulativeArrivalVector count p.1
  have hX : HasLaw X
      ((Measure.pi (fun _ : Fin count => expMeasure rate)).prod (expMeasure rate))
      (exponentialInterarrivalMeasure rate) :=
    postStopSplitLastFiniteGaps_hasLaw hrate τ count
  have hXmeas : Measurable X := measurable_postStopSplitLastFiniteGaps τ count
  have hS : MeasurableSet S :=
    measurableSet_terminalSurvivalEvent (measurable_finiteGapPrefixTime count)
      (measurableSet_finiteGapPrefixCarrier count horizon)
  have hcum : Measurable (cumulativeArrivalVector count) := by
    have hcoord : cumulativeArrivalVector count = cumulativeArrivalLinearMap count := by
      funext gaps
      exact (cumulativeArrivalLinearMap_apply count gaps).symm
    rw [hcoord]
    exact (LinearMap.continuous_on_pi (cumulativeArrivalLinearMap count)).measurable
  have hF : Measurable F := hcum.comp measurable_fst
  change Measure.map (F ∘ X)
      ((exponentialInterarrivalMeasure rate).restrict (X ⁻¹' S)) =
      (volume : Measure (Fin count → ℝ)).withDensity
        (finiteArrivalTerminalDensity rate horizon count)
  calc
    Measure.map (F ∘ X) ((exponentialInterarrivalMeasure rate).restrict (X ⁻¹' S)) =
        Measure.map F (Measure.map X
          ((exponentialInterarrivalMeasure rate).restrict (X ⁻¹' S))) := by
      simpa using (Measure.map_map hF hXmeas).symm
    _ = Measure.map F
        ((Measure.map X (exponentialInterarrivalMeasure rate)).restrict S) := by
      rw [Measure.restrict_map hXmeas hS]
    _ = Measure.map F
        (((Measure.pi (fun _ : Fin count => expMeasure rate)).prod (expMeasure rate)).restrict S) := by
      rw [hX.map_eq]
    _ = (volume : Measure (Fin count → ℝ)).withDensity
        (finiteArrivalTerminalDensity rate horizon count) := by
      exact map_cumulativeArrival_finiteTerminal_eq_withDensity hrate count

/-
The next finite-coordinate lemmas identify the gap carrier appearing in the
terminal-survival construction with the usual ordered region for arrival
epochs.  They are deterministic facts about a fixed finite vector.  In
particular, they do not turn an endpoint-selected real time into a stopping
time or make an arbitrary-start Poisson-process assertion.
-/

private theorem cumulativeArrivalVector_eq_filterSum
    (m : ℕ) (gaps : Fin m → ℝ) (i : Fin m) :
    cumulativeArrivalVector m gaps i =
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => j ≤ i), gaps j := by
  unfold cumulativeArrivalVector
  rw [← Finset.sum_subtype]
  intro j
  simp

private theorem cumulativeArrivalVector_nonneg
    {m : ℕ} {gaps : Fin m → ℝ} (h : ∀ i, 0 ≤ gaps i) (i : Fin m) :
    0 ≤ cumulativeArrivalVector m gaps i := by
  rw [cumulativeArrivalVector_eq_filterSum]
  exact Finset.sum_nonneg (fun j _ => h j)

private theorem cumulativeArrivalVector_monotone
    {m : ℕ} {gaps : Fin m → ℝ} (h : ∀ i, 0 ≤ gaps i) :
    Monotone (cumulativeArrivalVector m gaps) := by
  intro i j hij
  rw [cumulativeArrivalVector_eq_filterSum, cumulativeArrivalVector_eq_filterSum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk.trans hij
  · intro k _hk _hknot
    exact h k

private theorem cumulativeArrivalVector_le_total
    {m : ℕ} {gaps : Fin m → ℝ} (h : ∀ i, 0 ≤ gaps i) (i : Fin m) :
    cumulativeArrivalVector m gaps i ≤ finiteGapPrefixTime m gaps := by
  rw [cumulativeArrivalVector_eq_filterSum]
  unfold finiteGapPrefixTime
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact Finset.mem_univ k
  · intro k _hk _hknot
    exact h k

private theorem cumulativeArrivalVector_mem_orderedJumpRegion_of_mem_carrier
    {m : ℕ} {horizon : ℝ} {gaps : Fin m → ℝ}
    (hmem : gaps ∈ finiteGapPrefixCarrier m horizon) :
    cumulativeArrivalVector m gaps ∈ orderedJumpRegion m horizon := by
  rw [orderedJumpRegion_eq_closedRegion]
  refine ⟨?_, cumulativeArrivalVector_monotone hmem.1⟩
  intro i
  exact ⟨cumulativeArrivalVector_nonneg hmem.1 i,
    (cumulativeArrivalVector_le_total hmem.1 i).trans hmem.2⟩

private theorem cumulativeArrivalVector_zero_apply
    (n : ℕ) (gaps : Fin (n + 1) → ℝ) :
    cumulativeArrivalVector (n + 1) gaps 0 = gaps 0 := by
  rw [cumulativeArrivalVector_eq_filterSum]
  have hfilter :
      Finset.univ.filter (fun j : Fin (n + 1) => j ≤ 0) = {0} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hj
      apply Fin.ext
      exact Nat.eq_zero_of_le_zero (Fin.le_def.mp hj)
    · rintro rfl
      exact le_rfl
  rw [hfilter]
  simp

private theorem cumulativeArrivalVector_succ_apply
    (n : ℕ) (gaps : Fin (n + 1) → ℝ) (i : Fin n) :
    cumulativeArrivalVector (n + 1) gaps i.succ =
      cumulativeArrivalVector (n + 1) gaps i.castSucc + gaps i.succ := by
  rw [cumulativeArrivalVector_eq_filterSum,
    cumulativeArrivalVector_eq_filterSum]
  have hset :
      Finset.univ.filter (fun j : Fin (n + 1) => j ≤ i.succ) =
        insert i.succ (Finset.univ.filter (fun j : Fin (n + 1) => j ≤ i.castSucc)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      by_cases hji : j = i.succ
      · exact Or.inl hji
      · right
        apply Fin.le_def.mpr
        have hjlt : j < i.succ := lt_of_le_of_ne hj hji
        exact Nat.le_of_lt_succ (by simpa using (Fin.lt_def.mp hjlt))
    · rintro (rfl | hj)
      · exact le_rfl
      · apply Fin.le_def.mpr
        exact (Fin.le_def.mp hj).trans (Nat.le_succ _)
  have hnot : i.succ ∉
      Finset.univ.filter (fun j : Fin (n + 1) => j ≤ i.castSucc) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact not_le_of_gt Fin.castSucc_lt_succ
  rw [hset, Finset.sum_insert hnot]
  ac_rfl

private theorem gaps_nonneg_of_cumulativeArrivalVector_bounds_mono
    {n : ℕ} {gaps : Fin (n + 1) → ℝ}
    (hzero : 0 ≤ cumulativeArrivalVector (n + 1) gaps 0)
    (hmono : Monotone (cumulativeArrivalVector (n + 1) gaps)) :
    ∀ i, 0 ≤ gaps i := by
  intro i
  refine Fin.induction ?_ ?_ i
  · rw [← cumulativeArrivalVector_zero_apply n gaps]
    exact hzero
  · intro j _ih
    have hle := hmono (Fin.castSucc_le_succ j)
    rw [cumulativeArrivalVector_succ_apply] at hle
    linarith

private theorem cumulativeArrivalVector_last_apply
    (n : ℕ) (gaps : Fin (n + 1) → ℝ) :
    cumulativeArrivalVector (n + 1) gaps (Fin.last n) =
      finiteGapPrefixTime (n + 1) gaps := by
  rw [cumulativeArrivalVector_eq_filterSum]
  unfold finiteGapPrefixTime
  have hfilter :
      Finset.univ.filter (fun j : Fin (n + 1) => j ≤ Fin.last n) = Finset.univ := by
    ext j
    simp [Fin.le_last]
  rw [hfilter]

private theorem mem_carrier_of_cumulativeArrivalVector_mem_orderedJumpRegion
    {m : ℕ} {horizon : ℝ} {gaps : Fin m → ℝ}
    (horizon_nonneg : 0 ≤ horizon)
    (hmem : cumulativeArrivalVector m gaps ∈ orderedJumpRegion m horizon) :
    gaps ∈ finiteGapPrefixCarrier m horizon := by
  cases m with
  | zero =>
      constructor
      · intro i
        exact Fin.elim0 i
      · simpa [finiteGapPrefixTime] using horizon_nonneg
  | succ n =>
      rw [orderedJumpRegion_eq_closedRegion] at hmem
      constructor
      · exact gaps_nonneg_of_cumulativeArrivalVector_bounds_mono
          (hmem.1 0).1 hmem.2
      · rw [← cumulativeArrivalVector_last_apply n gaps]
        exact (hmem.1 (Fin.last n)).2

/--
For a nonnegative deterministic horizon, cumulative summation maps the finite
nonnegative-gap carrier with total at most that horizon exactly onto the
ordered arrival-epoch region.  This is a finite deterministic change of
coordinates.
-/
theorem cumulativeArrivalVector_mem_orderedJumpRegion_iff_mem_finiteGapPrefixCarrier
    {m : ℕ} {horizon : ℝ} {gaps : Fin m → ℝ}
    (horizon_nonneg : 0 ≤ horizon) :
    cumulativeArrivalVector m gaps ∈ orderedJumpRegion m horizon ↔
      gaps ∈ finiteGapPrefixCarrier m horizon := by
  constructor
  · exact mem_carrier_of_cumulativeArrivalVector_mem_orderedJumpRegion horizon_nonneg
  · exact cumulativeArrivalVector_mem_orderedJumpRegion_of_mem_carrier

/--
The inverse cumulative-arrival linear equivalence pulls the finite gap carrier
back from the ordered arrival-epoch region.  This is the coordinate identity
needed to read `finiteArrivalTerminalDensity` as a constant density on that
region.
-/
theorem cumulativeArrivalLinearEquiv_symm_mem_finiteGapPrefixCarrier_iff
    {m : ℕ} {horizon : ℝ} {epochs : Fin m → ℝ}
    (horizon_nonneg : 0 ≤ horizon) :
    (cumulativeArrivalLinearEquiv m).symm epochs ∈ finiteGapPrefixCarrier m horizon ↔
      epochs ∈ orderedJumpRegion m horizon := by
  let gaps := (cumulativeArrivalLinearEquiv m).symm epochs
  have hcum : cumulativeArrivalVector m gaps = epochs := by
    calc
      cumulativeArrivalVector m gaps = cumulativeArrivalLinearMap m gaps :=
        (cumulativeArrivalLinearMap_apply m gaps).symm
      _ = cumulativeArrivalLinearEquiv m gaps := rfl
      _ = epochs := (cumulativeArrivalLinearEquiv m).apply_symm_apply epochs
  rw [← cumulativeArrivalVector_mem_orderedJumpRegion_iff_mem_finiteGapPrefixCarrier
    horizon_nonneg]
  simpa [gaps] using congrArg (fun x : Fin m → ℝ =>
    x ∈ orderedJumpRegion m horizon) hcum

private theorem exponentialBlockDensity_eq_of_nonneg
    {rate : ℝ} {m : ℕ} {gaps : Fin m → ℝ}
    (rate_nonneg : 0 ≤ rate) (gaps_nonneg : ∀ i, 0 ≤ gaps i) :
    exponentialBlockDensity rate m gaps =
      ENNReal.ofReal (rate ^ m *
        Real.exp (-(rate * finiteGapPrefixTime m gaps))) := by
  unfold exponentialBlockDensity
  rw [show (∏ i : Fin m, exponentialPDF rate (gaps i)) =
      ∏ i : Fin m, ENNReal.ofReal (rate * Real.exp (-(rate * gaps i))) by
    apply Finset.prod_congr rfl
    intro i _
    exact exponentialPDF_of_nonneg (gaps_nonneg i)]
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · congr 1
    calc
      ∏ i : Fin m, rate * Real.exp (-(rate * gaps i)) =
          (∏ _ : Fin m, rate) * ∏ i : Fin m, Real.exp (-(rate * gaps i)) := by
            rw [Finset.prod_mul_distrib]
      _ = rate ^ m * Real.exp (∑ i : Fin m, -(rate * gaps i)) := by
            rw [Finset.prod_const, ← Real.exp_sum]
            simp
      _ = rate ^ m * Real.exp (-(rate * finiteGapPrefixTime m gaps)) := by
            congr 2
            unfold finiteGapPrefixTime
            rw [Finset.sum_neg_distrib]
            congr 1
            rw [Finset.mul_sum]
  · intro i _
    exact mul_nonneg rate_nonneg (le_of_lt (Real.exp_pos _))

/--
The finite Poisson arrival density in ordered-epoch coordinates: a constant
`rate ^ count * exp (-rate * horizon)` on the ordered jump region and zero
outside.  It is a finite deterministic-horizon normal form, not a statement
about an arbitrarily selected start time.
-/
def finiteArrivalOrderedDensity (rate horizon : ℝ) (count : ℕ) :
    (Fin count → ℝ) → ℝ≥0∞ :=
  (orderedJumpRegion count horizon).indicator
    (fun _ => ENNReal.ofReal (rate ^ count * Real.exp (-(rate * horizon))))

/--
At positive rate and a nonnegative deterministic horizon, the terminal-gap
construction of `finiteArrivalTerminalDensity` is exactly its constant
ordered-region normal form.  The equality is entirely finite-coordinate and
does not supply an arbitrary-start strong-Markov theorem.
-/
theorem finiteArrivalTerminalDensity_eq_finiteArrivalOrderedDensity
    {rate horizon : ℝ} (rate_pos : 0 < rate) (horizon_nonneg : 0 ≤ horizon)
    (count : ℕ) :
    finiteArrivalTerminalDensity rate horizon count =
      finiteArrivalOrderedDensity rate horizon count := by
  funext epochs
  let gaps := (cumulativeArrivalLinearEquiv count).symm epochs
  have hregion : epochs ∈ orderedJumpRegion count horizon ↔
      gaps ∈ finiteGapPrefixCarrier count horizon := by
    simpa [gaps] using
      (cumulativeArrivalLinearEquiv_symm_mem_finiteGapPrefixCarrier_iff
        horizon_nonneg (epochs := epochs)).symm
  change exponentialBlockDensity rate count gaps *
      terminalSurvivalDensity rate horizon (finiteGapPrefixTime count)
        (finiteGapPrefixCarrier count horizon) gaps =
      finiteArrivalOrderedDensity rate horizon count epochs
  by_cases hmem : gaps ∈ finiteGapPrefixCarrier count horizon
  · rw [terminalSurvivalDensity, Set.indicator_of_mem hmem,
      finiteArrivalOrderedDensity, Set.indicator_of_mem (hregion.mpr hmem)]
    rw [exponentialBlockDensity_eq_of_nonneg rate_pos.le hmem.1]
    have hleft_nonneg : 0 ≤ rate ^ count *
        Real.exp (-(rate * finiteGapPrefixTime count gaps)) :=
      mul_nonneg (pow_nonneg rate_pos.le _) (le_of_lt (Real.exp_pos _))
    rw [← ENNReal.ofReal_mul hleft_nonneg]
    congr 1
    calc
      (rate ^ count * Real.exp (-(rate * finiteGapPrefixTime count gaps))) *
          Real.exp (-(rate * (horizon - finiteGapPrefixTime count gaps))) =
          rate ^ count *
            (Real.exp (-(rate * finiteGapPrefixTime count gaps)) *
              Real.exp (-(rate * (horizon - finiteGapPrefixTime count gaps)))) := by
            ring
      _ = rate ^ count * Real.exp
          (-(rate * finiteGapPrefixTime count gaps) +
            -(rate * (horizon - finiteGapPrefixTime count gaps))) := by
            rw [Real.exp_add]
      _ = rate ^ count * Real.exp (-(rate * horizon)) := by
            congr 2
            ring
  · have hnotregion : epochs ∉ orderedJumpRegion count horizon := by
      intro hepochs
      exact hmem (hregion.mp hepochs)
    rw [terminalSurvivalDensity, Set.indicator_of_notMem hmem,
      finiteArrivalOrderedDensity, Set.indicator_of_notMem hnotregion]
    simp

/--
For every finite count, the canonical forward exponential-renewal path has an
actual cumulative-arrival subdensity after its terminal survival condition.
The event is `canonicalFiniteArrivalEvent`; connecting a selected endpoint to
that finite-gap event remains a separate paper-model obligation.
-/
theorem canonical_forward_finite_terminal_density
    {rate horizon : ℝ} (hrate : 0 < rate) (count : ℕ) :
    Measure.map (fun ω =>
      cumulativeArrivalVector count (canonicalSplitLastFiniteGaps count ω).1)
      ((exponentialInterarrivalMeasure rate).restrict
        (canonicalFiniteArrivalEvent count horizon)) =
      (volume : Measure (Fin count → ℝ)).withDensity
        (finiteArrivalTerminalDensity rate horizon count) :=
  canonical_cumulativeArrival_restrict_finiteTerminal_eq_withDensity hrate count

/--
For every positive finite count, the canonical renewal-count fiber itself has
the exact cumulative-arrival density.  The endpoint-selection step remains a
separate model obligation.
-/
theorem canonical_forward_positive_count_density
    {rate horizon : ℝ} (hrate : 0 < rate) (count : ℕ) :
    Measure.map (fun ω =>
      cumulativeArrivalVector (count + 1)
        (canonicalSplitLastFiniteGaps (count + 1) ω).1)
      ((exponentialInterarrivalMeasure rate).restrict
        {ω | canonicalRenewalCount horizon ω = count + 1}) =
      (volume : Measure (Fin (count + 1) → ℝ)).withDensity
        (finiteArrivalTerminalDensity rate horizon (count + 1)) :=
  canonical_cumulativeArrival_restrict_renewalCountSucc_eq_withDensity hrate count

/--
At a nonnegative deterministic horizon, the same actual density statement
holds for every finite forward renewal count, including zero.
-/
theorem canonical_forward_count_density
    {rate horizon : ℝ} (hrate : 0 < rate) (horizon_nonneg : 0 ≤ horizon)
    (count : ℕ) :
    Measure.map (fun ω =>
      cumulativeArrivalVector count (canonicalSplitLastFiniteGaps count ω).1)
      ((exponentialInterarrivalMeasure rate).restrict
        {ω | canonicalRenewalCount horizon ω = count}) =
      (volume : Measure (Fin count → ℝ)).withDensity
        (finiteArrivalTerminalDensity rate horizon count) :=
  canonical_cumulativeArrival_restrict_renewalCount_eq_withDensity
    hrate horizon_nonneg count

/--
The finite terminal density is an exact-count **subdensity**.  Its total mass
is the Poisson probability of that count, rather than one.  This normalization
is the bridge from the actual ordered-arrival measure to the count likelihood
in the corrected Theorem-2 argument.
-/
theorem finiteArrivalTerminalDensity_mass_real_eq_countLikelihood
    {rate horizon : ℝ} (hrate : 0 < rate) (horizon_nonneg : 0 ≤ horizon)
    (count : ℕ) :
    ((volume : Measure (Fin count → ℝ)).withDensity
      (finiteArrivalTerminalDensity rate horizon count)).real Set.univ =
      countLikelihood rate horizon count := by
  let F : (ℕ → ℝ) → Fin count → ℝ := fun ω =>
    cumulativeArrivalVector count (canonicalSplitLastFiniteGaps count ω).1
  have hcum : Measurable (cumulativeArrivalVector count) := by
    have hcoord : cumulativeArrivalVector count = cumulativeArrivalLinearMap count := by
      funext gaps
      exact (cumulativeArrivalLinearMap_apply count gaps).symm
    rw [hcoord]
    exact (LinearMap.continuous_on_pi (cumulativeArrivalLinearMap count)).measurable
  have hF : Measurable F := hcum.comp
    ((measurable_canonicalSplitLastFiniteGaps count).fst)
  have hmap := canonical_forward_finite_terminal_density
    (horizon := horizon) hrate count
  change ((volume : Measure (Fin count → ℝ)).withDensity
      (finiteArrivalTerminalDensity rate horizon count)).real Set.univ = _
  rw [← hmap]
  rw [Measure.real_def, Measure.map_apply hF MeasurableSet.univ]
  change (((exponentialInterarrivalMeasure rate).restrict
      (canonicalFiniteArrivalEvent count horizon)) Set.univ).toReal = _
  rw [Measure.restrict_congr_set
    (canonicalFiniteArrivalEvent_ae_eq_renewalCountFiber
      hrate horizon_nonneg count)]
  rw [Measure.restrict_apply MeasurableSet.univ]
  simp only [Set.univ_inter]
  exact hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
    (mul_nonneg hrate.le horizon_nonneg)
    (canonicalRenewalCount_hasLaw_poisson hrate horizon_nonneg) count

end

end LBG24SpatialUnderreporting
