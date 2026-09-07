import PG24NoisyMatchingMarkets.Theorem3LogBound
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# PG24 Theorem 3 iid dyadic maximum bridge

This module proves the finite-product coupling behind the logarithmic
maximum argument.  The source sequence is indexed by `Fin (n + 1)`, so the
`2 * n` sample has one fewer coordinate than two `n + 1` blocks.  We couple it
to the larger two-block sample and use pointwise monotonicity of the maximum.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

open Filter Topology MeasureTheory
open scoped BigOperators ProbabilityTheory

namespace IidMaximumDyadic

/-- Every coordinate of a nonempty finite sample is bounded by its top order
statistic. -/
theorem coordinate_le_topOrderStatistic
    {n : ℕ} [NeZero n] (sample : Fin n -> ℝ) (i : Fin n) :
    sample i <=
      AppliedModelingLib.Probability.upperOrderStatistic sample
        (AppliedModelingLib.Probability.topSampleRank (n := n)) := by
  by_contra h
  have hlt :
      AppliedModelingLib.Probability.upperOrderStatistic sample
          (AppliedModelingLib.Probability.topSampleRank (n := n)) < sample i :=
    lt_of_not_ge h
  have hexists :
      ∃ j : Fin n,
        AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := n)) < sample j :=
    ⟨i, hlt⟩
  have hself :
      AppliedModelingLib.Probability.upperOrderStatistic sample
          (AppliedModelingLib.Probability.topSampleRank (n := n)) <
        AppliedModelingLib.Probability.upperOrderStatistic sample
          (AppliedModelingLib.Probability.topSampleRank (n := n)) :=
    (AppliedModelingLib.Probability.exists_lt_iff_topOrderStatistic_gt sample _).mp hexists
  exact (lt_irrefl _ hself)

/-- Reindexing a finite nonempty sample preserves its maximum order
statistic. -/
theorem topOrderStatistic_reindex
    {m n : ℕ} [NeZero m] [NeZero n]
    (e : Fin m ≃ Fin n) (sample : Fin m -> ℝ) :
    AppliedModelingLib.Probability.upperOrderStatistic (fun j => sample (e.symm j))
        (AppliedModelingLib.Probability.topSampleRank (n := n)) =
      AppliedModelingLib.Probability.upperOrderStatistic sample
        (AppliedModelingLib.Probability.topSampleRank (n := m)) := by
  apply le_antisymm
  · apply AppliedModelingLib.Probability.upperOrderStatistic_le_of_forall_le
      (rankFromTop := AppliedModelingLib.Probability.topSampleRank (n := n))
    intro j
    exact coordinate_le_topOrderStatistic sample (e.symm j)
  · apply AppliedModelingLib.Probability.upperOrderStatistic_le_of_forall_le
      (rankFromTop := AppliedModelingLib.Probability.topSampleRank (n := m))
    intro i
    have hcoordinate := coordinate_le_topOrderStatistic
      (fun j => sample (e.symm j)) (e i)
    simpa using hcoordinate

/-- The top order statistic of a concatenated pair of nonempty samples is the
maximum of their top order statistics. -/
theorem topOrderStatistic_append
    (n : ℕ) (left right : Fin (n + 1) -> ℝ) :
    AppliedModelingLib.Probability.upperOrderStatistic (Fin.append left right)
        (AppliedModelingLib.Probability.topSampleRank (n := (n + 1) + (n + 1))) =
      max
        (AppliedModelingLib.Probability.upperOrderStatistic left
          (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
        (AppliedModelingLib.Probability.upperOrderStatistic right
          (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) := by
  apply le_antisymm
  · apply AppliedModelingLib.Probability.upperOrderStatistic_le_of_forall_le
      (rankFromTop := AppliedModelingLib.Probability.topSampleRank
        (n := (n + 1) + (n + 1)))
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [Fin.append_left]
      exact (coordinate_le_topOrderStatistic left j).trans
        (le_max_left
          (AppliedModelingLib.Probability.upperOrderStatistic left
            (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
          (AppliedModelingLib.Probability.upperOrderStatistic right
            (AppliedModelingLib.Probability.topSampleRank (n := n + 1))))
    · intro j
      rw [Fin.append_right]
      exact (coordinate_le_topOrderStatistic right j).trans
        (le_max_right
          (AppliedModelingLib.Probability.upperOrderStatistic left
            (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
          (AppliedModelingLib.Probability.upperOrderStatistic right
            (AppliedModelingLib.Probability.topSampleRank (n := n + 1))))
  · apply max_le
    · apply AppliedModelingLib.Probability.upperOrderStatistic_le_of_forall_le
        (rankFromTop := AppliedModelingLib.Probability.topSampleRank (n := n + 1))
      intro i
      have hcoordinate := coordinate_le_topOrderStatistic
        (Fin.append left right) (Fin.castAdd (n + 1) i)
      rw [Fin.append_left] at hcoordinate
      exact hcoordinate
    · apply AppliedModelingLib.Probability.upperOrderStatistic_le_of_forall_le
        (rankFromTop := AppliedModelingLib.Probability.topSampleRank (n := n + 1))
      intro i
      have hcoordinate := coordinate_le_topOrderStatistic
        (Fin.append left right) (Fin.natAdd (n + 1) i)
      rw [Fin.append_right] at hcoordinate
      exact hcoordinate

/-- Measurable equivalence that concatenates two length-`n + 1` samples. -/
noncomputable def dyadicAppendEquiv (n : ℕ) :
    ((Fin (n + 1) -> ℝ) × (Fin (n + 1) -> ℝ)) ≃ᵐ
      (Fin ((n + 1) + (n + 1)) -> ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin (n + 1) ⊕ Fin (n + 1) => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft
      (fun _ : Fin ((n + 1) + (n + 1)) => ℝ)
      finSumFinEquiv)

theorem dyadicAppendEquiv_apply (n : ℕ)
    (blocks : (Fin (n + 1) -> ℝ) × (Fin (n + 1) -> ℝ)) :
    dyadicAppendEquiv n blocks = Fin.append blocks.1 blocks.2 := by
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [dyadicAppendEquiv, MeasurableEquiv.trans_apply]
    rw [← finSumFinEquiv_apply_left]
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    rw [finSumFinEquiv_apply_left, Fin.append_left]
    rfl
  · intro j
    simp only [dyadicAppendEquiv, MeasurableEquiv.trans_apply]
    rw [← finSumFinEquiv_apply_right]
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    rw [finSumFinEquiv_apply_right, Fin.append_right]
    rfl

/-- The iid product measure is preserved by the two-block concatenation. -/
theorem dyadicAppend_measurePreserving
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] (n : ℕ) :
    MeasurePreserving (dyadicAppendEquiv n)
      ((Measure.pi (fun _ : Fin (n + 1) => noiseLaw)).prod
        (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)))
      (Measure.pi (fun _ : Fin ((n + 1) + (n + 1)) => noiseLaw)) := by
  let split :
      ((Fin (n + 1) -> ℝ) × (Fin (n + 1) -> ℝ)) ≃ᵐ
        (Fin (n + 1) ⊕ Fin (n + 1) -> ℝ) :=
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin (n + 1) ⊕ Fin (n + 1) => ℝ)).symm
  let reindex :
      (Fin (n + 1) ⊕ Fin (n + 1) -> ℝ) ≃ᵐ
        (Fin ((n + 1) + (n + 1)) -> ℝ) :=
    MeasurableEquiv.piCongrLeft
      (fun _ : Fin ((n + 1) + (n + 1)) => ℝ)
      finSumFinEquiv
  have hsplit :
      MeasurePreserving split
        ((Measure.pi (fun _ : Fin (n + 1) => noiseLaw)).prod
          (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)))
        (Measure.pi (fun _ : Fin (n + 1) ⊕ Fin (n + 1) => noiseLaw)) := by
    simpa [split] using
      (measurePreserving_sumPiEquivProdPi_symm
        (fun _ : Fin (n + 1) ⊕ Fin (n + 1) => noiseLaw))
  have hreindex :
      MeasurePreserving reindex
        (Measure.pi (fun _ : Fin (n + 1) ⊕ Fin (n + 1) => noiseLaw))
        (Measure.pi (fun _ : Fin ((n + 1) + (n + 1)) => noiseLaw)) := by
    simpa [reindex] using
      (measurePreserving_piCongrLeft
        (fun _ : Fin ((n + 1) + (n + 1)) => noiseLaw)
        finSumFinEquiv)
  simpa [dyadicAppendEquiv, split, reindex] using hreindex.comp hsplit

/-- Integral form of the iid two-block maximum identity. -/
theorem integral_topOrderStatistic_dyadicAppend_eq
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] (n : ℕ) :
    integral
        (Measure.pi (fun _ : Fin ((n + 1) + (n + 1)) => noiseLaw))
        (fun sample =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank
              (n := (n + 1) + (n + 1)))) =
      integral
        ((Measure.pi (fun _ : Fin (n + 1) => noiseLaw)).prod
          (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)))
        (fun blocks =>
          max
            (AppliedModelingLib.Probability.upperOrderStatistic blocks.1
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
            (AppliedModelingLib.Probability.upperOrderStatistic blocks.2
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))) := by
  let hmeasure := dyadicAppend_measurePreserving noiseLaw n
  calc
    integral
        (Measure.pi (fun _ : Fin ((n + 1) + (n + 1)) => noiseLaw))
        (fun sample =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank
              (n := (n + 1) + (n + 1)))) =
        integral
          ((Measure.pi (fun _ : Fin (n + 1) => noiseLaw)).prod
            (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)))
          (fun blocks =>
            AppliedModelingLib.Probability.upperOrderStatistic (dyadicAppendEquiv n blocks)
              (AppliedModelingLib.Probability.topSampleRank
                (n := (n + 1) + (n + 1)))) :=
      (hmeasure.integral_comp' _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with blocks
      rw [dyadicAppendEquiv_apply, topOrderStatistic_append]

/-- Reindexing a finite iid product preserves its product law. -/
theorem iidPi_reindex_measurePreserving
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {m n : ℕ} (e : Fin m ≃ Fin n) :
    MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e)
      (Measure.pi (fun _ : Fin m => noiseLaw))
      (Measure.pi (fun _ : Fin n => noiseLaw)) := by
  simpa using
    (measurePreserving_piCongrLeft
      (fun _ : Fin n => noiseLaw) e)

/-- The two-block product sample, reindexed as a sample with one extra
coordinate beyond `Fin (n + n + 1)`. -/
noncomputable def dyadicPaddedAppendEquiv (n : ℕ) :
    ((Fin (n + 1) -> ℝ) × (Fin (n + 1) -> ℝ)) ≃ᵐ
      (Fin ((n + n + 1) + 1) -> ℝ) :=
  (dyadicAppendEquiv n).trans
    (MeasurableEquiv.piCongrLeft
      (fun _ : Fin ((n + n + 1) + 1) => ℝ)
      (finCongr (by omega : (n + 1) + (n + 1) = (n + n + 1) + 1)))

theorem dyadicPaddedAppend_measurePreserving
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] (n : ℕ) :
    MeasurePreserving (dyadicPaddedAppendEquiv n)
      ((Measure.pi (fun _ : Fin (n + 1) => noiseLaw)).prod
        (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)))
      (Measure.pi (fun _ : Fin ((n + n + 1) + 1) => noiseLaw)) := by
  have happend := dyadicAppend_measurePreserving noiseLaw n
  have hreindex := iidPi_reindex_measurePreserving noiseLaw
    (finCongr (by omega : (n + 1) + (n + 1) = (n + n + 1) + 1))
  simpa [dyadicPaddedAppendEquiv] using hreindex.comp happend

/-- The padded reindexing still represents the maximum of the two original
blocks. -/
theorem topOrderStatistic_dyadicPaddedAppend
    (n : ℕ) (blocks : (Fin (n + 1) -> ℝ) × (Fin (n + 1) -> ℝ)) :
    AppliedModelingLib.Probability.upperOrderStatistic (dyadicPaddedAppendEquiv n blocks)
        (AppliedModelingLib.Probability.topSampleRank (n := (n + n + 1) + 1)) =
      max
        (AppliedModelingLib.Probability.upperOrderStatistic blocks.1
          (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
        (AppliedModelingLib.Probability.upperOrderStatistic blocks.2
          (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) := by
  let e : Fin ((n + 1) + (n + 1)) ≃ Fin ((n + n + 1) + 1) :=
    finCongr (by omega)
  have hreindex := topOrderStatistic_reindex e (Fin.append blocks.1 blocks.2)
  have happend := topOrderStatistic_append n blocks.1 blocks.2
  have happly :
      dyadicPaddedAppendEquiv n blocks =
        fun j => Fin.append blocks.1 blocks.2 (e.symm j) := by
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp only [dyadicPaddedAppendEquiv, MeasurableEquiv.trans_apply]
    rw [MeasurableEquiv.piCongrLeft_apply_apply, dyadicAppendEquiv_apply]
    simp [e]
  rw [happly]
  exact hreindex.trans happend

/-- Drop one coordinate from a finite sample.  The remaining coordinates are
enumerated by `Fin.succAbove`, so this definition never assumes an ordering
of names or positions. -/
def dropLast (m : ℕ) (sample : Fin (m + 1) -> ℝ) : Fin m -> ℝ :=
  fun j => sample ((Fin.last m).succAbove j)

theorem dropLast_measurePreserving
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] (m : ℕ) :
    MeasurePreserving (dropLast m)
      (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
      (Measure.pi (fun _ : Fin m => noiseLaw)) := by
  let split : (Fin (m + 1) -> ℝ) ≃ᵐ ℝ × (Fin m -> ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
  have hsplit :
      MeasurePreserving split
        (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
        (noiseLaw.prod (Measure.pi (fun _ : Fin m => noiseLaw))) := by
    simpa [split] using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (m + 1) => noiseLaw) (Fin.last m))
  have hsnd :
      MeasurePreserving Prod.snd
        (noiseLaw.prod (Measure.pi (fun _ : Fin m => noiseLaw)))
        (Measure.pi (fun _ : Fin m => noiseLaw)) := by
    exact measurePreserving_snd
  convert hsnd.comp hsplit using 1

/-- Removing a coordinate cannot increase the maximum. -/
theorem topOrderStatistic_dropLast_le
    (m : ℕ) [NeZero m] (sample : Fin (m + 1) -> ℝ) :
    AppliedModelingLib.Probability.upperOrderStatistic (dropLast m sample)
        (AppliedModelingLib.Probability.topSampleRank (n := m)) <=
      AppliedModelingLib.Probability.upperOrderStatistic sample
        (AppliedModelingLib.Probability.topSampleRank (n := m + 1)) := by
  apply AppliedModelingLib.Probability.upperOrderStatistic_le_of_forall_le
    (rankFromTop := AppliedModelingLib.Probability.topSampleRank (n := m))
  intro j
  exact coordinate_le_topOrderStatistic sample ((Fin.last m).succAbove j)

/-- The actual iid projection from two `n + 1` blocks to the source's
`2 * n + 1` coordinates. -/
def dyadicProjection (n : ℕ)
    (blocks : (Fin (n + 1) -> ℝ) × (Fin (n + 1) -> ℝ)) :
    Fin (n + n + 1) -> ℝ :=
  dropLast (n + n + 1) (dyadicPaddedAppendEquiv n blocks)

theorem dyadicProjection_measurePreserving
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] (n : ℕ) :
    MeasurePreserving (dyadicProjection n)
      ((Measure.pi (fun _ : Fin (n + 1) => noiseLaw)).prod
        (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)))
      (Measure.pi (fun _ : Fin (n + n + 1) => noiseLaw)) := by
  have hpad := dyadicPaddedAppend_measurePreserving noiseLaw n
  have hdrop := dropLast_measurePreserving noiseLaw (n + n + 1)
  simpa [dyadicProjection] using hdrop.comp hpad

/-- Change variables along a measure-preserving map without assuming that the
map is injective. -/
theorem integral_comp_of_measurePreserving
    {Omega Omega' : Type*} [MeasurableSpace Omega] [MeasurableSpace Omega']
    {mu : Measure Omega} {nu : Measure Omega'} {f : Omega -> Omega'}
    (hpres : MeasurePreserving f mu nu) (g : Omega' -> ℝ)
    (hg : AEStronglyMeasurable g nu) :
    integral mu (fun x => g (f x)) = integral nu g := by
  calc
    integral mu (fun x => g (f x)) = integral (Measure.map f mu) g :=
      (MeasureTheory.integral_map hpres.aemeasurable (hpres.map_eq ▸ hg)).symm
    _ = integral nu g := by rw [hpres.map_eq]

/-- Pointwise form of the padded two-block domination used for the dyadic
increment. -/
theorem topOrderStatistic_dyadicProjection_le
    (n : ℕ) (blocks : (Fin (n + 1) -> ℝ) × (Fin (n + 1) -> ℝ)) :
    AppliedModelingLib.Probability.upperOrderStatistic (dyadicProjection n blocks)
        (AppliedModelingLib.Probability.topSampleRank (n := n + n + 1)) <=
      max
        (AppliedModelingLib.Probability.upperOrderStatistic blocks.1
          (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
        (AppliedModelingLib.Probability.upperOrderStatistic blocks.2
          (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) := by
  have hdrop := topOrderStatistic_dropLast_le (n + n + 1)
    (dyadicPaddedAppendEquiv n blocks)
  rw [topOrderStatistic_dyadicPaddedAppend] at hdrop
  exact hdrop

/-- The maximum of two `L²` real random variables is again `L²`. -/
theorem memLp_max_of_memLp
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (X Y : Omega -> ℝ)
    (hX : MemLp X 2 mu) (hY : MemLp Y 2 mu) :
    MemLp (fun w => max (X w) (Y w)) 2 mu := by
  have hsum : MemLp (fun w => |X w| + |Y w|) 2 mu := by
    simpa only [Real.norm_eq_abs] using hX.norm.add hY.norm
  refine hsum.mono ?_ ?_
  · exact (hX.aemeasurable.max hY.aemeasurable).aestronglyMeasurable
  · filter_upwards with w
    change |max (X w) (Y w)| <= abs (|X w| + |Y w|)
    have hsum_nonneg : 0 <= |X w| + |Y w| :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    have habs : |max (X w) (Y w)| <= |X w| + |Y w| := by
      apply abs_le.mpr
      constructor
      · calc
          -(|X w| + |Y w|) <= X w := by
            linarith [neg_abs_le (X w), abs_nonneg (Y w)]
          _ <= max (X w) (Y w) := le_max_left _ _
      · apply max_le
        · linarith [le_abs_self (X w), abs_nonneg (Y w)]
        · linarith [le_abs_self (Y w), abs_nonneg (X w)]
    calc
      |max (X w) (Y w)| <= |X w| + |Y w| := habs
      _ = abs (|X w| + |Y w|) := (abs_of_nonneg hsum_nonneg).symm

/-- Coupling after deleting one iid coordinate proves monotonicity of expected
maxima whenever the two relevant finite samples are `L²`. -/
theorem iidExpectedTop_succ_mono
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] (n : ℕ)
    (hmem :
      MemLp
        (fun sample : Fin (n + 1) -> ℝ =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) 2
        (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)))
    (hmemSucc :
      MemLp
        (fun sample : Fin ((n + 1) + 1) -> ℝ =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := (n + 1) + 1))) 2
        (Measure.pi (fun _ : Fin ((n + 1) + 1) => noiseLaw))) :
    AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
        (fun k => Measure.pi (fun _ : Fin (k + 1) => noiseLaw)) n <=
      AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
        (fun k => Measure.pi (fun _ : Fin (k + 1) => noiseLaw)) (n + 1) := by
  have hdrop := dropLast_measurePreserving noiseLaw (n + 1)
  have hmemDrop :
      MemLp
        (fun sample : Fin ((n + 1) + 1) -> ℝ =>
          AppliedModelingLib.Probability.upperOrderStatistic (dropLast (n + 1) sample)
            (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) 2
        (Measure.pi (fun _ : Fin ((n + 1) + 1) => noiseLaw)) := by
    simpa [Function.comp_def] using hmem.comp_measurePreserving hdrop
  change
    integral (Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
        (fun sample =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) <=
      integral (Measure.pi (fun _ : Fin ((n + 1) + 1) => noiseLaw))
        (fun sample =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := (n + 1) + 1)))
  calc
    integral (Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
        (fun sample =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) =
        integral (Measure.pi (fun _ : Fin ((n + 1) + 1) => noiseLaw))
          (fun sample =>
            AppliedModelingLib.Probability.upperOrderStatistic (dropLast (n + 1) sample)
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) :=
      (integral_comp_of_measurePreserving hdrop _ hmem.aestronglyMeasurable).symm
    _ <= integral (Measure.pi (fun _ : Fin ((n + 1) + 1) => noiseLaw))
          (fun sample =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := (n + 1) + 1))) := by
      apply integral_mono_ae
        (hmemDrop.integrable (by norm_num))
        (hmemSucc.integrable (by norm_num))
      filter_upwards with sample
      exact topOrderStatistic_dropLast_le (n + 1) sample

/-- The iid two-block coupling gives the source dyadic increment estimate.
The `2 * n` maximum is represented by `Fin (2 * n + 1)` and is coupled to two
blocks of `n + 1` coordinates by deleting one padded coordinate. -/
theorem iidExpectedTop_doubling_increment_le
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (maxVariance : ℕ -> ℝ) (n : ℕ)
    (hmem :
      MemLp
        (fun sample : Fin (n + 1) -> ℝ =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) 2
        (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)))
    (hmemDouble :
      MemLp
        (fun sample : Fin (n + n + 1) -> ℝ =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := n + n + 1))) 2
        (Measure.pi (fun _ : Fin (n + n + 1) => noiseLaw)))
    (hvariance :
      ProbabilityTheory.variance
        (fun sample : Fin (n + 1) -> ℝ =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
        (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) <= maxVariance n) :
    AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
        (fun k => Measure.pi (fun _ : Fin (k + 1) => noiseLaw)) (n + n) -
      AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
        (fun k => Measure.pi (fun _ : Fin (k + 1) => noiseLaw)) n <=
      2 * Real.sqrt (maxVariance n) := by
  let mu : Measure (Fin (n + 1) -> ℝ) :=
    Measure.pi (fun _ : Fin (n + 1) => noiseLaw)
  let W : (Fin (n + 1) -> ℝ) -> ℝ := fun sample =>
    AppliedModelingLib.Probability.upperOrderStatistic sample
      (AppliedModelingLib.Probability.topSampleRank (n := n + 1))
  let W1 : ((Fin (n + 1) -> ℝ) × (Fin (n + 1) -> ℝ)) -> ℝ :=
    fun blocks => W blocks.1
  let W2 : ((Fin (n + 1) -> ℝ) × (Fin (n + 1) -> ℝ)) -> ℝ :=
    fun blocks => W blocks.2
  haveI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hmemW : MemLp W 2 mu := by
    simpa [W, mu] using hmem
  have hmemDouble' :
      MemLp
        (fun sample : Fin (n + n + 1) -> ℝ =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := n + n + 1))) 2
        (Measure.pi (fun _ : Fin (n + n + 1) => noiseLaw)) := by
    exact hmemDouble
  have hW1 : MemLp W1 2 (mu.prod mu) := by
    simpa [W1, W] using hmemW.comp_fst mu
  have hW2 : MemLp W2 2 (mu.prod mu) := by
    simpa [W2, W] using hmemW.comp_snd mu
  have hmax : MemLp (fun blocks => max (W1 blocks) (W2 blocks)) 2 (mu.prod mu) :=
    memLp_max_of_memLp (mu.prod mu) W1 W2 hW1 hW2
  have hWmeas : AEMeasurable W mu := by
    simpa [W, mu] using
      (AppliedModelingLib.Probability.upperOrderStatistic_measurable
        (AppliedModelingLib.Probability.topSampleRank (n := n + 1))).aemeasurable
  have hmean : integral (mu.prod mu) W2 = integral (mu.prod mu) W1 := by
    calc
      integral (mu.prod mu) W2 = integral mu W := by
        simpa [W2] using (integral_fun_snd (μ := mu) (ν := mu) W)
      _ = integral (mu.prod mu) W1 := by
        symm
        simpa [W1] using (integral_fun_fst (μ := mu) (ν := mu) W)
  have hvariance1 : ProbabilityTheory.variance W1 (mu.prod mu) =
      ProbabilityTheory.variance W mu := by
    simpa [W1, Function.comp_def] using
      (measurePreserving_fst (μ := mu) (ν := mu)).variance_fun_comp hWmeas
  have hvariance2 : ProbabilityTheory.variance W2 (mu.prod mu) =
      ProbabilityTheory.variance W mu := by
    simpa [W2, Function.comp_def] using
      (measurePreserving_snd (μ := mu) (ν := mu)).variance_fun_comp hWmeas
  have hsameVariance : ProbabilityTheory.variance W2 (mu.prod mu) =
      ProbabilityTheory.variance W1 (mu.prod mu) :=
    hvariance2.trans hvariance1.symm
  have hprojection := dyadicProjection_measurePreserving noiseLaw n
  have hmemProjection :
      MemLp
        (fun blocks : (Fin (n + 1) -> ℝ) × (Fin (n + 1) -> ℝ) =>
          AppliedModelingLib.Probability.upperOrderStatistic (dyadicProjection n blocks)
            (AppliedModelingLib.Probability.topSampleRank (n := n + n + 1))) 2
        (mu.prod mu) := by
    simpa [Function.comp_def, mu] using
      hmemDouble'.comp_measurePreserving hprojection
  have hprojectionLe :
      integral (Measure.pi (fun _ : Fin (n + n + 1) => noiseLaw))
          (fun sample =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + n + 1))) <=
        integral (mu.prod mu) (fun blocks => max (W1 blocks) (W2 blocks)) := by
    calc
      integral (Measure.pi (fun _ : Fin (n + n + 1) => noiseLaw))
          (fun sample =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + n + 1))) =
          integral (mu.prod mu)
            (fun blocks =>
              AppliedModelingLib.Probability.upperOrderStatistic (dyadicProjection n blocks)
                (AppliedModelingLib.Probability.topSampleRank (n := n + n + 1))) := by
        symm
        simpa [mu] using
          (integral_comp_of_measurePreserving hprojection _
            hmemDouble'.aestronglyMeasurable)
      _ <= integral (mu.prod mu) (fun blocks => max (W1 blocks) (W2 blocks)) := by
        apply integral_mono_ae
          (hmemProjection.integrable (by norm_num))
          (hmax.integrable (by norm_num))
        filter_upwards with blocks
        simpa [W1, W2, W] using topOrderStatistic_dyadicProjection_le n blocks
  have hmaxBound := theorem3_integral_max_le_mean_add_two_sqrt_variance
    (mu.prod mu) W1 W2 hW1 hW2 hmean hsameVariance
  have hvarianceW : ProbabilityTheory.variance W mu <= maxVariance n := by
    simpa [W, mu] using hvariance
  have hbound :
      integral (Measure.pi (fun _ : Fin (n + n + 1) => noiseLaw))
          (fun sample =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + n + 1))) <=
        integral mu W + 2 * Real.sqrt (maxVariance n) := by
    calc
      integral (Measure.pi (fun _ : Fin (n + n + 1) => noiseLaw))
          (fun sample =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + n + 1))) <=
          integral (mu.prod mu) (fun blocks => max (W1 blocks) (W2 blocks)) :=
        hprojectionLe
      _ <= integral (mu.prod mu) W1 +
          2 * Real.sqrt (ProbabilityTheory.variance W1 (mu.prod mu)) := hmaxBound
      _ = integral mu W + 2 * Real.sqrt (ProbabilityTheory.variance W mu) := by
        rw [hvariance1]
        have hfst : integral (mu.prod mu) W1 = integral mu W := by
          simpa [W1] using (integral_fun_fst (μ := mu) (ν := mu) W)
        rw [hfst]
      _ <= integral mu W + 2 * Real.sqrt (maxVariance n) := by
        have hsqrt : Real.sqrt (ProbabilityTheory.variance W mu) <=
            Real.sqrt (maxVariance n) := Real.sqrt_le_sqrt hvarianceW
        nlinarith
  change
    integral (Measure.pi (fun _ : Fin (n + n + 1) => noiseLaw))
        (fun sample =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := n + n + 1))) -
      integral mu W <= 2 * Real.sqrt (maxVariance n)
  linarith [hbound]

/-- Multiplicative-index spelling of `iidExpectedTop_doubling_increment_le`.
The proof keeps the finite sample witness in the additive form so its `Fin`
index is definitionally stable. -/
theorem iidExpectedTop_two_mul_increment_le
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (maxVariance : ℕ -> ℝ) (n : ℕ)
    (hmem :
      MemLp
        (fun sample : Fin (n + 1) -> ℝ =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) 2
        (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)))
    (hmemDouble :
      MemLp
        (fun sample : Fin (n + n + 1) -> ℝ =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := n + n + 1))) 2
        (Measure.pi (fun _ : Fin (n + n + 1) => noiseLaw)))
    (hvariance :
      ProbabilityTheory.variance
        (fun sample : Fin (n + 1) -> ℝ =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
        (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) <= maxVariance n) :
    AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
        (fun k => Measure.pi (fun _ : Fin (k + 1) => noiseLaw)) (2 * n) -
      AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
        (fun k => Measure.pi (fun _ : Fin (k + 1) => noiseLaw)) n <=
      2 * Real.sqrt (maxVariance n) := by
  simpa only [two_mul] using
    iidExpectedTop_doubling_increment_le noiseLaw maxVariance n
      hmem hmemDouble hvariance

end IidMaximumDyadic

end

end PG24NoisyMatchingMarkets
