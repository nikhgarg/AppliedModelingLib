import KR21Monoculture.ThreeFirmMallowsPMFBridge
import KR21Monoculture.DirectRankMeanBridge

open scoped BigOperators
open AppliedModelingLib

namespace KR21Monoculture

/-!
# Three-firm finite Mallows product-law bridge

The direct rank-mean calculations use rational finite masses.  This module
packages the relevant random inputs as actual `PMF`s and proves their atoms
are exactly the real casts of those rational masses.  In particular, the
algorithm ranking is a single shared draw at `q = 1/2`, while human rankings
are independent draws at `q = 4/7`; firm arrival is an independent uniform
draw over the six source orders.

This is deliberately only a finite ranking/arrival bridge.  It does not claim
an iid Uniform cardinal-value construction, an equilibrium result, or a
source-welfare bridge.
-/

open AppliedModelingLib.SocialChoice.Ranking

/-! ## Generic finite products -/

/-- The finite independent product of two discrete source laws. -/
noncomputable def sourceFinitePMFProduct
    {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β) : PMF (α × β) :=
  PMF.ofFintype (fun ab => p ab.1 * q ab.2) (by
    rw [Fintype.sum_prod_type]
    calc
      (∑ a : α, ∑ b : β, p a * q b) =
          ∑ a : α, p a * (∑ b : β, q b) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
      _ = ∑ a : α, p a := by
            have hq : (∑ b : β, q b) = 1 := by
              simpa only [tsum_fintype] using q.tsum_coe
            rw [hq]
            simp
      _ = 1 := by
            simpa only [tsum_fintype] using p.tsum_coe)

/-- Atom formula for the actual finite independent product law. -/
@[simp] theorem sourceFinitePMFProduct_apply
    {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β) (a : α) (b : β) :
    sourceFinitePMFProduct p q (a, b) = p a * q b := rfl

/-- Real atom formula for the actual finite independent product law. -/
theorem sourceFinitePMFProduct_apply_toReal
    {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β) (a : α) (b : β) :
    (sourceFinitePMFProduct p q (a, b)).toReal =
      (p a).toReal * (q b).toReal := by
  rw [sourceFinitePMFProduct_apply, ENNReal.toReal_mul]

/-! ## The three source input laws -/

/-- The actual four-candidate source algorithm-ranking law at inverse
Mallows parameter `q = 1/2`. -/
noncomputable def sourceAlgorithmRankingLaw : PMF SourceFourRanking :=
  sourceExecutableMallowsPMF sourceAlgorithmQ sourceAlgorithmQ_pos

/-- The actual four-candidate source human-ranking law at inverse Mallows
parameter `q = 4/7`. -/
noncomputable def sourceHumanRankingLaw : PMF SourceFourRanking :=
  sourceExecutableMallowsPMF sourceHumanQ sourceHumanQ_pos

/-- The actual uniform six-order firm-arrival law. -/
noncomputable def sourceUniformFirmOrderLaw : PMF SourceFirmOrder :=
  PMF.ofFintype
    (fun order => ENNReal.ofReal ((sourceUniformFirmOrderMass : ℚ) : ℝ))
    (by
      have hnonneg :
          ∀ order ∈ (Finset.univ : Finset SourceFirmOrder),
            0 ≤ ((sourceUniformFirmOrderMass : ℚ) : ℝ) := by
        intro order _
        norm_num [sourceUniformFirmOrderMass]
      have hsum :
          (∑ order : SourceFirmOrder,
            ((sourceUniformFirmOrderMass : ℚ) : ℝ)) = 1 := by
        exact_mod_cast sourceUniformFirmOrderMass_sum
      calc
        (∑ order : SourceFirmOrder,
          ENNReal.ofReal ((sourceUniformFirmOrderMass : ℚ) : ℝ)) =
            ENNReal.ofReal
              (∑ order : SourceFirmOrder,
                ((sourceUniformFirmOrderMass : ℚ) : ℝ)) := by
              rw [ENNReal.ofReal_sum_of_nonneg hnonneg]
        _ = 1 := by rw [hsum]; norm_num)

/-- The algorithm law has exactly the executable `q=1/2` source table as
its real atom masses. -/
theorem sourceAlgorithmRankingLaw_apply_toReal
    (algorithm : SourceFourRanking) :
    (sourceAlgorithmRankingLaw algorithm).toReal =
      ((sourceAlgorithmMallowsMass algorithm : ℚ) : ℝ) := by
  rw [sourceAlgorithmRankingLaw, sourceExecutableMallowsPMF,
    PMF.ofFintype_apply,
    ENNReal.toReal_ofReal
      (sourceExecutableMallowsMass_cast_nonneg
        sourceAlgorithmQ sourceAlgorithmQ_pos algorithm)]
  exact congrArg (fun x : ℚ => (x : ℝ))
    (sourceAlgorithmMallowsMass_eq_executable algorithm).symm

/-- The human law has exactly the executable `q=4/7` source table as its
real atom masses. -/
theorem sourceHumanRankingLaw_apply_toReal
    (human : SourceFourRanking) :
    (sourceHumanRankingLaw human).toReal =
      ((sourceHumanMallowsMass human : ℚ) : ℝ) := by
  rw [sourceHumanRankingLaw, sourceExecutableMallowsPMF,
    PMF.ofFintype_apply,
    ENNReal.toReal_ofReal
      (sourceExecutableMallowsMass_cast_nonneg
        sourceHumanQ sourceHumanQ_pos human)]
  exact congrArg (fun x : ℚ => (x : ℝ))
    (sourceHumanMallowsMass_eq_executable human).symm

/-- The packaged algorithm source law is the library's actual four-candidate
Mallows law at the source parameter `q=1/2`, not merely a table with the same
normalizing constant. -/
theorem sourceAlgorithmRankingLaw_apply_eq_mallowsSpecOfQ
    (algorithm : SourceFourRanking) :
    sourceAlgorithmRankingLaw algorithm =
      (MallowsSpec.ofQ (Equiv.refl (Candidate 2)) ((1 : ℝ) / 2)
        (by norm_num)).law (sourceFourRankingToRanking algorithm) := by
  rw [sourceAlgorithmRankingLaw]
  simpa only [sourceAlgorithmQ, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    using sourceExecutableMallowsPMF_apply_eq_mallowsSpecOfQ
      sourceAlgorithmQ sourceAlgorithmQ_pos algorithm

/-- The packaged human source law is the library's actual four-candidate
Mallows law at the source parameter `q=4/7`. -/
theorem sourceHumanRankingLaw_apply_eq_mallowsSpecOfQ
    (human : SourceFourRanking) :
    sourceHumanRankingLaw human =
      (MallowsSpec.ofQ (Equiv.refl (Candidate 2)) ((4 : ℝ) / 7)
        (by norm_num)).law (sourceFourRankingToRanking human) := by
  rw [sourceHumanRankingLaw]
  simpa only [sourceHumanQ, Rat.cast_div, Rat.cast_ofNat]
    using sourceExecutableMallowsPMF_apply_eq_mallowsSpecOfQ
      sourceHumanQ sourceHumanQ_pos human

/-- The arrival law has the literal `1/6` source mass at every named order. -/
theorem sourceUniformFirmOrderLaw_apply_toReal
    (order : SourceFirmOrder) :
    (sourceUniformFirmOrderLaw order).toReal =
      ((sourceUniformFirmOrderMass : ℚ) : ℝ) := by
  rw [sourceUniformFirmOrderLaw, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal]
  norm_num [sourceUniformFirmOrderMass]

/-! ## Shared AAA law -/

/-- One shared algorithm ranking and one independent uniform firm-arrival
order: the actual finite source law for the AAA rank-mean model. -/
noncomputable def sourceAAAProductLaw : PMF (SourceFourRanking × SourceFirmOrder) :=
  sourceFinitePMFProduct sourceAlgorithmRankingLaw sourceUniformFirmOrderLaw

/-- The PMF atom of the actual shared-AAA law is the real cast of the direct
rational joint mass. -/
theorem sourceAAAProductLaw_apply_toReal
    (algorithm : SourceFourRanking) (order : SourceFirmOrder) :
    (sourceAAAProductLaw (algorithm, order)).toReal =
      ((sourceDirectRankMeanAAAJointMass algorithm order : ℚ) : ℝ) := by
  rw [sourceAAAProductLaw, sourceFinitePMFProduct_apply_toReal,
    sourceAlgorithmRankingLaw_apply_toReal,
    sourceUniformFirmOrderLaw_apply_toReal]
  simp only [sourceDirectRankMeanAAAJointMass, Rat.cast_mul]

/-- The real finite-PMF expectation of the direct shared-AAA payoff. -/
noncomputable def sourceAAAProductLawExpectation : ℝ :=
  ∑ algorithm : SourceFourRanking,
    ∑ order : SourceFirmOrder,
      (sourceAAAProductLaw (algorithm, order)).toReal *
        (sourceDirectRankMeanConditionalAAA algorithm order : ℝ)

/-- The actual PMF expectation is exactly the real cast of the existing
direct rational AAA expectation. -/
theorem sourceAAAProductLawExpectation_eq_cast_direct :
    sourceAAAProductLawExpectation =
      ((sourceDirectRankMeanExpectedAAA : ℚ) : ℝ) := by
  unfold sourceAAAProductLawExpectation sourceDirectRankMeanExpectedAAA
  simp_rw [sourceAAAProductLaw_apply_toReal]
  norm_cast

/-! ## Independent HHH law -/

/-- The actual product law of two independently sampled human rankings. -/
noncomputable def sourceHumanPairRankingLaw :
    PMF (SourceFourRanking × SourceFourRanking) :=
  sourceFinitePMFProduct sourceHumanRankingLaw sourceHumanRankingLaw

/-- The actual product law of three independently sampled human rankings. -/
noncomputable def sourceHumanTripleRankingLaw :
    PMF ((SourceFourRanking × SourceFourRanking) × SourceFourRanking) :=
  sourceFinitePMFProduct sourceHumanPairRankingLaw sourceHumanRankingLaw

/-- The actual three-independent-human plus uniform-arrival law for the HHH
rank-mean model. -/
noncomputable def sourceHHHProductLaw :
    PMF (((SourceFourRanking × SourceFourRanking) × SourceFourRanking) ×
      SourceFirmOrder) :=
  sourceFinitePMFProduct sourceHumanTripleRankingLaw sourceUniformFirmOrderLaw

/-- The direct rational joint mass of the independent HHH ranking and arrival
experiment.  It only packages the already-proved three-human product mass
with the independent uniform arrival coordinate. -/
def sourceDirectRankMeanHHHJointMass
    (h0 h1 h2 : SourceFourRanking) (order : SourceFirmOrder) : ℚ :=
  sourceHumanTripleProductMass h0 h1 h2 * sourceUniformFirmOrderMass

/-- Every atom of the actual HHH PMF is exactly the real cast of its direct
rational three-human-plus-arrival joint mass. -/
theorem sourceHHHProductLaw_apply_toReal
    (h0 h1 h2 : SourceFourRanking) (order : SourceFirmOrder) :
    (sourceHHHProductLaw (((h0, h1), h2), order)).toReal =
      ((sourceDirectRankMeanHHHJointMass h0 h1 h2 order : ℚ) : ℝ) := by
  rw [sourceHHHProductLaw, sourceFinitePMFProduct_apply_toReal,
    sourceHumanTripleRankingLaw, sourceFinitePMFProduct_apply_toReal,
    sourceHumanPairRankingLaw, sourceFinitePMFProduct_apply_toReal]
  simp_rw [sourceHumanRankingLaw_apply_toReal]
  rw [sourceUniformFirmOrderLaw_apply_toReal]
  simp only [sourceDirectRankMeanHHHJointMass, sourceHumanTripleProductMass,
    Rat.cast_mul]

/-- The real finite-PMF expectation of the direct all-human payoff.  The
nesting is the canonical source-coordinate order and therefore makes every
independent human draw visible. -/
noncomputable def sourceHHHProductLawExpectation : ℝ :=
  ∑ order : SourceFirmOrder,
    ∑ h0 : SourceFourRanking,
      ∑ h1 : SourceFourRanking,
        ∑ h2 : SourceFourRanking,
          (sourceHHHProductLaw (((h0, h1), h2), order)).toReal *
            (sourceFocalUtility sourceProfileHHH .r0123
              (sourceHumanRankings h0 h1 h2) order : ℝ)

/-- The actual HHH PMF expectation is the real cast of the existing direct
finite three-human rank-mean expectation. -/
theorem sourceHHHProductLawExpectation_eq_cast_direct :
    sourceHHHProductLawExpectation =
      ((sourceDirectRankMeanExpectedHHH : ℚ) : ℝ) := by
  rw [← sourceCanonicalDirectRankMeanExpectedHHH_eq_direct]
  unfold sourceHHHProductLawExpectation sourceCanonicalDirectRankMeanExpectedHHH
    sourceCanonicalDirectRankMeanConditionalHHH
  simp_rw [sourceHHHProductLaw_apply_toReal]
  norm_cast
  simp only [sourceDirectRankMeanHHHJointMass]
  apply Finset.sum_congr rfl
  intro order _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h0 _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h1 _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h2 _
  ring

/-! ## Mixed algorithm/human laws -/

/-- The actual law of one shared algorithm ranking, one independent human
ranking, and one independent uniform arrival order.  It is used for both the
HAA and AAH rank-mean profiles; the profile determines which firm reads the
human ranking. -/
noncomputable def sourceOneHumanProductLaw :
    PMF ((SourceFourRanking × SourceFourRanking) × SourceFirmOrder) :=
  sourceFinitePMFProduct
    (sourceFinitePMFProduct sourceAlgorithmRankingLaw sourceHumanRankingLaw)
    sourceUniformFirmOrderLaw

/-- The rational atom mass of the one-human mixed source experiment. -/
def sourceDirectRankMeanOneHumanJointMass
    (algorithm human : SourceFourRanking) (order : SourceFirmOrder) : ℚ :=
  sourceAlgorithmMallowsMass algorithm * sourceHumanMallowsMass human *
    sourceUniformFirmOrderMass

/-- Atomwise correspondence between the actual PMF and the direct rational
one-human experiment. -/
theorem sourceOneHumanProductLaw_apply_toReal
    (algorithm human : SourceFourRanking) (order : SourceFirmOrder) :
    (sourceOneHumanProductLaw ((algorithm, human), order)).toReal =
      ((sourceDirectRankMeanOneHumanJointMass algorithm human order : ℚ) : ℝ) := by
  rw [sourceOneHumanProductLaw, sourceFinitePMFProduct_apply_toReal,
    sourceFinitePMFProduct_apply_toReal]
  simp_rw [sourceAlgorithmRankingLaw_apply_toReal,
    sourceHumanRankingLaw_apply_toReal]
  rw [sourceUniformFirmOrderLaw_apply_toReal]
  simp only [sourceDirectRankMeanOneHumanJointMass, Rat.cast_mul]

/-- The actual PMF expectation for the HAA direct rank-mean payoff. -/
noncomputable def sourceHAAProductLawExpectation : ℝ :=
  ∑ algorithm : SourceFourRanking,
    ∑ order : SourceFirmOrder,
      ∑ human : SourceFourRanking,
        (sourceOneHumanProductLaw ((algorithm, human), order)).toReal *
          (sourceFocalUtility sourceProfileHAA algorithm
            (sourceHumanRankings human .r0123 .r0123) order : ℝ)

/-- The HAA PMF expectation is the real cast of the existing direct rational
finite expectation. -/
theorem sourceHAAProductLawExpectation_eq_cast_direct :
    sourceHAAProductLawExpectation =
      ((sourceDirectRankMeanExpectedHAA : ℚ) : ℝ) := by
  unfold sourceHAAProductLawExpectation sourceDirectRankMeanExpectedHAA
    sourceDirectRankMeanConditionalHAA
  simp_rw [sourceOneHumanProductLaw_apply_toReal]
  norm_cast
  simp only [sourceDirectRankMeanOneHumanJointMass]
  apply Finset.sum_congr rfl
  intro algorithm _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro order _
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro human _
  ring

/-- The actual PMF expectation for the AAH direct rank-mean payoff. -/
noncomputable def sourceAAHProductLawExpectation : ℝ :=
  ∑ algorithm : SourceFourRanking,
    ∑ order : SourceFirmOrder,
      ∑ human : SourceFourRanking,
        (sourceOneHumanProductLaw ((algorithm, human), order)).toReal *
          (sourceFocalUtility sourceProfileAAH algorithm
            (sourceHumanRankings .r0123 .r0123 human) order : ℝ)

/-- The AAH PMF expectation is the real cast of the existing direct rational
finite expectation. -/
theorem sourceAAHProductLawExpectation_eq_cast_direct :
    sourceAAHProductLawExpectation =
      ((sourceDirectRankMeanExpectedAAH : ℚ) : ℝ) := by
  unfold sourceAAHProductLawExpectation sourceDirectRankMeanExpectedAAH
    sourceDirectRankMeanConditionalAAH
  simp_rw [sourceOneHumanProductLaw_apply_toReal]
  norm_cast
  simp only [sourceDirectRankMeanOneHumanJointMass]
  apply Finset.sum_congr rfl
  intro algorithm _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro order _
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro human _
  ring

/-- The actual law of one shared algorithm ranking, two independent human
rankings, and an independent uniform arrival order.  It is used for HAH and
AHH, with the profile specifying which firm receives each human coordinate. -/
noncomputable def sourceTwoHumanProductLaw :
    PMF ((SourceFourRanking × (SourceFourRanking × SourceFourRanking)) ×
      SourceFirmOrder) :=
  sourceFinitePMFProduct
    (sourceFinitePMFProduct sourceAlgorithmRankingLaw sourceHumanPairRankingLaw)
    sourceUniformFirmOrderLaw

/-- The rational atom mass of the two-human mixed source experiment. -/
def sourceDirectRankMeanTwoHumanJointMass
    (algorithm hLeft hRight : SourceFourRanking) (order : SourceFirmOrder) : ℚ :=
  sourceAlgorithmMallowsMass algorithm *
    sourceHumanPairProductMass hLeft hRight * sourceUniformFirmOrderMass

/-- Atomwise correspondence between the actual PMF and the direct rational
two-human experiment. -/
theorem sourceTwoHumanProductLaw_apply_toReal
    (algorithm hLeft hRight : SourceFourRanking) (order : SourceFirmOrder) :
    (sourceTwoHumanProductLaw ((algorithm, (hLeft, hRight)), order)).toReal =
      ((sourceDirectRankMeanTwoHumanJointMass algorithm hLeft hRight order : ℚ) : ℝ) := by
  rw [sourceTwoHumanProductLaw, sourceFinitePMFProduct_apply_toReal,
    sourceFinitePMFProduct_apply_toReal,
    sourceHumanPairRankingLaw, sourceFinitePMFProduct_apply_toReal]
  simp_rw [sourceAlgorithmRankingLaw_apply_toReal,
    sourceHumanRankingLaw_apply_toReal]
  rw [sourceUniformFirmOrderLaw_apply_toReal]
  simp only [sourceDirectRankMeanTwoHumanJointMass,
    sourceHumanPairProductMass, Rat.cast_mul]

/-- The actual PMF expectation for the HAH direct rank-mean payoff. -/
noncomputable def sourceHAHProductLawExpectation : ℝ :=
  ∑ algorithm : SourceFourRanking,
    ∑ order : SourceFirmOrder,
      ∑ h0 : SourceFourRanking,
        ∑ h2 : SourceFourRanking,
          (sourceTwoHumanProductLaw ((algorithm, (h0, h2)), order)).toReal *
            (sourceFocalUtility sourceProfileHAH algorithm
              (sourceHumanRankings h0 .r0123 h2) order : ℝ)

/-- The HAH PMF expectation is the real cast of the canonical direct product
expectation that displays both independent human coordinates. -/
theorem sourceHAHProductLawExpectation_eq_cast_canonical :
    sourceHAHProductLawExpectation =
      ((sourceCanonicalDirectRankMeanExpectedHAH : ℚ) : ℝ) := by
  unfold sourceHAHProductLawExpectation sourceCanonicalDirectRankMeanExpectedHAH
    sourceCanonicalDirectRankMeanConditionalHAH
  simp_rw [sourceTwoHumanProductLaw_apply_toReal]
  norm_cast
  simp only [sourceDirectRankMeanTwoHumanJointMass]
  apply Finset.sum_congr rfl
  intro algorithm _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro order _
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h0 _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h2 _
  ring

/-- The HAH PMF expectation is the real cast of the existing direct rational
finite expectation. -/
theorem sourceHAHProductLawExpectation_eq_cast_direct :
    sourceHAHProductLawExpectation =
      ((sourceDirectRankMeanExpectedHAH : ℚ) : ℝ) := by
  rw [sourceHAHProductLawExpectation_eq_cast_canonical,
    sourceCanonicalDirectRankMeanExpectedHAH_eq_direct]

/-- The actual PMF expectation for the AHH direct rank-mean payoff. -/
noncomputable def sourceAHHProductLawExpectation : ℝ :=
  ∑ algorithm : SourceFourRanking,
    ∑ order : SourceFirmOrder,
      ∑ h1 : SourceFourRanking,
        ∑ h2 : SourceFourRanking,
          (sourceTwoHumanProductLaw ((algorithm, (h1, h2)), order)).toReal *
            (sourceFocalUtility sourceProfileAHH algorithm
              (sourceHumanRankings .r0123 h1 h2) order : ℝ)

/-- The AHH PMF expectation is the real cast of the canonical direct product
expectation that displays both independent human coordinates. -/
theorem sourceAHHProductLawExpectation_eq_cast_canonical :
    sourceAHHProductLawExpectation =
      ((sourceCanonicalDirectRankMeanExpectedAHH : ℚ) : ℝ) := by
  unfold sourceAHHProductLawExpectation sourceCanonicalDirectRankMeanExpectedAHH
    sourceCanonicalDirectRankMeanConditionalAHH
  simp_rw [sourceTwoHumanProductLaw_apply_toReal]
  norm_cast
  simp only [sourceDirectRankMeanTwoHumanJointMass]
  apply Finset.sum_congr rfl
  intro algorithm _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro order _
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h1 _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h2 _
  ring

/-- The AHH PMF expectation is the real cast of the existing direct rational
finite expectation. -/
theorem sourceAHHProductLawExpectation_eq_cast_direct :
    sourceAHHProductLawExpectation =
      ((sourceDirectRankMeanExpectedAHH : ℚ) : ℝ) := by
  rw [sourceAHHProductLawExpectation_eq_cast_canonical,
    sourceCanonicalDirectRankMeanExpectedAHH_eq_direct]

end KR21Monoculture
