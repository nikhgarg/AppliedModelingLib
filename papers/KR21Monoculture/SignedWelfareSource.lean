import KR21Monoculture.QuantitativeWitnesses
import KR21Monoculture.MallowsOuterSource

open AppliedModelingLib

namespace KR21Monoculture

/-!
# Signed welfare and value-translation invariance

The source observation at 2101.05853.txt:555-568 is not a numerical claim.
It relies on a common translation of every candidate utility preserving the
ranking mechanisms, the strategic equilibrium, and the welfare gap.  This
module records that invariance explicitly and proves the genuinely unbounded
relative-loss consequence of any already-established strict equilibrium welfare
gap.

The conclusion is deliberately conditional on a real strict-dominance/welfare
certificate.  It does not manufacture the source paper's equilibrium witness,
and it does not infer translation invariance from a declaration name: the
translated model literally retains the two PMFs.
-/

/-- Translate every candidate's cardinal value while retaining both ranking laws
definitionally. -/
noncomputable def Model.translateValues {n : ℕ} (M : Model n) (shift : ℝ) : Model n where
  algorithmRanking := M.algorithmRanking
  humanRanking := M.humanRanking
  value := fun c => M.value c + shift

/-- The source ranking laws are unchanged by `Model.translateValues`. -/
theorem Model.translateValues_ranking_laws {n : ℕ} (M : Model n) (shift : ℝ) :
    (M.translateValues shift).algorithmRanking = M.algorithmRanking ∧
      (M.translateValues shift).humanRanking = M.humanRanking :=
  ⟨rfl, rfl⟩

/-- A common cardinal translation preserves the source's strict true order. -/
theorem StrictlyOrderedBy.add_const {n : ℕ} {center : Ranking n}
    {value : ValueProfile n} (hvalue : StrictlyOrderedBy center value)
    (shift : ℝ) :
    StrictlyOrderedBy center (fun c => value c + shift) := by
  intro a b hab
  linarith [hvalue hab]

/-- Translating all candidate values shifts first-mover utility by that constant. -/
theorem expectedFirstMoverUtility_add_const {n : ℕ}
    (mu : PMF (Ranking n)) (value : Candidate n → ℝ) (shift : ℝ) :
    expectedFirstMoverUtility mu (fun c => value c + shift) =
      expectedFirstMoverUtility mu value + shift := by
  unfold expectedFirstMoverUtility
  change pmfExp mu (fun pi => value (firstChoice pi) + shift) =
    pmfExp mu (fun pi => value (firstChoice pi)) + shift
  rw [pmfExp_add]
  simp

/-- Translating all candidate values shifts shared second-mover utility by that
constant. -/
theorem expectedSecondMoverShared_add_const {n : ℕ}
    (mu : PMF (Ranking n)) (value : Candidate n → ℝ) (shift : ℝ) :
    expectedSecondMoverShared mu (fun c => value c + shift) =
      expectedSecondMoverShared mu value + shift := by
  unfold expectedSecondMoverShared
  change pmfExp mu (fun pi => value (secondChoice pi) + shift) =
    pmfExp mu (fun pi => value (secondChoice pi)) + shift
  rw [pmfExp_add]
  simp

/-- Translating all candidate values shifts independent second-mover utility by
that constant. -/
theorem expectedSecondMoverIndependent_add_const {n : ℕ}
    (muSecond muFirst : PMF (Ranking n))
    (value : Candidate n → ℝ) (shift : ℝ) :
    expectedSecondMoverIndependent muSecond muFirst (fun c => value c + shift) =
      expectedSecondMoverIndependent muSecond muFirst value + shift := by
  unfold expectedSecondMoverIndependent
  rw [show (fun pi sigma => secondMoverUtility (fun c => value c + shift) pi sigma) =
      (fun pi sigma => secondMoverUtility value pi sigma + shift) by
        funext pi sigma
        rfl]
  rw [pmfPairExp_add]
  have hconst :
      pmfPairExp muSecond muFirst (fun _ _ => shift) = shift := by
    unfold pmfPairExp
    simp only [pmfExp_const]
  rw [hconst]

/-- Every first-mover payoff shifts by one copy of the value translation. -/
theorem Model.firstMoverEU_translateValues {n : ℕ}
    (M : Model n) (strategy : Strategy) (shift : ℝ) :
    Model.firstMoverEU (M.translateValues shift) strategy =
      Model.firstMoverEU M strategy + shift := by
  cases strategy <;>
    simp [Model.translateValues, Model.firstMoverEU, Model.rankingDist,
      expectedFirstMoverUtility_add_const]

/-- Every second-mover payoff shifts by one copy of the value translation. -/
theorem Model.secondMoverEU_translateValues {n : ℕ}
    (M : Model n) (first second : Strategy) (shift : ℝ) :
    Model.secondMoverEU (M.translateValues shift) first second =
      Model.secondMoverEU M first second + shift := by
  cases first <;> cases second <;>
    simp [Model.translateValues, Model.secondMoverEU, Model.rankingDist,
      expectedSecondMoverShared_add_const,
      expectedSecondMoverIndependent_add_const]

/-- At either symmetric profile, total welfare shifts by two copies of the
common value translation. -/
theorem Model.welfareRandomOrder_self_translateValues {n : ℕ}
    (M : Model n) (strategy : Strategy) (shift : ℝ) :
    Model.welfareRandomOrder (M.translateValues shift) strategy strategy =
      Model.welfareRandomOrder M strategy strategy + 2 * shift := by
  cases strategy
  · rw [Model.welfareRandomOrder_self, Model.welfareRandomOrder_self]
    unfold Model.welfareOrdered Model.translateValues
    rw [expectedFirstMoverUtility_add_const,
      expectedSecondMoverShared_add_const]
    ring
  · rw [Model.welfareRandomOrder_self, Model.welfareRandomOrder_self]
    unfold Model.welfareOrdered Model.translateValues Model.rankingDist
    exact expectedWelfareOrdered_add_const M.humanRanking M.humanRanking M.value shift

/-- Strict dominance is invariant under a common translation of all candidate
utilities. -/
theorem Model.algorithmStrictlyDominant_translateValues_iff {n : ℕ}
    (M : Model n) (shift : ℝ) :
    Model.AlgorithmStrictlyDominant (M.translateValues shift) ↔
      Model.AlgorithmStrictlyDominant M := by
  change
    ((M.translateValues shift).firstMoverEU Strategy.algorithm +
          (M.translateValues shift).secondMoverEU Strategy.algorithm Strategy.algorithm >
        (M.translateValues shift).firstMoverEU Strategy.human +
          (M.translateValues shift).secondMoverEU Strategy.algorithm Strategy.human ∧
      (M.translateValues shift).firstMoverEU Strategy.algorithm +
          (M.translateValues shift).secondMoverEU Strategy.human Strategy.algorithm >
        (M.translateValues shift).firstMoverEU Strategy.human +
          (M.translateValues shift).secondMoverEU Strategy.human Strategy.human) ↔
      (M.firstMoverEU Strategy.algorithm +
          M.secondMoverEU Strategy.algorithm Strategy.algorithm >
        M.firstMoverEU Strategy.human +
          M.secondMoverEU Strategy.algorithm Strategy.human ∧
      M.firstMoverEU Strategy.algorithm +
          M.secondMoverEU Strategy.human Strategy.algorithm >
        M.firstMoverEU Strategy.human +
          M.secondMoverEU Strategy.human Strategy.human)
  simp only [Model.firstMoverEU_translateValues,
    Model.secondMoverEU_translateValues]
  constructor <;> rintro ⟨hAgainstAlgorithm, hAgainstHuman⟩ <;>
    constructor <;> linarith

/-- The all-human versus all-algorithm welfare comparison is invariant under a
common translation of all candidate utilities. -/
theorem Model.humanProfileBeatsAlgorithmProfile_translateValues_iff {n : ℕ}
    (M : Model n) (shift : ℝ) :
    Model.HumanProfileBeatsAlgorithmProfile (M.translateValues shift) ↔
      Model.HumanProfileBeatsAlgorithmProfile M := by
  unfold Model.HumanProfileBeatsAlgorithmProfile
  rw [Model.welfareRandomOrder_self_translateValues,
    Model.welfareRandomOrder_self_translateValues]
  constructor <;> intro h <;> linarith

/-- A KR21 monoculture paradox survives a common translation of all candidate
utilities, with its ranking laws unchanged. -/
theorem Model.hasKR21MonocultureParadox_translateValues_iff {n : ℕ}
    (M : Model n) (shift : ℝ) :
    Model.HasKR21MonocultureParadox (M.translateValues shift) ↔
      Model.HasKR21MonocultureParadox M := by
  unfold Model.HasKR21MonocultureParadox
  rw [Model.algorithmStrictlyDominant_translateValues_iff,
    Model.humanProfileBeatsAlgorithmProfile_translateValues_iff]

/-- For fixed-center Mallows, the translated game is literally the game obtained
by supplying the translated source value profile to the same ranking family. -/
theorem fixedCenterMallowsPointFamily_modelAt_translateValues_eq
    {n : ℕ} (center : Ranking n) (value : ValueProfile n)
    (thetaA thetaH shift : ℝ) :
    ((fixedCenterMallowsPointFamily center value).modelAt thetaA thetaH).translateValues
        shift =
      (fixedCenterMallowsPointFamily center (fun c => value c + shift)).modelAt
        thetaA thetaH := by
  rfl

/-- Welfare loss relative to a positive social optimum. -/
noncomputable def relativeWelfareLoss (equilibriumWelfare optimumWelfare : ℝ) : ℝ :=
  (optimumWelfare - equilibriumWelfare) / optimumWelfare

/-- A strict welfare gap can be translated to make the equilibrium welfare
negative, the optimum positive, and the relative loss larger than any prescribed
positive bound. -/
theorem exists_value_translation_unbounded_relative_welfare_loss
    (equilibriumWelfare optimumWelfare bound : ℝ)
    (hgap : equilibriumWelfare < optimumWelfare) (hbound : 0 < bound) :
    ∃ shift,
      equilibriumWelfare + 2 * shift < 0 ∧
        0 < optimumWelfare + 2 * shift ∧
          bound < relativeWelfareLoss
            (equilibriumWelfare + 2 * shift)
            (optimumWelfare + 2 * shift) := by
  let gap := optimumWelfare - equilibriumWelfare
  let epsilon := gap / (bound + 1)
  let shift := (epsilon - optimumWelfare) / 2
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    linarith
  have hbound_one_pos : 0 < bound + 1 := by
    linarith
  have hepsilon_pos : 0 < epsilon := by
    exact div_pos hgap_pos hbound_one_pos
  have hepsilon_lt_gap : epsilon < gap := by
    rw [div_lt_iff₀ hbound_one_pos]
    nlinarith [hgap_pos, hbound]
  have hoptimum : optimumWelfare + 2 * shift = epsilon := by
    dsimp [shift]
    ring
  have hequilibrium : equilibriumWelfare + 2 * shift = epsilon - gap := by
    dsimp [shift, gap]
    ring
  have hratio : gap / epsilon = bound + 1 := by
    dsimp [epsilon]
    field_simp [ne_of_gt hgap_pos, ne_of_gt hbound_one_pos]
  refine ⟨shift, ?_, ?_, ?_⟩
  · rw [hequilibrium]
    exact sub_neg.mpr hepsilon_lt_gap
  · rw [hoptimum]
    exact hepsilon_pos
  · rw [relativeWelfareLoss, hequilibrium, hoptimum]
    calc
      bound < bound + 1 := by linarith
      _ = gap / epsilon := hratio.symm
      _ = (epsilon - (epsilon - gap)) / epsilon := by ring

/-- Source-facing strengthening of the signed-welfare observation.  Once an
actual KR21 equilibrium certificate is available, the literal same-ranking-law
translation yields a negative all-algorithm equilibrium, a positive all-human
benchmark, and an arbitrarily large relative loss. -/
theorem Model.exists_translateValues_with_unbounded_relative_welfare_loss {n : ℕ}
    (M : Model n) (hparadox : Model.HasKR21MonocultureParadox M)
    (bound : ℝ) (hbound : 0 < bound) :
    ∃ shift,
      Model.HasKR21MonocultureParadox (M.translateValues shift) ∧
        Model.welfareRandomOrder (M.translateValues shift)
          Strategy.algorithm Strategy.algorithm < 0 ∧
        0 < Model.welfareRandomOrder (M.translateValues shift)
          Strategy.human Strategy.human ∧
        bound < relativeWelfareLoss
          (Model.welfareRandomOrder (M.translateValues shift)
            Strategy.algorithm Strategy.algorithm)
          (Model.welfareRandomOrder (M.translateValues shift)
            Strategy.human Strategy.human) := by
  have hgap :
      Model.welfareRandomOrder M Strategy.algorithm Strategy.algorithm <
        Model.welfareRandomOrder M Strategy.human Strategy.human := by
    exact hparadox.2
  rcases exists_value_translation_unbounded_relative_welfare_loss
      (Model.welfareRandomOrder M Strategy.algorithm Strategy.algorithm)
      (Model.welfareRandomOrder M Strategy.human Strategy.human)
      bound hgap hbound with
    ⟨shift, hnegative, hpositive, hloss⟩
  refine ⟨shift,
    (Model.hasKR21MonocultureParadox_translateValues_iff M shift).2 hparadox,
    ?_, ?_, ?_⟩
  · rw [Model.welfareRandomOrder_self_translateValues]
    exact hnegative
  · rw [Model.welfareRandomOrder_self_translateValues]
    exact hpositive
  · rw [Model.welfareRandomOrder_self_translateValues,
      Model.welfareRandomOrder_self_translateValues]
    exact hloss

/-- The corrected fixed-center Mallows Theorem 1 route supplies the strict
equilibrium welfare gap needed by the signed-welfare result.  This is a genuine
source-model construction with deterministically known, strictly ordered values;
the common translation retains the fixed-center Mallows ranking laws exactly. -/
theorem fixedCenterMallows_exists_unbounded_relative_welfare_loss
    {n : ℕ} (center : Ranking n) (value : ValueProfile n)
    (hvalue : StrictlyOrderedBy center value) (hn : 0 < n)
    (thetaH : ℝ) (hthetaH : 0 < thetaH) (bound : ℝ) (hbound : 0 < bound) :
    ∃ thetaA, thetaH < thetaA ∧ ∃ shift,
      let M := (fixedCenterMallowsPointFamily center value).modelAt thetaA thetaH
      Model.HasKR21MonocultureParadox (M.translateValues shift) ∧
        Model.welfareRandomOrder (M.translateValues shift)
          Strategy.algorithm Strategy.algorithm < 0 ∧
        0 < Model.welfareRandomOrder (M.translateValues shift)
          Strategy.human Strategy.human ∧
        bound < relativeWelfareLoss
          (Model.welfareRandomOrder (M.translateValues shift)
            Strategy.algorithm Strategy.algorithm)
          (Model.welfareRandomOrder (M.translateValues shift)
            Strategy.human Strategy.human) := by
  rcases fixedCenterMallows_point_theorem1Target center value hvalue hn thetaH hthetaH with
    ⟨thetaA, hthetaA, hparadox⟩
  rcases Model.exists_translateValues_with_unbounded_relative_welfare_loss
      ((fixedCenterMallowsPointFamily center value).modelAt thetaA thetaH)
      hparadox bound hbound with
    ⟨shift, htranslated, hnegative, hpositive, hloss⟩
  exact ⟨thetaA, hthetaA, shift, htranslated, hnegative, hpositive, hloss⟩

end KR21Monoculture
