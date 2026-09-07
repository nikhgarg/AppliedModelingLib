import PKG25NoFreeLunch.PartitionCalibration
import PKG25NoFreeLunch.JointLawFinitePartition
import PKG25NoFreeLunch.ParameterizedS1

/-!
# PKG25 witness partition realizations

The finite witnesses in the source proof are not merely calibrated settings:
this module records the actual finite cell maps whose conditional label-one
probabilities reproduce their advertised predictors.  It first connects the
finite mass/conditional-label representation to the raw joint PMF used by the
source-facing partition construction.
-/

namespace PKG25NoFreeLunch

section FiniteJointBridge

theorem finiteJointLawPMF_inputMass_eq {n : ℕ}
    (S : FiniteCollaborationSetting n) (x : S.X) :
    jointInputMass (finiteJointLawPMF S) x = S.mass x := by
  simp [jointInputMass, pointAccuracy]
  ring

theorem finiteJointLawPMF_trueInputMass_eq {n : ℕ}
    (S : FiniteCollaborationSetting n) (x : S.X) :
    jointTrueInputMass (finiteJointLawPMF S) x = S.mass x * S.eta x := by
  simp [jointTrueInputMass, pointAccuracy]

theorem finiteJointLawPMF_partitionCellMass_eq {n : ℕ}
    (S : FiniteCollaborationSetting n) {Cell : Type}
    [Fintype Cell] [DecidableEq Cell] (cell : S.X → Cell) (c : Cell) :
    jointPartitionCellMass (finiteJointLawPMF S) cell c =
      partitionCellMass S.mass cell c := by
  unfold jointPartitionCellMass partitionCellMass
  refine Finset.sum_congr rfl ?_
  intro x _hx
  exact finiteJointLawPMF_inputMass_eq S x

theorem finiteJointLawPMF_partitionCellTrueMass_eq {n : ℕ}
    (S : FiniteCollaborationSetting n) {Cell : Type}
    [Fintype Cell] [DecidableEq Cell] (cell : S.X → Cell) (c : Cell) :
    jointPartitionCellTrueMass (finiteJointLawPMF S) cell c =
      partitionCellLabelMass S.mass S.eta cell c := by
  unfold jointPartitionCellTrueMass partitionCellLabelMass
  refine Finset.sum_congr rfl ?_
  intro x _hx
  exact finiteJointLawPMF_trueInputMass_eq S x

theorem finiteJointLawPMF_partitionPredictor_eq {n : ℕ}
    (S : FiniteCollaborationSetting n) {Cell : Type}
    [Fintype Cell] [DecidableEq Cell] (cell : S.X → Cell) (x : S.X) :
    jointPartitionPredictor (finiteJointLawPMF S) cell x =
      partitionPredictor S.mass S.eta cell x := by
  unfold jointPartitionPredictor partitionPredictor
  unfold jointPartitionCellPrediction partitionCellPrediction
  rw [finiteJointLawPMF_partitionCellMass_eq,
    finiteJointLawPMF_partitionCellTrueMass_eq]

end FiniteJointBridge

/-! ## Lemma 8 / Proposition 7: the `\{0,i\}` cells -/

/-- The source cell map for agent `i`: the distinguished pair is one cell,
and every other input point is a singleton cell. -/
def part1SourceCell {n : ℕ} (i : Fin n) : Part1Point n → Part1Point n
  | none => none
  | some j => if j = i then none else some j

theorem part1SourceCell_mass_none {n : ℕ} {b : Label} {p : Fin n → ℝ}
    (i : Fin n) :
    partitionCellMass (part1Mass b p) (part1SourceCell i) none =
      part1Mass b p none + part1Mass b p (some i) := by
  classical
  simp [partitionCellMass, Finset.sum_filter, part1SourceCell]

theorem part1SourceCell_trueMass_none {n : ℕ} {b : Label} {p : Fin n → ℝ}
    (i : Fin n) :
    partitionCellLabelMass (part1Mass b p) (part1Eta b) (part1SourceCell i) none =
      part1Mass b p (none : Part1Point n) * part1Eta b (none : Part1Point n) +
        part1Mass b p (some i) * part1Eta b (some i) := by
  classical
  simp [partitionCellLabelMass, Finset.sum_filter, part1SourceCell]

theorem part1SourceCell_mass_some {n : ℕ} {b : Label} {p : Fin n → ℝ}
    {i j : Fin n} (hji : j ≠ i) :
    partitionCellMass (part1Mass b p) (part1SourceCell i) (some j) =
      part1Mass b p (some j) := by
  classical
  have hcell : ∀ x : Fin n, (¬ x = i ∧ x = j) ↔ x = j := by
    intro x
    constructor
    · exact fun h => h.2
    · intro hx
      subst x
      exact ⟨hji, rfl⟩
  simp [partitionCellMass, Finset.sum_filter, part1SourceCell]
  simp_rw [hcell]
  simp

theorem part1SourceCell_trueMass_some {n : ℕ} {b : Label} {p : Fin n → ℝ}
    {i j : Fin n} (hji : j ≠ i) :
    partitionCellLabelMass (part1Mass b p) (part1Eta b) (part1SourceCell i) (some j) =
      part1Mass b p (some j) * part1Eta b (some j) := by
  classical
  have hcell : ∀ x : Fin n, (¬ x = i ∧ x = j) ↔ x = j := by
    intro x
    constructor
    · exact fun h => h.2
    · intro hx
      subst x
      exact ⟨hji, rfl⟩
  simp [partitionCellLabelMass, Finset.sum_filter, part1SourceCell]
  simp_rw [hcell]
  simp

theorem part1SourceCell_prediction_none {n : ℕ} {b : Label} {p : Fin n → ℝ}
    (hp : Interior p) (i : Fin n) :
    partitionCellPrediction (part1Mass b p) (part1Eta b) (part1SourceCell i) none =
      p i := by
  unfold partitionCellPrediction
  rw [part1SourceCell_mass_none, part1SourceCell_trueMass_none]
  have hpos :
      0 < part1Mass b p (none : Part1Point n) + part1Mass b p (some i) :=
    add_pos (part1Mass_none_pos hp) (part1Mass_some_pos hp i)
  rw [if_neg (ne_of_gt hpos)]
  rw [part1_pair_labelMass_eq hp i]
  field_simp [ne_of_gt hpos]

theorem part1SourceCell_prediction_some {n : ℕ} {b : Label} {p : Fin n → ℝ}
    (hp : Interior p) {i j : Fin n} (hji : j ≠ i) :
    partitionCellPrediction (part1Mass b p) (part1Eta b) (part1SourceCell i) (some j) =
      labelReal b := by
  unfold partitionCellPrediction
  rw [part1SourceCell_mass_some hji, part1SourceCell_trueMass_some hji]
  have hpos : 0 < part1Mass b p (some j) := part1Mass_some_pos hp j
  rw [if_neg (ne_of_gt hpos)]
  simp [part1Eta, ne_of_gt hpos]

/-- The source's Lemma 8 / Proposition 7 predictor is exactly the conditional
label-one probability of its stated finite cell map. -/
theorem part1SourceCell_partitionPredictor_eq {n : ℕ} {b : Label}
    {p : Fin n → ℝ} (hp : Interior p) (i : Fin n) (x : Part1Point n) :
    partitionPredictor (part1Mass b p) (part1Eta b) (part1SourceCell i) x =
      part1Pred b p i x := by
  cases x with
  | none =>
      simpa [partitionPredictor, part1SourceCell, part1Pred] using
        part1SourceCell_prediction_none (b := b) hp i
  | some j =>
      by_cases hji : j = i
      · subst j
        simpa [partitionPredictor, part1SourceCell, part1Pred] using
          part1SourceCell_prediction_none (b := b) hp i
      · simpa [partitionPredictor, part1SourceCell, part1Pred, hji] using
          part1SourceCell_prediction_some (b := b) hp hji

/-- Raw-joint form of the Lemma 8 / Proposition 7 partition provenance. -/
theorem part1SourceCell_rawPartitionPredictor_eq {n : ℕ} {b : Label}
    {p : Fin n → ℝ} (hp : Interior p) (i : Fin n) (x : Part1Point n) :
    jointPartitionPredictor (finiteJointLawPMF (part1Setting b p hp))
      (part1SourceCell i) x = part1Pred b p i x := by
  rw [finiteJointLawPMF_partitionPredictor_eq]
  exact part1SourceCell_partitionPredictor_eq hp i x

/-! ## Parameterized Proposition 9 `S₁` cells -/

/-- In the parameterized first Proposition 9 setting, agent `k` pools both
input points and every other agent keeps the two singleton cells. -/
noncomputable def part2S1ParamSourceCell {n : ℕ} (k i : Fin n) :
    Part2S1ParamPoint → Bool :=
  if i = k then fun _ => false else fun x => x

/-- The parameterized `S₁` predictors are exactly the conditional label-one
probabilities of the source's pooled/singleton partitions. -/
theorem part2S1ParamSourceCell_partitionPredictor_eq {n : ℕ} {ε : ℝ}
    (_hε0 : 0 < ε) (_hεhalf : ε < (1 : ℝ) / 2)
    (k i : Fin n) (x : Part2S1ParamPoint) :
    partitionPredictor part2S1ParamMass (part2S1ParamEta ε)
      (part2S1ParamSourceCell k i) x = part2S1ParamPred ε k i x := by
  by_cases hik : i = k
  · subst i
    cases x <;>
      simp [partitionPredictor, partitionCellPrediction, partitionCellMass,
        partitionCellLabelMass, part2S1ParamSourceCell,
        part2S1ParamMass, part2S1ParamEta, part2S1ParamPred,
        part2S1ParamKPred] <;> norm_num <;> ring
  · cases x <;>
      simp [partitionPredictor, partitionCellPrediction, partitionCellMass,
        partitionCellLabelMass, Finset.sum_filter, part2S1ParamSourceCell,
        part2S1ParamMass, part2S1ParamEta, part2S1ParamPred, hik];
        norm_num; ring

/-- Raw-joint form of the parameterized Proposition 9 `S₁` partition
provenance. -/
theorem part2S1ParamSourceCell_rawPartitionPredictor_eq {n : ℕ} {ε : ℝ}
    (hε0 : 0 < ε) (hεhalf : ε < (1 : ℝ) / 2)
    (k i : Fin n) (x : Part2S1ParamPoint) :
    jointPartitionPredictor
      (finiteJointLawPMF (part2S1ParamSetting ε hε0 hεhalf k))
      (part2S1ParamSourceCell k i) x = part2S1ParamPred ε k i x := by
  rw [finiteJointLawPMF_partitionPredictor_eq]
  exact part2S1ParamSourceCell_partitionPredictor_eq hε0 hεhalf k i x

/-! ## Proposition 9 `S₂` cells -/

/-- The source's `S₂` cell map (`source_tex/sections/proof.tex:217`).  Agent
`k` pools the two central points; every other agent pools the two points in
each branch that have its advertised `p_i` or `q_i` prediction. -/
def part2S2SourceCell {n : ℕ} (k i : Fin n) : Part2S2Point n → Part2S2Point n
  | (false, none) => (false, none)
  | (true, none) => if i = k then (false, none) else (true, none)
  | (false, some j) =>
      if i = k then (false, some j)
      else if j = i then (false, none) else (false, some j)
  | (true, some j) =>
      if i = k then (true, some j)
      else if j = i then (true, none) else (true, some j)

theorem part2S2SourceCell_k_mass_center {n : ℕ} {p q : Fin n → ℝ}
    (k : Fin n) :
    partitionCellMass (part2S2Mass p q) (part2S2SourceCell k k) (false, none) =
      part2S2Mass p q (false, none) + part2S2Mass p q (true, none) := by
  classical
  unfold partitionCellMass
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [part2S2SourceCell]
  ring

theorem part2S2SourceCell_k_trueMass_center {n : ℕ} {p q : Fin n → ℝ}
    (k : Fin n) :
    partitionCellLabelMass (part2S2Mass p q) part2S2Eta
      (part2S2SourceCell k k) (false, none) =
      part2S2Mass p q ((false, none) : Part2S2Point n) *
          part2S2Eta ((false, none) : Part2S2Point n) +
        part2S2Mass p q ((true, none) : Part2S2Point n) *
          part2S2Eta ((true, none) : Part2S2Point n) := by
  classical
  unfold partitionCellLabelMass
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [part2S2SourceCell]
  ring

theorem part2S2SourceCell_k_mass_false_some {n : ℕ} {p q : Fin n → ℝ}
    (k j : Fin n) :
    partitionCellMass (part2S2Mass p q) (part2S2SourceCell k k) (false, some j) =
      part2S2Mass p q (false, some j) := by
  classical
  unfold partitionCellMass
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [part2S2SourceCell]

theorem part2S2SourceCell_k_trueMass_false_some {n : ℕ} {p q : Fin n → ℝ}
    (k j : Fin n) :
    partitionCellLabelMass (part2S2Mass p q) part2S2Eta
      (part2S2SourceCell k k) (false, some j) =
      part2S2Mass p q (false, some j) * part2S2Eta (false, some j) := by
  classical
  unfold partitionCellLabelMass
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [part2S2SourceCell]

theorem part2S2SourceCell_k_mass_true_some {n : ℕ} {p q : Fin n → ℝ}
    (k j : Fin n) :
    partitionCellMass (part2S2Mass p q) (part2S2SourceCell k k) (true, some j) =
      part2S2Mass p q (true, some j) := by
  classical
  unfold partitionCellMass
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [part2S2SourceCell]

theorem part2S2SourceCell_k_trueMass_true_some {n : ℕ} {p q : Fin n → ℝ}
    (k j : Fin n) :
    partitionCellLabelMass (part2S2Mass p q) part2S2Eta
      (part2S2SourceCell k k) (true, some j) =
      part2S2Mass p q (true, some j) * part2S2Eta (true, some j) := by
  classical
  unfold partitionCellLabelMass
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [part2S2SourceCell]

theorem part2S2SourceCell_k_prediction_center {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) (k : Fin n) :
    partitionCellPrediction (part2S2Mass p q) part2S2Eta
      (part2S2SourceCell k k) (false, none) = (1 : ℝ) / 2 := by
  unfold partitionCellPrediction
  rw [part2S2SourceCell_k_mass_center, part2S2SourceCell_k_trueMass_center]
  simp only [part2S2Eta, part1Eta, labelReal, Bool.not_true, Bool.not_false,
    mul_zero, mul_one, zero_add]
  have hcenter := part2S2_center_masses_equal (p := p) (q := q) hp hq
  have htrue_pos := part2S2Mass_true_none_pos (p := p) (q := q) hp hq
  have hsum_pos :
      0 < part2S2Mass p q (false, none) + part2S2Mass p q (true, none) :=
    add_pos_of_nonneg_of_pos
      (part2S2Mass_nonneg hp hq (false, none)) htrue_pos
  rw [if_neg (ne_of_gt hsum_pos), hcenter]
  have hfalse_pos : 0 < part2S2Mass p q (false, none) := by
    rw [← hcenter]
    exact htrue_pos
  field_simp [ne_of_gt hfalse_pos]
  ring

theorem part2S2SourceCell_k_prediction_false_some {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) (k j : Fin n) :
    partitionCellPrediction (part2S2Mass p q) part2S2Eta
      (part2S2SourceCell k k) (false, some j) = (1 : ℝ) := by
  unfold partitionCellPrediction
  rw [part2S2SourceCell_k_mass_false_some,
    part2S2SourceCell_k_trueMass_false_some]
  have hpos : 0 < part2S2Mass p q (false, some j) :=
    mul_pos (part2S2WeightP_pos hp hq) (part1Mass_some_pos hp j)
  rw [if_neg (ne_of_gt hpos)]
  simp [part2S2Eta, part1Eta, labelReal, ne_of_gt hpos]

theorem part2S2SourceCell_k_prediction_true_some {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) (k j : Fin n) :
    partitionCellPrediction (part2S2Mass p q) part2S2Eta
      (part2S2SourceCell k k) (true, some j) = (0 : ℝ) := by
  unfold partitionCellPrediction
  rw [part2S2SourceCell_k_mass_true_some,
    part2S2SourceCell_k_trueMass_true_some]
  have hpos : 0 < part2S2Mass p q (true, some j) :=
    mul_pos (part2S2WeightQ_pos hp hq) (part1Mass_some_pos hq j)
  rw [if_neg (ne_of_gt hpos)]
  simp [part2S2Eta, part1Eta, labelReal]

theorem part2S2SourceCell_ne_mass_false_center {n : ℕ} {p q : Fin n → ℝ}
    {k i : Fin n} (hik : i ≠ k) :
    partitionCellMass (part2S2Mass p q) (part2S2SourceCell k i) (false, none) =
      part2S2Mass p q (false, none) + part2S2Mass p q (false, some i) := by
  classical
  unfold partitionCellMass
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [part2S2SourceCell, hik]
  refine Finset.sum_eq_zero ?_
  intro x _hx
  by_cases hxi : x = i <;> simp [hxi]

theorem part2S2SourceCell_ne_trueMass_false_center {n : ℕ} {p q : Fin n → ℝ}
    {k i : Fin n} (hik : i ≠ k) :
    partitionCellLabelMass (part2S2Mass p q) part2S2Eta
      (part2S2SourceCell k i) (false, none) =
      part2S2Mass p q ((false, none) : Part2S2Point n) *
          part2S2Eta ((false, none) : Part2S2Point n) +
        part2S2Mass p q ((false, some i) : Part2S2Point n) *
          part2S2Eta ((false, some i) : Part2S2Point n) := by
  classical
  unfold partitionCellLabelMass
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [part2S2SourceCell, hik]
  refine Finset.sum_eq_zero ?_
  intro x _hx
  by_cases hxi : x = i <;> simp [hxi]

theorem part2S2SourceCell_ne_mass_true_center {n : ℕ} {p q : Fin n → ℝ}
    {k i : Fin n} (hik : i ≠ k) :
    partitionCellMass (part2S2Mass p q) (part2S2SourceCell k i) (true, none) =
      part2S2Mass p q (true, none) + part2S2Mass p q (true, some i) := by
  classical
  unfold partitionCellMass
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [part2S2SourceCell, hik]
  refine Finset.sum_eq_zero ?_
  intro x _hx
  by_cases hxi : x = i <;> simp [hxi]

theorem part2S2SourceCell_ne_trueMass_true_center {n : ℕ} {p q : Fin n → ℝ}
    {k i : Fin n} (hik : i ≠ k) :
    partitionCellLabelMass (part2S2Mass p q) part2S2Eta
      (part2S2SourceCell k i) (true, none) =
      part2S2Mass p q ((true, none) : Part2S2Point n) *
          part2S2Eta ((true, none) : Part2S2Point n) +
        part2S2Mass p q ((true, some i) : Part2S2Point n) *
          part2S2Eta ((true, some i) : Part2S2Point n) := by
  classical
  unfold partitionCellLabelMass
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [part2S2SourceCell, hik]
  refine Finset.sum_eq_zero ?_
  intro x _hx
  by_cases hxi : x = i <;> simp [hxi]

theorem part2S2SourceCell_ne_prediction_false_center {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) {k i : Fin n} (hik : i ≠ k) :
    partitionCellPrediction (part2S2Mass p q) part2S2Eta
      (part2S2SourceCell k i) (false, none) = p i := by
  unfold partitionCellPrediction
  rw [part2S2SourceCell_ne_mass_false_center hik,
    part2S2SourceCell_ne_trueMass_false_center hik]
  have hlabel :
      part2S2Mass p q ((false, none) : Part2S2Point n) *
          part2S2Eta ((false, none) : Part2S2Point n) +
        part2S2Mass p q ((false, some i) : Part2S2Point n) *
          part2S2Eta ((false, some i) : Part2S2Point n) =
        p i * (part2S2Mass p q (false, none) +
          part2S2Mass p q (false, some i)) := by
    calc
      part2S2Mass p q ((false, none) : Part2S2Point n) *
            part2S2Eta ((false, none) : Part2S2Point n) +
          part2S2Mass p q ((false, some i) : Part2S2Point n) *
            part2S2Eta ((false, some i) : Part2S2Point n) =
          part2S2WeightP p q *
            (part1Mass true p none * part1Eta true none +
              part1Mass true p (some i) * part1Eta true (some i)) := by
            simp [part2S2Mass, part2S2Eta]
            ring
      _ = part2S2WeightP p q *
            (p i * (part1Mass true p none + part1Mass true p (some i))) := by
            rw [part1_pair_labelMass_eq hp i]
      _ = p i * (part2S2Mass p q (false, none) +
          part2S2Mass p q (false, some i)) := by
            simp [part2S2Mass]
            ring
  have hden_pos :
      0 < part2S2Mass p q (false, none) + part2S2Mass p q (false, some i) :=
    add_pos
      (mul_pos (part2S2WeightP_pos hp hq) (part1Mass_none_pos hp))
      (mul_pos (part2S2WeightP_pos hp hq) (part1Mass_some_pos hp i))
  rw [if_neg (ne_of_gt hden_pos), hlabel]
  field_simp [ne_of_gt hden_pos]

theorem part2S2SourceCell_ne_prediction_true_center {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) {k i : Fin n} (hik : i ≠ k) :
    partitionCellPrediction (part2S2Mass p q) part2S2Eta
      (part2S2SourceCell k i) (true, none) = q i := by
  unfold partitionCellPrediction
  rw [part2S2SourceCell_ne_mass_true_center hik,
    part2S2SourceCell_ne_trueMass_true_center hik]
  have hlabel :
      part2S2Mass p q ((true, none) : Part2S2Point n) *
          part2S2Eta ((true, none) : Part2S2Point n) +
        part2S2Mass p q ((true, some i) : Part2S2Point n) *
          part2S2Eta ((true, some i) : Part2S2Point n) =
        q i * (part2S2Mass p q (true, none) +
          part2S2Mass p q (true, some i)) := by
    calc
      part2S2Mass p q ((true, none) : Part2S2Point n) *
            part2S2Eta ((true, none) : Part2S2Point n) +
          part2S2Mass p q ((true, some i) : Part2S2Point n) *
            part2S2Eta ((true, some i) : Part2S2Point n) =
          part2S2WeightQ p q *
            (part1Mass false q none * part1Eta false none +
              part1Mass false q (some i) * part1Eta false (some i)) := by
            simp [part2S2Mass, part2S2Eta]
            ring
      _ = part2S2WeightQ p q *
            (q i * (part1Mass false q none + part1Mass false q (some i))) := by
            rw [part1_pair_labelMass_eq hq i]
      _ = q i * (part2S2Mass p q (true, none) +
          part2S2Mass p q (true, some i)) := by
            simp [part2S2Mass]
            ring
  have hden_pos :
      0 < part2S2Mass p q (true, none) + part2S2Mass p q (true, some i) :=
    add_pos
      (mul_pos (part2S2WeightQ_pos hp hq) (part1Mass_none_pos hq))
      (mul_pos (part2S2WeightQ_pos hp hq) (part1Mass_some_pos hq i))
  rw [if_neg (ne_of_gt hden_pos), hlabel]
  field_simp [ne_of_gt hden_pos]

theorem part2S2SourceCell_ne_mass_false_some {n : ℕ} {p q : Fin n → ℝ}
    {k i j : Fin n} (hik : i ≠ k) (hji : j ≠ i) :
    partitionCellMass (part2S2Mass p q) (part2S2SourceCell k i) (false, some j) =
      part2S2Mass p q (false, some j) := by
  classical
  unfold partitionCellMass
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [part2S2SourceCell, hik]
  have htrue_zero :
      (∑ x : Fin n,
        if (if x = i then (true, none) else (true, some x)) = (false, some j)
        then part2S2Mass p q (true, some x) else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x _hx
    by_cases hxi : x = i <;> simp [hxi]
  rw [htrue_zero, zero_add]
  have hfalse : ∀ x : Fin n,
      (if x = i then (false, none) else (false, some x)) = (false, some j) ↔ x = j := by
    intro x
    by_cases hxi : x = i
    · subst x
      have hij : i ≠ j := Ne.symm hji
      simp [hij]
    · simp [hxi]
  simp_rw [hfalse]
  simp

theorem part2S2SourceCell_ne_trueMass_false_some {n : ℕ} {p q : Fin n → ℝ}
    {k i j : Fin n} (hik : i ≠ k) (hji : j ≠ i) :
    partitionCellLabelMass (part2S2Mass p q) part2S2Eta
      (part2S2SourceCell k i) (false, some j) =
      part2S2Mass p q (false, some j) * part2S2Eta (false, some j) := by
  classical
  unfold partitionCellLabelMass
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [part2S2SourceCell, hik]
  have htrue_zero :
      (∑ x : Fin n,
        if (if x = i then (true, none) else (true, some x)) = (false, some j)
        then part2S2Mass p q (true, some x) * part2S2Eta (true, some x) else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x _hx
    by_cases hxi : x = i <;> simp [hxi]
  rw [htrue_zero, zero_add]
  have hfalse : ∀ x : Fin n,
      (if x = i then (false, none) else (false, some x)) = (false, some j) ↔ x = j := by
    intro x
    by_cases hxi : x = i
    · subst x
      have hij : i ≠ j := Ne.symm hji
      simp [hij]
    · simp [hxi]
  simp_rw [hfalse]
  simp

theorem part2S2SourceCell_ne_mass_true_some {n : ℕ} {p q : Fin n → ℝ}
    {k i j : Fin n} (hik : i ≠ k) (hji : j ≠ i) :
    partitionCellMass (part2S2Mass p q) (part2S2SourceCell k i) (true, some j) =
      part2S2Mass p q (true, some j) := by
  classical
  unfold partitionCellMass
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [part2S2SourceCell, hik]
  have hfalse_zero :
      (∑ x : Fin n,
        if (if x = i then (false, none) else (false, some x)) = (true, some j)
        then part2S2Mass p q (false, some x) else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x _hx
    by_cases hxi : x = i <;> simp [hxi]
  rw [hfalse_zero]
  have htrue : ∀ x : Fin n,
      (if x = i then (true, none) else (true, some x)) = (true, some j) ↔ x = j := by
    intro x
    by_cases hxi : x = i
    · subst x
      have hij : i ≠ j := Ne.symm hji
      simp [hij]
    · simp [hxi]
  simp_rw [htrue]
  simp

theorem part2S2SourceCell_ne_trueMass_true_some {n : ℕ} {p q : Fin n → ℝ}
    {k i j : Fin n} (hik : i ≠ k) (hji : j ≠ i) :
    partitionCellLabelMass (part2S2Mass p q) part2S2Eta
      (part2S2SourceCell k i) (true, some j) =
      part2S2Mass p q (true, some j) * part2S2Eta (true, some j) := by
  classical
  unfold partitionCellLabelMass
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [part2S2SourceCell, hik]
  have hfalse_zero :
      (∑ x : Fin n,
        if (if x = i then (false, none) else (false, some x)) = (true, some j)
        then part2S2Mass p q (false, some x) * part2S2Eta (false, some x) else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x _hx
    by_cases hxi : x = i <;> simp [hxi]
  rw [hfalse_zero]
  have htrue : ∀ x : Fin n,
      (if x = i then (true, none) else (true, some x)) = (true, some j) ↔ x = j := by
    intro x
    by_cases hxi : x = i
    · subst x
      have hij : i ≠ j := Ne.symm hji
      simp [hij]
    · simp [hxi]
  simp_rw [htrue]
  simp

theorem part2S2SourceCell_ne_prediction_false_some {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) {k i j : Fin n}
    (hik : i ≠ k) (hji : j ≠ i) :
    partitionCellPrediction (part2S2Mass p q) part2S2Eta
      (part2S2SourceCell k i) (false, some j) = (1 : ℝ) := by
  unfold partitionCellPrediction
  rw [part2S2SourceCell_ne_mass_false_some hik hji,
    part2S2SourceCell_ne_trueMass_false_some hik hji]
  have hpos : 0 < part2S2Mass p q (false, some j) :=
    mul_pos (part2S2WeightP_pos hp hq) (part1Mass_some_pos hp j)
  rw [if_neg (ne_of_gt hpos)]
  simp [part2S2Eta, part1Eta, labelReal, ne_of_gt hpos]

theorem part2S2SourceCell_ne_prediction_true_some {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) {k i j : Fin n}
    (hik : i ≠ k) (hji : j ≠ i) :
    partitionCellPrediction (part2S2Mass p q) part2S2Eta
      (part2S2SourceCell k i) (true, some j) = (0 : ℝ) := by
  unfold partitionCellPrediction
  rw [part2S2SourceCell_ne_mass_true_some hik hji,
    part2S2SourceCell_ne_trueMass_true_some hik hji]
  have hpos : 0 < part2S2Mass p q (true, some j) :=
    mul_pos (part2S2WeightQ_pos hp hq) (part1Mass_some_pos hq j)
  rw [if_neg (ne_of_gt hpos)]
  simp [part2S2Eta, part1Eta, labelReal]

theorem part2S2SourceCell_partitionPredictor_eq {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) (k i : Fin n) (x : Part2S2Point n) :
    partitionPredictor (part2S2Mass p q) part2S2Eta (part2S2SourceCell k i) x =
      part2S2Pred k p q i x := by
  by_cases hik : i = k
  · subst i
    rcases x with ⟨branch, point⟩
    cases branch
    · cases point with
      | none =>
          simpa [partitionPredictor, part2S2SourceCell, part2S2Pred] using
            part2S2SourceCell_k_prediction_center hp hq k
      | some j =>
          simpa [partitionPredictor, part2S2SourceCell, part2S2Pred,
            part2S2Eta, part1Eta, labelReal] using
            part2S2SourceCell_k_prediction_false_some hp hq k j
    · cases point with
      | none =>
          simpa [partitionPredictor, part2S2SourceCell, part2S2Pred] using
            part2S2SourceCell_k_prediction_center hp hq k
      | some j =>
          simpa [partitionPredictor, part2S2SourceCell, part2S2Pred,
            part2S2Eta, part1Eta, labelReal] using
            part2S2SourceCell_k_prediction_true_some hp hq k j
  · rcases x with ⟨branch, point⟩
    cases branch
    · cases point with
      | none =>
          simpa [partitionPredictor, part2S2SourceCell, part2S2Pred,
            part1Pred, hik] using
            part2S2SourceCell_ne_prediction_false_center hp hq hik
      | some j =>
          by_cases hji : j = i
          · subst j
            simpa [partitionPredictor, part2S2SourceCell, part2S2Pred,
              part1Pred, hik] using
              part2S2SourceCell_ne_prediction_false_center hp hq hik
          · simpa [partitionPredictor, part2S2SourceCell, part2S2Pred,
              part1Pred, part2S2Eta, part1Eta, labelReal, hik, hji] using
              part2S2SourceCell_ne_prediction_false_some hp hq hik hji
    · cases point with
      | none =>
          simpa [partitionPredictor, part2S2SourceCell, part2S2Pred,
            part1Pred, hik] using
            part2S2SourceCell_ne_prediction_true_center hp hq hik
      | some j =>
          by_cases hji : j = i
          · subst j
            simpa [partitionPredictor, part2S2SourceCell, part2S2Pred,
              part1Pred, hik] using
              part2S2SourceCell_ne_prediction_true_center hp hq hik
          · simpa [partitionPredictor, part2S2SourceCell, part2S2Pred,
              part1Pred, part2S2Eta, part1Eta, labelReal, hik, hji] using
              part2S2SourceCell_ne_prediction_true_some hp hq hik hji

/-- Raw-joint form of the Proposition 9 `S₂` partition provenance. -/
theorem part2S2SourceCell_rawPartitionPredictor_eq {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) (k i : Fin n) (x : Part2S2Point n) :
    jointPartitionPredictor (finiteJointLawPMF (part2S2Setting k p q hp hq))
      (part2S2SourceCell k i) x = part2S2Pred k p q i x := by
  rw [finiteJointLawPMF_partitionPredictor_eq]
  exact part2S2SourceCell_partitionPredictor_eq hp hq k i x

end PKG25NoFreeLunch
