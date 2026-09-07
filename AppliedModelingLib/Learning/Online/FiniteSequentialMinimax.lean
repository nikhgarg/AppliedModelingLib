import AppliedModelingLib.Learning.Online.SequentialComplexity
import AppliedModelingLib.Learning.Online.SequentialRelaxation
import Mathlib.Tactic

/-!
# Exact finite binary sequential minimax game

For linear OWAL correlation with binary labels, the sequential minimax value
admits a sharper finite specialization than the generic convex-Lipschitz
theorem.  This file develops the finite-context, finite-class dynamic program,
proves its real-label telescope, and bounds it directly by the source's global
sequential Rademacher process through an explicit adaptive-tree witness.  It
is a constructive, albeit generally computationally expensive, realization of
the finite upper-game guarantee.
-/

namespace AppliedModelingLib.Learning.Online

open scoped BigOperators

/-- The terminal best-comparator score of a finite score vector. -/
noncomputable def finiteScoreMaximum {Candidate : Type*}
    [Fintype Candidate] [Nonempty Candidate] (score : Candidate → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty score

/-- Add one signed comparator-reward coordinate to a score vector. -/
def finiteBinaryScoreShift {Candidate Context : Type*}
    (candidates : Candidate → Context → ℝ) (score : Candidate → ℝ)
    (context : Context) (sign : Bool) : Candidate → ℝ :=
  fun candidate => score candidate + rademacherSign sign * candidates candidate context

/-- The finite binary OWAL minimax value with a supplied accumulated
comparator-score vector.  One round chooses a context, then balances the two
possible label continuations. -/
noncomputable def finiteBinarySequentialMinimaxValue
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) :
    ℕ → (Candidate → ℝ) → ℝ
  | 0, score => finiteScoreMaximum score
  | remaining + 1, score =>
      Finset.univ.sup' Finset.univ_nonempty fun context =>
        (finiteBinarySequentialMinimaxValue candidates remaining
            (finiteBinaryScoreShift candidates score context true) +
          finiteBinarySequentialMinimaxValue candidates remaining
            (finiteBinaryScoreShift candidates score context false)) / 2

/-- The expected terminal comparator score on an inductively represented
binary adaptive context tree.  At each node the two child values are averaged
under an independent fair Rademacher sign. -/
noncomputable def finiteBinarySequentialTreeValue
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    (candidates : Candidate → Context → ℝ) :
    ∀ {horizon : ℕ}, (Candidate → ℝ) → BinarySequentialTree Context horizon → ℝ
  | 0, score, .leaf => finiteScoreMaximum score
  | remaining + 1, score, .node context continuations =>
      (finiteBinarySequentialTreeValue candidates
          (finiteBinaryScoreShift candidates score context true) (continuations true) +
        finiteBinarySequentialTreeValue candidates
          (finiteBinaryScoreShift candidates score context false) (continuations false)) / 2

/-- The finite sequential Rademacher process on a fixed context tree, with an
arbitrary initial comparator-score vector.  At zero initial score this is the
unnormalized process used by the source complexity definition. -/
noncomputable def finiteSequentialRademacherScoreSum
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    {horizon : ℕ} (candidates : Candidate → Context → ℝ) (score : Candidate → ℝ)
    (tree : SequentialTree Context horizon) : ℝ :=
  pmfExp (pmfProduct (Fin horizon) Bool (uniformPMF Bool)) fun signs =>
    finiteScoreMaximum (fun candidate => score candidate +
      ∑ round, rademacherSign (signs round) * candidates candidate (tree.eval signs round))

/-- The comparator sum below a converted binary-tree node separates into its
root contribution and the contribution of the child selected by the first
Rademacher sign. -/
theorem finiteSequentialRademacher_node_sum
    {Candidate Context : Type*} {horizon : ℕ}
    (candidates : Candidate → Context → ℝ) (root : Context)
    (continuations : Bool → BinarySequentialTree Context horizon)
    (signs : Fin (horizon + 1) → Bool) (candidate : Candidate) :
    (∑ round, rademacherSign (signs round) * candidates candidate
      ((BinarySequentialTree.node root continuations).toSequentialTree.eval signs round)) =
      rademacherSign (signs 0) * candidates candidate root +
        ∑ round, rademacherSign ((Fin.tail signs) round) * candidates candidate
          ((continuations (signs 0)).toSequentialTree.eval (Fin.tail signs) round) := by
  rw [Fin.sum_univ_succ]
  simp only [BinarySequentialTree.toSequentialTree_node_eval_zero,
    BinarySequentialTree.toSequentialTree_node_eval_succ]
  apply congrArg (fun value =>
    rademacherSign (signs 0) * candidates candidate root + value) ?_
  apply Finset.sum_congr rfl
  intro round _
  rfl

/-- Root-first factorization of the score-augmented Rademacher process on an
inductive binary tree. -/
theorem finiteSequentialRademacherScoreSum_node
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    {horizon : ℕ} (candidates : Candidate → Context → ℝ) (score : Candidate → ℝ)
    (root : Context) (continuations : Bool → BinarySequentialTree Context horizon) :
    finiteSequentialRademacherScoreSum candidates score
      (BinarySequentialTree.node root continuations).toSequentialTree =
      (finiteSequentialRademacherScoreSum candidates
          (finiteBinaryScoreShift candidates score root true)
          (continuations true).toSequentialTree +
        finiteSequentialRademacherScoreSum candidates
          (finiteBinaryScoreShift candidates score root false)
          (continuations false).toSequentialTree) / 2 := by
  unfold finiteSequentialRademacherScoreSum
  rw [pmfExp_pmfProduct_finCons_eq_pairExp]
  rw [pmfPairExp_swap]
  unfold pmfPairExp
  rw [pmfExp_uniformPMF_bool_eq_average]
  dsimp only
  congr 2
  · apply pmfExp_congr
    intro signs
    congr 1
    funext candidate
    rw [finiteSequentialRademacher_node_sum]
    simp only [Fin.cons_zero, Fin.tail_cons]
    unfold finiteBinaryScoreShift
    ring
  · apply pmfExp_congr
    intro signs
    congr 1
    funext candidate
    rw [finiteSequentialRademacher_node_sum]
    simp only [Fin.cons_zero, Fin.tail_cons]
    unfold finiteBinaryScoreShift
    ring

/-- The inductive binary-tree value is exactly the score-augmented finite
sequential Rademacher process of its converted context tree. -/
theorem finiteBinarySequentialTreeValue_eq_finiteSequentialRademacherScoreSum
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    (candidates : Candidate → Context → ℝ) :
    ∀ {horizon : ℕ} (score : Candidate → ℝ) (tree : BinarySequentialTree Context horizon),
      finiteBinarySequentialTreeValue candidates score tree =
        finiteSequentialRademacherScoreSum candidates score tree.toSequentialTree := by
  intro horizon
  induction horizon with
  | zero =>
      intro score tree
      cases tree
      unfold finiteBinarySequentialTreeValue finiteSequentialRademacherScoreSum
      simp
  | succ remaining ih =>
      intro score tree
      cases tree with
      | node root continuations =>
          simp only [finiteBinarySequentialTreeValue]
          rw [finiteSequentialRademacherScoreSum_node]
          rw [← ih (finiteBinaryScoreShift candidates score root true) (continuations true),
            ← ih (finiteBinaryScoreShift candidates score root false) (continuations false)]

/-- Starting from the zero score vector recovers the ordinary unnormalized
finite sequential Rademacher sum. -/
theorem finiteSequentialRademacherScoreSum_zero_eq_sum
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    {horizon : ℕ} (candidates : Candidate → Context → ℝ)
    (tree : SequentialTree Context horizon) :
    finiteSequentialRademacherScoreSum candidates (fun _ => 0) tree =
      finiteSequentialRademacherSum candidates tree := by
  unfold finiteSequentialRademacherScoreSum finiteSequentialRademacherSum finiteScoreMaximum
  apply pmfExp_congr
  intro signs
  congr 1
  funext candidate
  simp

/-- The finite binary sequential value is convex in its accumulated
comparator-score vector. -/
theorem finiteBinarySequentialMinimaxValue_convex
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) :
    ∀ (remaining : ℕ) (first second : Candidate → ℝ) (mixture : ℝ),
      mixture ∈ Set.Icc 0 1 →
      finiteBinarySequentialMinimaxValue candidates remaining
        (fun candidate => mixture * first candidate + (1 - mixture) * second candidate) ≤
        mixture * finiteBinarySequentialMinimaxValue candidates remaining first +
          (1 - mixture) * finiteBinarySequentialMinimaxValue candidates remaining second := by
  intro remaining
  induction remaining with
  | zero =>
      intro first second mixture hmixture
      simp only [finiteBinarySequentialMinimaxValue]
      unfold finiteScoreMaximum
      apply Finset.sup'_le Finset.univ_nonempty
      intro candidate _
      have hfirst : first candidate ≤ finiteScoreMaximum first := by
        unfold finiteScoreMaximum
        exact Finset.le_sup' first (Finset.mem_univ candidate)
      have hsecond : second candidate ≤ finiteScoreMaximum second := by
        unfold finiteScoreMaximum
        exact Finset.le_sup' second (Finset.mem_univ candidate)
      have hnonneg : 0 ≤ mixture := hmixture.1
      have hcomplement : 0 ≤ 1 - mixture := by linarith [hmixture.2]
      calc
        mixture * first candidate + (1 - mixture) * second candidate ≤
            mixture * finiteScoreMaximum first + (1 - mixture) * finiteScoreMaximum second :=
          add_le_add
            (mul_le_mul_of_nonneg_left hfirst hnonneg)
            (mul_le_mul_of_nonneg_left hsecond hcomplement)
        _ = mixture * finiteBinarySequentialMinimaxValue candidates 0 first +
              (1 - mixture) * finiteBinarySequentialMinimaxValue candidates 0 second := by
            rfl
  | succ remaining ih =>
      intro first second mixture hmixture
      simp only [finiteBinarySequentialMinimaxValue]
      apply Finset.sup'_le Finset.univ_nonempty
      intro context _
      have hnonneg : 0 ≤ mixture := hmixture.1
      have hcomplement : 0 ≤ 1 - mixture := by linarith [hmixture.2]
      have hbranch : ∀ sign : Bool,
          finiteBinarySequentialMinimaxValue candidates remaining
            (finiteBinaryScoreShift candidates
              (fun candidate => mixture * first candidate + (1 - mixture) * second candidate)
              context sign) ≤
            mixture * finiteBinarySequentialMinimaxValue candidates remaining
              (finiteBinaryScoreShift candidates first context sign) +
              (1 - mixture) * finiteBinarySequentialMinimaxValue candidates remaining
                (finiteBinaryScoreShift candidates second context sign) := by
        intro sign
        have h := ih (finiteBinaryScoreShift candidates first context sign)
          (finiteBinaryScoreShift candidates second context sign) mixture hmixture
        have hshift :
            finiteBinaryScoreShift candidates
                (fun candidate => mixture * first candidate + (1 - mixture) * second candidate)
                context sign =
              fun candidate =>
                mixture * finiteBinaryScoreShift candidates first context sign candidate +
                  (1 - mixture) * finiteBinaryScoreShift candidates second context sign candidate := by
          funext candidate
          unfold finiteBinaryScoreShift
          ring
        rw [hshift]
        exact h
      have htrue := hbranch true
      have hfalse := hbranch false
      have hfirstPair :
          (finiteBinarySequentialMinimaxValue candidates remaining
              (finiteBinaryScoreShift candidates first context true) +
            finiteBinarySequentialMinimaxValue candidates remaining
              (finiteBinaryScoreShift candidates first context false)) / 2 ≤
            finiteBinarySequentialMinimaxValue candidates (remaining + 1) first := by
        simp only [finiteBinarySequentialMinimaxValue]
        exact Finset.le_sup' (fun otherContext =>
          (finiteBinarySequentialMinimaxValue candidates remaining
              (finiteBinaryScoreShift candidates first otherContext true) +
            finiteBinarySequentialMinimaxValue candidates remaining
              (finiteBinaryScoreShift candidates first otherContext false)) / 2)
          (Finset.mem_univ context)
      have hsecondPair :
          (finiteBinarySequentialMinimaxValue candidates remaining
              (finiteBinaryScoreShift candidates second context true) +
            finiteBinarySequentialMinimaxValue candidates remaining
              (finiteBinaryScoreShift candidates second context false)) / 2 ≤
            finiteBinarySequentialMinimaxValue candidates (remaining + 1) second := by
        simp only [finiteBinarySequentialMinimaxValue]
        exact Finset.le_sup' (fun otherContext =>
          (finiteBinarySequentialMinimaxValue candidates remaining
              (finiteBinaryScoreShift candidates second otherContext true) +
            finiteBinarySequentialMinimaxValue candidates remaining
              (finiteBinaryScoreShift candidates second otherContext false)) / 2)
          (Finset.mem_univ context)
      have havg :
          (finiteBinarySequentialMinimaxValue candidates remaining
              (finiteBinaryScoreShift candidates
                (fun candidate => mixture * first candidate + (1 - mixture) * second candidate)
                context true) +
            finiteBinarySequentialMinimaxValue candidates remaining
              (finiteBinaryScoreShift candidates
                (fun candidate => mixture * first candidate + (1 - mixture) * second candidate)
                context false)) / 2 ≤
            mixture *
                ((finiteBinarySequentialMinimaxValue candidates remaining
                    (finiteBinaryScoreShift candidates first context true) +
                  finiteBinarySequentialMinimaxValue candidates remaining
                    (finiteBinaryScoreShift candidates first context false)) / 2) +
              (1 - mixture) *
                ((finiteBinarySequentialMinimaxValue candidates remaining
                    (finiteBinaryScoreShift candidates second context true) +
                  finiteBinarySequentialMinimaxValue candidates remaining
                    (finiteBinaryScoreShift candidates second context false)) / 2) := by
          linarith
      calc
        _ ≤ mixture *
                ((finiteBinarySequentialMinimaxValue candidates remaining
                    (finiteBinaryScoreShift candidates first context true) +
                  finiteBinarySequentialMinimaxValue candidates remaining
                    (finiteBinaryScoreShift candidates first context false)) / 2) +
              (1 - mixture) *
                ((finiteBinarySequentialMinimaxValue candidates remaining
                    (finiteBinaryScoreShift candidates second context true) +
                  finiteBinarySequentialMinimaxValue candidates remaining
                    (finiteBinaryScoreShift candidates second context false)) / 2) := havg
        _ ≤ mixture * finiteBinarySequentialMinimaxValue candidates (remaining + 1) first +
              (1 - mixture) * finiteBinarySequentialMinimaxValue candidates (remaining + 1) second :=
          add_le_add
            (mul_le_mul_of_nonneg_left hfirstPair hnonneg)
            (mul_le_mul_of_nonneg_left hsecondPair hcomplement)

/-- Every finite binary adaptive tree is bounded by the sequential minimax
value with the same starting comparator-score vector. -/
theorem finiteBinarySequentialTreeValue_le_minimaxValue
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) :
    ∀ {horizon : ℕ} (score : Candidate → ℝ) (tree : BinarySequentialTree Context horizon),
      finiteBinarySequentialTreeValue candidates score tree ≤
        finiteBinarySequentialMinimaxValue candidates horizon score := by
  intro horizon
  induction horizon with
  | zero =>
      intro score tree
      cases tree
      rfl
  | succ remaining ih =>
      intro score tree
      cases tree with
      | node context continuations =>
          simp only [finiteBinarySequentialTreeValue]
          have hpositive := ih
            (finiteBinaryScoreShift candidates score context true) (continuations true)
          have hnegative := ih
            (finiteBinaryScoreShift candidates score context false) (continuations false)
          have hroot :
              (finiteBinarySequentialMinimaxValue candidates remaining
                  (finiteBinaryScoreShift candidates score context true) +
                finiteBinarySequentialMinimaxValue candidates remaining
                  (finiteBinaryScoreShift candidates score context false)) / 2 ≤
                finiteBinarySequentialMinimaxValue candidates (remaining + 1) score := by
            simp only [finiteBinarySequentialMinimaxValue]
            exact Finset.le_sup' (fun otherContext =>
              (finiteBinarySequentialMinimaxValue candidates remaining
                  (finiteBinaryScoreShift candidates score otherContext true) +
                finiteBinarySequentialMinimaxValue candidates remaining
                  (finiteBinaryScoreShift candidates score otherContext false)) / 2)
              (Finset.mem_univ context)
          linarith

/-- A context attaining the finite one-step minimax supremum. -/
noncomputable def finiteBinarySequentialMinimaxBestContext
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) (remaining : ℕ)
    (score : Candidate → ℝ) : Context := by
  classical
  exact Classical.choose (Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun context =>
      (finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score context true) +
        finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score context false)) / 2))

/-- The selected context realizes the one-step finite minimax value. -/
theorem finiteBinarySequentialMinimaxBestContext_value
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) (remaining : ℕ)
    (score : Candidate → ℝ) :
    finiteBinarySequentialMinimaxValue candidates (remaining + 1) score =
      (finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score
            (finiteBinarySequentialMinimaxBestContext candidates remaining score) true) +
        finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score
            (finiteBinarySequentialMinimaxBestContext candidates remaining score) false)) / 2 := by
  classical
  unfold finiteBinarySequentialMinimaxBestContext
  simp only [finiteBinarySequentialMinimaxValue]
  exact (Classical.choose_spec (Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun context =>
      (finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score context true) +
        finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score context false)) / 2))).2

/-- A recursively selected adaptive tree that realizes the finite binary
sequential minimax value. -/
noncomputable def finiteBinarySequentialMinimaxOptimalTree
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) :
    ∀ (horizon : ℕ) (score : Candidate → ℝ), BinarySequentialTree Context horizon
  | 0, _ => .leaf
  | remaining + 1, score =>
      .node (finiteBinarySequentialMinimaxBestContext candidates remaining score)
        (fun sign => finiteBinarySequentialMinimaxOptimalTree candidates remaining
          (finiteBinaryScoreShift candidates score
            (finiteBinarySequentialMinimaxBestContext candidates remaining score) sign))

/-- The recursively selected adaptive tree attains the finite binary minimax
value exactly. -/
theorem finiteBinarySequentialMinimaxOptimalTree_value
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) :
    ∀ (horizon : ℕ) (score : Candidate → ℝ),
      finiteBinarySequentialTreeValue candidates score
        (finiteBinarySequentialMinimaxOptimalTree candidates horizon score) =
        finiteBinarySequentialMinimaxValue candidates horizon score := by
  intro horizon
  induction horizon with
  | zero =>
      intro score
      rfl
  | succ remaining ih =>
      intro score
      simp only [finiteBinarySequentialMinimaxOptimalTree,
        finiteBinarySequentialTreeValue]
      rw [ih (finiteBinaryScoreShift candidates score
            (finiteBinarySequentialMinimaxBestContext candidates remaining score) true),
        ih (finiteBinaryScoreShift candidates score
            (finiteBinarySequentialMinimaxBestContext candidates remaining score) false)]
      exact (finiteBinarySequentialMinimaxBestContext_value candidates remaining score).symm

/-- The finite binary minimax value at zero initial score is bounded by the
source's unnormalized global sequential Rademacher process.  The proof gives
an explicit adaptive tree witnessing this bound rather than invoking a
nonconstructive minimax oracle. -/
theorem finiteBinarySequentialMinimaxValue_le_finiteSequentialRademacherProcess
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) (horizon : ℕ) :
    finiteBinarySequentialMinimaxValue candidates horizon (fun _ => 0) ≤
      finiteSequentialRademacherProcess (horizon := horizon) candidates := by
  have hfinite :
      (Set.range (finiteSequentialRademacherSum candidates :
        SequentialTree Context horizon → ℝ)).Finite := by
    rw [show Set.range (finiteSequentialRademacherSum candidates :
        SequentialTree Context horizon → ℝ) =
        (finiteSequentialRademacherSum candidates : SequentialTree Context horizon → ℝ) ''
          Set.univ by
      ext value
      simp]
    exact Set.finite_univ.image _
  have hmember : finiteSequentialRademacherSum candidates
      (finiteBinarySequentialMinimaxOptimalTree candidates horizon (fun _ => 0)).toSequentialTree ∈
      Set.range (finiteSequentialRademacherSum candidates :
        SequentialTree Context horizon → ℝ) := ⟨_, rfl⟩
  calc
    finiteBinarySequentialMinimaxValue candidates horizon (fun _ => 0) =
        finiteBinarySequentialTreeValue candidates (fun _ => 0)
          (finiteBinarySequentialMinimaxOptimalTree candidates horizon (fun _ => 0)) := by
            exact (finiteBinarySequentialMinimaxOptimalTree_value candidates horizon (fun _ => 0)).symm
    _ = finiteSequentialRademacherScoreSum candidates (fun _ => 0)
          (finiteBinarySequentialMinimaxOptimalTree candidates horizon (fun _ => 0)).toSequentialTree :=
      finiteBinarySequentialTreeValue_eq_finiteSequentialRademacherScoreSum candidates _ _
    _ = finiteSequentialRademacherSum candidates
          (finiteBinarySequentialMinimaxOptimalTree candidates horizon (fun _ => 0)).toSequentialTree :=
      finiteSequentialRademacherScoreSum_zero_eq_sum candidates _
    _ ≤ finiteSequentialRademacherProcess (horizon := horizon) candidates := by
      unfold finiteSequentialRademacherProcess
      exact le_csSup hfinite.bddAbove hmember

/-- Every coordinate is below its finite terminal maximum. -/
theorem le_finiteScoreMaximum {Candidate : Type*}
    [Fintype Candidate] [Nonempty Candidate]
    (score : Candidate → ℝ) (candidate : Candidate) :
    score candidate ≤ finiteScoreMaximum score := by
  unfold finiteScoreMaximum
  exact Finset.le_sup' score (Finset.mem_univ candidate)

/-- A uniform coordinate upper bound controls the finite terminal maximum. -/
theorem finiteScoreMaximum_le_of_forall_le {Candidate : Type*}
    [Fintype Candidate] [Nonempty Candidate]
    (score : Candidate → ℝ) (bound : ℝ)
    (hbound : ∀ candidate, score candidate ≤ bound) :
    finiteScoreMaximum score ≤ bound := by
  unfold finiteScoreMaximum
  apply Finset.sup'_le Finset.univ_nonempty
  intro candidate _
  exact hbound candidate

/-- Finite coordinatewise `ℓ∞` control gives the same control on terminal
best-comparator values. -/
theorem abs_finiteScoreMaximum_sub_le_of_forall_abs_sub_le
    {Candidate : Type*} [Fintype Candidate] [Nonempty Candidate]
    (first second : Candidate → ℝ) (radius : ℝ)
    (hcoordinate : ∀ candidate, |first candidate - second candidate| ≤ radius) :
    |finiteScoreMaximum first - finiteScoreMaximum second| ≤ radius := by
  have hforward : finiteScoreMaximum first - finiteScoreMaximum second ≤ radius := by
    have hmax : finiteScoreMaximum first ≤ finiteScoreMaximum second + radius := by
      apply finiteScoreMaximum_le_of_forall_le
      intro candidate
      have hcoordinate' := abs_le.mp (hcoordinate candidate)
      calc
        first candidate ≤ second candidate + radius := by linarith [hcoordinate'.2]
        _ ≤ finiteScoreMaximum second + radius := by
          exact add_le_add_left
            (le_finiteScoreMaximum second candidate) radius
    linarith
  have hbackward : finiteScoreMaximum second - finiteScoreMaximum first ≤ radius := by
    have hmax : finiteScoreMaximum second ≤ finiteScoreMaximum first + radius := by
      apply finiteScoreMaximum_le_of_forall_le
      intro candidate
      have hcoordinate' := abs_le.mp (hcoordinate candidate)
      calc
        second candidate ≤ first candidate + radius := by linarith [hcoordinate'.1]
        _ ≤ finiteScoreMaximum first + radius := by
          exact add_le_add_left
            (le_finiteScoreMaximum first candidate) radius
    linarith
  exact abs_le.mpr ⟨by linarith, hforward⟩

/-- Averaging two quantities preserves a common absolute-error radius. -/
theorem abs_average_sub_le_of_abs_sub_le
    {firstPositive firstNegative secondPositive secondNegative radius : ℝ}
    (hpositive : |firstPositive - secondPositive| ≤ radius)
    (hnegative : |firstNegative - secondNegative| ≤ radius) :
    |(firstPositive + firstNegative) / 2 -
        (secondPositive + secondNegative) / 2| ≤ radius := by
  have hradius : 0 ≤ radius := (abs_nonneg _).trans hpositive
  calc
    |(firstPositive + firstNegative) / 2 -
        (secondPositive + secondNegative) / 2| =
        |((firstPositive - secondPositive) +
          (firstNegative - secondNegative)) / 2| := by
          congr 1
          ring
    _ = |(firstPositive - secondPositive) +
          (firstNegative - secondNegative)| / |(2 : ℝ)| := by rw [abs_div]
    _ = |(firstPositive - secondPositive) +
          (firstNegative - secondNegative)| / 2 := by norm_num
    _ ≤ (|firstPositive - secondPositive| + |firstNegative - secondNegative|) / 2 :=
      div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
    _ ≤ (radius + radius) / 2 :=
      div_le_div_of_nonneg_right (add_le_add hpositive hnegative) (by norm_num)
    _ = radius := by ring

/-- The finite binary sequential value is 1-Lipschitz in the accumulated
comparator-score vector for the coordinatewise `ℓ∞` norm. -/
theorem abs_finiteBinarySequentialMinimaxValue_sub_le_of_forall_abs_sub_le
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) :
    ∀ (remaining : ℕ) (first second : Candidate → ℝ) (radius : ℝ),
      (∀ candidate, |first candidate - second candidate| ≤ radius) →
      |finiteBinarySequentialMinimaxValue candidates remaining first -
        finiteBinarySequentialMinimaxValue candidates remaining second| ≤ radius := by
  intro remaining
  induction remaining with
  | zero =>
      intro first second radius hcoordinate
      simpa [finiteBinarySequentialMinimaxValue] using
        abs_finiteScoreMaximum_sub_le_of_forall_abs_sub_le first second radius hcoordinate
  | succ remaining ih =>
      intro first second radius hcoordinate
      simp only [finiteBinarySequentialMinimaxValue]
      apply abs_finiteScoreMaximum_sub_le_of_forall_abs_sub_le
      intro context
      have hshift : ∀ sign : Bool, ∀ candidate,
          |finiteBinaryScoreShift candidates first context sign candidate -
            finiteBinaryScoreShift candidates second context sign candidate| ≤ radius := by
        intro sign candidate
        unfold finiteBinaryScoreShift
        convert hcoordinate candidate using 1 <;> ring
      exact abs_average_sub_le_of_abs_sub_le
        (ih (finiteBinaryScoreShift candidates first context true)
          (finiteBinaryScoreShift candidates second context true) radius (hshift true))
        (ih (finiteBinaryScoreShift candidates first context false)
          (finiteBinaryScoreShift candidates second context false) radius (hshift false))

/-- The explicit finite binary minimax prediction at a context, with
`remaining` future rounds after the current one. -/
noncomputable def finiteBinarySequentialMinimaxPrediction
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) (remaining : ℕ)
    (score : Candidate → ℝ) (context : Context) : ℝ :=
  balancedTwoBranchPrediction
    (finiteBinarySequentialMinimaxValue candidates remaining
      (finiteBinaryScoreShift candidates score context true))
    (finiteBinarySequentialMinimaxValue candidates remaining
      (finiteBinaryScoreShift candidates score context false))

/-- Bounded comparators make the explicit finite minimax prediction feasible
in the source OWAL output interval. -/
theorem finiteBinarySequentialMinimaxPrediction_mem_Icc
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ)
    (hbounded : ∀ candidate context,
      candidates candidate context ∈ Set.Icc (-1 : ℝ) 1)
    (remaining : ℕ) (score : Candidate → ℝ) (context : Context) :
    finiteBinarySequentialMinimaxPrediction candidates remaining score context ∈
      Set.Icc (-1 : ℝ) 1 := by
  apply balancedTwoBranchPrediction_mem_Icc
  apply abs_finiteBinarySequentialMinimaxValue_sub_le_of_forall_abs_sub_le
  intro candidate
  unfold finiteBinaryScoreShift
  have hcandidate := hbounded candidate context
  calc
    |(score candidate + rademacherSign true * candidates candidate context) -
        (score candidate + rademacherSign false * candidates candidate context)| =
        |2 * candidates candidate context| := by
          congr 1
          simp [rademacherSign]
          ring
    _ = 2 * |candidates candidate context| := by
      rw [abs_mul, abs_of_nonneg (by norm_num)]
    _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left (abs_le.mpr hcandidate) (by norm_num)
    _ = 2 := by ring

/-- On the positive binary-label branch, the minimax prediction exactly
balances the two continuation values. -/
theorem finiteBinarySequentialMinimaxValue_positive_sub_prediction
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) (remaining : ℕ)
    (score : Candidate → ℝ) (context : Context) :
    finiteBinarySequentialMinimaxValue candidates remaining
        (finiteBinaryScoreShift candidates score context true) -
      finiteBinarySequentialMinimaxPrediction candidates remaining score context =
      (finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score context true) +
        finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score context false)) / 2 := by
  exact positiveBranch_sub_balancedTwoBranchPrediction _ _

/-- The negative binary-label branch has the same balanced continuation
value. -/
theorem finiteBinarySequentialMinimaxValue_negative_add_prediction
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) (remaining : ℕ)
    (score : Candidate → ℝ) (context : Context) :
    finiteBinarySequentialMinimaxValue candidates remaining
        (finiteBinaryScoreShift candidates score context false) +
      finiteBinarySequentialMinimaxPrediction candidates remaining score context =
      (finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score context true) +
        finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score context false)) / 2 := by
  exact negativeBranch_add_balancedTwoBranchPrediction _ _

/-- The explicit prediction makes the finite binary minimax value decrease on
either label branch.  This is the one-step admissibility condition that the
generic relaxation telescope consumes. -/
theorem finiteBinarySequentialMinimaxValue_one_step
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) (remaining : ℕ)
    (score : Candidate → ℝ) (context : Context) (sign : Bool) :
    finiteBinarySequentialMinimaxValue candidates remaining
        (finiteBinaryScoreShift candidates score context sign) -
      finiteBinarySequentialMinimaxPrediction candidates remaining score context *
        rademacherSign sign ≤
      finiteBinarySequentialMinimaxValue candidates (remaining + 1) score := by
  have hparent :
      (finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score context true) +
        finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score context false)) / 2 ≤
        finiteBinarySequentialMinimaxValue candidates (remaining + 1) score := by
    simp only [finiteBinarySequentialMinimaxValue]
    exact Finset.le_sup' (fun otherContext =>
      (finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score otherContext true) +
        finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score otherContext false)) / 2)
      (Finset.mem_univ context)
  cases sign
  · simpa [rademacherSign] using
      (finiteBinarySequentialMinimaxValue_negative_add_prediction
        candidates remaining score context).le.trans hparent
  · simpa [rademacherSign] using
      (finiteBinarySequentialMinimaxValue_positive_sub_prediction
        candidates remaining score context).le.trans hparent

/-- Add a real label contribution to each comparator score. -/
def finiteRealScoreShift {Candidate Context : Type*}
    (candidates : Candidate → Context → ℝ) (score : Candidate → ℝ)
    (context : Context) (label : ℝ) : Candidate → ℝ :=
  fun candidate => score candidate + label * candidates candidate context

/-- A real score update is the convex mixture of the two binary score updates
whose mixture mean is the real label. -/
theorem finiteRealScoreShift_eq_binary_mixture
    {Candidate Context : Type*} (candidates : Candidate → Context → ℝ)
    (score : Candidate → ℝ) (context : Context) (label : ℝ) :
    finiteRealScoreShift candidates score context label =
      fun candidate => ((1 + label) / 2) *
          finiteBinaryScoreShift candidates score context true candidate +
        (1 - (1 + label) / 2) *
          finiteBinaryScoreShift candidates score context false candidate := by
  funext candidate
  unfold finiteRealScoreShift finiteBinaryScoreShift rademacherSign
  simp
  ring

/-- The balanced finite minimax prediction has the same one-step guarantee
for every real label in the source interval `[-1,1]`.  Convexity reduces the
real score update to its two binary endpoint updates. -/
theorem finiteRealSequentialMinimaxValue_one_step
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) (remaining : ℕ)
    (score : Candidate → ℝ) (context : Context) (label : ℝ)
    (hlabel : label ∈ Set.Icc (-1 : ℝ) 1) :
    finiteBinarySequentialMinimaxValue candidates remaining
        (finiteRealScoreShift candidates score context label) -
      finiteBinarySequentialMinimaxPrediction candidates remaining score context * label ≤
      finiteBinarySequentialMinimaxValue candidates (remaining + 1) score := by
  let mixture : ℝ := (1 + label) / 2
  have hmixture : mixture ∈ Set.Icc 0 1 := by
    dsimp [mixture]
    constructor <;> linarith [hlabel.1, hlabel.2]
  have hconvex := finiteBinarySequentialMinimaxValue_convex candidates remaining
    (finiteBinaryScoreShift candidates score context true)
    (finiteBinaryScoreShift candidates score context false) mixture hmixture
  have hshift : finiteRealScoreShift candidates score context label =
      fun candidate => mixture * finiteBinaryScoreShift candidates score context true candidate +
        (1 - mixture) * finiteBinaryScoreShift candidates score context false candidate := by
    exact finiteRealScoreShift_eq_binary_mixture candidates score context label
  have hconvex' :
      finiteBinarySequentialMinimaxValue candidates remaining
        (finiteRealScoreShift candidates score context label) ≤
        mixture * finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score context true) +
          (1 - mixture) * finiteBinarySequentialMinimaxValue candidates remaining
            (finiteBinaryScoreShift candidates score context false) := by
    rw [hshift]
    exact hconvex
  have hparent :
      (finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score context true) +
        finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score context false)) / 2 ≤
        finiteBinarySequentialMinimaxValue candidates (remaining + 1) score := by
    simp only [finiteBinarySequentialMinimaxValue]
    exact Finset.le_sup' (fun otherContext =>
      (finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score otherContext true) +
        finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score otherContext false)) / 2)
      (Finset.mem_univ context)
  have hbalanceTrue := finiteBinarySequentialMinimaxValue_positive_sub_prediction
    candidates remaining score context
  have hbalanceFalse := finiteBinarySequentialMinimaxValue_negative_add_prediction
    candidates remaining score context
  let average : ℝ :=
    (finiteBinarySequentialMinimaxValue candidates remaining
        (finiteBinaryScoreShift candidates score context true) +
      finiteBinarySequentialMinimaxValue candidates remaining
        (finiteBinaryScoreShift candidates score context false)) / 2
  have hplus : finiteBinarySequentialMinimaxValue candidates remaining
      (finiteBinaryScoreShift candidates score context true) =
      average + finiteBinarySequentialMinimaxPrediction candidates remaining score context := by
    dsimp [average]
    linarith [hbalanceTrue]
  have hminus : finiteBinarySequentialMinimaxValue candidates remaining
      (finiteBinaryScoreShift candidates score context false) =
      average - finiteBinarySequentialMinimaxPrediction candidates remaining score context := by
    dsimp [average]
    linarith [hbalanceFalse]
  change finiteBinarySequentialMinimaxValue candidates remaining
      (finiteRealScoreShift candidates score context label) -
      finiteBinarySequentialMinimaxPrediction candidates remaining score context * label ≤ _
  dsimp [mixture] at hconvex'
  calc
    _ ≤ (1 + label) / 2 * finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score context true) +
        (1 - (1 + label) / 2) * finiteBinarySequentialMinimaxValue candidates remaining
          (finiteBinaryScoreShift candidates score context false) -
        finiteBinarySequentialMinimaxPrediction candidates remaining score context * label :=
      sub_le_sub_right hconvex' _
    _ = average := by
      rw [hplus, hminus]
      ring
    _ ≤ _ := by
      dsimp [average]
      exact hparent

/-- Update a finite comparator-score vector along a complete binary-labeled
observation suffix. -/
def finiteBinaryScoreRun {Candidate Context : Type*}
    (candidates : Candidate → Context → ℝ) :
    (Candidate → ℝ) → List (Context × Bool) → Candidate → ℝ
  | score, [] => score
  | score, observation :: remaining =>
      finiteBinaryScoreRun candidates
        (finiteBinaryScoreShift candidates score observation.1 observation.2) remaining

/-- Run the explicit finite minimax prediction rule over a prescribed binary
observation suffix, retaining the current score vector in the recursion. -/
noncomputable def finiteBinarySequentialMinimaxCumulativeCorrelation
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) :
    ℕ → (Candidate → ℝ) → List (Context × Bool) → ℝ
  | 0, _, _ => 0
  | _ + 1, _, [] => 0
  | remaining + 1, score, observation :: observations =>
      finiteBinarySequentialMinimaxPrediction candidates remaining score observation.1 *
          rademacherSign observation.2 +
        finiteBinarySequentialMinimaxCumulativeCorrelation candidates remaining
          (finiteBinaryScoreShift candidates score observation.1 observation.2) observations

/-- The finite binary minimax rule has regret at most its dynamic value on
every observation path of the declared horizon. -/
theorem finiteBinarySequentialMinimax_terminalScore_sub_cumulativeCorrelation_le
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) :
    ∀ (remaining : ℕ) (score : Candidate → ℝ) (observations : List (Context × Bool)),
      observations.length = remaining →
      finiteScoreMaximum (finiteBinaryScoreRun candidates score observations) -
        finiteBinarySequentialMinimaxCumulativeCorrelation candidates remaining score observations ≤
        finiteBinarySequentialMinimaxValue candidates remaining score := by
  intro remaining
  induction remaining with
  | zero =>
      intro score observations hlength
      cases observations with
      | nil =>
          simp [finiteBinaryScoreRun, finiteBinarySequentialMinimaxCumulativeCorrelation,
            finiteBinarySequentialMinimaxValue]
      | cons observation tail => simp at hlength
  | succ remaining ih =>
      intro score observations hlength
      cases observations with
      | nil => simp at hlength
      | cons observation tail =>
          have htailLength : tail.length = remaining := by
            simpa using Nat.succ.inj hlength
          have htail := ih
            (finiteBinaryScoreShift candidates score observation.1 observation.2)
            tail htailLength
          have hstep := finiteBinarySequentialMinimaxValue_one_step candidates remaining score
            observation.1 observation.2
          simp only [finiteBinaryScoreRun, finiteBinarySequentialMinimaxCumulativeCorrelation]
          linarith

/-- The score of each named comparator after a binary observation suffix is
its literal signed correlation on that suffix. -/
theorem finiteBinaryScoreRun_apply_eq_correlation
    {Candidate Context : Type*} (candidates : Candidate → Context → ℝ)
    (initial : Candidate → ℝ) (observations : List (Context × Bool))
    (candidate : Candidate) :
    finiteBinaryScoreRun candidates initial observations candidate =
      initial candidate +
        (observations.map fun observation =>
          candidates candidate observation.1 * rademacherSign observation.2).sum := by
  induction observations generalizing initial with
  | nil => simp [finiteBinaryScoreRun]
  | cons observation remaining ih =>
      simp only [finiteBinaryScoreRun, List.map_cons, List.sum_cons]
      rw [ih]
      unfold finiteBinaryScoreShift
      ring

/-- Comparator-wise source-form of the finite binary minimax guarantee. -/
theorem finiteBinarySequentialMinimax_comparatorRegret_le_value
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) (horizon : ℕ)
    (observations : List (Context × Bool)) (hlength : observations.length = horizon)
    (candidate : Candidate) :
    (observations.map fun observation =>
      candidates candidate observation.1 * rademacherSign observation.2).sum -
        finiteBinarySequentialMinimaxCumulativeCorrelation candidates horizon (fun _ => 0)
          observations ≤ finiteBinarySequentialMinimaxValue candidates horizon (fun _ => 0) := by
  have hterminal := finiteBinarySequentialMinimax_terminalScore_sub_cumulativeCorrelation_le
    candidates horizon (fun _ => 0) observations hlength
  have hcoordinate :
      (observations.map fun observation =>
        candidates candidate observation.1 * rademacherSign observation.2).sum ≤
      finiteScoreMaximum (finiteBinaryScoreRun candidates (fun _ => 0) observations) := by
    have hscore :
        finiteBinaryScoreRun candidates (fun _ => 0) observations candidate =
          (observations.map fun observation =>
            candidates candidate observation.1 * rademacherSign observation.2).sum := by
      simpa using
        (finiteBinaryScoreRun_apply_eq_correlation candidates (fun _ => 0) observations candidate)
    rw [← hscore]
    exact le_finiteScoreMaximum _ candidate
  linarith

/-- The explicit finite binary minimax algorithm has comparator regret at
most the unnormalized global sequential Rademacher process. -/
theorem finiteBinarySequentialMinimax_comparatorRegret_le_rademacherProcess
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) (horizon : ℕ)
    (observations : List (Context × Bool)) (hlength : observations.length = horizon)
    (candidate : Candidate) :
    (observations.map fun observation =>
      candidates candidate observation.1 * rademacherSign observation.2).sum -
        finiteBinarySequentialMinimaxCumulativeCorrelation candidates horizon (fun _ => 0)
          observations ≤ finiteSequentialRademacherProcess (horizon := horizon) candidates :=
  (finiteBinarySequentialMinimax_comparatorRegret_le_value
    candidates horizon observations hlength candidate).trans
      (finiteBinarySequentialMinimaxValue_le_finiteSequentialRademacherProcess
        candidates horizon)

/-- Source-normalized form of the finite binary minimax guarantee. -/
theorem finiteBinarySequentialMinimax_comparatorRegret_le_horizon_mul_complexity
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    {horizon : ℕ} (horizonPositive : 0 < horizon) (candidates : Candidate → Context → ℝ)
    (observations : List (Context × Bool)) (hlength : observations.length = horizon)
    (candidate : Candidate) :
    (observations.map fun observation =>
      candidates candidate observation.1 * rademacherSign observation.2).sum -
        finiteBinarySequentialMinimaxCumulativeCorrelation candidates horizon (fun _ => 0)
          observations ≤
        (horizon : ℝ) * finiteSequentialRademacherComplexity (horizon := horizon) candidates := by
  have hcast : (horizon : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt horizonPositive
  rw [show (horizon : ℝ) *
      finiteSequentialRademacherComplexity (horizon := horizon) candidates =
        finiteSequentialRademacherProcess (horizon := horizon) candidates by
      unfold finiteSequentialRademacherComplexity
      field_simp]
  exact finiteBinarySequentialMinimax_comparatorRegret_le_rademacherProcess
    candidates horizon observations hlength candidate

/-- Update a finite comparator-score vector along real labels in the source
interval. -/
def finiteRealScoreRun {Candidate Context : Type*}
    (candidates : Candidate → Context → ℝ) :
    (Candidate → ℝ) → List (Context × ℝ) → Candidate → ℝ
  | score, [] => score
  | score, observation :: remaining =>
      finiteRealScoreRun candidates
        (finiteRealScoreShift candidates score observation.1 observation.2) remaining

/-- The cumulative learner correlation of the real-label finite minimax
algorithm on a prescribed suffix. -/
noncomputable def finiteRealSequentialMinimaxCumulativeCorrelation
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) :
    ℕ → (Candidate → ℝ) → List (Context × ℝ) → ℝ
  | 0, _, _ => 0
  | _ + 1, _, [] => 0
  | remaining + 1, score, observation :: observations =>
      finiteBinarySequentialMinimaxPrediction candidates remaining score observation.1 * observation.2 +
        finiteRealSequentialMinimaxCumulativeCorrelation candidates remaining
          (finiteRealScoreShift candidates score observation.1 observation.2) observations

/-- The real-label finite minimax algorithm telescopes on every admissible
source path. -/
theorem finiteRealSequentialMinimax_terminalScore_sub_cumulativeCorrelation_le
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) :
    ∀ (remaining : ℕ) (score : Candidate → ℝ) (observations : List (Context × ℝ)),
      observations.length = remaining →
      (∀ observation ∈ observations, observation.2 ∈ Set.Icc (-1 : ℝ) 1) →
      finiteScoreMaximum (finiteRealScoreRun candidates score observations) -
        finiteRealSequentialMinimaxCumulativeCorrelation candidates remaining score observations ≤
        finiteBinarySequentialMinimaxValue candidates remaining score := by
  intro remaining
  induction remaining with
  | zero =>
      intro score observations hlength hlabels
      cases observations with
      | nil =>
          simp [finiteRealScoreRun, finiteRealSequentialMinimaxCumulativeCorrelation,
            finiteBinarySequentialMinimaxValue]
      | cons observation tail => simp at hlength
  | succ remaining ih =>
      intro score observations hlength hlabels
      cases observations with
      | nil => simp at hlength
      | cons observation tail =>
          have htailLength : tail.length = remaining := by
            simpa using Nat.succ.inj hlength
          have hheadLabel : observation.2 ∈ Set.Icc (-1 : ℝ) 1 :=
            hlabels observation (by simp)
          have htailLabels : ∀ next ∈ tail, next.2 ∈ Set.Icc (-1 : ℝ) 1 := by
            intro next hnext
            exact hlabels next (by simp [hnext])
          have htail := ih
            (finiteRealScoreShift candidates score observation.1 observation.2)
            tail htailLength htailLabels
          have hstep := finiteRealSequentialMinimaxValue_one_step candidates remaining score
            observation.1 observation.2 hheadLabel
          simp only [finiteRealScoreRun, finiteRealSequentialMinimaxCumulativeCorrelation]
          linarith

/-- The real-score state of each comparator is its literal correlation with
the real-label history. -/
theorem finiteRealScoreRun_apply_eq_correlation
    {Candidate Context : Type*} (candidates : Candidate → Context → ℝ)
    (initial : Candidate → ℝ) (observations : List (Context × ℝ))
    (candidate : Candidate) :
    finiteRealScoreRun candidates initial observations candidate =
      initial candidate +
        (observations.map fun observation =>
          candidates candidate observation.1 * observation.2).sum := by
  induction observations generalizing initial with
  | nil => simp [finiteRealScoreRun]
  | cons observation remaining ih =>
      simp only [finiteRealScoreRun, List.map_cons, List.sum_cons]
      rw [ih]
      unfold finiteRealScoreShift
      ring

/-- Comparator-wise real-label form of the finite minimax guarantee. -/
theorem finiteRealSequentialMinimax_comparatorRegret_le_value
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) (horizon : ℕ)
    (observations : List (Context × ℝ)) (hlength : observations.length = horizon)
    (hlabels : ∀ observation ∈ observations, observation.2 ∈ Set.Icc (-1 : ℝ) 1)
    (candidate : Candidate) :
    (observations.map fun observation =>
      candidates candidate observation.1 * observation.2).sum -
        finiteRealSequentialMinimaxCumulativeCorrelation candidates horizon (fun _ => 0)
          observations ≤ finiteBinarySequentialMinimaxValue candidates horizon (fun _ => 0) := by
  have hterminal := finiteRealSequentialMinimax_terminalScore_sub_cumulativeCorrelation_le
    candidates horizon (fun _ => 0) observations hlength hlabels
  have hcoordinate :
      (observations.map fun observation =>
        candidates candidate observation.1 * observation.2).sum ≤
      finiteScoreMaximum (finiteRealScoreRun candidates (fun _ => 0) observations) := by
    have hscore :
        finiteRealScoreRun candidates (fun _ => 0) observations candidate =
          (observations.map fun observation =>
            candidates candidate observation.1 * observation.2).sum := by
      simpa using
        (finiteRealScoreRun_apply_eq_correlation candidates (fun _ => 0) observations candidate)
    rw [← hscore]
    exact le_finiteScoreMaximum _ candidate
  linarith

/-- The explicit finite real-label minimax algorithm has comparator regret at
most the source's unnormalized global sequential Rademacher process. -/
theorem finiteRealSequentialMinimax_comparatorRegret_le_rademacherProcess
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    (candidates : Candidate → Context → ℝ) (horizon : ℕ)
    (observations : List (Context × ℝ)) (hlength : observations.length = horizon)
    (hlabels : ∀ observation ∈ observations, observation.2 ∈ Set.Icc (-1 : ℝ) 1)
    (candidate : Candidate) :
    (observations.map fun observation =>
      candidates candidate observation.1 * observation.2).sum -
        finiteRealSequentialMinimaxCumulativeCorrelation candidates horizon (fun _ => 0)
          observations ≤ finiteSequentialRademacherProcess (horizon := horizon) candidates :=
  (finiteRealSequentialMinimax_comparatorRegret_le_value
    candidates horizon observations hlength hlabels candidate).trans
    (finiteBinarySequentialMinimaxValue_le_finiteSequentialRademacherProcess
      candidates horizon)

/-- Source-normalized real-label form of the explicit finite minimax OWAL
guarantee. -/
theorem finiteRealSequentialMinimax_comparatorRegret_le_horizon_mul_complexity
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Context] [Nonempty Context]
    {horizon : ℕ} (horizonPositive : 0 < horizon)
    (candidates : Candidate → Context → ℝ)
    (observations : List (Context × ℝ)) (hlength : observations.length = horizon)
    (hlabels : ∀ observation ∈ observations, observation.2 ∈ Set.Icc (-1 : ℝ) 1)
    (candidate : Candidate) :
    (observations.map fun observation =>
      candidates candidate observation.1 * observation.2).sum -
        finiteRealSequentialMinimaxCumulativeCorrelation candidates horizon (fun _ => 0)
          observations ≤
        (horizon : ℝ) * finiteSequentialRademacherComplexity
          (horizon := horizon) candidates := by
  have hcast : (horizon : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt horizonPositive
  rw [show (horizon : ℝ) *
      finiteSequentialRademacherComplexity (horizon := horizon) candidates =
        finiteSequentialRademacherProcess (horizon := horizon) candidates by
      unfold finiteSequentialRademacherComplexity
      field_simp]
  exact finiteRealSequentialMinimax_comparatorRegret_le_rademacherProcess
    candidates horizon observations hlength hlabels candidate

end AppliedModelingLib.Learning.Online
