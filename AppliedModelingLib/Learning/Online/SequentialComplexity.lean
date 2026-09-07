import AppliedModelingLib.Learning.Online.Basic
import AppliedModelingLib.Foundations.Probability.PmfPrefix
import Mathlib.Tactic

/-!
# Finite sequential Rademacher complexity

The sequential-complexity endpoint for online learning is indexed by a binary
history tree, not by a fixed sample path.  This module supplies the finite
tree and Rademacher-process definitions on which minimax OWAL theorems can be
stated.  The tree at round `t` observes exactly the preceding `t` signs.
-/

namespace AppliedModelingLib.Learning.Online

open scoped BigOperators

/-- A depth-`horizon` sequential tree.  The value at a round receives only a
binary history of strictly earlier rounds. -/
abbrev SequentialTree (X : Type*) (horizon : ℕ) :=
  (round : Fin horizon) → (Fin round.1 → Bool) → X

/-- An inductive presentation of a finite binary-history context tree.  It is
equivalent to the function presentation `SequentialTree`, but exposes the
root and its two continuation trees directly for dynamic-programming and
minimax arguments. -/
inductive BinarySequentialTree (X : Type*) : ℕ → Type _ where
  | leaf : BinarySequentialTree X 0
  | node {horizon : ℕ} : X → (Bool → BinarySequentialTree X horizon) →
      BinarySequentialTree X (horizon + 1)

/-- Restrict a full Rademacher-sign realization to the strict history before a
given round. -/
def sequentialRademacherHistory {horizon : ℕ}
    (signs : Fin horizon → Bool) (round : Fin horizon) : Fin round.1 → Bool :=
  fun earlier => signs ⟨earlier.1, lt_trans earlier.2 round.2⟩

/-- Evaluate a sequential tree along one complete Rademacher-sign path. -/
def SequentialTree.eval {X : Type*} {horizon : ℕ}
    (tree : SequentialTree X horizon) (signs : Fin horizon → Bool)
    (round : Fin horizon) : X :=
  tree round (sequentialRademacherHistory signs round)

/-- Convert an inductive binary-history tree to the function-indexed tree
used in the sequential-Rademacher definition. -/
def BinarySequentialTree.toSequentialTree {X : Type*} :
    {horizon : ℕ} → BinarySequentialTree X horizon → SequentialTree X horizon
  | 0, .leaf => fun round => Fin.elim0 round
  | horizon + 1, .node root continuations => fun round =>
      Fin.cases (motive := fun index => (Fin index.1 → Bool) → X)
        (fun _ => root)
        (fun childRound history =>
          (continuations (history ⟨0, Nat.succ_pos _⟩)).toSequentialTree childRound
            (fun earlier => history ⟨earlier.1 + 1, Nat.succ_lt_succ earlier.2⟩)) round

/-- Evaluation of a converted node at its root is its stored root context. -/
@[simp] theorem BinarySequentialTree.toSequentialTree_node_eval_zero
    {X : Type*} {horizon : ℕ} (root : X)
    (continuations : Bool → BinarySequentialTree X horizon)
    (signs : Fin (horizon + 1) → Bool) :
    (BinarySequentialTree.node root continuations).toSequentialTree.eval signs 0 = root := by
  simp [BinarySequentialTree.toSequentialTree, SequentialTree.eval]

/-- Evaluation of a converted node after its first round is evaluation in the
child selected by the initial Rademacher sign. -/
@[simp] theorem BinarySequentialTree.toSequentialTree_node_eval_succ
    {X : Type*} {horizon : ℕ} (root : X)
    (continuations : Bool → BinarySequentialTree X horizon)
    (signs : Fin (horizon + 1) → Bool) (round : Fin horizon) :
    (BinarySequentialTree.node root continuations).toSequentialTree.eval signs round.succ =
      (continuations (signs 0)).toSequentialTree.eval (Fin.tail signs) round := by
  simp only [BinarySequentialTree.toSequentialTree, SequentialTree.eval]
  congr 1

/-- The equivalence which separates the first element of a `Fin (n+1)` iid
tape from its remaining `Fin n` suffix. -/
def optionFinFirstEquiv (n : ℕ) : Option (Fin n) ≃ Fin (n + 1) where
  toFun
    | none => 0
    | some index => index.succ
  invFun index := Fin.cases none some index
  left_inv item := by
    cases item <;> simp
  right_inv index := by
    refine Fin.cases ?_ ?_ index <;> simp

/-- An iid `Fin (n+1)` tape can be split into its first draw and its remaining
suffix.  This is the root-first counterpart of
`pmfExp_pmfProduct_finSucc_eq_pairExp`. -/
theorem pmfExp_pmfProduct_finCons_eq_pairExp
    {α : Type*} [Fintype α] [DecidableEq α] (n : ℕ)
    (μ : PMF α) (F : (Fin (n + 1) → α) → ℝ) :
    pmfExp (pmfProduct (Fin (n + 1)) α μ) F =
      pmfPairExp (pmfProduct (Fin n) α μ) μ
        (fun history fresh => F (Fin.cons fresh history)) := by
  calc
    pmfExp (pmfProduct (Fin (n + 1)) α μ) F =
        pmfExp (pmfProduct (Option (Fin n)) α μ)
          (fun sample => F (fun index => sample ((optionFinFirstEquiv n).symm index))) := by
            exact (pmfExp_pmfProduct_equiv (optionFinFirstEquiv n) μ F).symm
    _ = pmfPairExp (pmfProduct (Fin n) α μ) μ
          (fun history fresh => F (Fin.cons fresh history)) := by
            rw [pmfExp_pmfProduct_option_eq_pairExp]
            congr 1
            funext history fresh
            congr 1
            funext index
            refine Fin.cases ?_ ?_ index <;> simp [optionFinFirstEquiv, extendDraw]

/-- The fair Boolean PMF is the arithmetic mean of its two branches. -/
theorem pmfExp_uniformPMF_bool_eq_average (f : Bool → ℝ) :
    pmfExp (uniformPMF Bool) f = (f true + f false) / 2 := by
  norm_num [pmfExp, uniformPMF]
  ring

/-- The real Rademacher sign encoded by a Boolean branch. -/
def rademacherSign (sign : Bool) : ℝ := if sign then 1 else -1

/-- A fair Boolean Rademacher sign has mean zero. -/
theorem pmfExp_uniformPMF_rademacherSign :
    pmfExp (uniformPMF Bool) rademacherSign = 0 := by
  norm_num [pmfExp, uniformPMF, rademacherSign]

/-- A prediction selected before the last independent sign has zero signed
expectation.  This is the one-step martingale-difference calculation used in
the sequential-tree lower bound. -/
private theorem pmfExp_rademacherSign_mul_terminalPredictable_eq_zero
    (n : ℕ) (predictor : (Fin n → Bool) → ℝ) :
    pmfExp (pmfProduct (Fin (n + 1)) Bool (uniformPMF Bool))
        (fun signs => rademacherSign (signs (Fin.last n)) * predictor (Fin.init signs)) = 0 := by
  let e := optionFinEquivFinSucc n
  have hprefix : ∀ tape : Option (Fin n) → Bool,
      Fin.init (fun index : Fin (n + 1) => tape (e.symm index)) =
        (fun index => tape (some index)) := by
    intro tape
    funext index
    change tape (e.symm (Fin.castSucc index)) = tape (some index)
    simp [e, optionFinEquivFinSucc, Fin.castSucc_ne_last]
  have hlast : e.symm (Fin.last n) = none := by
    simp [e, optionFinEquivFinSucc]
  calc
    pmfExp (pmfProduct (Fin (n + 1)) Bool (uniformPMF Bool))
        (fun signs => rademacherSign (signs (Fin.last n)) * predictor (Fin.init signs)) =
      pmfExp (pmfProduct (Option (Fin n)) Bool (uniformPMF Bool))
        (fun tape => rademacherSign (tape none) * predictor (fun index => tape (some index))) := by
          rw [← pmfExp_pmfProduct_equiv e (uniformPMF Bool)]
          apply pmfExp_congr
          intro tape
          rw [hprefix tape]
          change rademacherSign (tape (e.symm (Fin.last n))) *
              predictor (fun index => tape (some index)) =
            rademacherSign (tape none) * predictor (fun index => tape (some index))
          rw [hlast]
    _ = 0 := pmfExp_pmfProduct_fresh_eq_zero (uniformPMF Bool)
      (fun history fresh => rademacherSign fresh * predictor history) (by
        intro history
        rw [pmfExp_mul_const]
        rw [pmfExp_uniformPMF_rademacherSign]
        ring)

/-- Every predictable real-valued strategy has zero correlation with an iid
Rademacher sequence.  At round `t` its value sees only the strict prefix
`σ_{<t}`; later signs are integrated out by the iid-prefix marginal theorem.
This is the formal probabilistic core of the adaptive-tree lower construction.
-/
theorem pmfExp_rademacherSign_mul_predictable_eq_zero
    (horizon : ℕ) (round : Fin horizon)
    (predictor : (Fin round.1 → Bool) → ℝ) :
    pmfExp (pmfProduct (Fin horizon) Bool (uniformPMF Bool))
        (fun signs => rademacherSign (signs round) *
          predictor (sequentialRademacherHistory signs round)) = 0 := by
  have hlength : round.1 + 1 ≤ horizon := Nat.succ_le_iff.mpr round.2
  let statistic : (Fin (round.1 + 1) → Bool) → ℝ := fun signs =>
    rademacherSign (signs (Fin.last round.1)) * predictor (Fin.init signs)
  calc
    pmfExp (pmfProduct (Fin horizon) Bool (uniformPMF Bool))
        (fun signs => rademacherSign (signs round) *
          predictor (sequentialRademacherHistory signs round)) =
      pmfExp (pmfProduct (Fin horizon) Bool (uniformPMF Bool))
        (fun signs => statistic (fun index => signs (Fin.castLE hlength index))) := by
          apply pmfExp_congr
          intro signs
          unfold statistic
          congr 2
    _ = pmfExp (pmfProduct (Fin (round.1 + 1)) Bool (uniformPMF Bool)) statistic :=
      pmfExp_pmfProduct_prefix_eq (uniformPMF Bool) hlength statistic
    _ = 0 := pmfExp_rademacherSign_mul_terminalPredictable_eq_zero round.1 predictor

/-- The unnormalized sequential Rademacher process on one fixed tree and one
finite hypothesis class. -/
noncomputable def finiteSequentialRademacherSum
    {Candidate X : Type*} [Fintype Candidate] [Nonempty Candidate]
    {horizon : ℕ} (hypotheses : Candidate → X → ℝ)
    (tree : SequentialTree X horizon) : ℝ := by
  classical
  exact pmfExp (pmfProduct (Fin horizon) Bool (uniformPMF Bool)) fun signs =>
    Finset.univ.sup' Finset.univ_nonempty fun candidate =>
      ∑ round, rademacherSign (signs round) * hypotheses candidate (tree.eval signs round)

/-- The normalized finite sequential Rademacher complexity on one prescribed
tree.  The global source complexity is the supremum of this quantity over
admissible trees. -/
noncomputable def finiteSequentialRademacherComplexityOnTree
    {Candidate X : Type*} [Fintype Candidate] [Nonempty Candidate]
    {horizon : ℕ} (hypotheses : Candidate → X → ℝ)
    (tree : SequentialTree X horizon) : ℝ :=
  finiteSequentialRademacherSum hypotheses tree / (horizon : ℝ)

/-- The unnormalized finite sequential Rademacher process, supremized over
all admissible binary context trees.  The source's normalized complexity is
this quantity divided by the horizon. -/
noncomputable def finiteSequentialRademacherProcess
    {Candidate X : Type*} [Fintype Candidate] [Nonempty Candidate]
    {horizon : ℕ} (hypotheses : Candidate → X → ℝ) : ℝ :=
  sSup (Set.range (finiteSequentialRademacherSum hypotheses :
    SequentialTree X horizon → ℝ))

/-- The finite global sequential Rademacher complexity, normalized by the
horizon exactly as in the OKK25 source. -/
noncomputable def finiteSequentialRademacherComplexity
    {Candidate X : Type*} [Fintype Candidate] [Nonempty Candidate]
    {horizon : ℕ} (hypotheses : Candidate → X → ℝ) : ℝ :=
  finiteSequentialRademacherProcess (horizon := horizon) hypotheses / (horizon : ℝ)

/-- The two-point convexity step in the sequential supervised-minimax proof.
For a finite comparator class, the average of the `±1` linear perturbation
maxima is bounded by the corresponding average at perturbations `±2`.  This
is the algebraic source of the factor two in the Rakhlin--Sridharan--Tewari
upper bound. -/
theorem finiteSup_signedPerturbation_le_double
    {Candidate : Type*} [Fintype Candidate] [Nonempty Candidate]
    (base direction : Candidate → ℝ) :
    (Finset.univ.sup' Finset.univ_nonempty fun candidate =>
      base candidate + direction candidate) +
      (Finset.univ.sup' Finset.univ_nonempty fun candidate =>
        base candidate - direction candidate) ≤
    (Finset.univ.sup' Finset.univ_nonempty fun candidate =>
      base candidate + 2 * direction candidate) +
      (Finset.univ.sup' Finset.univ_nonempty fun candidate =>
        base candidate - 2 * direction candidate) := by
  let upper : ℝ := Finset.univ.sup' Finset.univ_nonempty fun candidate =>
    base candidate + 2 * direction candidate
  let lower : ℝ := Finset.univ.sup' Finset.univ_nonempty fun candidate =>
    base candidate - 2 * direction candidate
  have hplus :
      Finset.univ.sup' Finset.univ_nonempty (fun candidate =>
        base candidate + direction candidate) ≤
        (3 / 4 : ℝ) * upper + (1 / 4 : ℝ) * lower := by
    apply Finset.sup'_le Finset.univ_nonempty
    intro candidate _
    have hupper : base candidate + 2 * direction candidate ≤ upper := by
      exact Finset.le_sup' (fun other => base other + 2 * direction other)
        (Finset.mem_univ candidate)
    have hlower : base candidate - 2 * direction candidate ≤ lower := by
      exact Finset.le_sup' (fun other => base other - 2 * direction other)
        (Finset.mem_univ candidate)
    calc
      base candidate + direction candidate =
          (3 / 4 : ℝ) * (base candidate + 2 * direction candidate) +
            (1 / 4 : ℝ) * (base candidate - 2 * direction candidate) := by ring
      _ ≤ (3 / 4 : ℝ) * upper + (1 / 4 : ℝ) * lower :=
        add_le_add
          (mul_le_mul_of_nonneg_left hupper (by norm_num))
          (mul_le_mul_of_nonneg_left hlower (by norm_num))
  have hminus :
      Finset.univ.sup' Finset.univ_nonempty (fun candidate =>
        base candidate - direction candidate) ≤
        (1 / 4 : ℝ) * upper + (3 / 4 : ℝ) * lower := by
    apply Finset.sup'_le Finset.univ_nonempty
    intro candidate _
    have hupper : base candidate + 2 * direction candidate ≤ upper := by
      exact Finset.le_sup' (fun other => base other + 2 * direction other)
        (Finset.mem_univ candidate)
    have hlower : base candidate - 2 * direction candidate ≤ lower := by
      exact Finset.le_sup' (fun other => base other - 2 * direction other)
        (Finset.mem_univ candidate)
    calc
      base candidate - direction candidate =
          (1 / 4 : ℝ) * (base candidate + 2 * direction candidate) +
            (3 / 4 : ℝ) * (base candidate - 2 * direction candidate) := by ring
      _ ≤ (1 / 4 : ℝ) * upper + (3 / 4 : ℝ) * lower :=
        add_le_add
          (mul_le_mul_of_nonneg_left hupper (by norm_num))
          (mul_le_mul_of_nonneg_left hlower (by norm_num))
  change _ + _ ≤ upper + lower
  linarith

/-- A deterministic predictor facing a sequential context tree.  The predictor
may depend on the current context and all prior signs, but not on the fresh
sign at the current round. -/
abbrev SequentialPredictor (X : Type*) (horizon : ℕ) :=
  (round : Fin horizon) → (Fin round.1 → Bool) → X → ℝ

/-- The signed correlation accumulated by a predictor along a tree path. -/
def sequentialPredictorSignedCorrelation
    {X : Type*} {horizon : ℕ} (tree : SequentialTree X horizon)
    (predictor : SequentialPredictor X horizon) (signs : Fin horizon → Bool) : ℝ :=
  ∑ round, rademacherSign (signs round) *
    predictor round (sequentialRademacherHistory signs round) (tree.eval signs round)

/-- A finite randomized sequential predictor.  Its law is selected before
the fresh label at the given history, as in the simultaneous-move OWAL
protocol. -/
abbrev SequentialRandomizedPredictor (Sample X : Type*) (horizon : ℕ) :=
  (round : Fin horizon) → (Fin round.1 → Bool) → PMF Sample

/-- The correlation used by a randomized OWAL: each sampled predictor is
integrated out at its selected PMF before multiplication by the label. -/
noncomputable def sequentialRandomizedPredictorSignedCorrelation
    {Sample X : Type*} [Fintype Sample] [DecidableEq Sample] {horizon : ℕ}
    (tree : SequentialTree X horizon)
    (predictor : SequentialRandomizedPredictor Sample X horizon)
    (output : Sample → X → ℝ) (signs : Fin horizon → Bool) : ℝ :=
  ∑ round, rademacherSign (signs round) *
    pmfExp (predictor round (sequentialRademacherHistory signs round))
      (fun sample => output sample (tree.eval signs round))

/-- The deterministic mean prediction represented by a randomized OWAL law. -/
noncomputable def SequentialRandomizedPredictor.mean
    {Sample X : Type*} [Fintype Sample] [DecidableEq Sample] {horizon : ℕ}
    (predictor : SequentialRandomizedPredictor Sample X horizon)
    (output : Sample → X → ℝ) : SequentialPredictor X horizon :=
  fun round history context => pmfExp (predictor round history)
    (fun sample => output sample context)

/-- The source randomized OWAL correlation is definitionally the correlation
of its deterministic mean predictor. -/
theorem sequentialRandomizedPredictorSignedCorrelation_eq_mean
    {Sample X : Type*} [Fintype Sample] [DecidableEq Sample] {horizon : ℕ}
    (tree : SequentialTree X horizon)
    (predictor : SequentialRandomizedPredictor Sample X horizon)
    (output : Sample → X → ℝ) :
    sequentialRandomizedPredictorSignedCorrelation tree predictor output =
      sequentialPredictorSignedCorrelation tree
        (SequentialRandomizedPredictor.mean predictor output) := by
  rfl

/-- The best signed comparator correlation on one sequential-tree path. -/
noncomputable def finiteSequentialComparatorSignedCorrelation
    {Candidate X : Type*} [Fintype Candidate] [Nonempty Candidate]
    {horizon : ℕ} (hypotheses : Candidate → X → ℝ)
    (tree : SequentialTree X horizon) (signs : Fin horizon → Bool) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty fun candidate =>
    ∑ round, rademacherSign (signs round) * hypotheses candidate (tree.eval signs round)

/-- Cumulative regret against the best comparator on a signed sequential path. -/
noncomputable def finiteSequentialSignedRegret
    {Candidate X : Type*} [Fintype Candidate] [Nonempty Candidate]
    {horizon : ℕ} (hypotheses : Candidate → X → ℝ)
    (tree : SequentialTree X horizon) (predictor : SequentialPredictor X horizon)
    (signs : Fin horizon → Bool) : ℝ :=
  finiteSequentialComparatorSignedCorrelation hypotheses tree signs -
    sequentialPredictorSignedCorrelation tree predictor signs

/-- The finite signed regret of a randomized OWAL, evaluated in the exact
expectation convention of the source simultaneous-move guarantee. -/
noncomputable def finiteSequentialRandomizedSignedRegret
    {Candidate Sample X : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Sample] [DecidableEq Sample] {horizon : ℕ}
    (hypotheses : Candidate → X → ℝ)
    (tree : SequentialTree X horizon)
    (predictor : SequentialRandomizedPredictor Sample X horizon)
    (output : Sample → X → ℝ) (signs : Fin horizon → Bool) : ℝ :=
  finiteSequentialComparatorSignedCorrelation hypotheses tree signs -
    sequentialRandomizedPredictorSignedCorrelation tree predictor output signs

/-- A randomized OWAL's exact expected regret is the deterministic signed
regret of its PMF mean predictor. -/
theorem finiteSequentialRandomizedSignedRegret_eq_mean
    {Candidate Sample X : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Sample] [DecidableEq Sample] {horizon : ℕ}
    (hypotheses : Candidate → X → ℝ)
    (tree : SequentialTree X horizon)
    (predictor : SequentialRandomizedPredictor Sample X horizon)
    (output : Sample → X → ℝ) :
    finiteSequentialRandomizedSignedRegret hypotheses tree predictor output =
      finiteSequentialSignedRegret hypotheses tree
        (SequentialRandomizedPredictor.mean predictor output) := by
  rfl

/-- The total correlation of any predictable strategy with iid Rademacher
labels is zero.  No boundedness assumption is needed for this finite exact
identity. -/
theorem pmfExp_sequentialPredictorSignedCorrelation_eq_zero
    {X : Type*} {horizon : ℕ} (tree : SequentialTree X horizon)
    (predictor : SequentialPredictor X horizon) :
    pmfExp (pmfProduct (Fin horizon) Bool (uniformPMF Bool))
        (sequentialPredictorSignedCorrelation tree predictor) = 0 := by
  unfold sequentialPredictorSignedCorrelation
  rw [pmfExp_sum]
  apply Finset.sum_eq_zero
  intro round _
  exact pmfExp_rademacherSign_mul_predictable_eq_zero horizon round
    (fun history => predictor round history (tree round history))

/-- Under iid Rademacher labels down any fixed adaptive context tree, the
expected signed regret of every predictable deterministic predictor is exactly
the unnormalized sequential Rademacher process of the comparator class. -/
theorem pmfExp_finiteSequentialSignedRegret_eq_rademacherSum
    {Candidate X : Type*} [Fintype Candidate] [Nonempty Candidate]
    {horizon : ℕ} (hypotheses : Candidate → X → ℝ)
    (tree : SequentialTree X horizon) (predictor : SequentialPredictor X horizon) :
    pmfExp (pmfProduct (Fin horizon) Bool (uniformPMF Bool))
        (finiteSequentialSignedRegret hypotheses tree predictor) =
      finiteSequentialRademacherSum hypotheses tree := by
  classical
  unfold finiteSequentialSignedRegret finiteSequentialRademacherSum
    finiteSequentialComparatorSignedCorrelation
  rw [pmfExp_sub, pmfExp_sequentialPredictorSignedCorrelation_eq_zero]
  ring

/-- Every deterministic predictable predictor has a concrete Rademacher path
on which its signed regret is at least the sequential Rademacher process.
Interpreting that path as an adaptive adversary is the finite lower-bound
construction required by the sequential-complexity definition. -/
theorem exists_finiteSequentialSignedRegret_ge_rademacherSum
    {Candidate X : Type*} [Fintype Candidate] [Nonempty Candidate]
    {horizon : ℕ} (hypotheses : Candidate → X → ℝ)
    (tree : SequentialTree X horizon) (predictor : SequentialPredictor X horizon) :
    ∃ signs : Fin horizon → Bool,
      finiteSequentialRademacherSum hypotheses tree ≤
        finiteSequentialSignedRegret hypotheses tree predictor signs := by
  classical
  let law := pmfProduct (Fin horizon) Bool (uniformPMF Bool)
  let regret := finiteSequentialSignedRegret hypotheses tree predictor
  let process := finiteSequentialRademacherSum hypotheses tree
  by_contra hnone
  have hall : ∀ signs : Fin horizon → Bool, regret signs < process := by
    intro signs
    exact lt_of_not_ge (fun hge => hnone ⟨signs, hge⟩)
  let defaultSigns : Fin horizon → Bool := fun _ => false
  have hmass : 0 < (law defaultSigns).toReal := by
    unfold law
    rw [pmfProduct_uniformPMF_eq_uniformPMF_fun]
    exact uniformPMF_apply_toReal_pos defaultSigns
  have hmean_lt : pmfExp law regret < process :=
    pmfExp_lt_of_forall_le_exists_lt law regret process
      (fun signs => (hall signs).le) ⟨defaultSigns, hmass, hall defaultSigns⟩
  have hmean_eq : pmfExp law regret = process := by
    exact pmfExp_finiteSequentialSignedRegret_eq_rademacherSum hypotheses tree predictor
  rw [hmean_eq] at hmean_lt
  exact lt_irrefl _ hmean_lt

/-- The adaptive-tree lower construction in the source's randomized OWAL
convention.  Randomization cannot remove the lower bound because the payoff
is linear and the PMF mean is itself a predictable deterministic predictor. -/
theorem exists_finiteSequentialRandomizedSignedRegret_ge_rademacherSum
    {Candidate Sample X : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Sample] [DecidableEq Sample] {horizon : ℕ}
    (hypotheses : Candidate → X → ℝ)
    (tree : SequentialTree X horizon)
    (predictor : SequentialRandomizedPredictor Sample X horizon)
    (output : Sample → X → ℝ) :
    ∃ signs : Fin horizon → Bool,
      finiteSequentialRademacherSum hypotheses tree ≤
        finiteSequentialRandomizedSignedRegret hypotheses tree predictor output signs := by
  rw [finiteSequentialRandomizedSignedRegret_eq_mean]
  exact exists_finiteSequentialSignedRegret_ge_rademacherSum hypotheses tree
    (SequentialRandomizedPredictor.mean predictor output)

/-- If a number bounds a predictor's regret on every path of every adaptive
context tree, it also bounds the unnormalized sequential Rademacher process.
Together with `exists_finiteSequentialSignedRegret_ge_rademacherSum`, this is
the finite deterministic lower half of the OWAL minimax theorem. -/
theorem finiteSequentialRademacherProcess_le_of_all_tree_path_regret_le
    {Candidate X : Type*} [Fintype Candidate] [Nonempty Candidate]
    {horizon : ℕ} [Nonempty (SequentialTree X horizon)]
    (hypotheses : Candidate → X → ℝ) (predictor : SequentialPredictor X horizon)
    (bound : ℝ)
    (hbound : ∀ (tree : SequentialTree X horizon) (signs : Fin horizon → Bool),
      finiteSequentialSignedRegret hypotheses tree predictor signs ≤ bound) :
    finiteSequentialRademacherProcess (horizon := horizon) hypotheses ≤ bound := by
  unfold finiteSequentialRademacherProcess
  apply csSup_le
  · let tree : SequentialTree X horizon := Classical.choice inferInstance
    exact ⟨finiteSequentialRademacherSum hypotheses tree, ⟨tree, rfl⟩⟩
  · intro process hprocess
    rcases hprocess with ⟨tree, rfl⟩
    rcases exists_finiteSequentialSignedRegret_ge_rademacherSum
      hypotheses tree predictor with ⟨signs, hregret⟩
    exact hregret.trans (hbound tree signs)

/-- Global adaptive-tree lower bound in the randomized OWAL convention. -/
theorem finiteSequentialRademacherProcess_le_of_all_tree_path_randomizedRegret_le
    {Candidate Sample X : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Sample] [DecidableEq Sample] {horizon : ℕ}
    [Nonempty (SequentialTree X horizon)]
    (hypotheses : Candidate → X → ℝ)
    (predictor : SequentialRandomizedPredictor Sample X horizon)
    (output : Sample → X → ℝ) (bound : ℝ)
    (hbound : ∀ (tree : SequentialTree X horizon) (signs : Fin horizon → Bool),
      finiteSequentialRandomizedSignedRegret hypotheses tree predictor output signs ≤ bound) :
    finiteSequentialRademacherProcess (horizon := horizon) hypotheses ≤ bound := by
  unfold finiteSequentialRademacherProcess
  apply csSup_le
  · let tree : SequentialTree X horizon := Classical.choice inferInstance
    exact ⟨finiteSequentialRademacherSum hypotheses tree, ⟨tree, rfl⟩⟩
  · intro process hprocess
    rcases hprocess with ⟨tree, rfl⟩
    rcases exists_finiteSequentialRandomizedSignedRegret_ge_rademacherSum
      hypotheses tree predictor output with ⟨signs, hregret⟩
    exact hregret.trans (hbound tree signs)

/-- Source-normalized form of the adaptive-tree lower bound.  For a positive
horizon, a uniform pathwise OWAL regret bound must be at least
`T * srad_T`; the equality in the first step records the normalization rather
than concealing it in asymptotic notation. -/
theorem horizon_mul_finiteSequentialRademacherComplexity_le_of_all_tree_path_regret_le
    {Candidate X : Type*} [Fintype Candidate] [Nonempty Candidate]
    {horizon : ℕ} [Nonempty (SequentialTree X horizon)]
    (horizonPositive : 0 < horizon)
    (hypotheses : Candidate → X → ℝ) (predictor : SequentialPredictor X horizon)
    (bound : ℝ)
    (hbound : ∀ (tree : SequentialTree X horizon) (signs : Fin horizon → Bool),
      finiteSequentialSignedRegret hypotheses tree predictor signs ≤ bound) :
    (horizon : ℝ) * finiteSequentialRademacherComplexity (horizon := horizon) hypotheses ≤ bound := by
  have hcast : (horizon : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt horizonPositive
  calc
    (horizon : ℝ) * finiteSequentialRademacherComplexity (horizon := horizon) hypotheses =
        finiteSequentialRademacherProcess (horizon := horizon) hypotheses := by
          unfold finiteSequentialRademacherComplexity
          field_simp
    _ ≤ bound := finiteSequentialRademacherProcess_le_of_all_tree_path_regret_le
      hypotheses predictor bound hbound

/-- Source-normalized randomized OWAL form of the adaptive-tree lower bound. -/
theorem horizon_mul_finiteSequentialRademacherComplexity_le_of_all_tree_path_randomizedRegret_le
    {Candidate Sample X : Type*} [Fintype Candidate] [Nonempty Candidate]
    [Fintype Sample] [DecidableEq Sample] {horizon : ℕ}
    [Nonempty (SequentialTree X horizon)]
    (horizonPositive : 0 < horizon)
    (hypotheses : Candidate → X → ℝ)
    (predictor : SequentialRandomizedPredictor Sample X horizon)
    (output : Sample → X → ℝ) (bound : ℝ)
    (hbound : ∀ (tree : SequentialTree X horizon) (signs : Fin horizon → Bool),
      finiteSequentialRandomizedSignedRegret hypotheses tree predictor output signs ≤ bound) :
    (horizon : ℝ) * finiteSequentialRademacherComplexity (horizon := horizon) hypotheses ≤ bound := by
  have hcast : (horizon : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt horizonPositive
  calc
    (horizon : ℝ) * finiteSequentialRademacherComplexity (horizon := horizon) hypotheses =
        finiteSequentialRademacherProcess (horizon := horizon) hypotheses := by
          unfold finiteSequentialRademacherComplexity
          field_simp
    _ ≤ bound := finiteSequentialRademacherProcess_le_of_all_tree_path_randomizedRegret_le
      hypotheses predictor output bound hbound

end AppliedModelingLib.Learning.Online
