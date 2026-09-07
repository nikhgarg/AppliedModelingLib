import GS62CollegeAdmissions.SourceCompletion
import Mathlib.Tactic.Ring

/-!
# Gale--Shapley's batched deferred-acceptance procedure

The 1962 proof advances in *stages*: every proposer who is free at the start of
a stage makes one proposal, while a proposer displaced during that stage waits
until the next stage.  This module implements that scheduling rule on top of
the reusable one-proposal DA transition and proves the paper's
`n^2 - 2n + 2` stage bound (written over naturals as `(n - 1)^2 + 1`).
-/

namespace GS62CollegeAdmissions
open AppliedModelingLib.Matching

variable {M W : Type*} [Fintype M] [Fintype W]
  [DecidableEq M] [DecidableEq W]

/-- The proposers free and able to propose at the start of a batched stage. -/
noncomputable def gsBatchedSchedule
    (val_m : M → W → ℝ) (s : DAState M W) : List M := by
  classical
  exact (Finset.univ.filter fun m => IsActiveMan val_m s m).toList

@[simp] theorem mem_gsBatchedSchedule_iff
    (val_m : M → W → ℝ) (s : DAState M W) (m : M) :
    m ∈ gsBatchedSchedule val_m s ↔ IsActiveMan val_m s m := by
  classical
  simp [gsBatchedSchedule]

theorem gsBatchedSchedule_nodup
    (val_m : M → W → ℝ) (s : DAState M W) :
    (gsBatchedSchedule val_m s).Nodup := by
  classical
  exact Finset.nodup_toList _

/-- One paper stage: schedule exactly the proposers active at stage start. -/
noncomputable def gsBatchedStep
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) : DAState M W :=
  daStateAfterSchedule val_m val_w s (gsBatchedSchedule val_m s)

/-- The batched state after a prescribed number of stages from any state. -/
noncomputable def gsStateAfterBatchesFrom
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    DAState M W → ℕ → DAState M W
  | s, 0 => s
  | s, stages + 1 =>
      gsStateAfterBatchesFrom val_m val_w (gsBatchedStep val_m val_w s) stages

/-- The paper's batched run from the empty initial state. -/
noncomputable def gsStateAfterBatches
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (stages : ℕ) : DAState M W :=
  gsStateAfterBatchesFrom val_m val_w (initialDAState M W) stages

@[simp] theorem gsStateAfterBatchesFrom_zero
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) :
    gsStateAfterBatchesFrom val_m val_w s 0 = s := rfl

@[simp] theorem gsStateAfterBatchesFrom_succ
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (stages : ℕ) :
    gsStateAfterBatchesFrom val_m val_w s (stages + 1) =
      gsStateAfterBatchesFrom val_m val_w
        (gsBatchedStep val_m val_w s) stages := rfl

theorem gsStateAfterBatchesFrom_add
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (a b : ℕ) :
    gsStateAfterBatchesFrom val_m val_w s (a + b) =
      gsStateAfterBatchesFrom val_m val_w
        (gsStateAfterBatchesFrom val_m val_w s a) b := by
  induction a generalizing s with
  | zero => simp
  | succ a ih =>
      simpa only [Nat.succ_add, gsStateAfterBatchesFrom] using
        ih (gsBatchedStep val_m val_w s)

private lemma active_after_other_scheduled_step
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) {m m' : M}
    (hactive : IsActiveMan val_m s m) (hne : m ≠ m') :
    IsActiveMan val_m (daStepByMan val_m val_w s m') m := by
  classical
  by_cases hactive' : IsActiveMan val_m s m'
  · have hnoholder : ∀ w, s.w_match w ≠ some m := by
      intro w hw
      have hm : s.m_match m = some w := (s.consistent m w).2 hw
      rw [hactive.1] at hm
      cases hm
    have hmatch : (daStepByMan val_m val_w s m').m_match m = none := by
      unfold daStepByMan
      rw [dif_pos hactive']
      dsimp only
      split_ifs <;> simp [hne, hactive.1, hnoholder]
    have hproposals :
        (daStepByMan val_m val_w s m').m_proposals m =
          s.m_proposals m := by
      have hfield := daStepByMan_m_proposals_eq_removeProposal_of_active
        val_m val_w s m' hactive'
      rw [congrFun hfield m]
      exact removeProposal_of_ne s _ hne
    exact ⟨hmatch, by simpa [hproposals] using hactive.2⟩
  · simpa [daStepByMan, hactive'] using hactive

private lemma active_after_schedule_of_not_mem
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (schedule : List M) (m : M)
    (hactive : IsActiveMan val_m s m) (hnot : m ∉ schedule) :
    IsActiveMan val_m
      (daStateAfterSchedule val_m val_w s schedule) m := by
  induction schedule generalizing s with
  | nil => simpa using hactive
  | cons m' rest ih =>
      have hpair : m ≠ m' ∧ m ∉ rest := by simpa using hnot
      have hne : m ≠ m' := hpair.1
      have hnotRest : m ∉ rest := hpair.2
      simpa [daStateAfterSchedule_cons] using
        ih (daStepByMan val_m val_w s m')
          (active_after_other_scheduled_step val_m val_w s hactive hne)
          hnotRest

private theorem remainingProposalCount_after_active_schedule
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (schedule : List M)
    (hnodup : schedule.Nodup)
    (hactive : ∀ m ∈ schedule, IsActiveMan val_m s m) :
    remainingProposalCount
        (daStateAfterSchedule val_m val_w s schedule) + schedule.length =
      remainingProposalCount s := by
  induction schedule generalizing s with
  | nil => simp
  | cons m rest ih =>
      have hmactive : IsActiveMan val_m s m := hactive m (by simp)
      have hrestNodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
      have hmnot : m ∉ rest := (List.nodup_cons.mp hnodup).1
      have hrestActive : ∀ x ∈ rest,
          IsActiveMan val_m (daStepByMan val_m val_w s m) x := by
        intro x hx
        have hxactive : IsActiveMan val_m s x := hactive x (by simp [hx])
        have hxm : x ≠ m := by
          intro heq
          subst x
          exact hmnot hx
        exact active_after_other_scheduled_step val_m val_w s hxactive hxm
      have htail := ih (daStepByMan val_m val_w s m)
        hrestNodup hrestActive
      have hhead := remainingProposalCount_daStepByMan_add_one_of_active
        val_m val_w s m hmactive
      simp only [daStateAfterSchedule_cons, List.length_cons]
      omega

/-- A batch consumes exactly one proposal per proposer active at its start. -/
theorem remainingProposalCount_gsBatchedStep
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) :
    remainingProposalCount (gsBatchedStep val_m val_w s) +
        (gsBatchedSchedule val_m s).length =
      remainingProposalCount s := by
  unfold gsBatchedStep
  exact remainingProposalCount_after_active_schedule val_m val_w s
    (gsBatchedSchedule val_m s)
    (gsBatchedSchedule_nodup val_m s)
    (fun m hm => (mem_gsBatchedSchedule_iff val_m s m).1 hm)

theorem remainingProposalCount_gsBatchedStep_add_one_of_active
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (hactive : ∃ m, IsActiveMan val_m s m) :
    remainingProposalCount (gsBatchedStep val_m val_w s) + 1 ≤
      remainingProposalCount s := by
  have hnonempty : (gsBatchedSchedule val_m s).length ≠ 0 := by
    rcases hactive with ⟨m, hm⟩
    have hpos : 0 < (gsBatchedSchedule val_m s).length :=
      List.length_pos_iff_exists_mem.mpr ⟨m,
        (mem_gsBatchedSchedule_iff val_m s m).2 hm⟩
    omega
  have hcount := remainingProposalCount_gsBatchedStep val_m val_w s
  omega

theorem gsBatchedStep_eq_self_of_not_active
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (hnot : ¬ ∃ m, IsActiveMan val_m s m) :
    gsBatchedStep val_m val_w s = s := by
  have hschedule : gsBatchedSchedule val_m s = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro m hm
    exact hnot ⟨m, (mem_gsBatchedSchedule_iff val_m s m).1 hm⟩
  simp [gsBatchedStep, hschedule]

theorem active_start_of_active_after_batches
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (stages : ℕ)
    (hactive : ∃ m, IsActiveMan val_m
      (gsStateAfterBatchesFrom val_m val_w s stages) m) :
    ∃ m, IsActiveMan val_m s m := by
  induction stages generalizing s with
  | zero => simpa using hactive
  | succ stages ih =>
      have hstep : ∃ m, IsActiveMan val_m (gsBatchedStep val_m val_w s) m :=
        ih (gsBatchedStep val_m val_w s) (by simpa [gsStateAfterBatchesFrom] using hactive)
      by_contra hnot
      have hself := gsBatchedStep_eq_self_of_not_active val_m val_w s hnot
      rw [hself] at hstep
      exact hnot hstep

private theorem remainingProposalCount_after_active_batches
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (stages : ℕ)
    (hactiveFinal : ∃ m, IsActiveMan val_m
      (gsStateAfterBatchesFrom val_m val_w s stages) m) :
    remainingProposalCount
        (gsStateAfterBatchesFrom val_m val_w s stages) + stages ≤
      remainingProposalCount s := by
  induction stages generalizing s with
  | zero => simp
  | succ stages ih =>
      have hactiveStep : ∃ m, IsActiveMan val_m
          (gsBatchedStep val_m val_w s) m :=
        active_start_of_active_after_batches val_m val_w
          (gsBatchedStep val_m val_w s) stages
          (by simpa [gsStateAfterBatchesFrom] using hactiveFinal)
      have htail := ih (gsBatchedStep val_m val_w s)
        (by simpa [gsStateAfterBatchesFrom] using hactiveFinal)
      have hone := remainingProposalCount_gsBatchedStep_add_one_of_active
        val_m val_w s
        (by
          by_contra hnot
          rw [gsBatchedStep_eq_self_of_not_active val_m val_w s hnot] at hactiveStep
          exact hnot hactiveStep)
      simpa [gsStateAfterBatchesFrom] using (show
        remainingProposalCount
            (gsStateAfterBatchesFrom val_m val_w
              (gsBatchedStep val_m val_w s) stages) + (stages + 1) ≤
          remainingProposalCount s by omega)

theorem gsBatchedStep_preserves_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (hinv : DAInvariants val_m val_w s) :
    DAInvariants val_m val_w (gsBatchedStep val_m val_w s) := by
  exact daStateAfterSchedule_satisfies_invariants val_m val_w s
    (gsBatchedSchedule val_m s) hinv

theorem gsStateAfterBatchesFrom_preserves_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (stages : ℕ)
    (hinv : DAInvariants val_m val_w s) :
    DAInvariants val_m val_w
      (gsStateAfterBatchesFrom val_m val_w s stages) := by
  induction stages generalizing s with
  | zero => simpa using hinv
  | succ stages ih =>
      exact ih (gsBatchedStep val_m val_w s)
        (gsBatchedStep_preserves_invariants val_m val_w s hinv)

private theorem remainingProposalCount_lower_bound_of_active_equal_sides
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W)
    (hcard : Fintype.card M = Fintype.card W)
    (hwAcceptable : ∀ w m, 0 < val_w w m)
    (hinv : DAInvariants val_m val_w s)
    (hactive : ∃ m, IsActiveMan val_m s m) :
    Fintype.card M ≤ remainingProposalCount s := by
  classical
  rcases hactive with ⟨m0, hm0⟩
  have hnotWComplete : ¬ ∀ w, ∃ m, s.w_match w = some m := by
    intro hwComplete
    let mu : Assignment M W := ⟨s.m_match, s.w_match, s.consistent⟩
    have hmComplete := Assignment.m_complete_of_w_complete_of_card_eq
      mu hcard hwComplete
    rcases hmComplete m0 with ⟨w, hw⟩
    change s.m_match m0 = some w at hw
    rw [hm0.1] at hw
    cases hw
  push Not at hnotWComplete
  rcases hnotWComplete with ⟨w0, hw0⟩
  have hwNone : s.w_match w0 = none := by
    cases hw : s.w_match w0 with
    | none => rfl
    | some m => exact False.elim (hw0 m hw)
  have hmem : ∀ m, w0 ∈ s.m_proposals m :=
    unmatched_woman_mem_proposals_of_invariants
      val_m val_w s hwAcceptable hinv hwNone
  unfold remainingProposalCount
  calc
    Fintype.card M = ∑ _m : M, 1 := by simp
    _ ≤ ∑ m : M, (s.m_proposals m).card := by
      exact Finset.sum_le_sum fun m _ =>
        Finset.card_pos.mpr ⟨w0, hmem m⟩

/-- Natural-number form of the source bound `n^2 - 2n + 2`. -/
def gsBatchedStageBound (n : ℕ) : ℕ := (n - 1) * (n - 1) + 1

/--
The batched marriage procedure terminates within `n^2 - 2n + 2` stages for a
nonempty equal-size strict complete market.
-/
theorem paper_gs62_batched_stage_bound
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hnonempty : 0 < Fintype.card M)
    (hacceptable : AllPairsAcceptable val_m val_w) :
    ¬ ∃ m, IsActiveMan val_m
      (gsStateAfterBatches val_m val_w
        (gsBatchedStageBound (Fintype.card M))) m := by
  classical
  let n := Fintype.card M
  let initial := initialDAState M W
  let first := gsBatchedStep val_m val_w initial
  let k := n - 1
  have hn : n = k + 1 := by
    dsimp [k]
    omega
  have hallActive : ∀ m, IsActiveMan val_m initial m := by
    intro m
    refine ⟨rfl, ?_⟩
    have hwNonempty : Nonempty W :=
      Fintype.card_pos_iff.mp (by simpa [hcard] using hnonempty)
    let w : W := Classical.choice hwNonempty
    exact ⟨w, by simp [initial, initialDAState],
      le_of_lt (hacceptable.1 m w)⟩
  have hscheduleLength : (gsBatchedSchedule val_m initial).length = n := by
    classical
    simp [gsBatchedSchedule, hallActive, n]
  have hfirstCount : remainingProposalCount first + n = n * n := by
    have hcount := remainingProposalCount_gsBatchedStep val_m val_w initial
    simpa [first, hscheduleLength, initial, n, hcard,
      remainingProposalCount_initial] using hcount
  intro hactiveFinal
  have hbound : gsBatchedStageBound n = k * k + 1 := by
    simp [gsBatchedStageBound, k]
  have hrun : gsStateAfterBatches val_m val_w (gsBatchedStageBound n) =
      gsStateAfterBatchesFrom val_m val_w first (k * k) := by
    simp [gsStateAfterBatches, first, initial, hbound,
      gsStateAfterBatchesFrom]
  have hactiveTail : ∃ m, IsActiveMan val_m
      (gsStateAfterBatchesFrom val_m val_w first (k * k)) m := by
    simpa [n, hrun] using hactiveFinal
  have htailCount := remainingProposalCount_after_active_batches
    val_m val_w first (k * k) hactiveTail
  have hinvFinal : DAInvariants val_m val_w
      (gsStateAfterBatchesFrom val_m val_w first (k * k)) := by
    apply gsStateAfterBatchesFrom_preserves_invariants
    apply gsBatchedStep_preserves_invariants
    exact initialDAState_satisfies_invariants val_m val_w
  have hlower := remainingProposalCount_lower_bound_of_active_equal_sides
    val_m val_w
    (gsStateAfterBatchesFrom val_m val_w first (k * k))
    hcard hacceptable.2 hinvFinal hactiveTail
  change n ≤ remainingProposalCount
    (gsStateAfterBatchesFrom val_m val_w first (k * k)) at hlower
  rw [hn] at hfirstCount hlower
  ring_nf at hfirstCount htailCount hlower
  omega

/-- The assignment returned at the source stage bound. -/
noncomputable def gsBatchedDeferredAcceptance
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    Assignment M W :=
  let s := gsStateAfterBatches val_m val_w
    (gsBatchedStageBound (Fintype.card M))
  ⟨s.m_match, s.w_match, s.consistent⟩

/-- The bounded batched procedure produces the stable marriage used in Theorem 1. -/
theorem paper_gs62_batched_procedure_stable
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hnonempty : 0 < Fintype.card M)
    (hacceptable : AllPairsAcceptable val_m val_w) :
    IsStable val_m val_w (gsBatchedDeferredAcceptance val_m val_w) := by
  let s := gsStateAfterBatches val_m val_w
    (gsBatchedStageBound (Fintype.card M))
  have hinv : DAInvariants val_m val_w s := by
    exact gsStateAfterBatchesFrom_preserves_invariants val_m val_w
      (initialDAState M W) _
      (initialDAState_satisfies_invariants val_m val_w)
  have hterm : ¬ ∃ m, IsActiveMan val_m s m := by
    exact paper_gs62_batched_stage_bound val_m val_w hcard hnonempty hacceptable
  exact stable_of_invariants_and_terminated val_m val_w s hinv hterm

end GS62CollegeAdmissions
