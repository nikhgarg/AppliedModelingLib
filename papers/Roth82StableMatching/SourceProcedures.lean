import Roth82StableMatching.MainTheorems

/-!
# Source procedures for Roth (1982)

This file exposes the two algorithms in the form in which the source states
them.  In particular, a deferred-acceptance round freezes the set of unmatched
proposers at the start of the round and lets each of them make one proposal;
a proposer rejected during that round therefore waits until the next round.
The serial-dictatorship trace records the women remaining before each indexed
man chooses.
-/

namespace Roth82StableMatching

open AppliedModelingLib.Matching

section BatchedDeferredAcceptance

variable {M W : Type*} [Fintype M] [Fintype W]
  [DecidableEq M] [DecidableEq W]

/--
The frozen proposer list for one source round.  The chosen active proposer is
put first only to make the finite-decrease proof transparent; the remaining
active proposers occur once each in the finite enumeration.
-/
noncomputable def paper_batched_active_schedule
    (val_m : M → W → ℝ) (s : DAState M W) : List M := by
  classical
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · let m₀ := Classical.choose hactive
    exact m₀ ::
      (((Finset.univ.filter fun m => IsActiveMan val_m s m).erase m₀).toList)
  · exact []

/-- The source round schedules exactly the proposers active at its start. -/
theorem mem_paper_batched_active_schedule_iff
    (val_m : M → W → ℝ) (s : DAState M W) (m : M) :
    m ∈ paper_batched_active_schedule val_m s ↔ IsActiveMan val_m s m := by
  classical
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · let m₀ := Classical.choose hactive
    have hm₀ : IsActiveMan val_m s m₀ := Classical.choose_spec hactive
    by_cases hm : m = m₀
    · subst m
      simp [paper_batched_active_schedule, hactive, m₀, hm₀]
    · simp [paper_batched_active_schedule, hactive, m₀, hm]
  · have hm : ¬ IsActiveMan val_m s m := fun hm => hactive ⟨m, hm⟩
    simp [paper_batched_active_schedule, hactive, hm]

/-- No proposer occurs twice in a source round. -/
theorem paper_batched_active_schedule_nodup
    (val_m : M → W → ℝ) (s : DAState M W) :
    (paper_batched_active_schedule val_m s).Nodup := by
  classical
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · let m₀ := Classical.choose hactive
    rw [paper_batched_active_schedule]
    simp only [hactive, ↓reduceDIte, List.nodup_cons]
    exact ⟨by simp, Finset.nodup_toList _⟩
  · simp [paper_batched_active_schedule, hactive]

/--
One batched proposal stage from the source: every proposer rejected at the
start of the stage proposes once, and no newly rejected proposer acts until a
later stage.
-/
noncomputable def paper_batched_da_round
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) : DAState M W :=
  daStateAfterSchedule val_m val_w s (paper_batched_active_schedule val_m s)

theorem paper_batched_da_round_eq_self_of_no_active
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (hactive : ¬ ∃ m, IsActiveMan val_m s m) :
    paper_batched_da_round val_m val_w s = s := by
  classical
  simp [paper_batched_da_round, paper_batched_active_schedule, hactive]

/-- A nonterminal source round consumes at least one proposal opportunity. -/
theorem paper_batched_da_round_remainingProposalCount_add_one_le
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (hactive : ∃ m, IsActiveMan val_m s m) :
    remainingProposalCount (paper_batched_da_round val_m val_w s) + 1 ≤
      remainingProposalCount s := by
  classical
  let m₀ := Classical.choose hactive
  let rest :=
    (((Finset.univ.filter fun m => IsActiveMan val_m s m).erase m₀).toList)
  have hm₀ : IsActiveMan val_m s m₀ := Classical.choose_spec hactive
  have hfirst :=
    remainingProposalCount_daStepByMan_add_one_of_active
      val_m val_w s m₀ hm₀
  have hrest :=
    daStateAfterSchedule_remainingProposalCount_le val_m val_w
      (daStepByMan val_m val_w s m₀) rest
  have hschedule : paper_batched_active_schedule val_m s = m₀ :: rest := by
    simp [paper_batched_active_schedule, hactive, m₀, rest]
  rw [paper_batched_da_round, hschedule, daStateAfterSchedule_cons]
  omega

/-- Iterate source rounds from an arbitrary DA state. -/
noncomputable def paper_batched_da_rounds_from
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    DAState M W → ℕ → DAState M W
  | s, 0 => s
  | s, rounds + 1 =>
      paper_batched_da_rounds_from val_m val_w
        (paper_batched_da_round val_m val_w s) rounds

theorem paper_batched_da_rounds_from_eq_self_of_no_active
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (hactive : ¬ ∃ m, IsActiveMan val_m s m) :
    ∀ rounds, paper_batched_da_rounds_from val_m val_w s rounds = s := by
  intro rounds
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      simp only [paper_batched_da_rounds_from]
      rw [paper_batched_da_round_eq_self_of_no_active val_m val_w s hactive]
      exact ih

/-- `r` source rounds suffice whenever at most `r` proposals remain. -/
theorem paper_batched_da_rounds_from_terminated_of_count_le
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    ∀ (rounds : ℕ) (s : DAState M W),
      remainingProposalCount s ≤ rounds →
        ¬ ∃ m, IsActiveMan val_m
          (paper_batched_da_rounds_from val_m val_w s rounds) m := by
  intro rounds
  induction rounds with
  | zero =>
      intro s hcount hactive
      have hpos := remainingProposalCount_pos_of_active val_m s hactive
      omega
  | succ rounds ih =>
      intro s hcount
      by_cases hactive : ∃ m, IsActiveMan val_m s m
      · have hdecrease :=
          paper_batched_da_round_remainingProposalCount_add_one_le
            val_m val_w s hactive
        simp only [paper_batched_da_rounds_from]
        apply ih (paper_batched_da_round val_m val_w s)
        omega
      · rw [paper_batched_da_rounds_from_eq_self_of_no_active
          val_m val_w s hactive]
        exact hactive

theorem paper_batched_da_round_preserves_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (hinv : DAInvariants val_m val_w s) :
    DAInvariants val_m val_w (paper_batched_da_round val_m val_w s) := by
  exact daStateAfterSchedule_satisfies_invariants val_m val_w s
    (paper_batched_active_schedule val_m s) hinv

theorem paper_batched_da_rounds_from_preserves_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (hinv : DAInvariants val_m val_w s) :
    ∀ rounds, DAInvariants val_m val_w
      (paper_batched_da_rounds_from val_m val_w s rounds) := by
  intro rounds
  induction rounds generalizing s with
  | zero => exact hinv
  | succ rounds ih =>
      exact ih (paper_batched_da_round val_m val_w s)
        (paper_batched_da_round_preserves_invariants val_m val_w s hinv)

theorem paper_batched_da_round_preserves_rejected_pair_impossible
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenStrictPreferenceProfile val_w)
    (hnozero : MenNoOutsideTie val_m)
    (s : DAState M W) (hinv : DAInvariants val_m val_w s)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s) :
    DARejectedPairImpossibleInvariant val_m val_w
      (paper_batched_da_round val_m val_w s) := by
  exact daStateAfterSchedule_satisfies_rejected_pair_impossible_no_outside_tie
    val_m val_w s (paper_batched_active_schedule val_m s)
    hstrictM hstrictW.acceptablyStrict hnozero hinv hrejected

theorem paper_batched_da_rounds_from_preserves_rejected_pair_impossible
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenStrictPreferenceProfile val_w)
    (hnozero : MenNoOutsideTie val_m)
    (s : DAState M W) (hinv : DAInvariants val_m val_w s)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s) :
    ∀ rounds, DARejectedPairImpossibleInvariant val_m val_w
      (paper_batched_da_rounds_from val_m val_w s rounds) := by
  intro rounds
  induction rounds generalizing s with
  | zero => exact hrejected
  | succ rounds ih =>
      exact ih (paper_batched_da_round val_m val_w s)
        (paper_batched_da_round_preserves_invariants val_m val_w s hinv)
        (paper_batched_da_round_preserves_rejected_pair_impossible
          val_m val_w hstrictM hstrictW hnozero s hinv hrejected)

/-- The source batched men-proposing DA state, with the paper's finite bound. -/
noncomputable def paper_batched_deferredAcceptanceState
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : DAState M W :=
  paper_batched_da_rounds_from val_m val_w (initialDAState M W)
    (Fintype.card M * Fintype.card W)

/-- The matching returned by the source batched men-proposing procedure. -/
noncomputable def paper_batched_deferredAcceptance
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Assignment M W :=
  let s := paper_batched_deferredAcceptanceState val_m val_w
  ⟨s.m_match, s.w_match, s.consistent⟩

theorem paper_batched_deferredAcceptanceState_terminated
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    ¬ ∃ m, IsActiveMan val_m
      (paper_batched_deferredAcceptanceState val_m val_w) m := by
  apply paper_batched_da_rounds_from_terminated_of_count_le val_m val_w
  simp [remainingProposalCount_initial]

theorem paper_batched_deferredAcceptanceState_satisfies_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    DAInvariants val_m val_w
      (paper_batched_deferredAcceptanceState val_m val_w) := by
  exact paper_batched_da_rounds_from_preserves_invariants val_m val_w
    (initialDAState M W) (initialDAState_satisfies_invariants val_m val_w)
    (Fintype.card M * Fintype.card W)

theorem paper_batched_deferredAcceptance_eq_deferredAcceptance
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w) :
    paper_batched_deferredAcceptance val_m val_w =
      deferredAcceptance val_m val_w := by
  rcases hdomain with ⟨hstrictM, hstrictW, hposM, hposW⟩
  let s := paper_batched_deferredAcceptanceState val_m val_w
  have hinv : DAInvariants val_m val_w s :=
    paper_batched_deferredAcceptanceState_satisfies_invariants val_m val_w
  have hterm : ¬ ∃ m, IsActiveMan val_m s m :=
    paper_batched_deferredAcceptanceState_terminated val_m val_w
  have hrejected : DARejectedPairImpossibleInvariant val_m val_w s := by
    exact paper_batched_da_rounds_from_preserves_rejected_pair_impossible
      val_m val_w
      (fun m w w' _ _ h => hstrictM m w w' h)
      hstrictW (fun m w hzero => by have := hposM m w; linarith)
      (initialDAState M W)
      (initialDAState_satisfies_invariants val_m val_w)
      (initialDAState_satisfies_rejected_pair_impossible val_m val_w)
      (Fintype.card M * Fintype.card W)
  exact daState_assignment_eq_deferredAcceptance_of_rejected_pair_impossible
    val_m val_w s hcard hstrictM hstrictW ⟨hposM, hposW⟩ hinv hterm hrejected

/-- Women-proposing source rounds, transported back to the original sides. -/
noncomputable def paper_women_batched_deferredAcceptance
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Assignment M W :=
  (paper_batched_deferredAcceptance (M := W) (W := M) val_w val_m).swap

theorem paper_women_batched_deferredAcceptance_eq_women_deferredAcceptance
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w) :
    paper_women_batched_deferredAcceptance val_m val_w =
      paper_women_deferredAcceptance val_m val_w := by
  rcases hdomain with ⟨hstrictM, hstrictW, hposM, hposW⟩
  have h := paper_batched_deferredAcceptance_eq_deferredAcceptance
    (M := W) (W := M) val_w val_m hcard.symm
      ⟨hstrictW, hstrictM, hposW, hposM⟩
  exact congrArg Assignment.swap h

end BatchedDeferredAcceptance

section SerialDictatorship

/-- Women not yet selected before priority index `k`. -/
noncomputable def paper_serial_dictatorship_remaining {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) (k : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun w =>
    ∀ j : Fin n, j.val < k → paper_serial_dictatorship_perm val_m j ≠ w

/-- The woman selected when indexed man `i` acts. -/
noncomputable def paper_serial_dictatorship_choice {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) (i : Fin n) : Fin n :=
  paper_serial_dictatorship_perm val_m i

theorem paper_serial_dictatorship_remaining_zero {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) :
    paper_serial_dictatorship_remaining val_m 0 = Finset.univ := by
  classical
  ext w
  simp [paper_serial_dictatorship_remaining]

/-- The current man's choice has not been used by an earlier man. -/
theorem paper_serial_dictatorship_choice_mem_remaining {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) (i : Fin n) :
    paper_serial_dictatorship_choice val_m i ∈
      paper_serial_dictatorship_remaining val_m i.val := by
  classical
  simp only [paper_serial_dictatorship_remaining,
    paper_serial_dictatorship_choice, Finset.mem_filter, Finset.mem_univ, true_and]
  intro j hj heq
  have hji : j = i := (paper_serial_dictatorship_perm val_m).injective heq
  subst j
  omega

/--
At its indexed step, serial dictatorship gives the man a weakly best woman
among precisely those not selected at earlier steps.
-/
theorem paper_serial_dictatorship_choice_is_best_remaining {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) (i : Fin n) (w : Fin n)
    (hw : w ∈ paper_serial_dictatorship_remaining val_m i.val) :
    val_m i w ≤ val_m i (paper_serial_dictatorship_choice val_m i) := by
  classical
  let p := paper_serial_dictatorship_perm val_m
  let q : Equiv.Perm (Fin n) := p.trans (Equiv.swap (p i) w)
  have hp_final : p ∈ paper_serial_perm_set_aux val_m n := by
    simpa [p, paper_serial_perm_set] using
      paper_serial_dictatorship_perm_mem val_m
  have hp_i : p ∈ paper_serial_perm_set_aux val_m i.val :=
    paper_serial_perm_set_aux_subset_of_le val_m (Nat.le_of_lt i.isLt) hp_final
  have hw_remaining :
      ∀ j : Fin n, j.val < i.val → p j ≠ w := by
    simpa [paper_serial_dictatorship_remaining, p] using
      (Finset.mem_filter.mp hw).2
  have hq_agree : ∀ j : Fin n, j.val < i.val → q j = p j := by
    intro j hj
    have hpj_ne_pi : p j ≠ p i := by
      intro heq
      have hji : j = i := p.injective heq
      subst j
      omega
    have hpj_ne_w : p j ≠ w := hw_remaining j hj
    change (Equiv.swap (p i) w) (p j) = p j
    exact Equiv.swap_apply_of_ne_of_ne hpj_ne_pi hpj_ne_w
  have hq_i : q ∈ paper_serial_perm_set_aux val_m i.val :=
    paper_serial_perm_set_aux_mem_of_agree_before val_m
      (Nat.le_of_lt i.isLt) hp_i hq_agree
  have hbest := paper_serial_dictatorship_perm_best_at val_m i hq_i
  have hqi : q i = w := by simp [q]
  simpa [paper_serial_dictatorship_choice, hqi] using hbest

/-- After man `i` chooses, exactly his chosen woman is removed. -/
theorem paper_serial_dictatorship_remaining_succ {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) (i : Fin n) :
    paper_serial_dictatorship_remaining val_m (i.val + 1) =
      (paper_serial_dictatorship_remaining val_m i.val).erase
        (paper_serial_dictatorship_choice val_m i) := by
  classical
  ext w
  simp only [paper_serial_dictatorship_remaining, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_erase,
    paper_serial_dictatorship_choice]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hwi
      exact h i (Nat.lt_succ_self i.val) hwi.symm
    · intro j hj
      exact h j (Nat.lt_trans hj (Nat.lt_succ_self i.val))
  · rintro ⟨hwi, hprior⟩ j hj
    have hjle : j.val ≤ i.val := Nat.le_of_lt_succ hj
    rcases Nat.lt_or_eq_of_le hjle with hjlt | hjeq
    · exact hprior j hjlt
    · have hji : j = i := Fin.ext hjeq
      subst j
      exact fun heq => hwi heq.symm

/-- No woman remains after all `n` indexed men have chosen. -/
theorem paper_serial_dictatorship_remaining_final {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) :
    paper_serial_dictatorship_remaining val_m n = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hall := (Finset.mem_filter.mp hw).2
  let p := paper_serial_dictatorship_perm val_m
  exact hall (p.symm w) (p.symm w).isLt (by simp [p])

/-- The step trace returns exactly the mechanism used in Theorem 4. -/
theorem paper_serial_dictatorship_trace_refines_mechanism {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) (val_w : Fin n → Fin n → ℝ)
    (m : Fin n) :
    (paper_serial_dictatorship_mechanism val_m val_w).m_match m =
      some (paper_serial_dictatorship_choice val_m m) := by
  rfl

end SerialDictatorship

section BeneficialBystanderExample

/-- Section 6: man `m₂` reports `w₃ > w₁ > w₂`. -/
def paper_roth82_section6_man2_report : Theorem3Agent → ℝ := fun w =>
  if w.1 = 2 then 3 else if w.1 = 0 then 2 else 1

/-- Section 6 reported men profile, changing only `m₂`'s row. -/
def paper_roth82_section6_reported_men :
    Theorem3Agent → Theorem3Agent → ℝ :=
  Function.update theorem3MenProfile 1 paper_roth82_section6_man2_report

theorem paper_roth82_section6_truthful_domain :
    paper_strict_marriage_domain theorem3MenProfile theorem3WomenProfilePrime := by
  refine ⟨theorem3_woman_prime_strict_preference_profile.1,
    theorem3_woman_prime_strict_preference_profile.2, ?_, ?_⟩
  · intro m w
    fin_cases m <;> fin_cases w <;> norm_num [theorem3MenProfile]
  · intro w m
    fin_cases w <;> fin_cases m <;>
      norm_num [theorem3WomenProfilePrime, theorem3WomenProfile,
        theorem3Woman0PrimeReport]

theorem paper_roth82_section6_reported_domain :
    paper_strict_marriage_domain
      paper_roth82_section6_reported_men theorem3WomenProfilePrime := by
  refine ⟨?_, theorem3_woman_prime_strict_preference_profile.2, ?_, ?_⟩
  · intro m w w' h
    fin_cases m <;> fin_cases w <;> fin_cases w' <;>
      simp [paper_roth82_section6_reported_men,
        paper_roth82_section6_man2_report, theorem3MenProfile] at h ⊢
  · intro m w
    fin_cases m <;> fin_cases w <;>
      norm_num [paper_roth82_section6_reported_men,
        paper_roth82_section6_man2_report, theorem3MenProfile]
  · intro w m
    fin_cases w <;> fin_cases m <;>
      norm_num [theorem3WomenProfilePrime, theorem3WomenProfile,
        theorem3Woman0PrimeReport]

/-- The source's truthful Section 6 profile has the listed outcome `y`. -/
theorem paper_roth82_section6_truthful_da_eq_y :
    deferredAcceptance theorem3MenProfile theorem3WomenProfilePrime =
      theorem3OutcomeY := by
  exact theorem3_stable_woman_prime_eq_y
    (deferredAcceptance theorem3MenProfile theorem3WomenProfilePrime)
    (paper_da_is_stable theorem3MenProfile theorem3WomenProfilePrime)

/-- The source's reported Section 6 profile has the listed outcome `x`. -/
theorem paper_roth82_section6_reported_da_eq_x :
    deferredAcceptance paper_roth82_section6_reported_men
      theorem3WomenProfilePrime = theorem3OutcomeX := by
  have hdomain := paper_roth82_section6_reported_domain
  rcases hdomain with ⟨hstrictM, hstrictW, hposM, hposW⟩
  have hxStable : IsStable paper_roth82_section6_reported_men
      theorem3WomenProfilePrime theorem3OutcomeX := by
    refine ⟨?_, ?_, ?_⟩
    · intro m
      fin_cases m <;>
        norm_num [valM, theorem3OutcomeX,
          paper_roth82_section6_reported_men,
          paper_roth82_section6_man2_report, theorem3MenProfile]
    · intro w
      fin_cases w <;>
        norm_num [valW, theorem3OutcomeX, theorem3WomenProfilePrime,
          theorem3WomenProfile, theorem3Woman0PrimeReport]
    · intro m w hm hw
      fin_cases m <;> fin_cases w <;>
        simp [valM, valW, theorem3OutcomeX,
          paper_roth82_section6_reported_men,
          paper_roth82_section6_man2_report, theorem3MenProfile,
          theorem3WomenProfilePrime, theorem3WomenProfile,
          theorem3Woman0PrimeReport] at hm hw <;> try linarith
  have hxOptimal : IsMenOptimalStable paper_roth82_section6_reported_men
      theorem3WomenProfilePrime theorem3OutcomeX := by
    refine ⟨hxStable, ?_⟩
    intro nu _hstable m
    cases hnu : nu.m_match m with
    | none =>
        fin_cases m <;>
          norm_num [valM, hnu, theorem3OutcomeX,
            paper_roth82_section6_reported_men,
            paper_roth82_section6_man2_report, theorem3MenProfile]
    | some w =>
        fin_cases m <;> fin_cases w <;>
          norm_num [valM, hnu, theorem3OutcomeX,
            paper_roth82_section6_reported_men,
            paper_roth82_section6_man2_report, theorem3MenProfile]
  have hdaOptimal : IsMenOptimalStable paper_roth82_section6_reported_men
      theorem3WomenProfilePrime
      (deferredAcceptance paper_roth82_section6_reported_men
        theorem3WomenProfilePrime) :=
    ⟨da_produces_stable_matching _ _,
      da_is_men_optimal_of_strict_preferences _ _ hstrictM hstrictW
        ⟨hposM, hposW⟩⟩
  exact (men_optimal_stable_matching_unique_of_card_eq_all_pairs_acceptable
    paper_roth82_section6_reported_men theorem3WomenProfilePrime
    (mu := theorem3OutcomeX)
    (nu := deferredAcceptance paper_roth82_section6_reported_men
      theorem3WomenProfilePrime)
    rfl hstrictM ⟨hposM, hposW⟩ hxOptimal hdaOptimal).symm

theorem paper_roth82_section6_truthful_batched_eq_y :
    paper_batched_deferredAcceptance theorem3MenProfile
      theorem3WomenProfilePrime = theorem3OutcomeY := by
  rw [paper_batched_deferredAcceptance_eq_deferredAcceptance
    theorem3MenProfile theorem3WomenProfilePrime rfl
    paper_roth82_section6_truthful_domain]
  exact paper_roth82_section6_truthful_da_eq_y

theorem paper_roth82_section6_reported_batched_eq_x :
    paper_batched_deferredAcceptance paper_roth82_section6_reported_men
      theorem3WomenProfilePrime = theorem3OutcomeX := by
  rw [paper_batched_deferredAcceptance_eq_deferredAcceptance
    paper_roth82_section6_reported_men theorem3WomenProfilePrime rfl
    paper_roth82_section6_reported_domain]
  exact paper_roth82_section6_reported_da_eq_x

/--
Section 6 exactly: `m₂` keeps `w₃`, while bystanders `m₁` and `m₃`
strictly improve under `m₂`'s report.
-/
theorem paper_roth82_section6_beneficial_bystanders :
    paper_matching_valM theorem3MenProfile 1
        (theorem3OutcomeY.m_match 1) =
      paper_matching_valM theorem3MenProfile 1
        (theorem3OutcomeX.m_match 1) ∧
    paper_matching_valM theorem3MenProfile 0
        (theorem3OutcomeY.m_match 0) <
      paper_matching_valM theorem3MenProfile 0
        (theorem3OutcomeX.m_match 0) ∧
    paper_matching_valM theorem3MenProfile 2
        (theorem3OutcomeY.m_match 2) <
      paper_matching_valM theorem3MenProfile 2
        (theorem3OutcomeX.m_match 2) := by
  norm_num [paper_matching_valM, theorem3OutcomeY, theorem3OutcomeX,
    theorem3MenProfile]

end BeneficialBystanderExample

end Roth82StableMatching
