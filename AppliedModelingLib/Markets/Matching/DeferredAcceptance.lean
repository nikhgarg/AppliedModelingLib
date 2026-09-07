import AppliedModelingLib.Markets.Matching.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace AppliedModelingLib
namespace Matching

variable {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

structure DAState (M W : Type*) where
  m_match : M → Option W
  w_match : W → Option M
  m_proposals : M → Finset W
  consistent : ∀ m w, m_match m = some w ↔ w_match w = some m

theorem DAState.ext {M W : Type*} {s t : DAState M W}
    (hm : ∀ m, s.m_match m = t.m_match m)
    (hw : ∀ w, s.w_match w = t.w_match w)
    (hp : ∀ m, s.m_proposals m = t.m_proposals m) :
    s = t := by
  cases s with
  | mk sm sw sp sc =>
      cases t with
      | mk tm tw tp tc =>
          have hsm : sm = tm := funext hm
          have hsw : sw = tw := funext hw
          have hsp : sp = tp := funext hp
          subst hsm
          subst hsw
          subst hsp
          simp

/-- Relabel the proposer side of a DA state. -/
def DAState.relabelMen {M M' W : Type*} (e : M ≃ M')
    (s : DAState M W) : DAState M' W where
  m_match m' := s.m_match (e.symm m')
  w_match w := Option.map e (s.w_match w)
  m_proposals m' := s.m_proposals (e.symm m')
  consistent m' w := by
    constructor
    · intro hmatch
      have hw : s.w_match w = some (e.symm m') :=
        (s.consistent (e.symm m') w).1 hmatch
      simp [hw]
    · intro hmatch
      cases hw : s.w_match w with
      | none =>
          simp [hw] at hmatch
      | some m =>
          have hem : e m = m' := by
            simpa [hw] using hmatch
          have hm : m = e.symm m' := by
            rw [← hem]
            simp
          exact (s.consistent (e.symm m') w).2 (by simpa [hw, hm])

@[simp] theorem DAState.relabelMen_m_match {M M' W : Type*}
    (e : M ≃ M') (s : DAState M W) (m' : M') :
    (s.relabelMen e).m_match m' = s.m_match (e.symm m') := rfl

@[simp] theorem DAState.relabelMen_w_match {M M' W : Type*}
    (e : M ≃ M') (s : DAState M W) (w : W) :
    (s.relabelMen e).w_match w = Option.map e (s.w_match w) := rfl

@[simp] theorem DAState.relabelMen_m_proposals {M M' W : Type*}
    (e : M ≃ M') (s : DAState M W) (m' : M') :
    (s.relabelMen e).m_proposals m' = s.m_proposals (e.symm m') := rfl

@[simp] theorem DAState.relabelMen_w_match_apply {M M' W : Type*}
    (e : M ≃ M') (s : DAState M W) (w : W) (m : M) :
    (s.relabelMen e).w_match w = some (e m) ↔ s.w_match w = some m := by
  cases h : s.w_match w with
  | none =>
      constructor
      · intro hm
        simp [h] at hm
      · intro hm
        exact False.elim (by simpa [h] using hm)
  | some m0 =>
      constructor
      · intro hm
        have heq : e m0 = e m := by
          simpa [h] using hm
        simpa [h, e.injective heq]
      · intro hm
        have : m0 = m := Option.some.inj (by simpa [h] using hm)
        simp [h, this]

@[simp] theorem DAState.relabelMen_symm_relabelMen {M M' W : Type*}
    (e : M ≃ M') (s : DAState M W) :
    (s.relabelMen e).relabelMen e.symm = s := by
  cases s with
  | mk m_match w_match m_proposals consistent =>
      simp [DAState.relabelMen]

@[simp] theorem DAState.relabelMen_relabelMen_symm {M M' W : Type*}
    (e : M ≃ M') (s : DAState M' W) :
    (s.relabelMen e.symm).relabelMen e = s := by
  cases s with
  | mk m_match w_match m_proposals consistent =>
      simp [DAState.relabelMen]

def initialDAState (M W : Type*) [Fintype W] : DAState M W where
  m_match _ := none
  w_match _ := none
  m_proposals _ := Finset.univ
  consistent m w := by simp

@[simp] theorem DAState.relabelMen_initial {M M' W : Type*} [Fintype W]
    (e : M ≃ M') :
    (initialDAState M W).relabelMen e = initialDAState M' W := by
  cases e
  rfl

/--
Divorce woman `w0` from her current holder, leaving all proposal histories
unchanged. This is the state operation needed by continued-proposal traces such
in random matching analyses.
-/
def divorceWomanState (s : DAState M W) (w0 : W) : DAState M W where
  m_match m := if s.w_match w0 = some m then none else s.m_match m
  w_match w := if w = w0 then none else s.w_match w
  m_proposals := s.m_proposals
  consistent m w := by
    by_cases hw : w = w0
    · subst w
      by_cases hm : s.w_match w0 = some m
      · simp [hm]
      · have hnot : s.m_match m ≠ some w0 := by
          intro hmatch
          exact hm ((s.consistent m w0).1 hmatch)
        simp [hm, hnot]
    · by_cases hm : s.w_match w0 = some m
      · have hnot : s.w_match w ≠ some m := by
          intro hwmatch
          have hmw0 : s.m_match m = some w0 := (s.consistent m w0).2 hm
          have hmw : s.m_match m = some w := (s.consistent m w).2 hwmatch
          have : w0 = w := Option.some.inj (hmw0.symm.trans hmw)
          exact hw this.symm
        simp [hw, hm, hnot]
      · simp [hw, hm, s.consistent m w]

@[simp] theorem divorceWomanState_w_match_self (s : DAState M W) (w0 : W) :
    (divorceWomanState s w0).w_match w0 = none := by
  simp [divorceWomanState]

/-- Divorcing `w0` leaves every other woman's match unchanged. -/
theorem divorceWomanState_w_match_of_ne (s : DAState M W) {w w0 : W}
    (hw : w ≠ w0) :
    (divorceWomanState s w0).w_match w = s.w_match w := by
  simp [divorceWomanState, hw]

@[simp] theorem divorceWomanState_m_proposals (s : DAState M W) (w0 : W) :
    (divorceWomanState s w0).m_proposals = s.m_proposals := rfl

theorem divorceWomanState_m_match_of_w_match
    (s : DAState M W) {w0 : W} {m : M}
    (hmatch : s.w_match w0 = some m) :
    (divorceWomanState s w0).m_match m = none := by
  simp [divorceWomanState, hmatch]

theorem divorceWomanState_m_match_of_not_w_match
    (s : DAState M W) {w0 : W} {m : M}
    (hmatch : s.w_match w0 ≠ some m) :
    (divorceWomanState s w0).m_match m = s.m_match m := by
  simp [divorceWomanState, hmatch]

def IsActiveMan (val_m : M → W → ℝ) (s : DAState M W) (m : M) : Prop :=
  s.m_match m = none ∧ ∃ w ∈ s.m_proposals m, 0 ≤ val_m m w

/--
Divorcing one woman from a terminated DA state can make at most her former
holder active.  Every other man's match and proposal opportunities are
unchanged, so a second active man would already have been active before the
divorce.
-/
theorem atMostOneActiveMan_divorceWomanState_of_no_active
    (val_m : M → W → ℝ) (s : DAState M W) (w0 : W)
    (hterminated : ¬ ∃ m, IsActiveMan val_m s m) :
    ∀ m₁ m₂ : M,
      IsActiveMan val_m (divorceWomanState s w0) m₁ →
      IsActiveMan val_m (divorceWomanState s w0) m₂ →
      m₁ = m₂ := by
  intro m₁ m₂ hm₁ hm₂
  have hholder₁ : s.w_match w0 = some m₁ := by
    by_contra hnot
    apply hterminated
    refine ⟨m₁, ?_⟩
    refine ⟨?_, ?_⟩
    · simpa [divorceWomanState, hnot] using hm₁.1
    · rcases hm₁.2 with ⟨w, hw, hval⟩
      exact ⟨w, by simpa [divorceWomanState] using hw, hval⟩
  have hholder₂ : s.w_match w0 = some m₂ := by
    by_contra hnot
    apply hterminated
    refine ⟨m₂, ?_⟩
    refine ⟨?_, ?_⟩
    · simpa [divorceWomanState, hnot] using hm₂.1
    · rcases hm₂.2 with ⟨w, hw, hval⟩
      exact ⟨w, by simpa [divorceWomanState] using hw, hval⟩
  exact Option.some.inj (hholder₁.symm.trans hholder₂)

def BestRemainingWoman (val_m : M → W → ℝ) (s : DAState M W) (m : M) (w : W) : Prop :=
  w ∈ s.m_proposals m ∧ 0 ≤ val_m m w ∧
  ∀ w' ∈ s.m_proposals m, 0 ≤ val_m m w' → val_m m w' ≤ val_m m w

theorem IsActiveMan_relabelMen_iff {M M' W : Type*}
    (val_m : M → W → ℝ) (e : M ≃ M') (s : DAState M W) (m' : M') :
    IsActiveMan (fun m' w => val_m (e.symm m') w) (s.relabelMen e) m' ↔
      IsActiveMan val_m s (e.symm m') := by
  simp [IsActiveMan]

theorem BestRemainingWoman_relabelMen_iff {M M' W : Type*}
    (val_m : M → W → ℝ) (e : M ≃ M') (s : DAState M W) (m' : M') (w : W) :
    BestRemainingWoman (fun m' w => val_m (e.symm m') w)
        (s.relabelMen e) m' w ↔
      BestRemainingWoman val_m s (e.symm m') w := by
  simp [BestRemainingWoman]

/-- Remove the proposal opportunity `m -> w` from a DA state's proposal sets. -/
def removeProposal (s : DAState M W) (m : M) (w : W) : M → Finset W :=
  fun m' => if m' = m then s.m_proposals m \ {w} else s.m_proposals m'

@[simp] lemma removeProposal_self (s : DAState M W) (m : M) (w : W) :
    removeProposal s m w m = s.m_proposals m \ {w} := by
  simp [removeProposal]

@[simp] lemma removeProposal_of_ne (s : DAState M W) {m m' : M} (w : W)
    (h : m' ≠ m) :
    removeProposal s m w m' = s.m_proposals m' := by
  simp [removeProposal, h]

lemma mem_removeProposal_iff (s : DAState M W) (m m' : M) (w w' : W) :
    w' ∈ removeProposal s m w m' ↔ w' ∈ s.m_proposals m' ∧ (m' = m → w' ≠ w) := by
  by_cases hm : m' = m
  · subst m'
    simp
  · simp [removeProposal, hm]

theorem removeProposal_relabelMen_apply {M M' W : Type*}
    [DecidableEq M'] [DecidableEq M] [DecidableEq W]
    (e : M ≃ M') (s : DAState M W) (m' x : M') (w : W) :
    removeProposal (s.relabelMen e) m' w x =
      removeProposal s (e.symm m') w (e.symm x) := by
  by_cases hx : x = m'
  · subst x
    simp [removeProposal]
  · have hsymm : e.symm x ≠ e.symm m' := by
      intro h
      exact hx (e.symm.injective h)
    simp [removeProposal, hx, hsymm]

theorem removeProposal_relabelMen {M M' W : Type*}
    [DecidableEq M'] [DecidableEq M] [DecidableEq W]
    (e : M ≃ M') (s : DAState M W) (m' : M') (w : W) :
    removeProposal (s.relabelMen e) m' w =
      fun x => removeProposal s (e.symm m') w (e.symm x) := by
  funext x
  exact removeProposal_relabelMen_apply e s m' x w

lemma not_mem_of_not_mem_removeProposal (s : DAState M W) {m m' : M} {w w' : W}
    (hnot : w' ∉ removeProposal s m w m') :
    w' ∉ s.m_proposals m' ∨ (m' = m ∧ w' = w) := by
  by_cases hm : m' = m
  · subst m'
    simp [removeProposal] at hnot
    by_cases hmem : w' ∈ s.m_proposals m
    · exact Or.inr ⟨rfl, hnot hmem⟩
    · exact Or.inl hmem
  · left
    simpa [removeProposal, hm] using hnot

lemma exists_best_woman (val_m : M → W → ℝ) (s : DAState M W) (m : M)
    (hact : IsActiveMan val_m s m) : ∃ w, BestRemainingWoman val_m s m w := by
  rcases hact with ⟨_, w0, hw0_mem, hw0_nonneg⟩
  let eligible : Finset W := (s.m_proposals m).filter fun w => 0 ≤ val_m m w
  have helig_nonempty : eligible.Nonempty := by
    refine ⟨w0, ?_⟩
    simp [eligible, hw0_mem, hw0_nonneg]
  obtain ⟨w, hw_eligible, hw_max⟩ :=
    Finset.exists_max_image eligible (fun w => val_m m w) helig_nonempty
  refine ⟨w, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hw_eligible).1
  · exact (Finset.mem_filter.mp hw_eligible).2
  · intro w' hw'_mem hw'_nonneg
    exact hw_max w' (by simp [eligible, hw'_mem, hw'_nonneg])

lemma acceptMatch_consistent (s : DAState M W) {m : M} {w : W}
    (hm_unmatched : s.m_match m = none) :
    ∀ m0 w0,
      (if m0 = m then some w
        else if s.w_match w = some m0 then none
        else s.m_match m0) = some w0 ↔
      Function.update s.w_match w (some m) w0 = some m0 := by
  intro m0 w0
  by_cases hm : m0 = m
  · subst m0
    by_cases hw : w0 = w
    · subst w0
      simp
    · have hw' : w ≠ w0 := fun h => hw h.symm
      have hnot_old : s.w_match w0 ≠ some m := by
        intro hwm
        have hmmatch : s.m_match m = some w0 := (s.consistent m w0).2 hwm
        rw [hm_unmatched] at hmmatch
        cases hmmatch
      simp [hw, hw', hnot_old]
  · by_cases hw : w0 = w
    · subst w0
      have hm' : m ≠ m0 := fun h => hm h.symm
      by_cases hcur : s.w_match w = some m0
      · simp [hm, hm', hcur]
      · have hnot_old : s.m_match m0 ≠ some w := by
          intro hmmatch
          exact hcur ((s.consistent m0 w).1 hmmatch)
        simp [hm, hm', hcur, hnot_old]
    · by_cases hcur : s.w_match w = some m0
      · have hnot_old : s.w_match w0 ≠ some m0 := by
          intro hwm0
          have hm_w : s.m_match m0 = some w := (s.consistent m0 w).2 hcur
          have hm_w0 : s.m_match m0 = some w0 := (s.consistent m0 w0).2 hwm0
          have : w0 = w := Option.some.inj (hm_w0.symm.trans hm_w)
          exact hw this
        simp [hm, hw, hcur, hnot_old]
      · simpa [hm, hw, hcur] using (s.consistent m0 w0)

noncomputable def daStep (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) : DAState M W :=
  have _ : Decidable (∃ m, IsActiveMan val_m s m) := Classical.propDecidable _
  if h : ∃ m, IsActiveMan val_m s m then
    let m := Classical.choose h
    let hact := Classical.choose_spec h
    let w_exists := exists_best_woman val_m s m hact
    let w := Classical.choose w_exists
    let hw_best := Classical.choose_spec w_exists
    let new_proposals := removeProposal s m w
    let m_current := s.w_match w
    let accepts :=
      match m_current with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m
    have _ : Decidable accepts := Classical.propDecidable _
    if hacc : accepts then
      let new_w_match := Function.update s.w_match w (some m)
      let new_m_match := fun m'' =>
        if m'' = m then some w
        else if m_current = some m'' then none
        else s.m_match m''
      { m_match := new_m_match
        w_match := new_w_match
        m_proposals := new_proposals
        consistent := by
          simpa [new_m_match, new_w_match, m_current] using
            acceptMatch_consistent s hact.1 }
    else
      { s with m_proposals := new_proposals }
  else
    s

/-- The proposer selected by `daStep` from an active state. -/
noncomputable def daStepChosenMan (val_m : M → W → ℝ) (s : DAState M W)
    (hactive : ∃ m, IsActiveMan val_m s m) : M :=
  Classical.choose hactive

/-- The woman selected by `daStep` for the chosen active proposer. -/
noncomputable def daStepChosenWoman (val_m : M → W → ℝ) (s : DAState M W)
    (hactive : ∃ m, IsActiveMan val_m s m) : W :=
  let m := daStepChosenMan val_m s hactive
  let hact : IsActiveMan val_m s m := Classical.choose_spec hactive
  Classical.choose (exists_best_woman val_m s m hact)

/-- The accept predicate used by `daStep` after the chosen proposal is selected. -/
def daStepChosenAccepts (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (hactive : ∃ m, IsActiveMan val_m s m) : Prop :=
  let m := daStepChosenMan val_m s hactive
  let w := daStepChosenWoman val_m s hactive
  match s.w_match w with
  | none => 0 ≤ val_w w m
  | some m' => val_w w m' < val_w w m

/--
One scheduled DA step for a named proposer.  If `m` is active, he proposes to
one of his best remaining acceptable women and the usual accept/reject update is
performed.  If `m` is inactive, the state is unchanged.
-/
noncomputable def daStepByMan (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (m : M) : DAState M W :=
  have _ : Decidable (IsActiveMan val_m s m) := Classical.propDecidable _
  if hact : IsActiveMan val_m s m then
    let w_exists := exists_best_woman val_m s m hact
    let w := Classical.choose w_exists
    let new_proposals := removeProposal s m w
    let m_current := s.w_match w
    let accepts :=
      match m_current with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m
    have _ : Decidable accepts := Classical.propDecidable _
    if hacc : accepts then
      let new_w_match := Function.update s.w_match w (some m)
      let new_m_match := fun m'' =>
        if m'' = m then some w
        else if m_current = some m'' then none
        else s.m_match m''
      { m_match := new_m_match
        w_match := new_w_match
        m_proposals := new_proposals
        consistent := by
          simpa [new_m_match, new_w_match, m_current] using
            acceptMatch_consistent s hact.1 }
    else
      { s with m_proposals := new_proposals }
  else
    s

/-- Run scheduled DA steps from a start state. -/
noncomputable def daStateAfterSchedule (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) (schedule : List M) : DAState M W :=
  schedule.foldl (fun s m => daStepByMan val_m val_w s m) start

@[simp] theorem daStateAfterSchedule_nil
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (start : DAState M W) :
    daStateAfterSchedule val_m val_w start [] = start := rfl

@[simp] theorem daStateAfterSchedule_cons
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) (m : M) (schedule : List M) :
    daStateAfterSchedule val_m val_w start (m :: schedule) =
      daStateAfterSchedule val_m val_w
        (daStepByMan val_m val_w start m) schedule := rfl

@[simp] theorem daStateAfterSchedule_append
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) (schedule₁ schedule₂ : List M) :
    daStateAfterSchedule val_m val_w start (schedule₁ ++ schedule₂) =
      daStateAfterSchedule val_m val_w
        (daStateAfterSchedule val_m val_w start schedule₁) schedule₂ := by
  simp [daStateAfterSchedule, List.foldl_append]

/-- The woman selected by a scheduled step for an active named proposer. -/
noncomputable def daStepByManChosenWoman
    (val_m : M → W → ℝ) (s : DAState M W) (m : M)
    (hact : IsActiveMan val_m s m) : W :=
  Classical.choose (exists_best_woman val_m s m hact)

/-- Whether woman `w` accepts a proposal from man `m` in state `s`. -/
def daWomanAcceptsProposal
    (val_w : W → M → ℝ) (s : DAState M W) (m : M) (w : W) : Prop :=
  match s.w_match w with
  | none => 0 ≤ val_w w m
  | some m' => val_w w m' < val_w w m

theorem daWomanAcceptsProposal_relabelMen_iff {M M' W : Type*}
    (val_w : W → M → ℝ) (e : M ≃ M') (s : DAState M W) (m' : M') (w : W) :
    daWomanAcceptsProposal (fun w m' => val_w w (e.symm m'))
        (s.relabelMen e) m' w ↔
      daWomanAcceptsProposal val_w s (e.symm m') w := by
  cases h : s.w_match w with
  | none =>
      simp [daWomanAcceptsProposal, h]
  | some m =>
      simp [daWomanAcceptsProposal, h]

/-- The accept predicate used by a scheduled step for an active named proposer. -/
def daStepByManAccepts
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (m : M) (hact : IsActiveMan val_m s m) : Prop :=
  let w := daStepByManChosenWoman val_m s m hact
  match s.w_match w with
  | none => 0 ≤ val_w w m
  | some m' => val_w w m' < val_w w m

theorem daStepByManAccepts_eq_daWomanAcceptsProposal
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (m : M) (hact : IsActiveMan val_m s m) :
    daStepByManAccepts val_m val_w s m hact =
      daWomanAcceptsProposal val_w s m
        (daStepByManChosenWoman val_m s m hact) := rfl

theorem daStepByMan_chosen_eq_daStep
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (hactive : ∃ m, IsActiveMan val_m s m) :
    daStepByMan val_m val_w s (daStepChosenMan val_m s hactive) =
      daStep val_m val_w s := by
  classical
  change daStepByMan val_m val_w s (Classical.choose hactive) =
    daStep val_m val_w s
  have hact : IsActiveMan val_m s (Classical.choose hactive) :=
    Classical.choose_spec hactive
  let w_exists :=
    exists_best_woman val_m s (Classical.choose hactive) hact
  let w := Classical.choose w_exists
  let accepts : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w w (Classical.choose hactive)
    | some m' => val_w w m' < val_w w (Classical.choose hactive)
  by_cases hacc : accepts
  · simp [daStepByMan, daStep, hactive, hact, w_exists, w, accepts, hacc]
  · simp [daStepByMan, daStep, hactive, hact, w_exists, w, accepts, hacc]

/--
If two woman-side profiles make the same accept/reject decision for the chosen
proposal in a fixed active state, then the DA step is the same under both
profiles.
-/
theorem daStep_eq_of_chosen_accepts_iff
    (val_m : M → W → ℝ) (val_w₁ val_w₂ : W → M → ℝ) (s : DAState M W)
    (hactive : ∃ m, IsActiveMan val_m s m)
    (hiff :
      daStepChosenAccepts val_m val_w₁ s hactive ↔
        daStepChosenAccepts val_m val_w₂ s hactive) :
    daStep val_m val_w₁ s = daStep val_m val_w₂ s := by
  classical
  let m := Classical.choose hactive
  let hact : IsActiveMan val_m s m := Classical.choose_spec hactive
  let w_exists := exists_best_woman val_m s m hact
  let w := Classical.choose w_exists
  let accepts₁ : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w₁ w m
    | some m' => val_w₁ w m' < val_w₁ w m
  let accepts₂ : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w₂ w m
    | some m' => val_w₂ w m' < val_w₂ w m
  have hiff' : accepts₁ ↔ accepts₂ := by
    simpa [daStepChosenAccepts, daStepChosenMan, daStepChosenWoman, m, hact,
      w_exists, w, accepts₁, accepts₂] using hiff
  by_cases hacc₁ : accepts₁
  · have hacc₂ : accepts₂ := hiff'.1 hacc₁
    simp [daStep, hactive, m, w, accepts₁, accepts₂,
      hacc₁, hacc₂]
  · have hacc₂ : ¬ accepts₂ := fun h => hacc₁ (hiff'.2 h)
    simp [daStep, hactive, m, w, accepts₁, accepts₂,
      hacc₁, hacc₂]

set_option linter.unusedSimpArgs false

/-- If `daStep` accepts the chosen proposal, the chosen woman holds the proposer. -/
theorem daStep_w_match_chosen_of_accepts
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hactive : ∃ m, IsActiveMan val_m s m)
    (hacc : daStepChosenAccepts val_m val_w s hactive) :
    (daStep val_m val_w s).w_match (daStepChosenWoman val_m s hactive) =
      some (daStepChosenMan val_m s hactive) := by
  classical
  let m := Classical.choose hactive
  let hact : IsActiveMan val_m s m := Classical.choose_spec hactive
  let w_exists := exists_best_woman val_m s m hact
  let w := Classical.choose w_exists
  let accepts : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w w m
    | some m' => val_w w m' < val_w w m
  have hacc' : accepts := by
    simpa [daStepChosenAccepts, daStepChosenMan, daStepChosenWoman, m, hact,
      w_exists, w, accepts] using hacc
  simpa [daStepChosenMan, daStepChosenWoman, m, hact, w_exists, w] using
    (by
      simp [daStep, hactive, m, hact, w_exists, w, accepts, hacc'])

/--
In an active DA step, the proposal-history field is exactly the old proposal
history with the chosen proposal removed.  This field is independent of the
accept/reject branch.
-/
theorem daStep_m_proposals_eq_removeProposal_of_active
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hactive : ∃ m, IsActiveMan val_m s m) :
    (daStep val_m val_w s).m_proposals =
      removeProposal s
        (daStepChosenMan val_m s hactive)
        (daStepChosenWoman val_m s hactive) := by
  classical
  let m := Classical.choose hactive
  let hact : IsActiveMan val_m s m := Classical.choose_spec hactive
  let w_exists := exists_best_woman val_m s m hact
  let w := Classical.choose w_exists
  let accepts : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w w m
    | some m' => val_w w m' < val_w w m
  by_cases hacc : accepts
  · simp [daStep, daStepChosenMan, daStepChosenWoman, hactive,
      m, hact, w_exists, w, accepts, hacc]
  · simp [daStep, daStepChosenMan, daStepChosenWoman, hactive,
      m, hact, w_exists, w, accepts, hacc]

/--
In an active scheduled DA step, the proposal-history field removes exactly the
named proposer's chosen proposal.  This field is independent of the
accept/reject branch.
-/
theorem daStepByMan_m_proposals_eq_removeProposal_of_active
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (m : M) (hact : IsActiveMan val_m s m) :
    (daStepByMan val_m val_w s m).m_proposals =
      removeProposal s m (daStepByManChosenWoman val_m s m hact) := by
  classical
  let w_exists := exists_best_woman val_m s m hact
  let w := Classical.choose w_exists
  let accepts : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w w m
    | some m' => val_w w m' < val_w w m
  by_cases hacc : accepts
  · simp [daStepByMan, hact, daStepByManChosenWoman, w_exists, w, accepts, hacc]
  · simp [daStepByMan, hact, daStepByManChosenWoman, w_exists, w, accepts, hacc]

theorem daStepByMan_m_proposals_relabelMen_of_chosenWoman {M M' W : Type*}
    [Fintype M] [Fintype M'] [Fintype W]
    [DecidableEq M] [DecidableEq M'] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (e : M ≃ M') (s : DAState M W) (m' : M')
    (hact : IsActiveMan val_m s (e.symm m'))
    (hchosen :
      daStepByManChosenWoman (fun m' w => val_m (e.symm m') w)
          (DAState.relabelMen e s) m'
          ((IsActiveMan_relabelMen_iff val_m e s m').2 hact) =
        daStepByManChosenWoman val_m s (e.symm m') hact) :
    (daStepByMan (fun m' w => val_m (e.symm m') w)
        (fun w m' => val_w w (e.symm m')) (DAState.relabelMen e s) m').m_proposals =
      (DAState.relabelMen e (daStepByMan val_m val_w s (e.symm m'))).m_proposals := by
  classical
  have hactRel : IsActiveMan (fun m' w => val_m (e.symm m') w)
      (DAState.relabelMen e s) m' := (IsActiveMan_relabelMen_iff val_m e s m').2 hact
  funext x
  rw [daStepByMan_m_proposals_eq_removeProposal_of_active
    (fun m' w => val_m (e.symm m') w)
    (fun w m' => val_w w (e.symm m')) (DAState.relabelMen e s) m' hactRel]
  change removeProposal (DAState.relabelMen e s) m'
      (daStepByManChosenWoman (fun m' w => val_m (e.symm m') w)
        (DAState.relabelMen e s) m' hactRel) x =
    (daStepByMan val_m val_w s (e.symm m')).m_proposals (e.symm x)
  rw [daStepByMan_m_proposals_eq_removeProposal_of_active val_m val_w s (e.symm m') hact]
  rw [hchosen]
  exact removeProposal_relabelMen_apply e s m' x
    (daStepByManChosenWoman val_m s (e.symm m') hact)

/-- If the chosen proposal is accepted, the chosen man holds the chosen woman
after the DA step. -/
theorem daStep_m_match_chosen_of_accepts
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hactive : ∃ m, IsActiveMan val_m s m)
    (hacc : daStepChosenAccepts val_m val_w s hactive) :
    (daStep val_m val_w s).m_match (daStepChosenMan val_m s hactive) =
      some (daStepChosenWoman val_m s hactive) := by
  classical
  let m := Classical.choose hactive
  let hact : IsActiveMan val_m s m := Classical.choose_spec hactive
  let w_exists := exists_best_woman val_m s m hact
  let w := Classical.choose w_exists
  let accepts : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w w m
    | some m' => val_w w m' < val_w w m
  have hacc' : accepts := by
    simpa [daStepChosenAccepts, daStepChosenMan, daStepChosenWoman, m, hact,
      w_exists, w, accepts] using hacc
  simpa [daStepChosenMan, daStepChosenWoman, m, hact, w_exists, w] using
    (by
      simp [daStep, hactive, m, hact, w_exists, w, accepts, hacc'])

/-- If the chosen proposal is accepted, the woman-match field is the update
that assigns the chosen woman to the chosen man. -/
theorem daStep_w_match_eq_update_of_accepts
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hactive : ∃ m, IsActiveMan val_m s m)
    (hacc : daStepChosenAccepts val_m val_w s hactive) :
    (daStep val_m val_w s).w_match =
      Function.update s.w_match
        (daStepChosenWoman val_m s hactive)
        (some (daStepChosenMan val_m s hactive)) := by
  classical
  let m := Classical.choose hactive
  let hact : IsActiveMan val_m s m := Classical.choose_spec hactive
  let w_exists := exists_best_woman val_m s m hact
  let w := Classical.choose w_exists
  let accepts : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w w m
    | some m' => val_w w m' < val_w w m
  have hacc' : accepts := by
    simpa [daStepChosenAccepts, daStepChosenMan, daStepChosenWoman, m, hact,
      w_exists, w, accepts] using hacc
  simp [daStep, daStepChosenMan, daStepChosenWoman, hactive,
    m, hact, w_exists, w, accepts, hacc']

/-- If the chosen proposal is accepted, the man-match field is the source
implementation's corresponding update. -/
theorem daStep_m_match_eq_update_of_accepts
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hactive : ∃ m, IsActiveMan val_m s m)
    (hacc : daStepChosenAccepts val_m val_w s hactive) :
    (daStep val_m val_w s).m_match =
      fun m'' =>
        if m'' = daStepChosenMan val_m s hactive then
          some (daStepChosenWoman val_m s hactive)
        else if s.w_match (daStepChosenWoman val_m s hactive) = some m'' then
          none
        else
          s.m_match m'' := by
  classical
  let m := Classical.choose hactive
  let hact : IsActiveMan val_m s m := Classical.choose_spec hactive
  let w_exists := exists_best_woman val_m s m hact
  let w := Classical.choose w_exists
  let accepts : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w w m
    | some m' => val_w w m' < val_w w m
  have hacc' : accepts := by
    simpa [daStepChosenAccepts, daStepChosenMan, daStepChosenWoman, m, hact,
      w_exists, w, accepts] using hacc
  have hm_eq : m = daStepChosenMan val_m s hactive := by
    rfl
  have hw_eq : w = daStepChosenWoman val_m s hactive := by
    rfl
  funext m''
  have hraw :
      (daStep val_m val_w s).m_match m'' =
        (if m'' = m then some w
        else if s.w_match w = some m'' then none
        else s.m_match m'') := by
    simp [daStep, hactive, m, hact, w_exists, w, accepts, hacc']
  rw [hraw, hm_eq, hw_eq]

/-- If a scheduled proposal is accepted, the woman-match field is updated. -/
theorem daStepByMan_w_match_eq_update_of_accepts
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (m : M) (hact : IsActiveMan val_m s m)
    (hacc : daStepByManAccepts val_m val_w s m hact) :
    (daStepByMan val_m val_w s m).w_match =
      Function.update s.w_match
        (daStepByManChosenWoman val_m s m hact) (some m) := by
  classical
  let w_exists := exists_best_woman val_m s m hact
  let w := Classical.choose w_exists
  let accepts : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w w m
    | some m' => val_w w m' < val_w w m
  have hacc' : accepts := by
    simpa [daStepByManAccepts, daStepByManChosenWoman, w_exists, w, accepts]
      using hacc
  simp [daStepByMan, daStepByManChosenWoman, hact, w_exists, w, accepts, hacc']

/-- If a scheduled proposal is accepted, the man-match field is updated. -/
theorem daStepByMan_m_match_eq_update_of_accepts
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (m : M) (hact : IsActiveMan val_m s m)
    (hacc : daStepByManAccepts val_m val_w s m hact) :
    (daStepByMan val_m val_w s m).m_match =
      fun m'' =>
        if m'' = m then
          some (daStepByManChosenWoman val_m s m hact)
        else if s.w_match (daStepByManChosenWoman val_m s m hact) = some m'' then
          none
        else
          s.m_match m'' := by
  classical
  let w_exists := exists_best_woman val_m s m hact
  let w := Classical.choose w_exists
  let accepts : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w w m
    | some m' => val_w w m' < val_w w m
  have hacc' : accepts := by
    simpa [daStepByManAccepts, daStepByManChosenWoman, w_exists, w, accepts]
      using hacc
  have hw_eq : w = daStepByManChosenWoman val_m s m hact := by
    rfl
  funext m''
  have hraw :
      (daStepByMan val_m val_w s m).m_match m'' =
        (if m'' = m then some w
        else if s.w_match w = some m'' then none
        else s.m_match m'') := by
    simp [daStepByMan, hact, w_exists, w, accepts, hacc']
  rw [hraw, hw_eq]

/-- If the chosen proposal is rejected, the woman-match field is unchanged. -/
theorem daStep_w_match_eq_self_of_not_accepts
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hactive : ∃ m, IsActiveMan val_m s m)
    (hacc : ¬ daStepChosenAccepts val_m val_w s hactive) :
    (daStep val_m val_w s).w_match = s.w_match := by
  classical
  let m := Classical.choose hactive
  let hact : IsActiveMan val_m s m := Classical.choose_spec hactive
  let w_exists := exists_best_woman val_m s m hact
  let w := Classical.choose w_exists
  let accepts : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w w m
    | some m' => val_w w m' < val_w w m
  have hacc' : ¬ accepts := by
    simpa [daStepChosenAccepts, daStepChosenMan, daStepChosenWoman, m, hact,
      w_exists, w, accepts] using hacc
  simp [daStep, daStepChosenMan, daStepChosenWoman, hactive,
    m, hact, w_exists, w, accepts, hacc']

/-- If a scheduled proposal is rejected, the woman-match field is unchanged. -/
theorem daStepByMan_w_match_eq_self_of_not_accepts
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (m : M) (hact : IsActiveMan val_m s m)
    (hacc : ¬ daStepByManAccepts val_m val_w s m hact) :
    (daStepByMan val_m val_w s m).w_match = s.w_match := by
  classical
  let w_exists := exists_best_woman val_m s m hact
  let w := Classical.choose w_exists
  let accepts : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w w m
    | some m' => val_w w m' < val_w w m
  have hacc' : ¬ accepts := by
    simpa [daStepByManAccepts, daStepByManChosenWoman, w_exists, w, accepts]
      using hacc
  simp [daStepByMan, daStepByManChosenWoman, hact, w_exists, w, accepts, hacc']

theorem daStepByMan_w_match_relabelMen_of_chosenWoman {M M' W : Type*}
    [Fintype M] [Fintype M'] [Fintype W]
    [DecidableEq M] [DecidableEq M'] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (e : M ≃ M') (s : DAState M W) (m' : M')
    (hact : IsActiveMan val_m s (e.symm m'))
    (hchosen :
      daStepByManChosenWoman (fun m' w => val_m (e.symm m') w)
          (DAState.relabelMen e s) m'
          ((IsActiveMan_relabelMen_iff val_m e s m').2 hact) =
        daStepByManChosenWoman val_m s (e.symm m') hact) :
    (daStepByMan (fun m' w => val_m (e.symm m') w)
        (fun w m' => val_w w (e.symm m')) (DAState.relabelMen e s) m').w_match =
      (DAState.relabelMen e (daStepByMan val_m val_w s (e.symm m'))).w_match := by
  classical
  have hactRel : IsActiveMan (fun m' w => val_m (e.symm m') w)
      (DAState.relabelMen e s) m' := (IsActiveMan_relabelMen_iff val_m e s m').2 hact
  have hchosenRel :
      daStepByManChosenWoman (fun m' w => val_m (e.symm m') w)
        (DAState.relabelMen e s) m' hactRel =
      daStepByManChosenWoman val_m s (e.symm m') hact := by
    simpa [hactRel] using hchosen
  have hacciff :
      daStepByManAccepts (fun m' w => val_m (e.symm m') w)
          (fun w m' => val_w w (e.symm m'))
          (DAState.relabelMen e s) m' hactRel ↔
        daStepByManAccepts val_m val_w s (e.symm m') hact := by
    rw [daStepByManAccepts_eq_daWomanAcceptsProposal
      (fun m' w => val_m (e.symm m') w)
      (fun w m' => val_w w (e.symm m')) (DAState.relabelMen e s) m' hactRel]
    rw [daStepByManAccepts_eq_daWomanAcceptsProposal val_m val_w s (e.symm m') hact]
    rw [hchosenRel]
    exact daWomanAcceptsProposal_relabelMen_iff val_w e s m'
      (daStepByManChosenWoman val_m s (e.symm m') hact)
  by_cases hacc : daStepByManAccepts val_m val_w s (e.symm m') hact
  · have haccRel :
        daStepByManAccepts (fun m' w => val_m (e.symm m') w)
          (fun w m' => val_w w (e.symm m'))
          (DAState.relabelMen e s) m' hactRel := hacciff.2 hacc
    rw [daStepByMan_w_match_eq_update_of_accepts
      (fun m' w => val_m (e.symm m') w)
      (fun w m' => val_w w (e.symm m'))
      (DAState.relabelMen e s) m' hactRel haccRel]
    funext y
    change Function.update (DAState.relabelMen e s).w_match
        (daStepByManChosenWoman (fun m' w => val_m (e.symm m') w)
          (DAState.relabelMen e s) m' hactRel) (some m') y =
      Option.map e ((daStepByMan val_m val_w s (e.symm m')).w_match y)
    rw [daStepByMan_w_match_eq_update_of_accepts val_m val_w s (e.symm m') hact hacc]
    by_cases hy : y = daStepByManChosenWoman val_m s (e.symm m') hact
    · subst y
      simp [Function.update, hchosenRel]
    · have hyRel :
        daStepByManChosenWoman (fun m' w => val_m (e.symm m') w)
          (DAState.relabelMen e s) m' hactRel ≠ y := by
          intro h
          apply hy
          rw [← hchosenRel]
          exact h.symm
      have hyRelSymm :
        y ≠ daStepByManChosenWoman (fun m' w => val_m (e.symm m') w)
          (DAState.relabelMen e s) m' hactRel := by
          intro h
          exact hyRel h.symm
      simp [Function.update, hy, hyRelSymm]
  · have haccRel :
        ¬ daStepByManAccepts (fun m' w => val_m (e.symm m') w)
          (fun w m' => val_w w (e.symm m'))
          (DAState.relabelMen e s) m' hactRel := fun h => hacc (hacciff.1 h)
    rw [daStepByMan_w_match_eq_self_of_not_accepts
      (fun m' w => val_m (e.symm m') w)
      (fun w m' => val_w w (e.symm m'))
      (DAState.relabelMen e s) m' hactRel haccRel]
    funext y
    change (DAState.relabelMen e s).w_match y =
      Option.map e ((daStepByMan val_m val_w s (e.symm m')).w_match y)
    rw [daStepByMan_w_match_eq_self_of_not_accepts val_m val_w s (e.symm m') hact hacc]
    rfl

/-- If the chosen proposal is rejected, the man-match field is unchanged. -/
theorem daStep_m_match_eq_self_of_not_accepts
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hactive : ∃ m, IsActiveMan val_m s m)
    (hacc : ¬ daStepChosenAccepts val_m val_w s hactive) :
    (daStep val_m val_w s).m_match = s.m_match := by
  classical
  let m := Classical.choose hactive
  let hact : IsActiveMan val_m s m := Classical.choose_spec hactive
  let w_exists := exists_best_woman val_m s m hact
  let w := Classical.choose w_exists
  let accepts : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w w m
    | some m' => val_w w m' < val_w w m
  have hacc' : ¬ accepts := by
    simpa [daStepChosenAccepts, daStepChosenMan, daStepChosenWoman, m, hact,
      w_exists, w, accepts] using hacc
  simp [daStep, daStepChosenMan, daStepChosenWoman, hactive,
    m, hact, w_exists, w, accepts, hacc']

/-- If a scheduled proposal is rejected, the man-match field is unchanged. -/
theorem daStepByMan_m_match_eq_self_of_not_accepts
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (m : M) (hact : IsActiveMan val_m s m)
    (hacc : ¬ daStepByManAccepts val_m val_w s m hact) :
    (daStepByMan val_m val_w s m).m_match = s.m_match := by
  classical
  let w_exists := exists_best_woman val_m s m hact
  let w := Classical.choose w_exists
  let accepts : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w w m
    | some m' => val_w w m' < val_w w m
  have hacc' : ¬ accepts := by
    simpa [daStepByManAccepts, daStepByManChosenWoman, w_exists, w, accepts]
      using hacc
  simp [daStepByMan, daStepByManChosenWoman, hact, w_exists, w, accepts, hacc']

theorem daStepByMan_m_match_relabelMen_of_chosenWoman {M M' W : Type*}
    [Fintype M] [Fintype M'] [Fintype W]
    [DecidableEq M] [DecidableEq M'] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (e : M ≃ M') (s : DAState M W) (m' : M')
    (hact : IsActiveMan val_m s (e.symm m'))
    (hchosen :
      daStepByManChosenWoman (fun m' w => val_m (e.symm m') w)
          (DAState.relabelMen e s) m'
          ((IsActiveMan_relabelMen_iff val_m e s m').2 hact) =
        daStepByManChosenWoman val_m s (e.symm m') hact) :
    (daStepByMan (fun m' w => val_m (e.symm m') w)
        (fun w m' => val_w w (e.symm m')) (DAState.relabelMen e s) m').m_match =
      (DAState.relabelMen e (daStepByMan val_m val_w s (e.symm m'))).m_match := by
  classical
  have hactRel : IsActiveMan (fun m' w => val_m (e.symm m') w)
      (DAState.relabelMen e s) m' := (IsActiveMan_relabelMen_iff val_m e s m').2 hact
  have hchosenRel :
      daStepByManChosenWoman (fun m' w => val_m (e.symm m') w)
        (DAState.relabelMen e s) m' hactRel =
      daStepByManChosenWoman val_m s (e.symm m') hact := by
    simpa [hactRel] using hchosen
  have hacciff :
      daStepByManAccepts (fun m' w => val_m (e.symm m') w)
          (fun w m' => val_w w (e.symm m'))
          (DAState.relabelMen e s) m' hactRel ↔
        daStepByManAccepts val_m val_w s (e.symm m') hact := by
    rw [daStepByManAccepts_eq_daWomanAcceptsProposal
      (fun m' w => val_m (e.symm m') w)
      (fun w m' => val_w w (e.symm m')) (DAState.relabelMen e s) m' hactRel]
    rw [daStepByManAccepts_eq_daWomanAcceptsProposal val_m val_w s (e.symm m') hact]
    rw [hchosenRel]
    exact daWomanAcceptsProposal_relabelMen_iff val_w e s m'
      (daStepByManChosenWoman val_m s (e.symm m') hact)
  by_cases hacc : daStepByManAccepts val_m val_w s (e.symm m') hact
  · have haccRel :
        daStepByManAccepts (fun m' w => val_m (e.symm m') w)
          (fun w m' => val_w w (e.symm m'))
          (DAState.relabelMen e s) m' hactRel := hacciff.2 hacc
    rw [daStepByMan_m_match_eq_update_of_accepts
      (fun m' w => val_m (e.symm m') w)
      (fun w m' => val_w w (e.symm m'))
      (DAState.relabelMen e s) m' hactRel haccRel]
    rw [hchosenRel]
    funext x
    change (if x = m' then
        some (daStepByManChosenWoman val_m s (e.symm m') hact)
      else if (DAState.relabelMen e s).w_match
          (daStepByManChosenWoman val_m s (e.symm m') hact) = some x then none
      else (DAState.relabelMen e s).m_match x) =
      (daStepByMan val_m val_w s (e.symm m')).m_match (e.symm x)
    rw [daStepByMan_m_match_eq_update_of_accepts val_m val_w s (e.symm m') hact hacc]
    by_cases hx : x = m'
    · subst x
      simp
    · have hxSymm : e.symm x ≠ e.symm m' := by
        intro h
        exact hx (e.symm.injective h)
      let w := daStepByManChosenWoman val_m s (e.symm m') hact
      have hwRelIff :
          (DAState.relabelMen e s).w_match w = some x ↔
            s.w_match w = some (e.symm x) := by
        simpa using (DAState.relabelMen_w_match_apply e s w (e.symm x))
      by_cases hcur : s.w_match w = some (e.symm x)
      · have hcurRel : (DAState.relabelMen e s).w_match w = some x := hwRelIff.2 hcur
        simp [hx, hxSymm, w, hcur, hcurRel]
      · have hcurRelMap : ¬ ∃ a, s.w_match w = some a ∧ e a = x := by
          rintro ⟨a, ha, he⟩
          apply hcur
          have haeq : a = e.symm x := by
            rw [← he]
            simp
          simpa [haeq] using ha
        simp [hx, hxSymm, w, hcur, hcurRelMap, DAState.relabelMen]
  · have haccRel :
        ¬ daStepByManAccepts (fun m' w => val_m (e.symm m') w)
          (fun w m' => val_w w (e.symm m'))
          (DAState.relabelMen e s) m' hactRel := fun h => hacc (hacciff.1 h)
    rw [daStepByMan_m_match_eq_self_of_not_accepts
      (fun m' w => val_m (e.symm m') w)
      (fun w m' => val_w w (e.symm m'))
      (DAState.relabelMen e s) m' hactRel haccRel]
    funext x
    change (DAState.relabelMen e s).m_match x =
      (daStepByMan val_m val_w s (e.symm m')).m_match (e.symm x)
    rw [daStepByMan_m_match_eq_self_of_not_accepts val_m val_w s (e.symm m') hact hacc]
    rfl

theorem daStepByMan_relabelMen_of_chosenWoman {M M' W : Type*}
    [Fintype M] [Fintype M'] [Fintype W]
    [DecidableEq M] [DecidableEq M'] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (e : M ≃ M') (s : DAState M W) (m' : M')
    (hact : IsActiveMan val_m s (e.symm m'))
    (hchosen :
      daStepByManChosenWoman (fun m' w => val_m (e.symm m') w)
          (DAState.relabelMen e s) m'
          ((IsActiveMan_relabelMen_iff val_m e s m').2 hact) =
        daStepByManChosenWoman val_m s (e.symm m') hact) :
    daStepByMan (fun m' w => val_m (e.symm m') w)
        (fun w m' => val_w w (e.symm m')) (DAState.relabelMen e s) m' =
      DAState.relabelMen e (daStepByMan val_m val_w s (e.symm m')) := by
  apply DAState.ext
  · intro x
    exact congrFun
      (daStepByMan_m_match_relabelMen_of_chosenWoman
        val_m val_w e s m' hact hchosen) x
  · intro w
    exact congrFun
      (daStepByMan_w_match_relabelMen_of_chosenWoman
        val_m val_w e s m' hact hchosen) w
  · intro x
    exact congrFun
      (daStepByMan_m_proposals_relabelMen_of_chosenWoman
        val_m val_w e s m' hact hchosen) x

set_option linter.unusedSimpArgs true

-- DA algorithm fold
noncomputable def deferredAcceptanceState (val_m : M → W → ℝ) (val_w : W → M → ℝ) : DAState M W :=
  let max_steps := Fintype.card M * Fintype.card W
  (List.range max_steps).foldl (fun s _ => daStep val_m val_w s) (initialDAState M W)

/--
The DA state after exactly `steps` iterations of the folded implementation.
This exposes the run prefix used by trace arguments while staying definitionally
aligned with `deferredAcceptanceState` at the fixed finite horizon.
-/
noncomputable def daStateAfterSteps
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (steps : ℕ) : DAState M W :=
  (List.range steps).foldl (fun s _ => daStep val_m val_w s) (initialDAState M W)

/-- The DA state after `steps` iterations starting from an arbitrary state. -/
noncomputable def daStateAfterStepsFrom
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) (steps : ℕ) : DAState M W :=
  (List.range steps).foldl (fun s _ => daStep val_m val_w s) start

@[simp] theorem daStateAfterStepsFrom_zero
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) :
    daStateAfterStepsFrom val_m val_w start 0 = start := by
  simp [daStateAfterStepsFrom]

@[simp] theorem daStateAfterStepsFrom_succ
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) (steps : ℕ) :
    daStateAfterStepsFrom val_m val_w start (steps + 1) =
      daStep val_m val_w (daStateAfterStepsFrom val_m val_w start steps) := by
  unfold daStateAfterStepsFrom
  rw [List.range_succ, List.foldl_append]
  simp

@[simp] theorem daStateAfterStepsFrom_succ_start
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) (steps : ℕ) :
    daStateAfterStepsFrom val_m val_w start (steps + 1) =
      daStateAfterStepsFrom val_m val_w
        (daStep val_m val_w start) steps := by
  induction steps with
  | zero =>
      simp
  | succ steps ih =>
      rw [daStateAfterStepsFrom_succ, ih, daStateAfterStepsFrom_succ]

theorem daStateAfterSteps_eq_daStateAfterStepsFrom_initial
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (steps : ℕ) :
    daStateAfterSteps val_m val_w steps =
      daStateAfterStepsFrom val_m val_w (initialDAState M W) steps := by
  rfl

@[simp] theorem daStateAfterSteps_zero
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    daStateAfterSteps val_m val_w 0 = initialDAState M W := by
  simp [daStateAfterSteps]

@[simp] theorem daStateAfterSteps_succ
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (steps : ℕ) :
    daStateAfterSteps val_m val_w (steps + 1) =
      daStep val_m val_w (daStateAfterSteps val_m val_w steps) := by
  unfold daStateAfterSteps
  rw [List.range_succ, List.foldl_append]
  simp

theorem deferredAcceptanceState_eq_daStateAfterSteps
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    deferredAcceptanceState val_m val_w =
      daStateAfterSteps val_m val_w (Fintype.card M * Fintype.card W) := by
  rfl

/--
If two woman-side profiles make the same accept/reject decision at every
state, then each folded DA prefix is identical under the two profiles.
-/
theorem daStateAfterSteps_eq_of_woman_acceptance_iff
    (val_m : M → W → ℝ) (val_w₁ val_w₂ : W → M → ℝ)
    (haccepts : ∀ s m w,
      daWomanAcceptsProposal val_w₁ s m w ↔
        daWomanAcceptsProposal val_w₂ s m w) :
    ∀ steps : ℕ,
      daStateAfterSteps val_m val_w₁ steps =
        daStateAfterSteps val_m val_w₂ steps := by
  intro steps
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [daStateAfterSteps_succ, daStateAfterSteps_succ, ih]
      by_cases hactive : ∃ m, IsActiveMan val_m
          (daStateAfterSteps val_m val_w₂ steps) m
      · apply daStep_eq_of_chosen_accepts_iff val_m val_w₁ val_w₂ _ hactive
        simpa [daStepChosenAccepts] using
          haccepts (daStateAfterSteps val_m val_w₂ steps)
            (daStepChosenMan val_m
              (daStateAfterSteps val_m val_w₂ steps) hactive)
            (daStepChosenWoman val_m
              (daStateAfterSteps val_m val_w₂ steps) hactive)
      · simp [daStep, hactive]

/--
The folded deferred-acceptance outcome is invariant under a woman-side profile
replacement that preserves every statewise accept/reject decision.
-/
theorem deferredAcceptanceState_eq_of_woman_acceptance_iff
    (val_m : M → W → ℝ) (val_w₁ val_w₂ : W → M → ℝ)
    (haccepts : ∀ s m w,
      daWomanAcceptsProposal val_w₁ s m w ↔
        daWomanAcceptsProposal val_w₂ s m w) :
    deferredAcceptanceState val_m val_w₁ =
      deferredAcceptanceState val_m val_w₂ := by
  rw [deferredAcceptanceState_eq_daStateAfterSteps,
    deferredAcceptanceState_eq_daStateAfterSteps]
  exact daStateAfterSteps_eq_of_woman_acceptance_iff val_m val_w₁ val_w₂
    haccepts (Fintype.card M * Fintype.card W)

noncomputable def deferredAcceptance (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Assignment M W where
  m_match := (deferredAcceptanceState val_m val_w).m_match
  w_match := (deferredAcceptanceState val_m val_w).w_match
  consistent_m := (deferredAcceptanceState val_m val_w).consistent

/-! ### Local Invariants -/

/-- Number of proposal opportunities that have not yet been used. -/
def remainingProposalCount (s : DAState M W) : ℕ :=
  ∑ m : M, (s.m_proposals m).card

/-- Initially, every man can still propose to every woman. -/
lemma remainingProposalCount_initial :
    remainingProposalCount (initialDAState M W) = Fintype.card M * Fintype.card W := by
  simp [remainingProposalCount, initialDAState, Finset.sum_const]

lemma remainingProposalCount_le_card_mul (s : DAState M W) :
    remainingProposalCount s ≤ Fintype.card M * Fintype.card W := by
  classical
  unfold remainingProposalCount
  calc
    (∑ m : M, (s.m_proposals m).card) ≤
        ∑ _m : M, Fintype.card W := by
        exact Finset.sum_le_sum fun m _hm =>
          Finset.card_le_univ (s.m_proposals m)
    _ = Fintype.card M * Fintype.card W := by
        simp [Finset.sum_const]

/-- Any active state has at least one remaining proposal opportunity. -/
lemma remainingProposalCount_pos_of_active
    (val_m : M → W → ℝ) (s : DAState M W)
    (hactive : ∃ m, IsActiveMan val_m s m) :
    0 < remainingProposalCount s := by
  rcases hactive with ⟨m, _hm_unmatched, w, hw_mem, _hw_nonneg⟩
  have hcard_pos : 0 < (s.m_proposals m).card :=
    Finset.card_pos.mpr ⟨w, hw_mem⟩
  have hle : (s.m_proposals m).card ≤ remainingProposalCount s := by
    unfold remainingProposalCount
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset M))
      (f := fun m => (s.m_proposals m).card)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
  exact lt_of_lt_of_le hcard_pos hle

/-- Removing an available proposal lowers the remaining proposal count by one. -/
lemma remainingProposalCount_removeProposal_add_one
    (s : DAState M W) {m : M} {w : W}
    (hw : w ∈ s.m_proposals m) :
    (∑ m' : M, ((removeProposal s m w) m').card) + 1 =
      remainingProposalCount s := by
  classical
  let oldCount : M → ℕ := fun m' => (s.m_proposals m').card
  let newCount : M → ℕ := fun m' => ((removeProposal s m w) m').card
  have hnew_at_m : newCount m + 1 = oldCount m := by
    simpa [newCount, oldCount, removeProposal, Finset.sdiff_singleton_eq_erase] using
      (Finset.card_erase_add_one (s := s.m_proposals m) (a := w) hw)
  have hnew_off :
      (∑ x ∈ (Finset.univ : Finset M).erase m, newCount x) =
        ∑ x ∈ (Finset.univ : Finset M).erase m, oldCount x := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hx_ne : x ≠ m := (Finset.mem_erase.mp hx).1
    simp [newCount, oldCount, removeProposal, hx_ne]
  have hnew_sum := Finset.sum_erase_add
    (s := (Finset.univ : Finset M)) (f := newCount) (a := m) (Finset.mem_univ m)
  have hold_sum := Finset.sum_erase_add
    (s := (Finset.univ : Finset M)) (f := oldCount) (a := m) (Finset.mem_univ m)
  have hnew_total : (∑ m' : M, newCount m') + 1 = ∑ m' : M, oldCount m' := by
    rw [← hnew_sum, ← hold_sum, hnew_off]
    linarith
  simpa [remainingProposalCount, oldCount, newCount] using hnew_total

/-- If no man is active, a DA step leaves the state unchanged. -/
lemma daStep_eq_self_of_not_active
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hnot : ¬ ∃ m, IsActiveMan val_m s m) :
    daStep val_m val_w s = s := by
  simp [daStep, hnot]

theorem daStateAfterSteps_eq_self_add_of_not_active
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (steps extra : ℕ)
    (hnot : ¬ ∃ m, IsActiveMan val_m (daStateAfterSteps val_m val_w steps) m) :
    daStateAfterSteps val_m val_w (steps + extra) =
      daStateAfterSteps val_m val_w steps := by
  induction extra with
  | zero =>
      simp
  | succ extra ih =>
      rw [Nat.add_succ, daStateAfterSteps_succ, ih,
        daStep_eq_self_of_not_active val_m val_w
          (daStateAfterSteps val_m val_w steps) hnot]

theorem daStateAfterStepsFrom_eq_self_add_of_not_active
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) (steps extra : ℕ)
    (hnot : ¬ ∃ m, IsActiveMan val_m
      (daStateAfterStepsFrom val_m val_w start steps) m) :
    daStateAfterStepsFrom val_m val_w start (steps + extra) =
      daStateAfterStepsFrom val_m val_w start steps := by
  induction extra with
  | zero =>
      simp
  | succ extra ih =>
      rw [Nat.add_succ, daStateAfterStepsFrom_succ, ih,
        daStep_eq_self_of_not_active val_m val_w
          (daStateAfterStepsFrom val_m val_w start steps) hnot]

/--
The schedule of proposers selected by the canonical folded DA implementation
from an arbitrary prefix.  If the current prefix is inactive, the schedule
stops early because all later folded DA steps are identities.
-/
noncomputable def daChosenManScheduleFrom
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) : ℕ → List M
  | 0 => []
  | steps + 1 =>
      by
      classical
      exact
      if hactive : ∃ m, IsActiveMan val_m start m then
        daStepChosenMan val_m start hactive ::
          daChosenManScheduleFrom val_m val_w
            (daStep val_m val_w start) steps
      else
        []

/--
Running the chosen-proposer schedule from a prefix reproduces the canonical
folded DA prefix from the same state.
-/
theorem daStateAfterSchedule_daChosenManScheduleFrom_eq_daStateAfterStepsFrom
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) (steps : ℕ) :
    daStateAfterSchedule val_m val_w start
        (daChosenManScheduleFrom val_m val_w start steps) =
      daStateAfterStepsFrom val_m val_w start steps := by
  induction steps generalizing start with
  | zero =>
      simp [daChosenManScheduleFrom]
  | succ steps ih =>
      by_cases hactive : ∃ m, IsActiveMan val_m start m
      · rw [daStateAfterStepsFrom_succ_start]
        simpa [daChosenManScheduleFrom, hactive, daStateAfterSchedule_cons,
          daStepByMan_chosen_eq_daStep val_m val_w start hactive]
          using ih (daStep val_m val_w start)
      · have hself :
          daStateAfterStepsFrom val_m val_w start (steps + 1) = start := by
            simpa using
              daStateAfterStepsFrom_eq_self_add_of_not_active
                val_m val_w start 0 (steps + 1)
                (by simpa using hactive)
        simpa [daChosenManScheduleFrom, hactive] using hself.symm

theorem deferredAcceptanceState_eq_daStateAfterSteps_of_not_active
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (steps : ℕ)
    (hle : steps ≤ Fintype.card M * Fintype.card W)
    (hnot : ¬ ∃ m, IsActiveMan val_m (daStateAfterSteps val_m val_w steps) m) :
    deferredAcceptanceState val_m val_w =
      daStateAfterSteps val_m val_w steps := by
  have hadd :
      steps + (Fintype.card M * Fintype.card W - steps) =
        Fintype.card M * Fintype.card W := Nat.add_sub_of_le hle
  rw [deferredAcceptanceState_eq_daStateAfterSteps, ← hadd]
  exact daStateAfterSteps_eq_self_add_of_not_active val_m val_w steps
    (Fintype.card M * Fintype.card W - steps) hnot

/-- A finite Boolean trace has a final true time immediately before false. -/
lemma exists_last_true_before_false_nat
    {P : ℕ → Prop} {N : ℕ} (h0 : P 0) (hN : ¬ P N) :
    ∃ t, t < N ∧ P t ∧ ¬ P (t + 1) := by
  classical
  let Q : ℕ → Prop := fun n => ¬ P n
  have hQ : ∃ n, Q n := ⟨N, hN⟩
  let n := Nat.find hQ
  have hnQ : Q n := Nat.find_spec hQ
  have hnpos : 0 < n := by
    by_contra hnot
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hnot
    have hnQ0 : ¬ P 0 := by
      simpa [Q, hn0] using hnQ
    exact hnQ0 h0
  refine ⟨n - 1, ?_, ?_, ?_⟩
  · have hnleN : n ≤ N := Nat.find_min' hQ hN
    exact lt_of_lt_of_le (Nat.sub_one_lt hnpos.ne') hnleN
  · by_contra hnotP
    have hnle : n ≤ n - 1 := Nat.find_min' hQ hnotP
    exact (not_lt_of_ge hnle) (Nat.sub_one_lt hnpos.ne')
  · have hs : n - 1 + 1 = n :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt hnpos)
    simpa [Q, hs] using hnQ

/-- A DA step can only remove proposal opportunities; it never adds one. -/
theorem m_proposals_daStep_subset
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (m0 : M) :
    (daStep val_m val_w s).m_proposals m0 ⊆ s.m_proposals m0 := by
  classical
  intro w0 hw0
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · unfold daStep at hw0
    rw [dif_pos hactive] at hw0
    let m := Classical.choose hactive
    have hact : IsActiveMan val_m s m := by
      simpa [m] using Classical.choose_spec hactive
    let w_exists := exists_best_woman val_m s m hact
    let w := Classical.choose w_exists
    let accepts : Prop :=
      match s.w_match w with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m
    by_cases hacc : accepts
    · have hmemRemove : w0 ∈ removeProposal s m w m0 := by
        simpa [m, hact, w_exists, w, accepts, hacc] using hw0
      exact ((mem_removeProposal_iff s m m0 w w0).1 hmemRemove).1
    · have hmemRemove : w0 ∈ removeProposal s m w m0 := by
        simpa [m, hact, w_exists, w, accepts, hacc] using hw0
      exact ((mem_removeProposal_iff s m m0 w w0).1 hmemRemove).1
  · simpa [daStep, hactive] using hw0

/-- Proposal opportunities are monotone decreasing along DA run prefixes. -/
theorem m_proposals_daStateAfterSteps_subset_add
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps extra : ℕ) (m : M) :
    (daStateAfterSteps val_m val_w (steps + extra)).m_proposals m ⊆
      (daStateAfterSteps val_m val_w steps).m_proposals m := by
  induction extra with
  | zero =>
      intro w hw
      simpa using hw
  | succ extra ih =>
      intro w hw
      have hstep :
          w ∈ (daStateAfterSteps val_m val_w (steps + extra)).m_proposals m := by
        exact m_proposals_daStep_subset val_m val_w
          (daStateAfterSteps val_m val_w (steps + extra)) m
          (by
            simpa only [Nat.add_succ, daStateAfterSteps_succ] using hw)
      exact ih hstep

/-- Later DA run prefixes have proposal sets contained in earlier prefixes. -/
theorem m_proposals_daStateAfterSteps_subset_of_le
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {steps later : ℕ} (hle : steps ≤ later) (m : M) :
    (daStateAfterSteps val_m val_w later).m_proposals m ⊆
      (daStateAfterSteps val_m val_w steps).m_proposals m := by
  have hadd : steps + (later - steps) = later := Nat.add_sub_of_le hle
  simpa [hadd] using
    m_proposals_daStateAfterSteps_subset_add val_m val_w steps (later - steps) m

/-- Proposal opportunities are monotone decreasing along arbitrary-start DA prefixes. -/
theorem m_proposals_daStateAfterStepsFrom_subset_add
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) (steps extra : ℕ) (m : M) :
    (daStateAfterStepsFrom val_m val_w start (steps + extra)).m_proposals m ⊆
      (daStateAfterStepsFrom val_m val_w start steps).m_proposals m := by
  induction extra with
  | zero =>
      intro w hw
      simpa using hw
  | succ extra ih =>
      intro w hw
      have hstep :
          w ∈ (daStateAfterStepsFrom val_m val_w start
              (steps + extra)).m_proposals m := by
        exact m_proposals_daStep_subset val_m val_w
          (daStateAfterStepsFrom val_m val_w start (steps + extra)) m
          (by
            simpa only [Nat.add_succ, daStateAfterStepsFrom_succ] using hw)
      exact ih hstep

/-- Later arbitrary-start DA prefixes have proposal sets contained in earlier prefixes. -/
theorem m_proposals_daStateAfterStepsFrom_subset_of_le
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) {steps later : ℕ} (hle : steps ≤ later) (m : M) :
    (daStateAfterStepsFrom val_m val_w start later).m_proposals m ⊆
      (daStateAfterStepsFrom val_m val_w start steps).m_proposals m := by
  have hadd : steps + (later - steps) = later := Nat.add_sub_of_le hle
  simpa [hadd] using
    m_proposals_daStateAfterStepsFrom_subset_add
      val_m val_w start steps (later - steps) m

/-- If a proposal opportunity is gone at a prefix, it remains gone at later prefixes. -/
theorem not_mem_daStateAfterSteps_of_not_mem_of_le
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {steps later : ℕ} (hle : steps ≤ later) {m : M} {w : W}
    (hnot : w ∉ (daStateAfterSteps val_m val_w steps).m_proposals m) :
    w ∉ (daStateAfterSteps val_m val_w later).m_proposals m := by
  intro hmem
  exact hnot
    (m_proposals_daStateAfterSteps_subset_of_le val_m val_w hle m hmem)

/-- If a proposal opportunity is gone at an arbitrary-start prefix, it remains gone later. -/
theorem not_mem_daStateAfterStepsFrom_of_not_mem_of_le
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) {steps later : ℕ} (hle : steps ≤ later)
    {m : M} {w : W}
    (hnot : w ∉ (daStateAfterStepsFrom val_m val_w start steps).m_proposals m) :
    w ∉ (daStateAfterStepsFrom val_m val_w start later).m_proposals m := by
  intro hmem
  exact hnot
    (m_proposals_daStateAfterStepsFrom_subset_of_le
      val_m val_w start hle m hmem)

/-- The final DA state has no more proposal opportunities than any earlier prefix. -/
theorem m_proposals_deferredAcceptanceState_subset_after_steps
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : ℕ) (hle : steps ≤ Fintype.card M * Fintype.card W) (m : M) :
    (deferredAcceptanceState val_m val_w).m_proposals m ⊆
      (daStateAfterSteps val_m val_w steps).m_proposals m := by
  have hsubset :=
    m_proposals_daStateAfterSteps_subset_of_le val_m val_w hle m
  simpa [deferredAcceptanceState_eq_daStateAfterSteps] using hsubset

/-- If a proposal opportunity is gone at a prefix, it is gone in the final DA state. -/
theorem not_mem_deferredAcceptanceState_of_not_mem_after_steps
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : ℕ) (hle : steps ≤ Fintype.card M * Fintype.card W)
    {m : M} {w : W}
    (hnot : w ∉ (daStateAfterSteps val_m val_w steps).m_proposals m) :
    w ∉ (deferredAcceptanceState val_m val_w).m_proposals m := by
  intro hmem
  exact hnot
    (m_proposals_deferredAcceptanceState_subset_after_steps val_m val_w
      steps hle m hmem)

/--
If a specific proposal opportunity disappears in one DA step, then that man was
the active proposer and that woman was his best remaining acceptable option.
-/
theorem proposal_removed_at_daStep
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    {m : M} {w : W}
    (hmem : w ∈ s.m_proposals m)
    (hnot : w ∉ (daStep val_m val_w s).m_proposals m) :
    IsActiveMan val_m s m ∧ BestRemainingWoman val_m s m w := by
  classical
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · unfold daStep at hnot
    rw [dif_pos hactive] at hnot
    let m0 := Classical.choose hactive
    have hact : IsActiveMan val_m s m0 := by
      simpa [m0] using Classical.choose_spec hactive
    let w_exists := exists_best_woman val_m s m0 hact
    let w0 := Classical.choose w_exists
    have hwbest : BestRemainingWoman val_m s m0 w0 := by
      simpa [w0, w_exists] using Classical.choose_spec w_exists
    let accepts : Prop :=
      match s.w_match w0 with
      | none => 0 ≤ val_w w0 m0
      | some m' => val_w w0 m' < val_w w0 m0
    by_cases hacc : accepts
    · have hnotRemove : w ∉ removeProposal s m0 w0 m := by
        simpa [m0, hact, w_exists, w0, accepts, hacc] using hnot
      rcases not_mem_of_not_mem_removeProposal s hnotRemove with hnotOld | ⟨hm, hw⟩
      · exact False.elim (hnotOld hmem)
      · subst m
        subst w
        exact ⟨hact, hwbest⟩
    · have hnotRemove : w ∉ removeProposal s m0 w0 m := by
        simpa [m0, hact, w_exists, w0, accepts, hacc] using hnot
      rcases not_mem_of_not_mem_removeProposal s hnotRemove with hnotOld | ⟨hm, hw⟩
      · exact False.elim (hnotOld hmem)
      · subst m
        subst w
        exact ⟨hact, hwbest⟩
  · have hsame : daStep val_m val_w s = s :=
      daStep_eq_self_of_not_active val_m val_w s hactive
    exact False.elim (hnot (by simpa [hsame] using hmem))

/-- Run-prefix version of `proposal_removed_at_daStep`. -/
theorem proposal_removed_at_daStateAfterSteps_succ
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : ℕ) {m : M} {w : W}
    (hmem : w ∈ (daStateAfterSteps val_m val_w steps).m_proposals m)
    (hnot :
      w ∉ (daStateAfterSteps val_m val_w (steps + 1)).m_proposals m) :
    IsActiveMan val_m (daStateAfterSteps val_m val_w steps) m ∧
      BestRemainingWoman val_m (daStateAfterSteps val_m val_w steps) m w := by
  exact proposal_removed_at_daStep val_m val_w
    (daStateAfterSteps val_m val_w steps) hmem
    (by simpa [daStateAfterSteps_succ] using hnot)

/--
Once `m` has already used the proposal opportunity to `w` and is not currently
matched to `w`, one DA step cannot rematch `m` to `w`.
-/
theorem m_match_ne_of_not_mem_proposal_daStep
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    {m : M} {w : W}
    (hnot : w ∉ s.m_proposals m)
    (hne : s.m_match m ≠ some w) :
    (daStep val_m val_w s).m_match m ≠ some w := by
  classical
  intro hafter
  by_cases hactive : ∃ a, IsActiveMan val_m s a
  · unfold daStep at hafter
    rw [dif_pos hactive] at hafter
    let a := Classical.choose hactive
    have hact : IsActiveMan val_m s a := by
      simpa [a] using Classical.choose_spec hactive
    let w_exists := exists_best_woman val_m s a hact
    let w0 := Classical.choose w_exists
    have hwbest : BestRemainingWoman val_m s a w0 := by
      simpa [w0, w_exists] using Classical.choose_spec w_exists
    let accepts : Prop :=
      match s.w_match w0 with
      | none => 0 ≤ val_w w0 a
      | some m' => val_w w0 m' < val_w w0 a
    by_cases hacc : accepts
    · by_cases hm : m = a
      · have hw_eq : w0 = w := by
          exact Option.some.inj
            (by simpa [a, w0, accepts, hacc, hm] using hafter)
        have hmem : w ∈ s.m_proposals m := by
          rw [hm]
          simpa [hw_eq] using hwbest.1
        exact hnot hmem
      · by_cases hcur : s.w_match w0 = some m
        · have hpref : val_w w0 m < val_w w0 a := by
            simpa [accepts, hcur] using hacc
          have hnone : (none : Option W) = some w := by
            simpa [a, w0, hcur, hpref, hm] using hafter
          cases hnone
        · have hold : s.m_match m = some w := by
            simpa [a, w0, accepts, hacc, hm, hcur] using hafter
          exact hne hold
    · have hold : s.m_match m = some w := by
        simpa [a, w0, accepts, hacc] using hafter
      exact hne hold
  · have hsame : daStep val_m val_w s = s :=
      daStep_eq_self_of_not_active val_m val_w s hactive
    exact hne (by simpa [hsame] using hafter)

/--
If a proposal opportunity is gone at a prefix and the man is not then holding
that woman, no later prefix can match them.
-/
theorem m_match_ne_daStateAfterSteps_of_not_mem_of_ne_of_le
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {steps later : ℕ} (hle : steps ≤ later) {m : M} {w : W}
    (hnot : w ∉ (daStateAfterSteps val_m val_w steps).m_proposals m)
    (hne : (daStateAfterSteps val_m val_w steps).m_match m ≠ some w) :
    (daStateAfterSteps val_m val_w later).m_match m ≠ some w := by
  have hadd : steps + (later - steps) = later := Nat.add_sub_of_le hle
  suffices
      (daStateAfterSteps val_m val_w (steps + (later - steps))).m_match m ≠
        some w by
    simpa [hadd] using this
  induction later - steps with
  | zero =>
      simpa using hne
  | succ extra ih =>
      have hnotCur :
          w ∉ (daStateAfterSteps val_m val_w (steps + extra)).m_proposals m := by
        exact not_mem_daStateAfterSteps_of_not_mem_of_le val_m val_w
          (Nat.le_add_right steps extra) hnot
      have hnext :=
        m_match_ne_of_not_mem_proposal_daStep val_m val_w
          (daStateAfterSteps val_m val_w (steps + extra)) hnotCur ih
      have hs :
          daStateAfterSteps val_m val_w (steps + (extra + 1)) =
            daStep val_m val_w
              (daStateAfterSteps val_m val_w (steps + extra)) := by
        rw [← Nat.add_assoc, daStateAfterSteps_succ]
      simpa [hs] using hnext

/--
Arbitrary-start version: if a proposal opportunity is gone at a prefix and the
man is not then holding that woman, no later prefix from the same start can
match them.
-/
theorem m_match_ne_daStateAfterStepsFrom_of_not_mem_of_ne_of_le
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) {steps later : ℕ} (hle : steps ≤ later)
    {m : M} {w : W}
    (hnot : w ∉ (daStateAfterStepsFrom val_m val_w start steps).m_proposals m)
    (hne : (daStateAfterStepsFrom val_m val_w start steps).m_match m ≠
      some w) :
    (daStateAfterStepsFrom val_m val_w start later).m_match m ≠ some w := by
  have hadd : steps + (later - steps) = later := Nat.add_sub_of_le hle
  suffices
      (daStateAfterStepsFrom val_m val_w start
          (steps + (later - steps))).m_match m ≠ some w by
    simpa [hadd] using this
  induction later - steps with
  | zero =>
      simpa using hne
  | succ extra ih =>
      have hnotCur :
          w ∉ (daStateAfterStepsFrom val_m val_w start
              (steps + extra)).m_proposals m := by
        exact not_mem_daStateAfterStepsFrom_of_not_mem_of_le val_m val_w
          start (Nat.le_add_right steps extra) hnot
      have hnext :=
        m_match_ne_of_not_mem_proposal_daStep val_m val_w
          (daStateAfterStepsFrom val_m val_w start (steps + extra))
          hnotCur ih
      have hs :
          daStateAfterStepsFrom val_m val_w start (steps + (extra + 1)) =
            daStep val_m val_w
              (daStateAfterStepsFrom val_m val_w start (steps + extra)) := by
        rw [← Nat.add_assoc, daStateAfterStepsFrom_succ]
      simpa [hs] using hnext

/--
Final-state version: a spent proposal cannot become a later match unless the
man was already holding that woman at the prefix.
-/
theorem m_match_ne_deferredAcceptanceState_of_not_mem_after_steps
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {steps : ℕ} (hle : steps ≤ Fintype.card M * Fintype.card W)
    {m : M} {w : W}
    (hnot : w ∉ (daStateAfterSteps val_m val_w steps).m_proposals m)
    (hne : (daStateAfterSteps val_m val_w steps).m_match m ≠ some w) :
    (deferredAcceptanceState val_m val_w).m_match m ≠ some w := by
  simpa [deferredAcceptanceState_eq_daStateAfterSteps] using
    m_match_ne_daStateAfterSteps_of_not_mem_of_ne_of_le
      val_m val_w hle hnot hne

/--
If a proposal opportunity is already gone by a DA prefix, then an earlier
concrete step removed it.
-/
theorem exists_proposal_removal_step_before_of_not_mem_daStateAfterSteps
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {steps : ℕ} {m : M} {w : W}
    (hnot : w ∉ (daStateAfterSteps val_m val_w steps).m_proposals m) :
    ∃ t, t < steps ∧
      w ∈ (daStateAfterSteps val_m val_w t).m_proposals m ∧
      w ∉ (daStateAfterSteps val_m val_w (t + 1)).m_proposals m := by
  let P : ℕ → Prop := fun t =>
    w ∈ (daStateAfterSteps val_m val_w t).m_proposals m
  have h0 : P 0 := by
    simp [P, initialDAState]
  have hN : ¬ P steps := by
    simpa [P] using hnot
  simpa [P] using exists_last_true_before_false_nat (P := P) h0 hN

set_option linter.unusedSimpArgs false

/-- A woman's held-match value weakly increases after one DA step. -/
theorem woman_match_value_daStep_mono
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (w0 : W) :
    valW val_w w0 (s.w_match w0) ≤
      valW val_w w0 ((daStep val_m val_w s).w_match w0) := by
  classical
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · let m := Classical.choose hactive
    have hact : IsActiveMan val_m s m := by
      simpa [m] using Classical.choose_spec hactive
    let w_exists := exists_best_woman val_m s m hact
    let w := Classical.choose w_exists
    let accepts : Prop :=
      match s.w_match w with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m
    by_cases hacc : accepts
    · by_cases hw0 : w0 = w
      · subst w0
        have hafter : (daStep val_m val_w s).w_match w = some m := by
          simp [daStep, hactive, m, hact, w_exists, w, accepts, hacc]
        cases hcur : s.w_match w with
        | none =>
            have hnonneg : 0 ≤ val_w w m := by
              simpa [accepts, hcur] using hacc
            simpa [valW, hcur, hafter] using hnonneg
        | some mcur =>
            have hpref : val_w w mcur < val_w w m := by
              simpa [accepts, hcur] using hacc
            have hle : val_w w mcur ≤ val_w w m := le_of_lt hpref
            simpa [valW, hcur, hafter] using hle
      · have hafter : (daStep val_m val_w s).w_match w0 = s.w_match w0 := by
          simp [daStep, hactive, m, hact, w_exists, w, accepts, hacc,
            Function.update, hw0]
        simp [hafter]
    · have hafter : (daStep val_m val_w s).w_match w0 = s.w_match w0 := by
        simp [daStep, hactive, m, hact, w_exists, w, accepts, hacc]
      simp [hafter]
  · simp [daStep, hactive]

/-- A woman's held-match value is monotone along DA run prefixes. -/
theorem woman_match_value_daStateAfterSteps_mono_add
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps extra : ℕ) (w : W) :
    valW val_w w ((daStateAfterSteps val_m val_w steps).w_match w) ≤
      valW val_w w
        ((daStateAfterSteps val_m val_w (steps + extra)).w_match w) := by
  induction extra with
  | zero =>
      simp
  | succ extra ih =>
      have hstep :=
        woman_match_value_daStep_mono val_m val_w
          (daStateAfterSteps val_m val_w (steps + extra)) w
      have hstep' :
          valW val_w w
              ((daStateAfterSteps val_m val_w (steps + extra)).w_match w) ≤
            valW val_w w
              ((daStateAfterSteps val_m val_w (steps + (extra + 1))).w_match w) := by
        rw [← Nat.add_assoc, daStateAfterSteps_succ]
        exact hstep
      exact le_trans ih hstep'

/-- Later DA run prefixes give every woman a weakly better held match. -/
theorem woman_match_value_daStateAfterSteps_mono_of_le
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {steps later : ℕ} (hle : steps ≤ later) (w : W) :
    valW val_w w ((daStateAfterSteps val_m val_w steps).w_match w) ≤
      valW val_w w ((daStateAfterSteps val_m val_w later).w_match w) := by
  have hadd : steps + (later - steps) = later := Nat.add_sub_of_le hle
  simpa [hadd] using
    woman_match_value_daStateAfterSteps_mono_add val_m val_w steps (later - steps) w

/-- A woman's held-match value is monotone along arbitrary-start DA run prefixes. -/
theorem woman_match_value_daStateAfterStepsFrom_mono_add
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) (steps extra : ℕ) (w : W) :
    valW val_w w ((daStateAfterStepsFrom val_m val_w start steps).w_match w) ≤
      valW val_w w
        ((daStateAfterStepsFrom val_m val_w start (steps + extra)).w_match w) := by
  induction extra with
  | zero =>
      simp
  | succ extra ih =>
      have hstep :=
        woman_match_value_daStep_mono val_m val_w
          (daStateAfterStepsFrom val_m val_w start (steps + extra)) w
      have hstep' :
          valW val_w w
              ((daStateAfterStepsFrom val_m val_w start (steps + extra)).w_match w) ≤
            valW val_w w
              ((daStateAfterStepsFrom val_m val_w start
                (steps + (extra + 1))).w_match w) := by
        rw [← Nat.add_assoc, daStateAfterStepsFrom_succ]
        exact hstep
      exact le_trans ih hstep'

/-- Later arbitrary-start DA run prefixes give every woman a weakly better held match. -/
theorem woman_match_value_daStateAfterStepsFrom_mono_of_le
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) {steps later : ℕ} (hle : steps ≤ later) (w : W) :
    valW val_w w ((daStateAfterStepsFrom val_m val_w start steps).w_match w) ≤
      valW val_w w ((daStateAfterStepsFrom val_m val_w start later).w_match w) := by
  have hadd : steps + (later - steps) = later := Nat.add_sub_of_le hle
  simpa [hadd] using
    woman_match_value_daStateAfterStepsFrom_mono_add
      val_m val_w start steps (later - steps) w

/-- The final DA state gives every woman a weakly better held match than any prefix. -/
theorem woman_match_value_deferredAcceptanceState_mono_after_steps
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : ℕ) (hle : steps ≤ Fintype.card M * Fintype.card W) (w : W) :
    valW val_w w ((daStateAfterSteps val_m val_w steps).w_match w) ≤
      valW val_w w ((deferredAcceptanceState val_m val_w).w_match w) := by
  have hmono :=
    woman_match_value_daStateAfterSteps_mono_of_le val_m val_w hle w
  simpa [deferredAcceptanceState_eq_daStateAfterSteps] using hmono

/--
If a proposal opportunity disappears in a DA step, then after that step the
woman holds someone she weakly prefers to the proposer.
-/
theorem woman_value_ge_of_proposal_removed_at_daStep
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    {m : M} {w : W}
    (hmem : w ∈ s.m_proposals m)
    (hnot : w ∉ (daStep val_m val_w s).m_proposals m) :
    val_w w m ≤ valW val_w w ((daStep val_m val_w s).w_match w) := by
  classical
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · let m0 := Classical.choose hactive
    have hact : IsActiveMan val_m s m0 := by
      simpa [m0] using Classical.choose_spec hactive
    let w_exists := exists_best_woman val_m s m0 hact
    let w0 := Classical.choose w_exists
    let accepts : Prop :=
      match s.w_match w0 with
      | none => 0 ≤ val_w w0 m0
      | some m' => val_w w0 m' < val_w w0 m0
    by_cases hacc : accepts
    · have hnotRemove : w ∉ removeProposal s m0 w0 m := by
        simpa [daStep, hactive, m0, hact, w_exists, w0, accepts, hacc] using hnot
      rcases not_mem_of_not_mem_removeProposal s hnotRemove with hnotOld | ⟨hm, hw⟩
      · exact False.elim (hnotOld hmem)
      · subst m
        subst w
        have hafter : (daStep val_m val_w s).w_match w0 = some m0 := by
          simp [daStep, hactive, m0, hact, w_exists, w0, accepts, hacc]
        simp [valW, hafter]
    · have hnotRemove : w ∉ removeProposal s m0 w0 m := by
        simpa [daStep, hactive, m0, hact, w_exists, w0, accepts, hacc] using hnot
      rcases not_mem_of_not_mem_removeProposal s hnotRemove with hnotOld | ⟨hm, hw⟩
      · exact False.elim (hnotOld hmem)
      · subst m
        subst w
        have hafter : (daStep val_m val_w s).w_match w0 = s.w_match w0 := by
          simp [daStep, hactive, m0, hact, w_exists, w0, accepts, hacc]
        cases hcur : s.w_match w0 with
        | none =>
            have hle : val_w w0 m0 ≤ 0 := by
              have hnotNonneg : ¬ 0 ≤ val_w w0 m0 := by
                simpa [accepts, hcur] using hacc
              exact le_of_not_ge hnotNonneg
            simpa [valW, hcur, hafter] using hle
        | some mcur =>
            have hle : val_w w0 m0 ≤ val_w w0 mcur := by
              have hnotlt : ¬ val_w w0 mcur < val_w w0 m0 := by
                simpa [accepts, hcur] using hacc
              exact le_of_not_gt hnotlt
            simpa [valW, hcur, hafter] using hle
  · have hsame : daStep val_m val_w s = s :=
      daStep_eq_self_of_not_active val_m val_w s hactive
    exact False.elim (hnot (by simpa [hsame] using hmem))

set_option linter.unusedSimpArgs true

/--
Run-prefix/final-state version: after a removed proposal, the final woman-side
match is weakly preferred by that woman to the proposer.
-/
theorem woman_final_value_ge_of_proposal_removed_at_daStateAfterSteps
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {steps : ℕ} {m : M} {w : W}
    (hsteps : steps < Fintype.card M * Fintype.card W)
    (hmem : w ∈ (daStateAfterSteps val_m val_w steps).m_proposals m)
    (hnot :
      w ∉ (daStateAfterSteps val_m val_w (steps + 1)).m_proposals m) :
    val_w w m ≤ valW val_w w ((deferredAcceptanceState val_m val_w).w_match w) := by
  have hstep :
      val_w w m ≤
        valW val_w w
          ((daStateAfterSteps val_m val_w (steps + 1)).w_match w) :=
    by
      have hraw :=
        woman_value_ge_of_proposal_removed_at_daStep val_m val_w
          (daStateAfterSteps val_m val_w steps) hmem
          (by simpa [daStateAfterSteps_succ] using hnot)
      simpa [daStateAfterSteps_succ] using hraw
  have hle : steps + 1 ≤ Fintype.card M * Fintype.card W :=
    Nat.succ_le_of_lt hsteps
  have hmono :=
    woman_match_value_deferredAcceptanceState_mono_after_steps
      val_m val_w (steps + 1) hle w
  exact le_trans hstep hmono

/--
If one DA step takes woman `w0` from weakly below a threshold man `r` to strictly
above him, the active proposer at that step proposed to `w0` and is strictly
preferred by `w0` to `r`.
-/
theorem woman_threshold_crossed_at_daStep
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (w0 : W) (r : M)
    (hbefore : valW val_w w0 (s.w_match w0) ≤ val_w w0 r)
    (hafter : val_w w0 r <
      valW val_w w0 ((daStep val_m val_w s).w_match w0)) :
    ∃ a,
      IsActiveMan val_m s a ∧
        BestRemainingWoman val_m s a w0 ∧
        (daStep val_m val_w s).w_match w0 = some a ∧
        val_w w0 r < val_w w0 a := by
  classical
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · let a := Classical.choose hactive
    have hact : IsActiveMan val_m s a := by
      simpa [a] using Classical.choose_spec hactive
    let w_exists := exists_best_woman val_m s a hact
    let w := Classical.choose w_exists
    have hwbest : BestRemainingWoman val_m s a w := by
      simpa [w, w_exists] using Classical.choose_spec w_exists
    let accepts : Prop :=
      match s.w_match w with
      | none => 0 ≤ val_w w a
      | some m' => val_w w m' < val_w w a
    by_cases hacc : accepts
    · by_cases hw0 : w0 = w
      · subst w0
        have hafterMatch : (daStep val_m val_w s).w_match w = some a := by
          simp [daStep, hactive, a, w, accepts, hacc]
        refine ⟨a, hact, hwbest, hafterMatch, ?_⟩
        simpa [valW, hafterMatch] using hafter
      · have hsame :
          (daStep val_m val_w s).w_match w0 = s.w_match w0 := by
          simp [daStep, hactive, a, w, accepts, hacc,
            Function.update, hw0]
        have hlt : val_w w0 r < valW val_w w0 (s.w_match w0) := by
          simpa [hsame] using hafter
        exact False.elim ((not_lt_of_ge hbefore) hlt)
    · have hsame :
          (daStep val_m val_w s).w_match w0 = s.w_match w0 := by
        simp [daStep, hactive, a, w, accepts, hacc]
      have hlt : val_w w0 r < valW val_w w0 (s.w_match w0) := by
        simpa [hsame] using hafter
      exact False.elim ((not_lt_of_ge hbefore) hlt)
  · have hsame : daStep val_m val_w s = s :=
      daStep_eq_self_of_not_active val_m val_w s hactive
    have hlt : val_w w0 r < valW val_w w0 (s.w_match w0) := by
      simpa [hsame] using hafter
    exact False.elim ((not_lt_of_ge hbefore) hlt)

/-- Run-prefix version of `woman_threshold_crossed_at_daStep`. -/
theorem woman_threshold_crossed_at_daStateAfterSteps_succ
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : ℕ) (w : W) (r : M)
    (hbefore :
      valW val_w w ((daStateAfterSteps val_m val_w steps).w_match w) ≤
        val_w w r)
    (hafter :
      val_w w r <
        valW val_w w
          ((daStateAfterSteps val_m val_w (steps + 1)).w_match w)) :
    ∃ a,
      IsActiveMan val_m (daStateAfterSteps val_m val_w steps) a ∧
        BestRemainingWoman val_m
          (daStateAfterSteps val_m val_w steps) a w ∧
        (daStateAfterSteps val_m val_w (steps + 1)).w_match w = some a ∧
        val_w w r < val_w w a := by
  rcases woman_threshold_crossed_at_daStep val_m val_w
      (daStateAfterSteps val_m val_w steps) w r hbefore
      (by simpa [daStateAfterSteps_succ] using hafter) with
    ⟨a, hact, hbest, hmatch, hpref⟩
  exact ⟨a, hact, hbest, by simpa [daStateAfterSteps_succ] using hmatch, hpref⟩

/--
If a woman's prefix trace eventually crosses a strict threshold, then there is
a first crossing step.
-/
theorem exists_woman_threshold_crossing_step_before
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {steps : ℕ} {w : W} {r : M}
    (hstart :
      ¬ val_w w r <
        valW val_w w ((daStateAfterSteps val_m val_w 0).w_match w))
    (hend :
      val_w w r <
        valW val_w w ((daStateAfterSteps val_m val_w steps).w_match w)) :
    ∃ t, t < steps ∧
      ¬ val_w w r <
        valW val_w w ((daStateAfterSteps val_m val_w t).w_match w) ∧
      val_w w r <
        valW val_w w ((daStateAfterSteps val_m val_w (t + 1)).w_match w) := by
  let P : ℕ → Prop := fun t =>
    ¬ val_w w r <
      valW val_w w ((daStateAfterSteps val_m val_w t).w_match w)
  have hN : ¬ P steps := by
    intro hnot
    exact hnot hend
  simpa [P] using exists_last_true_before_false_nat (P := P) hstart hN

/-- An active DA step consumes exactly one remaining proposal opportunity. -/
lemma remainingProposalCount_daStep_add_one_of_active
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hactive : ∃ m, IsActiveMan val_m s m) :
    remainingProposalCount (daStep val_m val_w s) + 1 =
      remainingProposalCount s := by
  classical
  unfold daStep
  rw [dif_pos hactive]
  let m := Classical.choose hactive
  have hact : IsActiveMan val_m s m := by
    simpa [m] using Classical.choose_spec hactive
  let w_exists := exists_best_woman val_m s m hact
  let w := Classical.choose w_exists
  have hwbest : BestRemainingWoman val_m s m w := by
    simpa [w, w_exists] using Classical.choose_spec w_exists
  have hremove := remainingProposalCount_removeProposal_add_one
    (s := s) (m := m) (w := w) hwbest.1
  let accepts : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w w m
    | some m' => val_w w m' < val_w w m
  by_cases hacc : accepts
  · simpa [m, hact, w_exists, w, accepts, hacc, remainingProposalCount] using hremove
  · simpa [m, hact, w_exists, w, accepts, hacc, remainingProposalCount] using hremove

/-- An active scheduled DA step consumes exactly one proposal opportunity. -/
lemma remainingProposalCount_daStepByMan_add_one_of_active
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (m : M)
    (hact : IsActiveMan val_m s m) :
    remainingProposalCount (daStepByMan val_m val_w s m) + 1 =
      remainingProposalCount s := by
  classical
  unfold daStepByMan
  rw [dif_pos hact]
  let w_exists := exists_best_woman val_m s m hact
  let w := Classical.choose w_exists
  have hwbest : BestRemainingWoman val_m s m w := by
    simpa [w, w_exists] using Classical.choose_spec w_exists
  have hremove := remainingProposalCount_removeProposal_add_one
    (s := s) (m := m) (w := w) hwbest.1
  let accepts : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w w m
    | some m' => val_w w m' < val_w w m
  by_cases hacc : accepts
  · simpa [w_exists, w, accepts, hacc, remainingProposalCount] using hremove
  · simpa [w_exists, w, accepts, hacc, remainingProposalCount] using hremove

/-- A scheduled DA step never increases the remaining proposal count. -/
lemma remainingProposalCount_daStepByMan_le
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (m : M) :
    remainingProposalCount (daStepByMan val_m val_w s m) ≤
      remainingProposalCount s := by
  by_cases hact : IsActiveMan val_m s m
  · have hcount :=
      remainingProposalCount_daStepByMan_add_one_of_active
        val_m val_w s m hact
    omega
  · simp [daStepByMan, hact]

lemma foldl_daStepByMan_remainingProposalCount_le
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (schedule : List M) (s : DAState M W) :
    remainingProposalCount
        (schedule.foldl (fun s m => daStepByMan val_m val_w s m) s) ≤
      remainingProposalCount s := by
  induction schedule generalizing s with
  | nil =>
      simp
  | cons m schedule ih =>
      rw [List.foldl_cons]
      exact le_trans (ih (daStepByMan val_m val_w s m))
        (remainingProposalCount_daStepByMan_le val_m val_w s m)

theorem daStateAfterSchedule_remainingProposalCount_le
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) (schedule : List M) :
    remainingProposalCount
        (daStateAfterSchedule val_m val_w start schedule) ≤
      remainingProposalCount start := by
  unfold daStateAfterSchedule
  exact foldl_daStepByMan_remainingProposalCount_le
    val_m val_w schedule start

/-- Once no man is active, any further list of DA steps leaves the state unchanged. -/
lemma foldl_daStep_eq_self_of_not_active
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : List ℕ) (s : DAState M W)
    (hnot : ¬ ∃ m, IsActiveMan val_m s m) :
    steps.foldl (fun s _ => daStep val_m val_w s) s = s := by
  induction steps generalizing s with
  | nil =>
      rfl
  | cons _ steps ih =>
      rw [List.foldl_cons, daStep_eq_self_of_not_active val_m val_w s hnot]
      exact ih s hnot

/--
If the number of remaining proposal opportunities is bounded by the number of
steps left, then after those steps no man is active.
-/
lemma no_active_after_steps_of_count_le_length
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : List ℕ) (s : DAState M W)
    (hcount : remainingProposalCount s ≤ steps.length) :
    ¬ ∃ m, IsActiveMan val_m
      (steps.foldl (fun s _ => daStep val_m val_w s) s) m := by
  induction steps generalizing s with
  | nil =>
      intro hactive
      have hpos := remainingProposalCount_pos_of_active val_m s hactive
      simp at hcount
      linarith
  | cons _ steps ih =>
      by_cases hactive : ∃ m, IsActiveMan val_m s m
      · have hstep_count :=
          remainingProposalCount_daStep_add_one_of_active val_m val_w s hactive
        have hcount_step : remainingProposalCount (daStep val_m val_w s) ≤ steps.length := by
          have hsucc :
              remainingProposalCount (daStep val_m val_w s) + 1 ≤ steps.length + 1 := by
            simpa [hstep_count] using hcount
          exact Nat.succ_le_succ_iff.mp hsucc
        simpa [List.foldl_cons] using ih (daStep val_m val_w s) hcount_step
      · rw [List.foldl_cons,
          daStep_eq_self_of_not_active val_m val_w s hactive]
        simpa [foldl_daStep_eq_self_of_not_active val_m val_w steps s hactive] using hactive

theorem no_active_daStateAfterStepsFrom_of_remainingProposalCount_le
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) {steps : ℕ}
    (hcount : remainingProposalCount start ≤ steps) :
    ¬ ∃ m, IsActiveMan val_m
      (daStateAfterStepsFrom val_m val_w start steps) m := by
  unfold daStateAfterStepsFrom
  exact no_active_after_steps_of_count_le_length
    val_m val_w (List.range steps) start (by simpa using hcount)

theorem no_active_daStateAfterSchedule_daChosenManScheduleFrom_of_remainingProposalCount_le
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) {steps : ℕ}
    (hcount : remainingProposalCount start ≤ steps) :
    ¬ ∃ m, IsActiveMan val_m
      (daStateAfterSchedule val_m val_w start
        (daChosenManScheduleFrom val_m val_w start steps)) m := by
  rw [daStateAfterSchedule_daChosenManScheduleFrom_eq_daStateAfterStepsFrom]
  exact
    no_active_daStateAfterStepsFrom_of_remainingProposalCount_le
      val_m val_w start hcount

theorem no_active_daStateAfterStepsFrom_card_mul
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) :
    ¬ ∃ m, IsActiveMan val_m
      (daStateAfterStepsFrom val_m val_w start
        (Fintype.card M * Fintype.card W)) m :=
  no_active_daStateAfterStepsFrom_of_remainingProposalCount_le
    val_m val_w start (remainingProposalCount_le_card_mul start)

def ManIRInvariant (val_m : M → W → ℝ) (s : DAState M W) : Prop :=
  ∀ m w, s.m_match m = some w → 0 ≤ val_m m w

def WomanIRInvariant (val_w : W → M → ℝ) (s : DAState M W) : Prop :=
  ∀ w m, s.w_match w = some m → 0 ≤ val_w w m

def MatchedProposedInvariant (s : DAState M W) : Prop :=
  ∀ m w, s.m_match m = some w → w ∉ s.m_proposals m

def WomanRejectionInvariant (val_w : W → M → ℝ) (s : DAState M W) : Prop :=
  ∀ w m', w ∉ s.m_proposals m' →
    s.m_match m' ≠ some w →
    val_w w m' < 0 ∨ (∃ m, s.w_match w = some m ∧ val_w w m' ≤ val_w w m)

def WomanRejectionInvariantExcept
    (val_w : W → M → ℝ) (s : DAState M W) (w0 : W) : Prop :=
  ∀ w, w ≠ w0 → ∀ m', w ∉ s.m_proposals m' →
    s.m_match m' ≠ some w →
    val_w w m' < 0 ∨ (∃ m, s.w_match w = some m ∧ val_w w m' ≤ val_w w m)

def ManProposalOrderInvariant (val_m : M → W → ℝ) (s : DAState M W) : Prop :=
  ∀ m w w', w ∉ s.m_proposals m → w' ∈ s.m_proposals m → 0 ≤ val_m m w' →
    val_m m w' ≤ val_m m w

def DAInvariants (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W) : Prop :=
  ManIRInvariant val_m s ∧
  WomanIRInvariant val_w s ∧
  MatchedProposedInvariant s ∧
  WomanRejectionInvariant val_w s ∧
  ManProposalOrderInvariant val_m s

/--
If every woman finds every man individually rational, then a woman who is
currently single has not rejected any proposal.  Equivalently, her name still
appears in every man's remaining-proposal set.

This is the DA-state form of the standard deferred-decisions observation that
the set of proposals already made is disjoint from the set of single women.
-/
theorem mem_m_proposals_of_woman_single_of_women_nonneg
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hinv : DAInvariants val_m val_w s)
    (hwomen_nonneg : ∀ w m, 0 ≤ val_w w m)
    {w : W} (hsingle : s.w_match w = none) (m : M) :
    w ∈ s.m_proposals m := by
  by_contra hnot_mem
  have hnot_match : s.m_match m ≠ some w := by
    intro hmatch
    have hwoman_match : s.w_match w = some m :=
      (s.consistent m w).1 hmatch
    rw [hsingle] at hwoman_match
    simp at hwoman_match
  rcases hinv.2.2.2.1 w m hnot_mem hnot_match with hnegative | ⟨m', hm', _⟩
  · exact (not_lt_of_ge (hwomen_nonneg w m)) hnegative
  · rw [hsingle] at hm'
    simp at hm'

def DAInvariantsExceptWoman
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (w0 : W) : Prop :=
  ManIRInvariant val_m s ∧
  WomanIRInvariant val_w s ∧
  MatchedProposedInvariant s ∧
  WomanRejectionInvariantExcept val_w s w0 ∧
  ManProposalOrderInvariant val_m s

theorem WomanRejectionInvariant.except
    {val_w : W → M → ℝ} {s : DAState M W}
    (h : WomanRejectionInvariant val_w s) (w0 : W) :
    WomanRejectionInvariantExcept val_w s w0 := by
  intro w _hne m hnot hnotMatch
  exact h w m hnot hnotMatch

theorem DAInvariants.exceptWoman
    {val_m : M → W → ℝ} {val_w : W → M → ℝ} {s : DAState M W}
    (h : DAInvariants val_m val_w s) (w0 : W) :
    DAInvariantsExceptWoman val_m val_w s w0 := by
  rcases h with ⟨hmanIR, hwomanIR, hmatchedProposed, hwomanReject,
    hproposalOrder⟩
  exact ⟨hmanIR, hwomanIR, hmatchedProposed,
    hwomanReject.except w0, hproposalOrder⟩

theorem divorceWomanState_satisfies_invariants_except_of_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (w0 : W)
    (hinv : DAInvariants val_m val_w s) :
    DAInvariantsExceptWoman val_m val_w (divorceWomanState s w0) w0 := by
  rcases hinv with ⟨hmanIR, hwomanIR, hmatchedProposed, hwomanReject,
    hproposalOrder⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m w hmatch
    by_cases hm : s.w_match w0 = some m
    · simp [divorceWomanState, hm] at hmatch
    · exact hmanIR m w (by simpa [divorceWomanState, hm] using hmatch)
  · intro w m hmatch
    by_cases hw : w = w0
    · subst w
      simp [divorceWomanState] at hmatch
    · exact hwomanIR w m (by simpa [divorceWomanState, hw] using hmatch)
  · intro m w hmatch
    by_cases hm : s.w_match w0 = some m
    · simp [divorceWomanState, hm] at hmatch
    · exact hmatchedProposed m w
        (by simpa [divorceWomanState, hm] using hmatch)
  · intro w hne m hnot hnotMatch
    have hnotOld : s.m_match m ≠ some w := by
      intro hmatchOld
      by_cases hm : s.w_match w0 = some m
      · have hmw0 : s.m_match m = some w0 := (s.consistent m w0).2 hm
        have hw_eq : w = w0 := Option.some.inj (hmatchOld.symm.trans hmw0)
        exact hne hw_eq
      · have hnew : (divorceWomanState s w0).m_match m = some w := by
          simpa [divorceWomanState, hm] using hmatchOld
        exact hnotMatch hnew
    rcases hwomanReject w m (by simpa [divorceWomanState] using hnot)
        hnotOld with hneg | ⟨mcur, hwcur, hle⟩
    · exact Or.inl hneg
    · exact Or.inr ⟨mcur,
        by simpa [divorceWomanState, hne] using hwcur, hle⟩
  · intro m w w' hnot hmem hnonneg
    exact hproposalOrder m w w'
      (by simpa [divorceWomanState] using hnot)
      (by simpa [divorceWomanState] using hmem) hnonneg

theorem divorceWomanState_preserves_invariantsExceptWoman_same
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (w0 : W)
    (hinv : DAInvariantsExceptWoman val_m val_w s w0) :
    DAInvariantsExceptWoman val_m val_w (divorceWomanState s w0) w0 := by
  rcases hinv with ⟨hmanIR, hwomanIR, hmatchedProposed, hwomanReject,
    hproposalOrder⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m w hmatch
    by_cases hm : s.w_match w0 = some m
    · simp [divorceWomanState, hm] at hmatch
    · exact hmanIR m w (by simpa [divorceWomanState, hm] using hmatch)
  · intro w m hmatch
    by_cases hw : w = w0
    · subst w
      simp [divorceWomanState] at hmatch
    · exact hwomanIR w m (by simpa [divorceWomanState, hw] using hmatch)
  · intro m w hmatch
    by_cases hm : s.w_match w0 = some m
    · simp [divorceWomanState, hm] at hmatch
    · exact hmatchedProposed m w
        (by simpa [divorceWomanState, hm] using hmatch)
  · intro w hne m hnot hnotMatch
    have hnotOld : s.m_match m ≠ some w := by
      intro hmatchOld
      by_cases hm : s.w_match w0 = some m
      · have hmw0 : s.m_match m = some w0 := (s.consistent m w0).2 hm
        have hw_eq : w = w0 := Option.some.inj (hmatchOld.symm.trans hmw0)
        exact hne hw_eq
      · have hnew : (divorceWomanState s w0).m_match m = some w := by
          simpa [divorceWomanState, hm] using hmatchOld
        exact hnotMatch hnew
    rcases hwomanReject w hne m (by simpa [divorceWomanState] using hnot)
        hnotOld with hneg | ⟨mcur, hwcur, hle⟩
    · exact Or.inl hneg
    · exact Or.inr ⟨mcur,
        by simpa [divorceWomanState, hne] using hwcur, hle⟩
  · intro m w w' hnot hmem hnonneg
    exact hproposalOrder m w w'
      (by simpa [divorceWomanState] using hnot)
      (by simpa [divorceWomanState] using hmem) hnonneg

/--
If an invariant DA state leaves a woman unmatched, then she has not rejected any
acceptable proposal: every man still has the opportunity to propose to her.
-/
lemma unmatched_woman_mem_proposals_of_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hwAcceptable : ∀ w m, 0 < val_w w m)
    (hinv : DAInvariants val_m val_w s)
    {w : W} (hwNone : s.w_match w = none) :
    ∀ m, w ∈ s.m_proposals m := by
  intro m
  by_contra hnot
  rcases hinv with ⟨_hmanIR, _hwomanIR, _hmatchedProposed, hwomanReject,
    _hproposalOrder⟩
  have hnotMatched : s.m_match m ≠ some w := by
    intro hmatch
    have hwMatch : s.w_match w = some m := (s.consistent m w).1 hmatch
    rw [hwNone] at hwMatch
    cases hwMatch
  rcases hwomanReject w m hnot hnotMatched with hneg | ⟨mcur, hwcur, _hle⟩
  · have hpos := hwAcceptable w m
    linarith
  · rw [hwNone] at hwcur
    cases hwcur

lemma initialDAState_satisfies_invariants (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    DAInvariants val_m val_w (initialDAState M W) := by
  simp [DAInvariants, ManIRInvariant, WomanIRInvariant, MatchedProposedInvariant,
    WomanRejectionInvariant, ManProposalOrderInvariant, initialDAState]

def DAStepPreservesInvariantsCertificate (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  ∀ s, DAInvariants val_m val_w s → DAInvariants val_m val_w (daStep val_m val_w s)

lemma daStep_preserves_invariants (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W) :
    DAStepPreservesInvariantsCertificate val_m val_w →
    DAInvariants val_m val_w s → DAInvariants val_m val_w (daStep val_m val_w s) := by
  intro hcert
  exact hcert s

lemma manProposalOrder_removeProposal
    (val_m : M → W → ℝ) (s : DAState M W) {m : M} {w : W}
    (hwbest : BestRemainingWoman val_m s m w)
    (horder : ManProposalOrderInvariant val_m s) :
    ∀ m0 w0 w1, w0 ∉ removeProposal s m w m0 →
      w1 ∈ removeProposal s m w m0 → 0 ≤ val_m m0 w1 →
      val_m m0 w1 ≤ val_m m0 w0 := by
  intro m0 w0 w1 hnotNew hmemNew hnonneg
  have hmemOld : w1 ∈ s.m_proposals m0 :=
    ((mem_removeProposal_iff s m m0 w w1).1 hmemNew).1
  rcases not_mem_of_not_mem_removeProposal s hnotNew with hnotOld | ⟨hm0, hw0⟩
  · exact horder m0 w0 w1 hnotOld hmemOld hnonneg
  · subst m0
    subst w0
    exact hwbest.2.2 w1 hmemOld hnonneg

lemma rejectStep_preserves_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) {m : M} {w : W}
    (hact : IsActiveMan val_m s m)
    (hwbest : BestRemainingWoman val_m s m w)
    (hreject :
      ¬ match s.w_match w with
        | none => 0 ≤ val_w w m
        | some m' => val_w w m' < val_w w m)
    (hinv : DAInvariants val_m val_w s) :
    DAInvariants val_m val_w { s with m_proposals := removeProposal s m w } := by
  rcases hinv with ⟨hmanIR, hwomanIR, hmatchedProposed, hwomanReject, hproposalOrder⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m0 w0 hmatch
    exact hmanIR m0 w0 hmatch
  · intro w0 m0 hmatch
    exact hwomanIR w0 m0 hmatch
  · intro m0 w0 hmatch
    by_cases hm0 : m0 = m
    · subst m0
      rw [hact.1] at hmatch
      cases hmatch
    · simpa [removeProposal, hm0] using hmatchedProposed m0 w0 hmatch
  · intro w0 m0 hnotNew hnotMatched
    rcases not_mem_of_not_mem_removeProposal s hnotNew with hnotOld | ⟨hm0, hw0⟩
    · exact hwomanReject w0 m0 hnotOld hnotMatched
    · subst m0
      subst w0
      cases hcur : s.w_match w with
      | none =>
          left
          have hnotNonneg : ¬ 0 ≤ val_w w m := by
            simpa [hcur] using hreject
          exact lt_of_not_ge hnotNonneg
      | some mcur =>
          right
          refine ⟨mcur, rfl, ?_⟩
          have hnotPref : ¬ val_w w mcur < val_w w m := by
            simpa [hcur] using hreject
          exact le_of_not_gt hnotPref
  · exact manProposalOrder_removeProposal val_m s hwbest hproposalOrder

lemma acceptStep_preserves_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) {m : M} {w : W}
    (hact : IsActiveMan val_m s m)
    (hwbest : BestRemainingWoman val_m s m w)
    (haccept :
      match s.w_match w with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m)
    (hinv : DAInvariants val_m val_w s) :
    DAInvariants val_m val_w
      { m_match := fun m'' =>
          if m'' = m then some w
          else if s.w_match w = some m'' then none
          else s.m_match m''
        w_match := Function.update s.w_match w (some m)
        m_proposals := removeProposal s m w
        consistent := by
          simpa using acceptMatch_consistent s hact.1 } := by
  rcases hinv with ⟨hmanIR, hwomanIR, hmatchedProposed, hwomanReject, hproposalOrder⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m0 w0 hmatch
    by_cases hm0 : m0 = m
    · subst m0
      simp at hmatch
      subst w0
      exact hwbest.2.1
    · by_cases hcur : s.w_match w = some m0
      · simp [hm0, hcur] at hmatch
      · have hold : s.m_match m0 = some w0 := by
          simpa [hm0, hcur] using hmatch
        exact hmanIR m0 w0 hold
  · intro w0 m0 hmatch
    by_cases hw0 : w0 = w
    · subst w0
      simp at hmatch
      subst m0
      cases hcur : s.w_match w with
      | none =>
          simpa [hcur] using haccept
      | some mcur =>
          have hcurIR : 0 ≤ val_w w mcur := hwomanIR w mcur hcur
          have hpref : val_w w mcur < val_w w m := by
            simpa [hcur] using haccept
          linarith
    · have hold : s.w_match w0 = some m0 := by
        simpa [Function.update, hw0] using hmatch
      exact hwomanIR w0 m0 hold
  · intro m0 w0 hmatch
    by_cases hm0 : m0 = m
    · subst m0
      simp at hmatch
      subst w0
      simp [removeProposal]
    · by_cases hcur : s.w_match w = some m0
      · simp [hm0, hcur] at hmatch
      · have hold : s.m_match m0 = some w0 := by
          simpa [hm0, hcur] using hmatch
        simpa [removeProposal, hm0] using hmatchedProposed m0 w0 hold
  · intro w0 m0 hnotNew hnotMatchedNew
    rcases not_mem_of_not_mem_removeProposal s hnotNew with hnotOld | ⟨hm0, hw0⟩
    · by_cases holdMatch : s.m_match m0 = some w0
      · have hm0_ne_m : m0 ≠ m := by
          intro hm0
          subst m0
          rw [hact.1] at holdMatch
          cases holdMatch
        by_cases hcur : s.w_match w = some m0
        · have holdW : s.m_match m0 = some w := (s.consistent m0 w).2 hcur
          have hw0_eq : w0 = w := by
            exact Option.some.inj (holdMatch.symm.trans holdW)
          subst w0
          right
          refine ⟨m, by simp, ?_⟩
          have hpref : val_w w m0 < val_w w m := by
            simpa [hcur] using haccept
          exact le_of_lt hpref
        · exfalso
          exact hnotMatchedNew (by simpa [hm0_ne_m, hcur] using holdMatch)
      · rcases hwomanReject w0 m0 hnotOld holdMatch with hneg | ⟨mold, hwold, hleOld⟩
        · exact Or.inl hneg
        · by_cases hw0 : w0 = w
          · subst w0
            right
            refine ⟨m, by simp, ?_⟩
            have hpref : val_w w mold < val_w w m := by
              simpa [hwold] using haccept
            exact le_trans hleOld (le_of_lt hpref)
          · right
            refine ⟨mold, ?_, hleOld⟩
            simpa [Function.update, hw0] using hwold
    · subst m0
      subst w0
      exfalso
      exact hnotMatchedNew (by simp)
  · exact manProposalOrder_removeProposal val_m s hwbest hproposalOrder

theorem daStepByMan_preserves_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (m : M)
    (hinv : DAInvariants val_m val_w s) :
    DAInvariants val_m val_w (daStepByMan val_m val_w s m) := by
  classical
  unfold daStepByMan
  by_cases hact : IsActiveMan val_m s m
  · rw [dif_pos hact]
    let w_exists := exists_best_woman val_m s m hact
    let w := Classical.choose w_exists
    have hwbest : BestRemainingWoman val_m s m w := by
      simpa [w, w_exists] using Classical.choose_spec w_exists
    let accepts : Prop :=
      match s.w_match w with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m
    by_cases hacc : accepts
    · simpa [w_exists, w, accepts, hacc] using
        acceptStep_preserves_invariants val_m val_w s hact hwbest hacc hinv
    · simpa [w_exists, w, accepts, hacc] using
        rejectStep_preserves_invariants val_m val_w s hact hwbest hacc hinv
  · simpa [hact] using hinv

lemma foldl_daStepByMan_preserves_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (schedule : List M) (s : DAState M W)
    (hinv : DAInvariants val_m val_w s) :
    DAInvariants val_m val_w
      (schedule.foldl (fun s m => daStepByMan val_m val_w s m) s) := by
  induction schedule generalizing s with
  | nil =>
      simpa using hinv
  | cons m schedule ih =>
      simp [List.foldl_cons]
      exact ih (daStepByMan val_m val_w s m)
        (daStepByMan_preserves_invariants val_m val_w s m hinv)

theorem daStateAfterSchedule_satisfies_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) (schedule : List M)
    (hinvStart : DAInvariants val_m val_w start) :
    DAInvariants val_m val_w
      (daStateAfterSchedule val_m val_w start schedule) := by
  unfold daStateAfterSchedule
  exact foldl_daStepByMan_preserves_invariants
    val_m val_w schedule start hinvStart

lemma rejectStep_preserves_invariantsExceptWoman
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (target : W) {m : M} {w : W}
    (hact : IsActiveMan val_m s m)
    (hwbest : BestRemainingWoman val_m s m w)
    (hreject :
      ¬ match s.w_match w with
        | none => 0 ≤ val_w w m
        | some m' => val_w w m' < val_w w m)
    (hinv : DAInvariantsExceptWoman val_m val_w s target) :
    DAInvariantsExceptWoman val_m val_w
      { s with m_proposals := removeProposal s m w } target := by
  rcases hinv with ⟨hmanIR, hwomanIR, hmatchedProposed, hwomanReject,
    hproposalOrder⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m0 w0 hmatch
    exact hmanIR m0 w0 hmatch
  · intro w0 m0 hmatch
    exact hwomanIR w0 m0 hmatch
  · intro m0 w0 hmatch
    by_cases hm0 : m0 = m
    · subst m0
      rw [hact.1] at hmatch
      cases hmatch
    · simpa [removeProposal, hm0] using hmatchedProposed m0 w0 hmatch
  · intro w0 hw0_ne_target m0 hnotNew hnotMatched
    rcases not_mem_of_not_mem_removeProposal s hnotNew with hnotOld | ⟨hm0, hw0⟩
    · exact hwomanReject w0 hw0_ne_target m0 hnotOld hnotMatched
    · subst m0
      subst w0
      cases hcur : s.w_match w with
      | none =>
          left
          have hnotNonneg : ¬ 0 ≤ val_w w m := by
            simpa [hcur] using hreject
          exact lt_of_not_ge hnotNonneg
      | some mcur =>
          right
          refine ⟨mcur, rfl, ?_⟩
          have hnotPref : ¬ val_w w mcur < val_w w m := by
            simpa [hcur] using hreject
          exact le_of_not_gt hnotPref
  · exact manProposalOrder_removeProposal val_m s hwbest hproposalOrder

lemma acceptStep_preserves_invariantsExceptWoman
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (target : W) {m : M} {w : W}
    (hact : IsActiveMan val_m s m)
    (hwbest : BestRemainingWoman val_m s m w)
    (haccept :
      match s.w_match w with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m)
    (hinv : DAInvariantsExceptWoman val_m val_w s target) :
    DAInvariantsExceptWoman val_m val_w
      { m_match := fun m'' =>
          if m'' = m then some w
          else if s.w_match w = some m'' then none
          else s.m_match m''
        w_match := Function.update s.w_match w (some m)
        m_proposals := removeProposal s m w
        consistent := by
          simpa using acceptMatch_consistent s hact.1 } target := by
  rcases hinv with ⟨hmanIR, hwomanIR, hmatchedProposed, hwomanReject,
    hproposalOrder⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m0 w0 hmatch
    by_cases hm0 : m0 = m
    · subst m0
      simp at hmatch
      subst w0
      exact hwbest.2.1
    · by_cases hcur : s.w_match w = some m0
      · simp [hm0, hcur] at hmatch
      · have hold : s.m_match m0 = some w0 := by
          simpa [hm0, hcur] using hmatch
        exact hmanIR m0 w0 hold
  · intro w0 m0 hmatch
    by_cases hw0 : w0 = w
    · subst w0
      simp at hmatch
      subst m0
      cases hcur : s.w_match w with
      | none =>
          simpa [hcur] using haccept
      | some mcur =>
          have hcurIR : 0 ≤ val_w w mcur := hwomanIR w mcur hcur
          have hpref : val_w w mcur < val_w w m := by
            simpa [hcur] using haccept
          linarith
    · have hold : s.w_match w0 = some m0 := by
        simpa [Function.update, hw0] using hmatch
      exact hwomanIR w0 m0 hold
  · intro m0 w0 hmatch
    by_cases hm0 : m0 = m
    · subst m0
      simp at hmatch
      subst w0
      simp [removeProposal]
    · by_cases hcur : s.w_match w = some m0
      · simp [hm0, hcur] at hmatch
      · have hold : s.m_match m0 = some w0 := by
          simpa [hm0, hcur] using hmatch
        simpa [removeProposal, hm0] using hmatchedProposed m0 w0 hold
  · intro w0 hw0_ne_target m0 hnotNew hnotMatchedNew
    rcases not_mem_of_not_mem_removeProposal s hnotNew with hnotOld | ⟨hm0, hw0⟩
    · by_cases holdMatch : s.m_match m0 = some w0
      · have hm0_ne_m : m0 ≠ m := by
          intro hm0
          subst m0
          rw [hact.1] at holdMatch
          cases holdMatch
        by_cases hcur : s.w_match w = some m0
        · have holdW : s.m_match m0 = some w := (s.consistent m0 w).2 hcur
          have hw0_eq : w0 = w := by
            exact Option.some.inj (holdMatch.symm.trans holdW)
          subst w0
          right
          refine ⟨m, by simp, ?_⟩
          have hpref : val_w w m0 < val_w w m := by
            simpa [hcur] using haccept
          exact le_of_lt hpref
        · exfalso
          exact hnotMatchedNew (by simpa [hm0_ne_m, hcur] using holdMatch)
      · rcases hwomanReject w0 hw0_ne_target m0 hnotOld holdMatch with
          hneg | ⟨mold, hwold, hleOld⟩
        · exact Or.inl hneg
        · by_cases hw0 : w0 = w
          · subst w0
            right
            refine ⟨m, by simp, ?_⟩
            have hpref : val_w w mold < val_w w m := by
              simpa [hwold] using haccept
            exact le_trans hleOld (le_of_lt hpref)
          · right
            refine ⟨mold, ?_, hleOld⟩
            simpa [Function.update, hw0] using hwold
    · subst m0
      subst w0
      exfalso
      exact hnotMatchedNew (by simp)
  · exact manProposalOrder_removeProposal val_m s hwbest hproposalOrder

theorem daStep_preserves_invariants_certificate
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    DAStepPreservesInvariantsCertificate val_m val_w := by
  intro s hinv
  classical
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · unfold daStep
    rw [dif_pos hactive]
    let m := Classical.choose hactive
    have hact : IsActiveMan val_m s m := by
      simpa [m] using Classical.choose_spec hactive
    let w_exists := exists_best_woman val_m s m hact
    let w := Classical.choose w_exists
    have hwbest : BestRemainingWoman val_m s m w := by
      simpa [w, w_exists] using Classical.choose_spec w_exists
    let accepts : Prop :=
      match s.w_match w with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m
    by_cases hacc : accepts
    · simpa [m, hact, w_exists, w, accepts, hacc] using
        acceptStep_preserves_invariants val_m val_w s hact hwbest hacc hinv
    · simpa [m, hact, w_exists, w, accepts, hacc] using
        rejectStep_preserves_invariants val_m val_w s hact hwbest hacc hinv
  · simpa [daStep, hactive] using hinv

/-- A list of DA steps preserves the invariants when each individual step does. -/
lemma foldl_daStep_preserves_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : List ℕ) (s : DAState M W)
    (hstep : DAStepPreservesInvariantsCertificate val_m val_w)
    (hinv : DAInvariants val_m val_w s) :
    DAInvariants val_m val_w
      (steps.foldl (fun s _ => daStep val_m val_w s) s) := by
  induction steps generalizing s with
  | nil =>
      simpa using hinv
  | cons _ steps ih =>
      simp [List.foldl_cons]
      exact ih (daStep val_m val_w s) (hstep s hinv)

theorem daStateAfterStepsFrom_satisfies_invariants_of_step_certificate
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) (steps : ℕ)
    (hstep : DAStepPreservesInvariantsCertificate val_m val_w)
    (hinvStart : DAInvariants val_m val_w start) :
    DAInvariants val_m val_w
      (daStateAfterStepsFrom val_m val_w start steps) := by
  unfold daStateAfterStepsFrom
  exact foldl_daStep_preserves_invariants val_m val_w
    (List.range steps) start hstep hinvStart

theorem daStateAfterStepsFrom_satisfies_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) (steps : ℕ)
    (hinvStart : DAInvariants val_m val_w start) :
    DAInvariants val_m val_w
      (daStateAfterStepsFrom val_m val_w start steps) :=
  daStateAfterStepsFrom_satisfies_invariants_of_step_certificate
    val_m val_w start steps (daStep_preserves_invariants_certificate val_m val_w)
    hinvStart

def DAStepPreservesInvariantsExceptWomanCertificate
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (w0 : W) : Prop :=
  ∀ s, DAInvariantsExceptWoman val_m val_w s w0 →
    DAInvariantsExceptWoman val_m val_w (daStep val_m val_w s) w0

theorem daStep_preserves_invariantsExceptWoman_certificate
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (target : W) :
    DAStepPreservesInvariantsExceptWomanCertificate val_m val_w target := by
  intro s hinv
  classical
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · unfold daStep
    rw [dif_pos hactive]
    let m := Classical.choose hactive
    have hact : IsActiveMan val_m s m := by
      simpa [m] using Classical.choose_spec hactive
    let w_exists := exists_best_woman val_m s m hact
    let w := Classical.choose w_exists
    have hwbest : BestRemainingWoman val_m s m w := by
      simpa [w, w_exists] using Classical.choose_spec w_exists
    let accepts : Prop :=
      match s.w_match w with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m
    by_cases hacc : accepts
    · simpa [m, hact, w_exists, w, accepts, hacc] using
        acceptStep_preserves_invariantsExceptWoman
          val_m val_w s target hact hwbest hacc hinv
    · simpa [m, hact, w_exists, w, accepts, hacc] using
        rejectStep_preserves_invariantsExceptWoman
          val_m val_w s target hact hwbest hacc hinv
  · simpa [daStep, hactive] using hinv

lemma foldl_daStep_preserves_invariantsExceptWoman
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (w0 : W)
    (steps : List ℕ) (s : DAState M W)
    (hstep : DAStepPreservesInvariantsExceptWomanCertificate val_m val_w w0)
    (hinv : DAInvariantsExceptWoman val_m val_w s w0) :
    DAInvariantsExceptWoman val_m val_w
      (steps.foldl (fun s _ => daStep val_m val_w s) s) w0 := by
  induction steps generalizing s with
  | nil =>
      simpa using hinv
  | cons _ steps ih =>
      simp [List.foldl_cons]
      exact ih (daStep val_m val_w s) (hstep s hinv)

theorem daStateAfterStepsFrom_satisfies_invariantsExceptWoman_of_step_certificate
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (w0 : W) (start : DAState M W) (steps : ℕ)
    (hstep : DAStepPreservesInvariantsExceptWomanCertificate val_m val_w w0)
    (hinvStart : DAInvariantsExceptWoman val_m val_w start w0) :
    DAInvariantsExceptWoman val_m val_w
      (daStateAfterStepsFrom val_m val_w start steps) w0 := by
  unfold daStateAfterStepsFrom
  exact foldl_daStep_preserves_invariantsExceptWoman val_m val_w w0
    (List.range steps) start hstep hinvStart

theorem daStateAfterStepsFrom_satisfies_invariantsExceptWoman
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (w0 : W) (start : DAState M W) (steps : ℕ)
    (hinvStart : DAInvariantsExceptWoman val_m val_w start w0) :
    DAInvariantsExceptWoman val_m val_w
      (daStateAfterStepsFrom val_m val_w start steps) w0 :=
  daStateAfterStepsFrom_satisfies_invariantsExceptWoman_of_step_certificate
    val_m val_w w0 start steps
    (daStep_preserves_invariantsExceptWoman_certificate val_m val_w w0)
    hinvStart

def DAStateInvariantCertificate (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  DAInvariants val_m val_w (deferredAcceptanceState val_m val_w)

lemma deferredAcceptanceState_satisfies_invariants (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    DAStateInvariantCertificate val_m val_w →
    DAInvariants val_m val_w (deferredAcceptanceState val_m val_w) := by
  intro hcert
  exact hcert

/-- The deferred-acceptance final state satisfies the invariants if each step preserves them. -/
theorem deferredAcceptanceState_satisfies_invariants_of_step_certificate
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstep : DAStepPreservesInvariantsCertificate val_m val_w) :
    DAStateInvariantCertificate val_m val_w := by
  unfold DAStateInvariantCertificate deferredAcceptanceState
  exact foldl_daStep_preserves_invariants val_m val_w
    (List.range (Fintype.card M * Fintype.card W))
    (initialDAState M W) hstep
    (initialDAState_satisfies_invariants val_m val_w)

/-- Every finite DA run prefix satisfies the invariants when each step preserves them. -/
theorem daStateAfterSteps_satisfies_invariants_of_step_certificate
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : ℕ)
    (hstep : DAStepPreservesInvariantsCertificate val_m val_w) :
    DAInvariants val_m val_w (daStateAfterSteps val_m val_w steps) := by
  unfold daStateAfterSteps
  exact foldl_daStep_preserves_invariants val_m val_w
    (List.range steps)
    (initialDAState M W) hstep
    (initialDAState_satisfies_invariants val_m val_w)

theorem daStateAfterSteps_satisfies_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : ℕ) :
    DAInvariants val_m val_w (daStateAfterSteps val_m val_w steps) :=
  daStateAfterSteps_satisfies_invariants_of_step_certificate val_m val_w steps
    (daStep_preserves_invariants_certificate val_m val_w)

/--
Stability away from one exceptional woman. This is useful for continued DA
runs that deliberately divorce a target woman and let only her rejection
invariant be reset.
-/
def IsStableExceptWoman
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) (target : W) : Prop :=
  (∀ m, 0 ≤ valM val_m m (mu.m_match m)) ∧
  (∀ w, 0 ≤ valW val_w w (mu.w_match w)) ∧
  (∀ m w, w ≠ target →
    valM val_m m (mu.m_match m) < val_m m w →
    valW val_w w (mu.w_match w) < val_w w m → False)

/--
A matching that is stable away from one exceptional woman is fully stable once
blocking pairs with that exceptional woman are also ruled out.
-/
theorem stable_of_stableExceptWoman_and_no_target_block
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) (target : W)
    (hexcept : IsStableExceptWoman val_m val_w mu target)
    (hno_target_block : ∀ m,
      valM val_m m (mu.m_match m) < val_m m target →
      valW val_w target (mu.w_match target) < val_w target m → False) :
    IsStable val_m val_w mu := by
  rcases hexcept with ⟨hmanIR, hwomanIR, hblock_except⟩
  refine ⟨hmanIR, hwomanIR, ?_⟩
  intro m w hm hw
  by_cases hw_target : w = target
  · subst w
    exact hno_target_block m hm hw
  · exact hblock_except m w hw_target hm hw

/--
If a state satisfies the invariants and no men are active (termination), 
then the matching is stable.
-/
lemma stable_of_invariants_and_terminated (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hinv : DAInvariants val_m val_w s)
    (hterm : ¬ ∃ m, IsActiveMan val_m s m) :
    IsStable val_m val_w ⟨s.m_match, s.w_match, s.consistent⟩ := by
  rcases hinv with ⟨hmanIR, hwomanIR, hmatchedProposed, hwomanReject, hproposalOrder⟩
  refine ⟨?_, ?_, ?_⟩
  · intro m
    cases hmatch : s.m_match m with
    | none =>
        simp [valM, hmatch]
    | some w =>
        simpa [valM, hmatch] using hmanIR m w hmatch
  · intro w
    cases hmatch : s.w_match w with
    | none =>
        simp [valW, hmatch]
    | some m =>
        simpa [valW, hmatch] using hwomanIR w m hmatch
  · intro m w hm hw
    by_cases hremaining : w ∈ s.m_proposals m
    · cases hmatch : s.m_match m with
      | none =>
          have hpositive : 0 < val_m m w := by
            simpa [valM, hmatch] using hm
          exact hterm ⟨m, hmatch, ⟨w, hremaining, le_of_lt hpositive⟩⟩
      | some wcur =>
          have hnotCurrentRemaining : wcur ∉ s.m_proposals m :=
            hmatchedProposed m wcur hmatch
          have hstrict : val_m m wcur < val_m m w := by
            simpa [valM, hmatch] using hm
          have hnonneg : 0 ≤ val_m m w :=
            le_trans (hmanIR m wcur hmatch) (le_of_lt hstrict)
          have hle : val_m m w ≤ val_m m wcur :=
            hproposalOrder m wcur w hnotCurrentRemaining hremaining hnonneg
          linarith
    · have hnotMatched : s.m_match m ≠ some w := by
        intro hmatch
        have hself : val_m m w < val_m m w := by
          simpa [valM, hmatch] using hm
        exact (lt_irrefl (val_m m w)) hself
      have hrej := hwomanReject w m hremaining hnotMatched
      rcases hrej with hnegative | ⟨mcur, hwcur, hrejectsForCurrent⟩
      · have hcurrentNonneg : 0 ≤ valW val_w w (s.w_match w) := by
          cases hmatch : s.w_match w with
          | none =>
              simp [valW]
          | some mcur =>
              simpa [valW, hmatch] using hwomanIR w mcur hmatch
        have hpositive : 0 < val_w w m := lt_of_le_of_lt hcurrentNonneg hw
        linarith
      · have hcurrentStrict : val_w w mcur < val_w w m := by
          simpa [valW, hwcur] using hw
        linarith

lemma stableExceptWoman_of_invariantsExceptWoman_and_terminated
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (target : W)
    (hinv : DAInvariantsExceptWoman val_m val_w s target)
    (hterm : ¬ ∃ m, IsActiveMan val_m s m) :
    IsStableExceptWoman val_m val_w
      ⟨s.m_match, s.w_match, s.consistent⟩ target := by
  rcases hinv with ⟨hmanIR, hwomanIR, hmatchedProposed, hwomanReject,
    hproposalOrder⟩
  refine ⟨?_, ?_, ?_⟩
  · intro m
    cases hmatch : s.m_match m with
    | none =>
        simp [valM, hmatch]
    | some w =>
        simpa [valM, hmatch] using hmanIR m w hmatch
  · intro w
    cases hmatch : s.w_match w with
    | none =>
        simp [valW, hmatch]
    | some m =>
        simpa [valW, hmatch] using hwomanIR w m hmatch
  · intro m w hne hm hw
    by_cases hremaining : w ∈ s.m_proposals m
    · cases hmatch : s.m_match m with
      | none =>
          have hpositive : 0 < val_m m w := by
            simpa [valM, hmatch] using hm
          exact hterm ⟨m, hmatch, ⟨w, hremaining, le_of_lt hpositive⟩⟩
      | some wcur =>
          have hnotCurrentRemaining : wcur ∉ s.m_proposals m :=
            hmatchedProposed m wcur hmatch
          have hstrict : val_m m wcur < val_m m w := by
            simpa [valM, hmatch] using hm
          have hnonneg : 0 ≤ val_m m w :=
            le_trans (hmanIR m wcur hmatch) (le_of_lt hstrict)
          have hle : val_m m w ≤ val_m m wcur :=
            hproposalOrder m wcur w hnotCurrentRemaining hremaining hnonneg
          linarith
    · have hnotMatched : s.m_match m ≠ some w := by
        intro hmatch
        have hself : val_m m w < val_m m w := by
          simpa [valM, hmatch] using hm
        exact (lt_irrefl (val_m m w)) hself
      have hrej := hwomanReject w hne m hremaining hnotMatched
      rcases hrej with hnegative | ⟨mcur, hwcur, hrejectsForCurrent⟩
      · have hcurrentNonneg : 0 ≤ valW val_w w (s.w_match w) := by
          cases hmatch : s.w_match w with
          | none =>
              simp [valW]
          | some mcur =>
              simpa [valW, hmatch] using hwomanIR w mcur hmatch
        have hpositive : 0 < val_w w m := lt_of_le_of_lt hcurrentNonneg hw
        linarith
      · have hcurrentStrict : val_w w mcur < val_w w m := by
          simpa [valW, hwcur] using hw
        linarith

def DATerminationCertificate (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  ¬ ∃ m, IsActiveMan val_m (deferredAcceptanceState val_m val_w) m

/-- The finite folded DA implementation terminates within `|M| * |W|` steps. -/
theorem deferredAcceptanceState_terminated (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    DATerminationCertificate val_m val_w := by
  unfold DATerminationCertificate deferredAcceptanceState
  exact no_active_after_steps_of_count_le_length val_m val_w
    (List.range (Fintype.card M * Fintype.card W))
    (initialDAState M W)
    (by simp [remainingProposalCount_initial])

def DaProducesStableMatchingCertificate (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  DAStepPreservesInvariantsCertificate val_m val_w

theorem da_produces_stable_matching_of_certificate (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcert : DaProducesStableMatchingCertificate val_m val_w) :
    IsStable val_m val_w (deferredAcceptance val_m val_w) := by
  have hstate : DAStateInvariantCertificate val_m val_w :=
    deferredAcceptanceState_satisfies_invariants_of_step_certificate val_m val_w hcert
  exact stable_of_invariants_and_terminated val_m val_w (deferredAcceptanceState val_m val_w)
    hstate (deferredAcceptanceState_terminated val_m val_w)

theorem deferredAcceptanceState_satisfies_invariants_closed
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    DAStateInvariantCertificate val_m val_w :=
  deferredAcceptanceState_satisfies_invariants_of_step_certificate val_m val_w
    (daStep_preserves_invariants_certificate val_m val_w)

theorem da_produces_stable_matching (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    IsStable val_m val_w (deferredAcceptance val_m val_w) :=
  da_produces_stable_matching_of_certificate val_m val_w
    (daStep_preserves_invariants_certificate val_m val_w)

/--
If a nonmanipulating proposer is weakly better off after one proposer's report
change, that proposer cannot have exhausted a woman ranked below his truthful
DA partner.  The statement is independent of preference completeness: the
strict positivity assumption is needed only for the named truthful partner.
-/
theorem nonmanipulator_proposal_remains_of_weakly_better
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m mk : M) (report_m : W → ℝ) (w wk : W)
    (hmk_ne_m : mk ≠ m)
    (hxmk : (deferredAcceptance val_m val_w).m_match mk = some wk)
    (hxmk_pos : 0 < val_m mk wk)
    (hweak :
      valM val_m mk ((deferredAcceptance val_m val_w).m_match mk) ≤
        valM val_m mk
          ((deferredAcceptance (Function.update val_m m report_m) val_w).m_match mk))
    (hpref : val_m mk w < val_m mk wk) :
    w ∈ (deferredAcceptanceState
      (Function.update val_m m report_m) val_w).m_proposals mk := by
  let reported := Function.update val_m m report_m
  by_contra hnot
  let N := Fintype.card M * Fintype.card W
  have hnotAtN :
      w ∉ (daStateAfterSteps reported val_w N).m_proposals mk := by
    simpa [N, deferredAcceptanceState_eq_daStateAfterSteps] using hnot
  rcases exists_proposal_removal_step_before_of_not_mem_daStateAfterSteps
      reported val_w hnotAtN with
    ⟨t, ht, hmem, hremoved⟩
  have hproposal :=
    proposal_removed_at_daStateAfterSteps_succ reported val_w t hmem hremoved
  cases hy : (deferredAcceptance reported val_w).m_match mk with
  | none =>
      have hweak' : val_m mk wk ≤ 0 := by
        simpa [valM, reported, Function.update, hmk_ne_m, hxmk, hy] using hweak
      linarith
  | some wy =>
      have hge : val_m mk wk ≤ val_m mk wy := by
        simpa [valM, reported, Function.update, hmk_ne_m, hxmk, hy] using hweak
      have hwy_gt_w : val_m mk w < val_m mk wy := lt_of_lt_of_le hpref hge
      have hnotWyAtT :
          wy ∉ (daStateAfterSteps reported val_w t).m_proposals mk := by
        intro hmemWy
        have hnonneg : 0 ≤ reported mk wy := by
          have hyIR := (da_produces_stable_matching reported val_w).1 mk
          simpa [valM, hy] using hyIR
        have hleReported := hproposal.2.2.2 wy hmemWy hnonneg
        have hleTrue : val_m mk wy ≤ val_m mk w := by
          simpa [reported, Function.update, hmk_ne_m] using hleReported
        linarith
      have hnotMatchAtT :
          (daStateAfterSteps reported val_w t).m_match mk ≠ some wy := by
        rw [hproposal.1.1]
        simp
      have hnotFinal :
          (deferredAcceptanceState reported val_w).m_match mk ≠ some wy :=
        m_match_ne_deferredAcceptanceState_of_not_mem_after_steps
          reported val_w (Nat.le_of_lt ht) hnotWyAtT hnotMatchAtT
      have hyState :
          (deferredAcceptanceState reported val_w).m_match mk = some wy := by
        simpa [deferredAcceptance, reported] using hy
      exact hnotFinal hyState

/-- Men have strict preferences over women. -/
def MenStrictPreferenceProfile (val_m : M → W → ℝ) : Prop :=
  ∀ m w w', val_m m w = val_m m w' → w = w'

/-- No woman is exactly tied with a man's outside option. -/
def MenNoOutsideTie (val_m : M → W → ℝ) : Prop :=
  ∀ m w, val_m m w ≠ 0

/-- No man is exactly tied with a woman's outside option. -/
def WomenNoOutsideTie (val_w : W → M → ℝ) : Prop :=
  ∀ w m, val_w w m ≠ 0

/--
Men have strict preferences on the acceptable region.  This supports
incomplete-list markets where multiple unacceptable alternatives may tie.
-/
def MenAcceptableStrictPreferenceProfile (val_m : M → W → ℝ) : Prop :=
  ∀ m w w', 0 ≤ val_m m w → 0 ≤ val_m m w' →
    val_m m w = val_m m w' → w = w'

theorem BestRemainingWoman_eq_of_acceptablyStrict
    (val_m : M → W → ℝ) (s : DAState M W) (m : M) {w₁ w₂ : W}
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hbest₁ : BestRemainingWoman val_m s m w₁)
    (hbest₂ : BestRemainingWoman val_m s m w₂) :
    w₁ = w₂ := by
  have hle₂₁ : val_m m w₂ ≤ val_m m w₁ :=
    hbest₁.2.2 w₂ hbest₂.1 hbest₂.2.1
  have hle₁₂ : val_m m w₁ ≤ val_m m w₂ :=
    hbest₂.2.2 w₁ hbest₁.1 hbest₁.2.1
  exact hstrictM m w₁ w₂ hbest₁.2.1 hbest₂.2.1
    (le_antisymm hle₁₂ hle₂₁)

theorem daStepByManChosenWoman_relabelMen_eq_of_acceptablyStrict {M' : Type*}
    [Fintype M'] [DecidableEq M']
    (val_m : M → W → ℝ) (e : M ≃ M') (s : DAState M W) (m' : M')
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hact : IsActiveMan val_m s (e.symm m')) :
    daStepByManChosenWoman (fun m' w => val_m (e.symm m') w)
        (DAState.relabelMen e s) m'
        ((IsActiveMan_relabelMen_iff val_m e s m').2 hact) =
      daStepByManChosenWoman val_m s (e.symm m') hact := by
  classical
  let hactRel : IsActiveMan (fun m' w => val_m (e.symm m') w)
      (DAState.relabelMen e s) m' := (IsActiveMan_relabelMen_iff val_m e s m').2 hact
  have hbestRel :
      BestRemainingWoman (fun m' w => val_m (e.symm m') w)
        (DAState.relabelMen e s) m'
        (daStepByManChosenWoman (fun m' w => val_m (e.symm m') w)
          (DAState.relabelMen e s) m' hactRel) :=
    Classical.choose_spec (exists_best_woman
      (fun m' w => val_m (e.symm m') w)
      (DAState.relabelMen e s) m' hactRel)
  have hbestRelOrig :
      BestRemainingWoman val_m s (e.symm m')
        (daStepByManChosenWoman (fun m' w => val_m (e.symm m') w)
          (DAState.relabelMen e s) m' hactRel) :=
    (BestRemainingWoman_relabelMen_iff val_m e s m' _).1 hbestRel
  have hbestOrig :
      BestRemainingWoman val_m s (e.symm m')
        (daStepByManChosenWoman val_m s (e.symm m') hact) :=
    Classical.choose_spec (exists_best_woman val_m s (e.symm m') hact)
  exact BestRemainingWoman_eq_of_acceptablyStrict val_m s (e.symm m')
    hstrictM hbestRelOrig hbestOrig

theorem daStepByMan_relabelMen_of_acceptablyStrict {M' : Type*}
    [Fintype M'] [DecidableEq M']
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (e : M ≃ M') (s : DAState M W) (m' : M')
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m) :
    daStepByMan (fun m' w => val_m (e.symm m') w)
        (fun w m' => val_w w (e.symm m')) (DAState.relabelMen e s) m' =
      DAState.relabelMen e (daStepByMan val_m val_w s (e.symm m')) := by
  by_cases hact : IsActiveMan val_m s (e.symm m')
  · exact daStepByMan_relabelMen_of_chosenWoman val_m val_w e s m' hact
      (daStepByManChosenWoman_relabelMen_eq_of_acceptablyStrict
        val_m e s m' hstrictM hact)
  · have hnotRel :
        ¬ IsActiveMan (fun m' w => val_m (e.symm m') w)
          (DAState.relabelMen e s) m' :=
      fun h => hact ((IsActiveMan_relabelMen_iff val_m e s m').1 h)
    simp [daStepByMan, hact, hnotRel]

theorem daStateAfterSchedule_relabelMen_of_acceptablyStrict {M' : Type*}
    [Fintype M'] [DecidableEq M']
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (e : M ≃ M') (start : DAState M W) (schedule : List M')
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m) :
    daStateAfterSchedule (fun m' w => val_m (e.symm m') w)
        (fun w m' => val_w w (e.symm m'))
        (DAState.relabelMen e start) schedule =
      DAState.relabelMen e
        (daStateAfterSchedule val_m val_w start (schedule.map e.symm)) := by
  induction schedule generalizing start with
  | nil =>
      simp
  | cons m' rest ih =>
      simp [daStateAfterSchedule_cons]
      rw [daStepByMan_relabelMen_of_acceptablyStrict val_m val_w e start m' hstrictM]
      exact ih (daStepByMan val_m val_w start (e.symm m'))

/-- Women have strict preferences over men. -/
def WomenStrictPreferenceProfile (val_w : W → M → ℝ) : Prop :=
  ∀ w m m', val_w w m = val_w w m' → m = m'

/--
Women have strict preferences on the individually-rational region.  This is
the optional-market analogue of `WomenStrictPreferenceProfile`: alternatives
that are both below the outside option may tie without affecting DA choices.
-/
def WomenAcceptableStrictPreferenceProfile (val_w : W → M → ℝ) : Prop :=
  ∀ w m m', 0 ≤ val_w w m → 0 ≤ val_w w m' →
    val_w w m = val_w w m' → m = m'

theorem WomenStrictPreferenceProfile.acceptablyStrict
    {val_w : W → M → ℝ}
    (hstrict : WomenStrictPreferenceProfile val_w) :
    WomenAcceptableStrictPreferenceProfile val_w := by
  intro w m m' _ _ heq
  exact hstrict w m m' heq

/--
All potential pairs are acceptable to both sides. This is the marriage-problem
specialization where every agent must be matched.
-/
def AllPairsAcceptable (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  (∀ m w, 0 < val_m m w) ∧ (∀ w m, 0 < val_w w m)

/--
On an equal-size all-acceptable marriage market, every stable matching is
complete. If a man and a woman were both unmatched, their mutually positive
values would make them a blocking pair; equal cardinalities rule out only one
side having unmatched agents.
-/
theorem stable_complete_of_card_eq_all_pairs_acceptable
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (mu : Assignment M W)
    (hcard : Fintype.card M = Fintype.card W)
    (hacceptable : AllPairsAcceptable val_m val_w)
    (hstable : IsStable val_m val_w mu) :
    (∀ m, ∃ w, mu.m_match m = some w) ∧
      (∀ w, ∃ m, mu.w_match w = some m) := by
  classical
  have hmComplete : ∀ m, ∃ w, mu.m_match m = some w := by
    intro m
    by_cases hm : ∃ w, mu.m_match m = some w
    · exact hm
    · have hm_none : mu.m_match m = none := by
        cases hmatch : mu.m_match m with
        | none => rfl
        | some w => exact False.elim (hm ⟨w, hmatch⟩)
      have hnotWComplete : ¬ ∀ w, ∃ m, mu.w_match w = some m := by
        intro hwComplete
        have hmCompleteFromWomen :
            ∀ m, ∃ w, mu.m_match m = some w :=
          Assignment.m_complete_of_w_complete_of_card_eq
            (mu := mu) hcard hwComplete
        exact hm (hmCompleteFromWomen m)
      obtain ⟨w, hnoW⟩ := not_forall.mp hnotWComplete
      have hw_none : mu.w_match w = none := by
        cases hmatch : mu.w_match w with
        | none => rfl
        | some m' =>
            exact False.elim (hnoW ⟨m', hmatch⟩)
      have hm_block : valM val_m m (mu.m_match m) < val_m m w := by
        simpa [valM, hm_none] using hacceptable.1 m w
      have hw_block : valW val_w w (mu.w_match w) < val_w w m := by
        simpa [valW, hw_none] using hacceptable.2 w m
      exact False.elim (hstable.2.2 m w hm_block hw_block)
  exact ⟨hmComplete,
    Assignment.w_complete_of_m_complete_of_card_eq
      (mu := mu) hcard hmComplete⟩

/--
When every pair is acceptable and there are at least as many women as men,
every stable matching assigns a woman to every man.  Women may remain
unmatched when the inequality is strict.
-/
theorem stable_m_complete_of_card_le_all_pairs_acceptable
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (mu : Assignment M W)
    (hcard : Fintype.card M ≤ Fintype.card W)
    (hacceptable : AllPairsAcceptable val_m val_w)
    (hstable : IsStable val_m val_w mu) :
    ∀ m, ∃ w, mu.m_match m = some w := by
  classical
  intro m
  by_contra hm
  have hm_none : mu.m_match m = none := by
    cases hmatch : mu.m_match m with
    | none => rfl
    | some w => exact False.elim (hm ⟨w, hmatch⟩)
  have hwComplete : ∀ w, ∃ m', mu.w_match w = some m' := by
    intro w
    by_contra hw
    have hw_none : mu.w_match w = none := by
      cases hmatch : mu.w_match w with
      | none => rfl
      | some m' => exact False.elim (hw ⟨m', hmatch⟩)
    have hm_block : valM val_m m (mu.m_match m) < val_m m w := by
      simpa [valM, hm_none] using hacceptable.1 m w
    have hw_block : valW val_w w (mu.w_match w) < val_w w m := by
      simpa [valW, hw_none] using hacceptable.2 w m
    exact hstable.2.2 m w hm_block hw_block
  have hWcard : Fintype.card W =
      Fintype.card {w : W // mu.w_match w ≠ none} := by
    apply Nat.le_antisymm
    · let f : W → {w : W // mu.w_match w ≠ none} := fun w =>
        ⟨w, by
          rcases hwComplete w with ⟨m', hm'⟩
          rw [hm']
          simp⟩
      exact Fintype.card_le_of_injective f (fun w₁ w₂ h =>
        Subtype.ext_iff.mp h)
    · exact Fintype.card_subtype_le (fun w : W => mu.w_match w ≠ none)
  have hmatched :
      Fintype.card {m : M // mu.m_match m ≠ none} =
        Fintype.card {w : W // mu.w_match w ≠ none} :=
    Fintype.card_congr (Assignment.matchedMenEquivWomen mu)
  have hmlt : Fintype.card {m' : M // mu.m_match m' ≠ none} < Fintype.card M :=
    Fintype.card_subtype_lt (p := fun m' : M => mu.m_match m' ≠ none)
      (x := m) (by simp [hm_none])
  have : Fintype.card W < Fintype.card M := by
    calc
      Fintype.card W = Fintype.card {w : W // mu.w_match w ≠ none} := hWcard
      _ = Fintype.card {m' : M // mu.m_match m' ≠ none} := hmatched.symm
      _ < Fintype.card M := hmlt
  exact (not_lt_of_ge hcard) this

/--
The men-proposing DA outcome matches every man when all pairs are acceptable
and the women side is at least as large as the men side.
-/
theorem deferredAcceptance_m_complete_of_card_le_all_pairs_acceptable
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M ≤ Fintype.card W)
    (hacceptable : AllPairsAcceptable val_m val_w) :
    ∀ m, ∃ w, (deferredAcceptance val_m val_w).m_match m = some w := by
  exact stable_m_complete_of_card_le_all_pairs_acceptable
    val_m val_w (deferredAcceptance val_m val_w) hcard hacceptable
    (da_produces_stable_matching val_m val_w)

/--
On equal-size all-acceptable marriage markets, the DA outcome matches every man
and every woman. This is the completeness bridge between the no-outside-option
marriage model and the generic optional-partner DA encoding.
-/
theorem deferredAcceptance_complete_of_card_eq_all_pairs_acceptable
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hacceptable : AllPairsAcceptable val_m val_w) :
    (∀ m, ∃ w, (deferredAcceptance val_m val_w).m_match m = some w) ∧
      (∀ w, ∃ m, (deferredAcceptance val_m val_w).w_match w = some m) := by
  classical
  let s := deferredAcceptanceState val_m val_w
  have hinv : DAInvariants val_m val_w s := by
    simpa [s, DAStateInvariantCertificate] using
      deferredAcceptanceState_satisfies_invariants_closed val_m val_w
  have hterm : ¬ ∃ m, IsActiveMan val_m s m := by
    have htermCert := deferredAcceptanceState_terminated val_m val_w
    simpa [s, DATerminationCertificate] using htermCert
  let mu : Assignment M W := ⟨s.m_match, s.w_match, s.consistent⟩
  have hmComplete : ∀ m, ∃ w, s.m_match m = some w := by
    intro m
    cases hm : s.m_match m with
    | some w =>
        exact ⟨w, rfl⟩
    | none =>
        have hnoRemaining : ∀ w, w ∉ s.m_proposals m := by
          intro w hw
          exact hterm ⟨m, hm, ⟨w, hw, le_of_lt (hacceptable.1 m w)⟩⟩
        have hwComplete : ∀ w, ∃ m, s.w_match w = some m := by
          intro w
          have hnotMatched : s.m_match m ≠ some w := by
            rw [hm]
            simp
          rcases hinv.2.2.2.1 w m (hnoRemaining w) hnotMatched with
            hneg | ⟨mcur, hwcur, _hle⟩
          · have hpos := hacceptable.2 w m
            linarith
          · exact ⟨mcur, hwcur⟩
        have hmCompleteFromWomen :
            ∀ m, ∃ w, s.m_match m = some w := by
          simpa [mu] using
            Assignment.m_complete_of_w_complete_of_card_eq
              (mu := mu) hcard hwComplete
        rcases hmCompleteFromWomen m with ⟨w, hw⟩
        rw [hm] at hw
        cases hw
  have hwComplete : ∀ w, ∃ m, s.w_match w = some m := by
    simpa [mu] using
      Assignment.w_complete_of_m_complete_of_card_eq
        (mu := mu) hcard hmComplete
  constructor
  · intro m
    simpa [deferredAcceptance, s] using hmComplete m
  · intro w
    simpa [deferredAcceptance, s] using hwComplete w

/--
The proposing-side "possible woman" invariant: if a man has already lost access
to a woman and is not currently holding her, then no stable matching can pair
them.
-/
def DARejectedPairImpossibleInvariant
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W) : Prop :=
  ∀ mu, IsStable val_m val_w mu →
    ∀ m w, w ∉ s.m_proposals m → s.m_match m ≠ some w →
      mu.m_match m ≠ some w

/-- Initially no pair has been rejected, so the rejected-pair invariant is vacuous. -/
lemma initialDAState_satisfies_rejected_pair_impossible
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    DARejectedPairImpossibleInvariant val_m val_w (initialDAState M W) := by
  intro mu hstable m w hnot _
  simp [initialDAState] at hnot

lemma better_than_best_not_remaining
    (val_m : M → W → ℝ) (s : DAState M W) {m : M} {w : W}
    (hacceptable : ∀ m w, 0 < val_m m w)
    (hwbest : BestRemainingWoman val_m s m w) :
    ∀ w', val_m m w < val_m m w' → w' ∉ s.m_proposals m := by
  intro w' hbetter hmem
  have hle := hwbest.2.2 w' hmem (le_of_lt (hacceptable m w'))
  linarith

/--
If woman `w` rejects `r` in favor of `a`, and `a` has just proposed to `w`,
then no stable matching can pair `r` with `w`. This is the local blocking-pair
step in the proof of proposer optimality.
-/
lemma stable_matching_excludes_rejected_pair
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (mu : Assignment M W)
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hacceptable : AllPairsAcceptable val_m val_w)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s)
    (hstable : IsStable val_m val_w mu)
    {a r : M} {w : W}
    (hne : a ≠ r)
    (hbetterRemoved : ∀ w', val_m a w < val_m a w' → w' ∉ s.m_proposals a)
    (hnotCurrentBetter : ∀ w', val_m a w < val_m a w' → s.m_match a ≠ some w')
    (hwomanPref : val_w w r < val_w w a) :
    mu.m_match r ≠ some w := by
  intro hrw
  have hw_mu : mu.w_match w = some r := (mu.consistent_m r w).1 hrw
  have hmanPref : valM val_m a (mu.m_match a) < val_m a w := by
    cases ha_mu : mu.m_match a with
    | none =>
        simpa [valM, ha_mu] using hacceptable.1 a w
    | some wmu =>
        have hne_wmu : wmu ≠ w := by
          intro heq
          have hw_a : mu.w_match w = some a := by
            simpa [heq] using (mu.consistent_m a wmu).1 ha_mu
          have : some a = some r := by
            rw [← hw_a, hw_mu]
          exact hne (Option.some.inj this)
        by_cases hle : val_m a wmu ≤ val_m a w
        · have hneq : val_m a wmu ≠ val_m a w := by
            intro heq
            exact hne_wmu (hstrictM a wmu w heq)
          exact lt_of_le_of_ne hle hneq
        · have hbetter : val_m a w < val_m a wmu := lt_of_not_ge hle
          exact False.elim
            (hrejected mu hstable a wmu
              (hbetterRemoved wmu hbetter)
              (hnotCurrentBetter wmu hbetter)
              ha_mu)
  have hwomanPref' : valW val_w w (mu.w_match w) < val_w w a := by
    simpa [valW, hw_mu] using hwomanPref
  exact hstable.2.2 a w hmanPref hwomanPref'

lemma rejectStep_preserves_rejected_pair_impossible
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) {m : M} {w : W}
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hstrictW : WomenStrictPreferenceProfile val_w)
    (hacceptable : AllPairsAcceptable val_m val_w)
    (hact : IsActiveMan val_m s m)
    (hwbest : BestRemainingWoman val_m s m w)
    (hreject :
      ¬ match s.w_match w with
        | none => 0 ≤ val_w w m
        | some m' => val_w w m' < val_w w m)
    (hinv : DAInvariants val_m val_w s)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s) :
    DARejectedPairImpossibleInvariant val_m val_w
      { s with m_proposals := removeProposal s m w } := by
  rcases hinv with ⟨_hmanIR, _hwomanIR, hmatchedProposed, _hwomanReject,
    hproposalOrder⟩
  intro mu hstable m0 w0 hnotNew hnotMatchNew
  rcases not_mem_of_not_mem_removeProposal s hnotNew with hnotOld | ⟨hm0, hw0⟩
  · exact hrejected mu hstable m0 w0 hnotOld hnotMatchNew
  · subst m0
    subst w0
    cases hcur : s.w_match w with
    | none =>
        intro hmu
        have hw_mu : mu.w_match w = some m := (mu.consistent_m m w).1 hmu
        have hwIR := hstable.2.1 w
        have hnotNonneg : ¬ 0 ≤ val_w w m := by
          simpa [hcur] using hreject
        have hnonneg : 0 ≤ val_w w m := by
          simpa [valW, hw_mu] using hwIR
        exact hnotNonneg hnonneg
    | some a =>
        have ha_match : s.m_match a = some w := (s.consistent a w).2 hcur
        have hne : a ≠ m := by
          intro h
          subst a
          rw [hact.1] at ha_match
          cases ha_match
        have hle : val_w w m ≤ val_w w a := by
          have hnotlt : ¬ val_w w a < val_w w m := by
            simpa [hcur] using hreject
          exact le_of_not_gt hnotlt
        have hwomanPref : val_w w m < val_w w a := by
          have hneq : val_w w m ≠ val_w w a := by
            intro heq
            exact hne ((hstrictW w m a heq).symm)
          exact lt_of_le_of_ne hle hneq
        refine stable_matching_excludes_rejected_pair val_m val_w s mu
          hstrictM hacceptable hrejected hstable hne ?_ ?_ hwomanPref
        · intro w' hbetter hmem
          have hnotCurrent : w ∉ s.m_proposals a :=
            hmatchedProposed a w ha_match
          have hle' := hproposalOrder a w w' hnotCurrent hmem
            (le_of_lt (hacceptable.1 a w'))
          linarith
        · intro w' hbetter hmatch
          rw [ha_match] at hmatch
          injection hmatch with hw'
          subst w'
          linarith

lemma acceptStep_preserves_rejected_pair_impossible
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) {m : M} {w : W}
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hacceptable : AllPairsAcceptable val_m val_w)
    (hact : IsActiveMan val_m s m)
    (hwbest : BestRemainingWoman val_m s m w)
    (haccept :
      match s.w_match w with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s) :
    DARejectedPairImpossibleInvariant val_m val_w
      { m_match := fun m'' =>
          if m'' = m then some w
          else if s.w_match w = some m'' then none
          else s.m_match m''
        w_match := Function.update s.w_match w (some m)
        m_proposals := removeProposal s m w
        consistent := by
          simpa using acceptMatch_consistent s hact.1 } := by
  intro mu hstable m0 w0 hnotNew hnotMatchNew
  rcases not_mem_of_not_mem_removeProposal s hnotNew with hnotOld | ⟨hm0, hw0⟩
  · by_cases holdMatch : s.m_match m0 = some w0
    · have hm0_ne_m : m0 ≠ m := by
        intro hm0
        subst m0
        rw [hact.1] at holdMatch
        cases holdMatch
      by_cases hcur0 : s.w_match w = some m0
      · have holdW : s.m_match m0 = some w := (s.consistent m0 w).2 hcur0
        have hw0_eq : w0 = w := Option.some.inj (holdMatch.symm.trans holdW)
        subst w0
        have hne : m ≠ m0 := fun h => hm0_ne_m h.symm
        have hwomanPref : val_w w m0 < val_w w m := by
          simpa [hcur0] using haccept
        exact stable_matching_excludes_rejected_pair val_m val_w s mu
          hstrictM hacceptable hrejected hstable hne
          (better_than_best_not_remaining val_m s hacceptable.1 hwbest)
          (by
            intro w' _ hmatch
            rw [hact.1] at hmatch
            cases hmatch)
          hwomanPref
      · exact False.elim (hnotMatchNew (by simpa [hm0_ne_m, hcur0] using holdMatch))
    · exact hrejected mu hstable m0 w0 hnotOld holdMatch
  · subst m0
    subst w0
    exact False.elim (hnotMatchNew (by simp))

theorem daStep_preserves_rejected_pair_impossible
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hstrictW : WomenStrictPreferenceProfile val_w)
    (hacceptable : AllPairsAcceptable val_m val_w) :
    ∀ s, DAInvariants val_m val_w s →
      DARejectedPairImpossibleInvariant val_m val_w s →
        DARejectedPairImpossibleInvariant val_m val_w
          (daStep val_m val_w s) := by
  intro s hinv hrejected
  classical
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · unfold daStep
    rw [dif_pos hactive]
    let m := Classical.choose hactive
    have hact : IsActiveMan val_m s m := by
      simpa [m] using Classical.choose_spec hactive
    let w_exists := exists_best_woman val_m s m hact
    let w := Classical.choose w_exists
    have hwbest : BestRemainingWoman val_m s m w := by
      simpa [w, w_exists] using Classical.choose_spec w_exists
    let accepts : Prop :=
      match s.w_match w with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m
    by_cases hacc : accepts
    · simpa [m, hact, w_exists, w, accepts, hacc] using
        acceptStep_preserves_rejected_pair_impossible
          val_m val_w s hstrictM hacceptable hact hwbest hacc hrejected
    · simpa [m, hact, w_exists, w, accepts, hacc] using
        rejectStep_preserves_rejected_pair_impossible
          val_m val_w s hstrictM hstrictW hacceptable hact hwbest hacc hinv
          hrejected
  · simpa [daStep, hactive] using hrejected

lemma foldl_daStep_preserves_rejected_pair_impossible
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : List ℕ) (s : DAState M W)
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hstrictW : WomenStrictPreferenceProfile val_w)
    (hacceptable : AllPairsAcceptable val_m val_w)
    (hinv : DAInvariants val_m val_w s)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s) :
    DARejectedPairImpossibleInvariant val_m val_w
      (steps.foldl (fun s _ => daStep val_m val_w s) s) := by
  induction steps generalizing s with
  | nil =>
      simpa using hrejected
  | cons _ steps ih =>
      rw [List.foldl_cons]
      exact ih (daStep val_m val_w s)
        (daStep_preserves_invariants_certificate val_m val_w s hinv)
        (daStep_preserves_rejected_pair_impossible val_m val_w
          hstrictM hstrictW hacceptable s hinv hrejected)

theorem deferredAcceptanceState_satisfies_rejected_pair_impossible
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hstrictW : WomenStrictPreferenceProfile val_w)
    (hacceptable : AllPairsAcceptable val_m val_w) :
    DARejectedPairImpossibleInvariant val_m val_w
      (deferredAcceptanceState val_m val_w) := by
  unfold deferredAcceptanceState
  exact foldl_daStep_preserves_rejected_pair_impossible val_m val_w
    (List.range (Fintype.card M * Fintype.card W))
    (initialDAState M W)
    hstrictM hstrictW hacceptable
    (initialDAState_satisfies_invariants val_m val_w)
    (initialDAState_satisfies_rejected_pair_impossible val_m val_w)

/--
If `w` is the best acceptable remaining woman, every strictly better woman has
already been removed.  Unlike `better_than_best_not_remaining`, this form does
not require all pairs to be acceptable.
-/
lemma better_than_best_not_remaining_of_best
    (val_m : M → W → ℝ) (s : DAState M W) {m : M} {w : W}
    (hwbest : BestRemainingWoman val_m s m w) :
    ∀ w', val_m m w < val_m m w' → w' ∉ s.m_proposals m := by
  intro w' hbetter hmem
  have hnonneg : 0 ≤ val_m m w' :=
    le_trans hwbest.2.1 (le_of_lt hbetter)
  have hle := hwbest.2.2 w' hmem hnonneg
  linarith

/--
No-outside-tie variant of the local rejected-pair exclusion.  The proposed
woman `w` only needs to be weakly acceptable to proposer `a`; no outside tie
turns that into the strict preference over being unmatched needed for blocking.
-/
lemma stable_matching_excludes_rejected_pair_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (mu : Assignment M W)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hnozero : MenNoOutsideTie val_m)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s)
    (hstable : IsStable val_m val_w mu)
    {a r : M} {w : W}
    (hne : a ≠ r)
    (hw_nonneg : 0 ≤ val_m a w)
    (hbetterRemoved : ∀ w', val_m a w < val_m a w' → w' ∉ s.m_proposals a)
    (hnotCurrentBetter : ∀ w', val_m a w < val_m a w' → s.m_match a ≠ some w')
    (hwomanPref : val_w w r < val_w w a) :
    mu.m_match r ≠ some w := by
  intro hrw
  have hw_mu : mu.w_match w = some r := (mu.consistent_m r w).1 hrw
  have hmanPref : valM val_m a (mu.m_match a) < val_m a w := by
    cases ha_mu : mu.m_match a with
    | none =>
        have hpos : 0 < val_m a w :=
          lt_of_le_of_ne hw_nonneg (hnozero a w).symm
        simpa [valM, ha_mu] using hpos
    | some wmu =>
        have hne_wmu : wmu ≠ w := by
          intro heq
          have hw_a : mu.w_match w = some a := by
            simpa [heq] using (mu.consistent_m a wmu).1 ha_mu
          have : some a = some r := by
            rw [← hw_a, hw_mu]
          exact hne (Option.some.inj this)
        by_cases hle : val_m a wmu ≤ val_m a w
        · have hneq : val_m a wmu ≠ val_m a w := by
            intro heq
            have hwmu_nonneg : 0 ≤ val_m a wmu := by
              simpa [valM, ha_mu] using hstable.1 a
            exact hne_wmu (hstrictM a wmu w hwmu_nonneg hw_nonneg heq)
          exact lt_of_le_of_ne hle hneq
        · have hbetter : val_m a w < val_m a wmu := lt_of_not_ge hle
          exact False.elim
            (hrejected mu hstable a wmu
              (hbetterRemoved wmu hbetter)
              (hnotCurrentBetter wmu hbetter)
              ha_mu)
  have hwomanPref' : valW val_w w (mu.w_match w) < val_w w a := by
    simpa [valW, hw_mu] using hwomanPref
  exact hstable.2.2 a w hmanPref hwomanPref'

lemma rejectStep_preserves_rejected_pair_impossible_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) {m : M} {w : W}
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile val_w)
    (hnozero : MenNoOutsideTie val_m)
    (hact : IsActiveMan val_m s m)
    (hwbest : BestRemainingWoman val_m s m w)
    (hreject :
      ¬ match s.w_match w with
        | none => 0 ≤ val_w w m
        | some m' => val_w w m' < val_w w m)
    (hinv : DAInvariants val_m val_w s)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s) :
    DARejectedPairImpossibleInvariant val_m val_w
      { s with m_proposals := removeProposal s m w } := by
  rcases hinv with ⟨hmanIR, hwomanIR, hmatchedProposed, _hwomanReject,
    hproposalOrder⟩
  intro mu hstable m0 w0 hnotNew hnotMatchNew
  rcases not_mem_of_not_mem_removeProposal s hnotNew with hnotOld | ⟨hm0, hw0⟩
  · exact hrejected mu hstable m0 w0 hnotOld hnotMatchNew
  · subst m0
    subst w0
    cases hcur : s.w_match w with
    | none =>
        intro hmu
        have hw_mu : mu.w_match w = some m := (mu.consistent_m m w).1 hmu
        have hwIR := hstable.2.1 w
        have hnotNonneg : ¬ 0 ≤ val_w w m := by
          simpa [hcur] using hreject
        have hnonneg : 0 ≤ val_w w m := by
          simpa [valW, hw_mu] using hwIR
        exact hnotNonneg hnonneg
    | some a =>
        have ha_match : s.m_match a = some w := (s.consistent a w).2 hcur
        have hne : a ≠ m := by
          intro h
          subst a
          rw [hact.1] at ha_match
          cases ha_match
        have hle : val_w w m ≤ val_w w a := by
          have hnotlt : ¬ val_w w a < val_w w m := by
            simpa [hcur] using hreject
          exact le_of_not_gt hnotlt
        have hwomanPref : val_w w m < val_w w a := by
          have hneq : val_w w m ≠ val_w w a := by
            intro heq
            have ha_nonneg : 0 ≤ val_w w a :=
              hwomanIR w a hcur
            have hm_nonneg : 0 ≤ val_w w m := by
              rw [heq]
              exact ha_nonneg
            exact hne ((hstrictW w m a hm_nonneg ha_nonneg heq).symm)
          exact lt_of_le_of_ne hle hneq
        refine stable_matching_excludes_rejected_pair_no_outside_tie
          val_m val_w s mu hstrictM hnozero hrejected hstable hne
          (hmanIR a w ha_match) ?_ ?_ hwomanPref
        · intro w' hbetter hmem
          have hnotCurrent : w ∉ s.m_proposals a :=
            hmatchedProposed a w ha_match
          have hnonneg : 0 ≤ val_m a w' := by
            have hcurIR : 0 ≤ val_m a w := hmanIR a w ha_match
            linarith
          have hle' := hproposalOrder a w w' hnotCurrent hmem hnonneg
          linarith
        · intro w' hbetter hmatch
          rw [ha_match] at hmatch
          injection hmatch with hw'
          subst w'
          linarith

lemma acceptStep_preserves_rejected_pair_impossible_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) {m : M} {w : W}
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hnozero : MenNoOutsideTie val_m)
    (hact : IsActiveMan val_m s m)
    (hwbest : BestRemainingWoman val_m s m w)
    (haccept :
      match s.w_match w with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s) :
    DARejectedPairImpossibleInvariant val_m val_w
      { m_match := fun m'' =>
          if m'' = m then some w
          else if s.w_match w = some m'' then none
          else s.m_match m''
        w_match := Function.update s.w_match w (some m)
        m_proposals := removeProposal s m w
        consistent := by
          simpa using acceptMatch_consistent s hact.1 } := by
  intro mu hstable m0 w0 hnotNew hnotMatchNew
  rcases not_mem_of_not_mem_removeProposal s hnotNew with hnotOld | ⟨hm0, hw0⟩
  · by_cases holdMatch : s.m_match m0 = some w0
    · have hm0_ne_m : m0 ≠ m := by
        intro hm0
        subst m0
        rw [hact.1] at holdMatch
        cases holdMatch
      by_cases hcur0 : s.w_match w = some m0
      · have holdW : s.m_match m0 = some w := (s.consistent m0 w).2 hcur0
        have hw0_eq : w0 = w := Option.some.inj (holdMatch.symm.trans holdW)
        subst w0
        have hne : m ≠ m0 := fun h => hm0_ne_m h.symm
        have hwomanPref : val_w w m0 < val_w w m := by
          simpa [hcur0] using haccept
        exact stable_matching_excludes_rejected_pair_no_outside_tie
          val_m val_w s mu hstrictM hnozero hrejected hstable hne
          hwbest.2.1
          (better_than_best_not_remaining_of_best val_m s hwbest)
          (by
            intro w' _ hmatch
            rw [hact.1] at hmatch
            cases hmatch)
          hwomanPref
      · exact False.elim (hnotMatchNew (by simpa [hm0_ne_m, hcur0] using holdMatch))
    · exact hrejected mu hstable m0 w0 hnotOld holdMatch
  · subst m0
    subst w0
    exact False.elim (hnotMatchNew (by simp))

theorem daStep_preserves_rejected_pair_impossible_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile val_w)
    (hnozero : MenNoOutsideTie val_m) :
    ∀ s, DAInvariants val_m val_w s →
      DARejectedPairImpossibleInvariant val_m val_w s →
        DARejectedPairImpossibleInvariant val_m val_w
          (daStep val_m val_w s) := by
  intro s hinv hrejected
  classical
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · unfold daStep
    rw [dif_pos hactive]
    let m := Classical.choose hactive
    have hact : IsActiveMan val_m s m := by
      simpa [m] using Classical.choose_spec hactive
    let w_exists := exists_best_woman val_m s m hact
    let w := Classical.choose w_exists
    have hwbest : BestRemainingWoman val_m s m w := by
      simpa [w, w_exists] using Classical.choose_spec w_exists
    let accepts : Prop :=
      match s.w_match w with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m
    by_cases hacc : accepts
    · simpa [m, hact, w_exists, w, accepts, hacc] using
        acceptStep_preserves_rejected_pair_impossible_no_outside_tie
          val_m val_w s hstrictM hnozero hact hwbest hacc hrejected
    · simpa [m, hact, w_exists, w, accepts, hacc] using
        rejectStep_preserves_rejected_pair_impossible_no_outside_tie
          val_m val_w s hstrictM hstrictW hnozero hact hwbest hacc hinv
          hrejected
  · simpa [daStep, hactive] using hrejected

theorem daStepByMan_preserves_rejected_pair_impossible_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile val_w)
    (hnozero : MenNoOutsideTie val_m) :
    ∀ s m, DAInvariants val_m val_w s →
      DARejectedPairImpossibleInvariant val_m val_w s →
        DARejectedPairImpossibleInvariant val_m val_w
          (daStepByMan val_m val_w s m) := by
  intro s m hinv hrejected
  classical
  unfold daStepByMan
  by_cases hact : IsActiveMan val_m s m
  · rw [dif_pos hact]
    let w_exists := exists_best_woman val_m s m hact
    let w := Classical.choose w_exists
    have hwbest : BestRemainingWoman val_m s m w := by
      simpa [w, w_exists] using Classical.choose_spec w_exists
    let accepts : Prop :=
      match s.w_match w with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m
    by_cases hacc : accepts
    · simpa [w_exists, w, accepts, hacc] using
        acceptStep_preserves_rejected_pair_impossible_no_outside_tie
          val_m val_w s hstrictM hnozero hact hwbest hacc hrejected
    · simpa [w_exists, w, accepts, hacc] using
        rejectStep_preserves_rejected_pair_impossible_no_outside_tie
          val_m val_w s hstrictM hstrictW hnozero hact hwbest hacc hinv
          hrejected
  · simpa [hact] using hrejected

lemma foldl_daStep_preserves_rejected_pair_impossible_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : List ℕ) (s : DAState M W)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile val_w)
    (hnozero : MenNoOutsideTie val_m)
    (hinv : DAInvariants val_m val_w s)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s) :
    DARejectedPairImpossibleInvariant val_m val_w
      (steps.foldl (fun s _ => daStep val_m val_w s) s) := by
  induction steps generalizing s with
  | nil =>
      simpa using hrejected
  | cons _ steps ih =>
      rw [List.foldl_cons]
      exact ih (daStep val_m val_w s)
        (daStep_preserves_invariants_certificate val_m val_w s hinv)
        (daStep_preserves_rejected_pair_impossible_no_outside_tie val_m val_w
          hstrictM hstrictW hnozero s hinv hrejected)

lemma foldl_daStepByMan_preserves_rejected_pair_impossible_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (schedule : List M) (s : DAState M W)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile val_w)
    (hnozero : MenNoOutsideTie val_m)
    (hinv : DAInvariants val_m val_w s)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s) :
    DARejectedPairImpossibleInvariant val_m val_w
      (schedule.foldl (fun s m => daStepByMan val_m val_w s m) s) := by
  induction schedule generalizing s with
  | nil =>
      simpa using hrejected
  | cons m schedule ih =>
      rw [List.foldl_cons]
      exact ih (daStepByMan val_m val_w s m)
        (daStepByMan_preserves_invariants val_m val_w s m hinv)
        (daStepByMan_preserves_rejected_pair_impossible_no_outside_tie
          val_m val_w hstrictM hstrictW hnozero s m hinv hrejected)

theorem daStateAfterSchedule_satisfies_rejected_pair_impossible_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (start : DAState M W) (schedule : List M)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile val_w)
    (hnozero : MenNoOutsideTie val_m)
    (hinvStart : DAInvariants val_m val_w start)
    (hrejectedStart : DARejectedPairImpossibleInvariant val_m val_w start) :
    DARejectedPairImpossibleInvariant val_m val_w
      (daStateAfterSchedule val_m val_w start schedule) := by
  unfold daStateAfterSchedule
  exact foldl_daStepByMan_preserves_rejected_pair_impossible_no_outside_tie
    val_m val_w schedule start hstrictM hstrictW hnozero hinvStart
    hrejectedStart

theorem deferredAcceptanceState_satisfies_rejected_pair_impossible_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile val_w)
    (hnozero : MenNoOutsideTie val_m) :
    DARejectedPairImpossibleInvariant val_m val_w
      (deferredAcceptanceState val_m val_w) := by
  unfold deferredAcceptanceState
  exact foldl_daStep_preserves_rejected_pair_impossible_no_outside_tie
    val_m val_w
    (List.range (Fintype.card M * Fintype.card W))
    (initialDAState M W)
    hstrictM hstrictW hnozero
    (initialDAState_satisfies_invariants val_m val_w)
    (initialDAState_satisfies_rejected_pair_impossible val_m val_w)

def DaIsMenOptimalCertificate (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  ∀ mu', IsStable val_m val_w mu' →
    ∀ m, valM val_m m (mu'.m_match m) ≤ valM val_m m ((deferredAcceptance val_m val_w).m_match m)

/--
Any terminal DA state satisfying the standard invariants and the rejected-pair
certificate is men-optimal among stable matchings.  This is the schedule-free
core of proposer optimality; `deferredAcceptanceState` is only one way to
produce such a terminal state.
-/
theorem daState_is_men_optimal_of_rejected_pair_impossible
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hinv : DAInvariants val_m val_w s)
    (hterm : ¬ ∃ m, IsActiveMan val_m s m)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s) :
    ∀ mu', IsStable val_m val_w mu' →
      ∀ m, valM val_m m (mu'.m_match m) ≤ valM val_m m (s.m_match m) := by
  intro mu hstable m
  rcases hinv with ⟨hmanIR, _hwomanIR, hmatchedProposed, _hwomanReject,
    hproposalOrder⟩
  by_contra hnot
  have hgt :
      valM val_m m (s.m_match m) < valM val_m m (mu.m_match m) :=
    lt_of_not_ge hnot
  cases hmu : mu.m_match m with
  | none =>
      have hfinalIR : 0 ≤ valM val_m m (s.m_match m) := by
        cases hfinal : s.m_match m with
        | none =>
            simp [valM]
        | some w =>
            simpa [valM, hfinal] using hmanIR m w hfinal
      simp [valM, hmu] at hgt
      simp [valM] at hfinalIR
      linarith
  | some w =>
      have hnotFinal : s.m_match m ≠ some w := by
        intro hfinal
        simp [valM, hmu, hfinal] at hgt
      have hnotRemaining : w ∉ s.m_proposals m := by
        intro hremaining
        cases hfinal : s.m_match m with
        | none =>
            have hpositive : 0 < val_m m w := by
              simpa [valM, hmu, hfinal] using hgt
            exact hterm ⟨m, hfinal, ⟨w, hremaining, le_of_lt hpositive⟩⟩
        | some wcur =>
            have hnotCurrentRemaining : wcur ∉ s.m_proposals m :=
              hmatchedProposed m wcur hfinal
            have hbetter : val_m m wcur < val_m m w := by
              simpa [valM, hmu, hfinal] using hgt
            have hnonneg : 0 ≤ val_m m w := by
              have hcurIR : 0 ≤ val_m m wcur := hmanIR m wcur hfinal
              linarith
            have hle := hproposalOrder m wcur w hnotCurrentRemaining
              hremaining hnonneg
            linarith
      exact hrejected mu hstable m w hnotRemaining hnotFinal hmu

theorem da_is_men_optimal_of_rejected_pair_impossible
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstate : DAStateInvariantCertificate val_m val_w)
    (hterm : DATerminationCertificate val_m val_w)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w
      (deferredAcceptanceState val_m val_w)) :
    DaIsMenOptimalCertificate val_m val_w := by
  unfold DaIsMenOptimalCertificate
  intro mu hstable m
  change valM val_m m (mu.m_match m) ≤
    valM val_m m ((deferredAcceptanceState val_m val_w).m_match m)
  exact
    daState_is_men_optimal_of_rejected_pair_impossible val_m val_w
      (deferredAcceptanceState val_m val_w)
      hstate hterm hrejected mu hstable m

theorem da_is_men_optimal_of_strict_preferences
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hstrictW : WomenStrictPreferenceProfile val_w)
    (hacceptable : AllPairsAcceptable val_m val_w) :
    DaIsMenOptimalCertificate val_m val_w :=
  da_is_men_optimal_of_rejected_pair_impossible val_m val_w
    (deferredAcceptanceState_satisfies_invariants_closed val_m val_w)
    (deferredAcceptanceState_terminated val_m val_w)
    (deferredAcceptanceState_satisfies_rejected_pair_impossible val_m val_w
      hstrictM hstrictW hacceptable)

/--
Men-proposing deferred acceptance is proposer-optimal in an optional market
when proposers are strict on acceptable partners, no proposer is indifferent
to being unmatched, and receivers are strict on acceptable partners.

Unlike `da_is_men_optimal_of_strict_preferences`, this theorem allows several
unacceptable partners to tie below the outside option.  The no-outside-tie
condition is exactly what turns an individually-rational proposed pair into a
strict improvement over being unmatched in the rejected-pair argument.
-/
theorem da_is_men_optimal_of_acceptably_strict_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile val_w)
    (hnozero : MenNoOutsideTie val_m) :
    DaIsMenOptimalCertificate val_m val_w := by
  exact
    da_is_men_optimal_of_rejected_pair_impossible val_m val_w
      (deferredAcceptanceState_satisfies_invariants_closed val_m val_w)
      (deferredAcceptanceState_terminated val_m val_w)
      (deferredAcceptanceState_satisfies_rejected_pair_impossible_no_outside_tie
        val_m val_w hstrictM hstrictW hnozero)

/-- A stable matching that every man weakly prefers to every other stable matching. -/
def IsMenOptimalStable
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  IsStable val_m val_w mu ∧
    ∀ nu, IsStable val_m val_w nu →
      ∀ m, valM val_m m (nu.m_match m) ≤ valM val_m m (mu.m_match m)

/--
A terminal DA state with the standard invariants and rejected-pair certificate
is itself a men-optimal stable matching.
-/
theorem daState_assignment_is_men_optimal_stable_of_rejected_pair_impossible
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hinv : DAInvariants val_m val_w s)
    (hterm : ¬ ∃ m, IsActiveMan val_m s m)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s) :
    IsMenOptimalStable val_m val_w
      ⟨s.m_match, s.w_match, s.consistent⟩ := by
  refine ⟨?_, ?_⟩
  · exact stable_of_invariants_and_terminated val_m val_w s hinv hterm
  · exact
      daState_is_men_optimal_of_rejected_pair_impossible
        val_m val_w s hinv hterm hrejected

/--
Two complete matchings with the same man-side values are equal when men's
preferences over women are strict.
-/
theorem assignment_eq_of_complete_same_man_values_of_strict
    (val_m : M → W → ℝ) {mu nu : Assignment M W}
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hmuComplete : ∀ m, ∃ w, mu.m_match m = some w)
    (hnuComplete : ∀ m, ∃ w, nu.m_match m = some w)
    (hvalue : ∀ m, valM val_m m (mu.m_match m) =
      valM val_m m (nu.m_match m)) :
    mu = nu := by
  classical
  apply Assignment.ext_of_m_match
  intro m
  rcases hmuComplete m with ⟨wmu, hmu⟩
  rcases hnuComplete m with ⟨wnu, hnu⟩
  have hval : val_m m wmu = val_m m wnu := by
    simpa [valM, hmu, hnu] using hvalue m
  have hw : wmu = wnu := hstrictM m wmu wnu hval
  simpa [hmu, hnu, hw]

/--
Two matchings with the same man-side values are equal when men are strict over
women and no woman is tied with the outside option.  This is the incomplete-list
replacement for the complete-market uniqueness lemma.
-/
theorem assignment_eq_of_same_man_values_of_strict_no_outside_tie
    (val_m : M → W → ℝ) {mu nu : Assignment M W}
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hnozero : MenNoOutsideTie val_m)
    (hvalue : ∀ m, valM val_m m (mu.m_match m) =
      valM val_m m (nu.m_match m)) :
    mu = nu := by
  classical
  apply Assignment.ext_of_m_match
  intro m
  cases hmu : mu.m_match m with
  | none =>
      cases hnu : nu.m_match m with
      | none =>
          rfl
      | some wnu =>
          have hval : (0 : ℝ) = val_m m wnu := by
            simpa [valM, hmu, hnu] using hvalue m
          exact False.elim (hnozero m wnu hval.symm)
  | some wmu =>
      cases hnu : nu.m_match m with
      | none =>
          have hval : val_m m wmu = (0 : ℝ) := by
            simpa [valM, hmu, hnu] using hvalue m
          exact False.elim (hnozero m wmu hval)
      | some wnu =>
          have hval : val_m m wmu = val_m m wnu := by
            simpa [valM, hmu, hnu] using hvalue m
          have hw : wmu = wnu := hstrictM m wmu wnu hval
          simpa [hmu, hnu, hw]

/--
Two stable matchings with the same man-side values are equal when men are
strict over acceptable women and no woman is tied with the outside option.
-/
theorem assignment_eq_of_same_man_values_of_acceptably_strict_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {mu nu : Assignment M W}
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hnozero : MenNoOutsideTie val_m)
    (hmuStable : IsStable val_m val_w mu)
    (hnuStable : IsStable val_m val_w nu)
    (hvalue : ∀ m, valM val_m m (mu.m_match m) =
      valM val_m m (nu.m_match m)) :
    mu = nu := by
  classical
  apply Assignment.ext_of_m_match
  intro m
  cases hmu : mu.m_match m with
  | none =>
      cases hnu : nu.m_match m with
      | none =>
          rfl
      | some wnu =>
          have hval : (0 : ℝ) = val_m m wnu := by
            simpa [valM, hmu, hnu] using hvalue m
          exact False.elim (hnozero m wnu hval.symm)
  | some wmu =>
      cases hnu : nu.m_match m with
      | none =>
          have hval : val_m m wmu = (0 : ℝ) := by
            simpa [valM, hmu, hnu] using hvalue m
          exact False.elim (hnozero m wmu hval)
      | some wnu =>
          have hval : val_m m wmu = val_m m wnu := by
            simpa [valM, hmu, hnu] using hvalue m
          have hwmu_nonneg : 0 ≤ val_m m wmu := by
            simpa [valM, hmu] using hmuStable.1 m
          have hwnu_nonneg : 0 ≤ val_m m wnu := by
            simpa [valM, hnu] using hnuStable.1 m
          have hw : wmu = wnu :=
            hstrictM m wmu wnu hwmu_nonneg hwnu_nonneg hval
          simpa [hmu, hnu, hw]

/-- The men-optimal stable matching is unique among complete stable matchings. -/
theorem men_optimal_stable_matching_unique_of_complete
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {mu nu : Assignment M W}
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hmu : IsMenOptimalStable val_m val_w mu)
    (hnu : IsMenOptimalStable val_m val_w nu)
    (hmuComplete : ∀ m, ∃ w, mu.m_match m = some w)
    (hnuComplete : ∀ m, ∃ w, nu.m_match m = some w) :
    mu = nu := by
  refine assignment_eq_of_complete_same_man_values_of_strict
    val_m hstrictM hmuComplete hnuComplete ?_
  intro m
  exact le_antisymm (hnu.2 mu hmu.1 m) (hmu.2 nu hnu.1 m)

/--
The men-optimal stable matching is unique for incomplete lists when men's
values are strict over women and none ties the outside option.
-/
theorem men_optimal_stable_matching_unique_of_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {mu nu : Assignment M W}
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hnozero : MenNoOutsideTie val_m)
    (hmu : IsMenOptimalStable val_m val_w mu)
    (hnu : IsMenOptimalStable val_m val_w nu) :
    mu = nu := by
  refine assignment_eq_of_same_man_values_of_strict_no_outside_tie
    val_m hstrictM hnozero ?_
  intro m
  exact le_antisymm (hnu.2 mu hmu.1 m) (hmu.2 nu hnu.1 m)

/--
The men-optimal stable matching is unique for incomplete lists when men's
acceptable values are strict and none ties the outside option.
-/
theorem men_optimal_stable_matching_unique_of_acceptably_strict_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {mu nu : Assignment M W}
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hnozero : MenNoOutsideTie val_m)
    (hmu : IsMenOptimalStable val_m val_w mu)
    (hnu : IsMenOptimalStable val_m val_w nu) :
    mu = nu := by
  refine assignment_eq_of_same_man_values_of_acceptably_strict_no_outside_tie
    val_m val_w hstrictM hnozero hmu.1 hnu.1 ?_
  intro m
  exact le_antisymm (hnu.2 mu hmu.1 m) (hmu.2 nu hnu.1 m)

/--
On an equal-size all-acceptable marriage market, men-optimal stable matchings
are unique. This is the theorem-level uniqueness core behind proposal-order
independence statements.
-/
theorem men_optimal_stable_matching_unique_of_card_eq_all_pairs_acceptable
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {mu nu : Assignment M W}
    (hcard : Fintype.card M = Fintype.card W)
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hacceptable : AllPairsAcceptable val_m val_w)
    (hmu : IsMenOptimalStable val_m val_w mu)
    (hnu : IsMenOptimalStable val_m val_w nu) :
    mu = nu := by
  exact men_optimal_stable_matching_unique_of_complete
    val_m val_w hstrictM hmu hnu
    (stable_complete_of_card_eq_all_pairs_acceptable
      val_m val_w mu hcard hacceptable hmu.1).1
    (stable_complete_of_card_eq_all_pairs_acceptable
      val_m val_w nu hcard hacceptable hnu.1).1

/--
Schedule-independence bridge for complete strict markets: any terminal DA state
with the standard invariants and rejected-pair certificate gives the same
matching as the repository's folded `deferredAcceptance` implementation.
-/
theorem daState_assignment_eq_deferredAcceptance_of_rejected_pair_impossible
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hcard : Fintype.card M = Fintype.card W)
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hstrictW : WomenStrictPreferenceProfile val_w)
    (hacceptable : AllPairsAcceptable val_m val_w)
    (hinv : DAInvariants val_m val_w s)
    (hterm : ¬ ∃ m, IsActiveMan val_m s m)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s) :
    ⟨s.m_match, s.w_match, s.consistent⟩ =
      deferredAcceptance val_m val_w := by
  have hstate :
      IsMenOptimalStable val_m val_w
        ⟨s.m_match, s.w_match, s.consistent⟩ :=
    daState_assignment_is_men_optimal_stable_of_rejected_pair_impossible
      val_m val_w s hinv hterm hrejected
  have hda : IsMenOptimalStable val_m val_w
      (deferredAcceptance val_m val_w) := by
    exact
      ⟨da_produces_stable_matching val_m val_w,
        da_is_men_optimal_of_strict_preferences
          val_m val_w hstrictM hstrictW hacceptable⟩
  exact
    men_optimal_stable_matching_unique_of_card_eq_all_pairs_acceptable
      val_m val_w hcard hstrictM hacceptable hstate hda

/--
Schedule-independence bridge for incomplete strict markets with no outside
ties. Compared with the complete-market bridge, this theorem takes the
rejected-pair certificate for the repository DA state as an explicit input,
making the uniqueness step usable before that certificate is generalized away
from all-acceptable markets.
-/
theorem daState_assignment_eq_deferredAcceptance_of_rejected_pair_impossible_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hnozero : MenNoOutsideTie val_m)
    (hinv : DAInvariants val_m val_w s)
    (hterm : ¬ ∃ m, IsActiveMan val_m s m)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s)
    (hdaRejected : DARejectedPairImpossibleInvariant val_m val_w
      (deferredAcceptanceState val_m val_w)) :
    ⟨s.m_match, s.w_match, s.consistent⟩ =
      deferredAcceptance val_m val_w := by
  have hstate :
      IsMenOptimalStable val_m val_w
        ⟨s.m_match, s.w_match, s.consistent⟩ :=
    daState_assignment_is_men_optimal_stable_of_rejected_pair_impossible
      val_m val_w s hinv hterm hrejected
  have hda : IsMenOptimalStable val_m val_w
      (deferredAcceptance val_m val_w) := by
    refine ⟨da_produces_stable_matching val_m val_w, ?_⟩
    exact
      daState_is_men_optimal_of_rejected_pair_impossible val_m val_w
        (deferredAcceptanceState val_m val_w)
        (deferredAcceptanceState_satisfies_invariants_closed val_m val_w)
        (deferredAcceptanceState_terminated val_m val_w)
        hdaRejected
  exact
    men_optimal_stable_matching_unique_of_no_outside_tie
      val_m val_w hstrictM hnozero hstate hda

/--
Schedule-independence bridge for incomplete markets with acceptable-region
strict men values and no outside ties.
-/
theorem daState_assignment_eq_deferredAcceptance_of_rejected_pair_impossible_acceptably_strict_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hnozero : MenNoOutsideTie val_m)
    (hinv : DAInvariants val_m val_w s)
    (hterm : ¬ ∃ m, IsActiveMan val_m s m)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s)
    (hdaRejected : DARejectedPairImpossibleInvariant val_m val_w
      (deferredAcceptanceState val_m val_w)) :
    ⟨s.m_match, s.w_match, s.consistent⟩ =
      deferredAcceptance val_m val_w := by
  have hstate :
      IsMenOptimalStable val_m val_w
        ⟨s.m_match, s.w_match, s.consistent⟩ :=
    daState_assignment_is_men_optimal_stable_of_rejected_pair_impossible
      val_m val_w s hinv hterm hrejected
  have hda : IsMenOptimalStable val_m val_w
      (deferredAcceptance val_m val_w) := by
    refine ⟨da_produces_stable_matching val_m val_w, ?_⟩
    exact
      daState_is_men_optimal_of_rejected_pair_impossible val_m val_w
        (deferredAcceptanceState val_m val_w)
        (deferredAcceptanceState_satisfies_invariants_closed val_m val_w)
        (deferredAcceptanceState_terminated val_m val_w)
        hdaRejected
  exact
    men_optimal_stable_matching_unique_of_acceptably_strict_no_outside_tie
      val_m val_w hstrictM hnozero hstate hda

/--
A terminating scheduled deferred-acceptance run has the canonical
men-proposing outcome on an incomplete strict market.
-/
theorem daStateAfterSchedule_assignment_eq_deferredAcceptance_of_acceptably_strict_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (schedule : List M)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile val_w)
    (hnozero : MenNoOutsideTie val_m)
    (hterm : ¬ ∃ m, IsActiveMan val_m
      (daStateAfterSchedule val_m val_w (initialDAState M W) schedule) m) :
    let s := daStateAfterSchedule val_m val_w (initialDAState M W) schedule
    ⟨s.m_match, s.w_match, s.consistent⟩ = deferredAcceptance val_m val_w := by
  intro s
  exact
    daState_assignment_eq_deferredAcceptance_of_rejected_pair_impossible_acceptably_strict_no_outside_tie
      val_m val_w s hstrictM hnozero
      (daStateAfterSchedule_satisfies_invariants val_m val_w
        (initialDAState M W) schedule
        (initialDAState_satisfies_invariants val_m val_w))
      hterm
      (daStateAfterSchedule_satisfies_rejected_pair_impossible_no_outside_tie
        val_m val_w (initialDAState M W) schedule hstrictM hstrictW hnozero
        (initialDAState_satisfies_invariants val_m val_w)
        (initialDAState_satisfies_rejected_pair_impossible val_m val_w))
      (deferredAcceptanceState_satisfies_rejected_pair_impossible_no_outside_tie
        val_m val_w hstrictM hstrictW hnozero)

/--
On an equal-size all-acceptable strict marriage market, the men-proposing DA
outcome is women-pessimal among stable matchings.

The proof uses men-optimality: if some woman strictly preferred her
men-proposing DA partner to her partner in another stable matching, then that
DA partner weakly prefers his DA wife to his partner in the other stable
matching. Strict preferences make this a strict preference unless the pair is
already matched there, so the pair blocks the other stable matching.
-/
theorem da_is_women_pessimal_of_strict_preferences
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hstrictW : WomenStrictPreferenceProfile val_w)
    (hacceptable : AllPairsAcceptable val_m val_w) :
    ∀ mu, IsStable val_m val_w mu →
      ∀ w, valW val_w w ((deferredAcceptance val_m val_w).w_match w) ≤
        valW val_w w (mu.w_match w) := by
  classical
  intro mu hstable w
  by_contra hnot
  have hw_gt :
      valW val_w w (mu.w_match w) <
        valW val_w w ((deferredAcceptance val_m val_w).w_match w) :=
    lt_of_not_ge hnot
  have hdaComplete :=
    deferredAcceptance_complete_of_card_eq_all_pairs_acceptable
      val_m val_w hcard hacceptable
  have hmuComplete :=
    stable_complete_of_card_eq_all_pairs_acceptable
      val_m val_w mu hcard hacceptable hstable
  rcases hdaComplete.2 w with ⟨m, hda_w⟩
  rcases hmuComplete.2 w with ⟨m', hmu_w⟩
  have hda_m : (deferredAcceptance val_m val_w).m_match m = some w :=
    ((deferredAcceptance val_m val_w).consistent_m m w).2 hda_w
  have hw_pref : val_w w m' < val_w w m := by
    simpa [valW, hmu_w, hda_w] using hw_gt
  have hm_ne : m ≠ m' := by
    intro hm
    subst m'
    exact (lt_irrefl (val_w w m)) hw_pref
  rcases hmuComplete.1 m with ⟨wmu, hmu_m⟩
  have hwmu_ne : wmu ≠ w := by
    intro hwmu
    subst wmu
    have hmu_w_from_m : mu.w_match w = some m :=
      (mu.consistent_m m w).1 hmu_m
    have : m = m' := Option.some.inj (hmu_w_from_m.symm.trans hmu_w)
    exact hm_ne this
  have hmenOpt :=
    da_is_men_optimal_of_strict_preferences
      val_m val_w hstrictM hstrictW hacceptable
  have hm_le :
      valM val_m m (mu.m_match m) ≤
        valM val_m m ((deferredAcceptance val_m val_w).m_match m) :=
    hmenOpt mu hstable m
  have hm_pref_le : val_m m wmu ≤ val_m m w := by
    simpa [valM, hmu_m, hda_m] using hm_le
  have hm_pref : val_m m wmu < val_m m w := by
    have hneq : val_m m wmu ≠ val_m m w := by
      intro heq
      exact hwmu_ne (hstrictM m wmu w heq)
    exact lt_of_le_of_ne hm_pref_le hneq
  have hm_blocks : valM val_m m (mu.m_match m) < val_m m w := by
    simpa [valM, hmu_m] using hm_pref
  have hw_blocks : valW val_w w (mu.w_match w) < val_w w m := by
    simpa [valW, hmu_w] using hw_pref
  exact hstable.2.2 m w hm_blocks hw_blocks

/--
In an optional market, the men-proposing deferred-acceptance outcome is
women-pessimal among stable matchings when preferences are strict on acceptable
partners and no proposer is tied with being unmatched.

Unlike `da_is_women_pessimal_of_strict_preferences`, this theorem permits
ties among unacceptable partners.  A strictly preferred DA partner is forced
to be matched; the remaining blocking-pair argument then uses only acceptable
partners and the no-outside-tie condition.
-/
theorem da_is_women_pessimal_of_acceptably_strict_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile val_w)
    (hnozero : MenNoOutsideTie val_m) :
    ∀ mu, IsStable val_m val_w mu →
      ∀ w, valW val_w w ((deferredAcceptance val_m val_w).w_match w) ≤
        valW val_w w (mu.w_match w) := by
  classical
  intro mu hstable w
  by_contra hnot
  have hw_gt :
      valW val_w w (mu.w_match w) <
        valW val_w w ((deferredAcceptance val_m val_w).w_match w) :=
    lt_of_not_ge hnot
  have hda_w_matched : ∃ m, (deferredAcceptance val_m val_w).w_match w = some m := by
    by_contra hnone
    simp only [not_exists] at hnone
    have hda_none : (deferredAcceptance val_m val_w).w_match w = none := by
      cases hda : (deferredAcceptance val_m val_w).w_match w with
      | none => rfl
      | some m => exact False.elim (hnone m hda)
    have hmu_nonneg : 0 ≤ valW val_w w (mu.w_match w) := hstable.2.1 w
    simp [valW, hda_none] at hw_gt
    cases hmu : mu.w_match w with
    | none => simp [valW, hmu] at hmu_nonneg hw_gt
    | some m =>
        simp [valW, hmu] at hmu_nonneg hw_gt
        linarith
  rcases hda_w_matched with ⟨m, hda_w⟩
  have hda_m : (deferredAcceptance val_m val_w).m_match m = some w :=
    ((deferredAcceptance val_m val_w).consistent_m m w).2 hda_w
  have hmenOpt :=
    da_is_men_optimal_of_acceptably_strict_no_outside_tie
      val_m val_w hstrictM hstrictW hnozero
  cases hmu_m : mu.m_match m with
  | none =>
      have hm_le : 0 ≤ val_m m w := by
        have := hmenOpt mu hstable m
        simpa [valM, hmu_m, hda_m] using this
      have hm_pos : 0 < val_m m w := lt_of_le_of_ne hm_le (Ne.symm (hnozero m w))
      have hm_blocks : valM val_m m (mu.m_match m) < val_m m w := by
        simpa [valM, hmu_m] using hm_pos
      have hw_blocks : valW val_w w (mu.w_match w) < val_w w m := by
        simpa [valW, hda_w] using hw_gt
      exact hstable.2.2 m w hm_blocks hw_blocks
  | some wmu =>
      have hwmu_ne : wmu ≠ w := by
        intro hwmu
        subst wmu
        have hmu_w : mu.w_match w = some m :=
          (mu.consistent_m m w).1 hmu_m
        have : val_w w m < val_w w m := by
          simpa [valW, hmu_w, hda_w] using hw_gt
        exact (lt_irrefl (val_w w m)) this
      have hm_le : val_m m wmu ≤ val_m m w := by
        have := hmenOpt mu hstable m
        simpa [valM, hmu_m, hda_m] using this
      have hmu_nonneg : 0 ≤ val_m m wmu := by
        simpa [valM, hmu_m] using hstable.1 m
      have hda_nonneg : 0 ≤ val_m m w := by
        simpa [valM, hda_m] using (da_produces_stable_matching val_m val_w).1 m
      have hm_ne : val_m m wmu ≠ val_m m w := by
        intro heq
        exact hwmu_ne (hstrictM m wmu w hmu_nonneg hda_nonneg heq)
      have hm_pref : val_m m wmu < val_m m w := lt_of_le_of_ne hm_le hm_ne
      have hm_blocks : valM val_m m (mu.m_match m) < val_m m w := by
        simpa [valM, hmu_m] using hm_pref
      have hw_blocks : valW val_w w (mu.w_match w) < val_w w m := by
        simpa [valW, hda_w] using hw_gt
      exact hstable.2.2 m w hm_blocks hw_blocks

/--
Women-proposing deferred acceptance, represented on the original `(M, W)` sides
by running men-proposing DA after swapping the two sides, then swapping the
assignment back.
-/
noncomputable def womenDeferredAcceptance
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Assignment M W :=
  (deferredAcceptance (M := W) (W := M) val_w val_m).swap

/-- Women-proposing deferred acceptance produces a stable matching. -/
theorem womenDeferredAcceptance_stable
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    IsStable val_m val_w (womenDeferredAcceptance val_m val_w) := by
  unfold womenDeferredAcceptance
  exact (isStable_swap_iff val_w val_m
    (deferredAcceptance (M := W) (W := M) val_w val_m)).2
    (da_produces_stable_matching val_w val_m)

/--
On strict all-acceptable markets, women-proposing deferred acceptance is
women-optimal among stable matchings.
-/
theorem womenDeferredAcceptance_is_women_optimal_of_strict_preferences
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hstrictW : WomenStrictPreferenceProfile val_w)
    (hacceptable : AllPairsAcceptable val_m val_w) :
    ∀ mu, IsStable val_m val_w mu →
      ∀ w, valW val_w w (mu.w_match w) ≤
        valW val_w w ((womenDeferredAcceptance val_m val_w).w_match w) := by
  intro mu hstable w
  have hswapStable : IsStable val_w val_m mu.swap :=
    (isStable_swap_iff val_m val_w mu).2 hstable
  have hopt :=
    da_is_men_optimal_of_strict_preferences
      (M := W) (W := M) val_w val_m
      hstrictW hstrictM ⟨hacceptable.2, hacceptable.1⟩
      mu.swap hswapStable w
  simpa [womenDeferredAcceptance, valM, valW] using hopt

/--
In an optional market, women-proposing deferred acceptance is women-optimal
among stable matchings when preferences are strict on acceptable partners and
no woman is tied with being unmatched.
-/
theorem womenDeferredAcceptance_is_women_optimal_of_acceptably_strict_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile val_w)
    (hnozero : WomenNoOutsideTie val_w) :
    ∀ mu, IsStable val_m val_w mu →
      ∀ w, valW val_w w (mu.w_match w) ≤
        valW val_w w ((womenDeferredAcceptance val_m val_w).w_match w) := by
  intro mu hstable w
  have hswapStable : IsStable val_w val_m mu.swap :=
    (isStable_swap_iff val_m val_w mu).2 hstable
  have hopt :=
    da_is_men_optimal_of_acceptably_strict_no_outside_tie
      (M := W) (W := M) val_w val_m hstrictW hstrictM hnozero
      mu.swap hswapStable w
  simpa [womenDeferredAcceptance, valM, valW] using hopt

/--
On an equal-size strict all-acceptable market, women-proposing deferred
acceptance is men-pessimal among stable matchings.
-/
theorem womenDeferredAcceptance_is_men_pessimal_of_strict_preferences
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hstrictW : WomenStrictPreferenceProfile val_w)
    (hacceptable : AllPairsAcceptable val_m val_w) :
    ∀ mu, IsStable val_m val_w mu →
      ∀ m, valM val_m m ((womenDeferredAcceptance val_m val_w).m_match m) ≤
        valM val_m m (mu.m_match m) := by
  intro mu hstable m
  have hswapStable : IsStable val_w val_m mu.swap :=
    (isStable_swap_iff val_m val_w mu).2 hstable
  have hpess :=
    da_is_women_pessimal_of_strict_preferences
      (M := W) (W := M) val_w val_m hcard.symm
      hstrictW hstrictM ⟨hacceptable.2, hacceptable.1⟩
      mu.swap hswapStable m
  simpa [womenDeferredAcceptance, valM, valW] using hpess

/--
In an optional market, women-proposing deferred acceptance is men-pessimal
among stable matchings when preferences are strict on acceptable partners and
no woman is tied with being unmatched.
-/
theorem womenDeferredAcceptance_is_men_pessimal_of_acceptably_strict_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile val_w)
    (hnozero : WomenNoOutsideTie val_w) :
    ∀ mu, IsStable val_m val_w mu →
      ∀ m, valM val_m m ((womenDeferredAcceptance val_m val_w).m_match m) ≤
        valM val_m m (mu.m_match m) := by
  intro mu hstable m
  have hswapStable : IsStable val_w val_m mu.swap :=
    (isStable_swap_iff val_m val_w mu).2 hstable
  have hpess :=
    da_is_women_pessimal_of_acceptably_strict_no_outside_tie
      (M := W) (W := M) val_w val_m hstrictW hstrictM hnozero
      mu.swap hswapStable m
  simpa [womenDeferredAcceptance, valM, valW] using hpess

/--
In an equally sized optional market, every stable matching has the same
unmatched men and women as men-proposing deferred acceptance.

The proof compares the two side-optimal DA outcomes.  Each one-sided inclusion
of unmatched agents follows from optimality and individual rationality; the
matched-men/matched-women bijection then turns the inclusions into equalities.
-/
theorem unmatched_iff_deferredAcceptance_of_acceptably_strict_no_outside_tie
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile val_w)
    (hnozeroM : MenNoOutsideTie val_m)
    (hnozeroW : WomenNoOutsideTie val_w)
    (mu : Assignment M W) (hstable : IsStable val_m val_w mu) :
    (∀ m, mu.m_match m = none ↔ (deferredAcceptance val_m val_w).m_match m = none) ∧
      ∀ w, mu.w_match w = none ↔ (deferredAcceptance val_m val_w).w_match w = none := by
  classical
  let da := deferredAcceptance val_m val_w
  let wda := womenDeferredAcceptance val_m val_w
  have hdaStable : IsStable val_m val_w da := da_produces_stable_matching val_m val_w
  have hwdaStable : IsStable val_m val_w wda :=
    womenDeferredAcceptance_stable val_m val_w
  have hmenOpt :=
    da_is_men_optimal_of_acceptably_strict_no_outside_tie
      val_m val_w hstrictM hstrictW hnozeroM
  have hwomenOpt :=
    womenDeferredAcceptance_is_women_optimal_of_acceptably_strict_no_outside_tie
      val_m val_w hstrictM hstrictW hnozeroW
  have hmenPess :=
    womenDeferredAcceptance_is_men_pessimal_of_acceptably_strict_no_outside_tie
      val_m val_w hstrictM hstrictW hnozeroW
  have hwomenPess :=
    da_is_women_pessimal_of_acceptably_strict_no_outside_tie
      val_m val_w hstrictM hstrictW hnozeroM
  have hda_to_wda_m : ∀ m, da.m_match m = none → wda.m_match m = none := by
    intro m hdaNone
    cases hwda : wda.m_match m with
    | none => rfl
    | some w =>
        have hle : val_m m w ≤ 0 := by
          have := hmenOpt wda hwdaStable m
          simpa [da, wda, valM, hdaNone, hwda] using this
        have hnonneg : 0 ≤ val_m m w := by
          simpa [wda, valM, hwda] using hwdaStable.1 m
        exact False.elim (hnozeroM m w (le_antisymm hle hnonneg))
  have hwda_to_da_w : ∀ w, wda.w_match w = none → da.w_match w = none := by
    intro w hwdaNone
    cases hda : da.w_match w with
    | none => rfl
    | some m =>
        have hle : val_w w m ≤ 0 := by
          have := hwomenOpt da hdaStable w
          simpa [da, wda, valW, hda, hwdaNone] using this
        have hnonneg : 0 ≤ val_w w m := by
          simpa [da, valW, hda] using hdaStable.2.1 w
        exact False.elim (hnozeroW w m (le_antisymm hle hnonneg))
  let menFromDa : {m : M // da.m_match m = none} →
      {m : M // wda.m_match m = none} := fun m => ⟨m, hda_to_wda_m m m.2⟩
  have hmenFromDa_injective : Function.Injective menFromDa := by
    intro x y hxy
    apply Subtype.ext
    have hvalues : (menFromDa x : M) = (menFromDa y : M) :=
      congrArg (fun z : {m : M // wda.m_match m = none} => (z : M)) hxy
    simpa [menFromDa] using hvalues
  have hmenCardLe :
      Fintype.card {m : M // da.m_match m = none} ≤
        Fintype.card {m : M // wda.m_match m = none} :=
    Fintype.card_le_of_injective menFromDa hmenFromDa_injective
  let womenFromWda : {w : W // wda.w_match w = none} →
      {w : W // da.w_match w = none} := fun w => ⟨w, hwda_to_da_w w w.2⟩
  have hwomenFromWda_injective : Function.Injective womenFromWda := by
    intro x y hxy
    apply Subtype.ext
    have hvalues : (womenFromWda x : W) = (womenFromWda y : W) :=
      congrArg (fun z : {w : W // da.w_match w = none} => (z : W)) hxy
    simpa [womenFromWda] using hvalues
  have hwomenCardLe :
      Fintype.card {w : W // wda.w_match w = none} ≤
        Fintype.card {w : W // da.w_match w = none} :=
    Fintype.card_le_of_injective womenFromWda hwomenFromWda_injective
  have hdaCard := Assignment.card_unmatched_men_eq_card_unmatched_women da hcard
  have hwdaCard := Assignment.card_unmatched_men_eq_card_unmatched_women wda hcard
  have hmenCard :
      Fintype.card {m : M // da.m_match m = none} =
        Fintype.card {m : M // wda.m_match m = none} := by
    apply Nat.le_antisymm hmenCardLe
    calc
      Fintype.card {m : M // wda.m_match m = none} =
          Fintype.card {w : W // wda.w_match w = none} := hwdaCard
      _ ≤ Fintype.card {w : W // da.w_match w = none} := hwomenCardLe
      _ = Fintype.card {m : M // da.m_match m = none} := hdaCard.symm
  have hwomenCard :
      Fintype.card {w : W // wda.w_match w = none} =
        Fintype.card {w : W // da.w_match w = none} := by
    apply Nat.le_antisymm hwomenCardLe
    calc
      Fintype.card {w : W // da.w_match w = none} =
          Fintype.card {m : M // da.m_match m = none} := hdaCard.symm
      _ ≤ Fintype.card {m : M // wda.m_match m = none} := hmenCardLe
      _ = Fintype.card {w : W // wda.w_match w = none} := hwdaCard
  have hda_iff_wda_m : ∀ m, da.m_match m = none ↔ wda.m_match m = none := by
    intro m
    constructor
    · exact hda_to_wda_m m
    · intro hwdaNone
      have hsurj : Function.Surjective menFromDa :=
        (Fintype.bijective_iff_injective_and_card menFromDa).2
          ⟨hmenFromDa_injective, hmenCard⟩ |>.2
      rcases hsurj ⟨m, hwdaNone⟩ with ⟨x, hx⟩
      have hxm : (x : M) = m := congrArg Subtype.val hx
      simpa [hxm] using x.2
  have hda_iff_wda_w : ∀ w, da.w_match w = none ↔ wda.w_match w = none := by
    intro w
    constructor
    · intro hdaNone
      have hsurj : Function.Surjective womenFromWda :=
        (Fintype.bijective_iff_injective_and_card womenFromWda).2
          ⟨hwomenFromWda_injective, hwomenCard⟩ |>.2
      rcases hsurj ⟨w, hdaNone⟩ with ⟨x, hx⟩
      have hxw : (x : W) = w := congrArg Subtype.val hx
      simpa [hxw] using x.2
    · exact hwda_to_da_w w
  refine ⟨?_, ?_⟩
  · intro m
    constructor
    · intro hmuNone
      have hwdaNone : wda.m_match m = none := by
        cases hwda : wda.m_match m with
        | none => rfl
        | some w =>
            have hle : val_m m w ≤ 0 := by
              have := hmenPess mu hstable m
              simpa [wda, valM, hwda, hmuNone] using this
            have hnonneg : 0 ≤ val_m m w := by
              simpa [wda, valM, hwda] using hwdaStable.1 m
            exact False.elim (hnozeroM m w (le_antisymm hle hnonneg))
      exact (hda_iff_wda_m m).mpr hwdaNone
    · intro hdaNone
      cases hmu : mu.m_match m with
      | none => rfl
      | some w =>
          have hle : val_m m w ≤ 0 := by
            have := hmenOpt mu hstable m
            simpa [da, valM, hmu, hdaNone] using this
          have hnonneg : 0 ≤ val_m m w := by
            simpa [valM, hmu] using hstable.1 m
          exact False.elim (hnozeroM m w (le_antisymm hle hnonneg))
  · intro w
    constructor
    · intro hmuNone
      cases hda : da.w_match w with
      | none => rfl
      | some m =>
          have hle : val_w w m ≤ 0 := by
            have := hwomenPess mu hstable w
            simpa [da, valW, hda, hmuNone] using this
          have hnonneg : 0 ≤ val_w w m := by
            simpa [da, valW, hda] using hdaStable.2.1 w
          exact False.elim (hnozeroW w m (le_antisymm hle hnonneg))
    · intro hdaNone
      have hwdaNone : wda.w_match w = none := (hda_iff_wda_w w).mp hdaNone
      cases hmu : mu.w_match w with
      | none => rfl
      | some m =>
          have hle : val_w w m ≤ 0 := by
            have := hwomenOpt mu hstable w
            simpa [wda, valW, hmu, hwdaNone] using this
          have hnonneg : 0 ≤ val_w w m := by
            simpa [valW, hmu] using hstable.2.1 w
          exact False.elim (hnozeroW w m (le_antisymm hle hnonneg))

/-- A DA state with invariants and no active man is stable. -/
theorem daState_stable_of_invariants_and_termination (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (hinv : DAInvariants val_m val_w s)
    (hterm : ¬ ∃ m, IsActiveMan val_m s m) :
    IsStable val_m val_w ⟨s.m_match, s.w_match, s.consistent⟩ :=
  stable_of_invariants_and_terminated val_m val_w s hinv hterm

/-- Stable matching from separated DA certificate components.

This gives a direct API that avoids unpacking `DaProducesStableMatchingCertificate`.
-/
theorem deferredAcceptance_stable_of_certificate
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstate : DAStateInvariantCertificate val_m val_w)
    (hterm : DATerminationCertificate val_m val_w) :
    IsStable val_m val_w (deferredAcceptance val_m val_w) :=
  stable_of_invariants_and_terminated
    val_m val_w
    (deferredAcceptanceState val_m val_w)
    hstate hterm

/-- Alias with the existing full DA certificate term. -/
theorem deferredAcceptance_stable_of_certificate'
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcert : DaProducesStableMatchingCertificate val_m val_w) :
    IsStable val_m val_w (deferredAcceptance val_m val_w) :=
  da_produces_stable_matching_of_certificate val_m val_w hcert

end Matching
end AppliedModelingLib
