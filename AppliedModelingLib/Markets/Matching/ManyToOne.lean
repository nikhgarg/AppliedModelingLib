import AppliedModelingLib.Markets.Matching.Basic
import AppliedModelingLib.Markets.Matching.DeferredAcceptance
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Sigma

/-!
# Many-to-One Matching

This module contains the reusable assignment and stability API for
college-admissions and hospitals/residents style markets with capacities.

## Main declarations

- `ManyToOneAssignment`: applicants assigned to at most one college, colleges
  assigned finite rosters.
- `ManyToOneAssignment.RespectsQuota`: roster sizes are bounded by quotas.
- `ManyToOne.IsStable`: individual rationality plus no applicant-college
  blocking pair.
- `ManyToOneAssignment.ofOneToOne`: quota-one embedding of ordinary
  one-to-one assignments.
-/

namespace AppliedModelingLib
namespace Matching

/-- A many-to-one assignment between applicants and colleges. -/
structure ManyToOneAssignment (Applicants Colleges : Type*) where
  app_match : Applicants → Option Colleges
  college_roster : Colleges → Finset Applicants
  consistent : ∀ a c, app_match a = some c ↔ a ∈ college_roster c

namespace ManyToOneAssignment

/-- A many-to-one assignment respects college quotas. -/
def RespectsQuota {Applicants Colleges : Type*}
    (quota : Colleges → ℕ) (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  ∀ c, (mu.college_roster c).card ≤ quota c

/-- Embed a one-to-one assignment as a many-to-one assignment. -/
def ofOneToOne {Applicants Colleges : Type*}
    [Fintype Applicants] [DecidableEq Colleges]
    (mu : Assignment Applicants Colleges) :
    ManyToOneAssignment Applicants Colleges where
  app_match := mu.m_match
  college_roster c := (Finset.univ : Finset Applicants).filter fun a =>
    mu.m_match a = some c
  consistent a c := by
    constructor
    · intro h
      simp [h]
    · intro h
      exact (Finset.mem_filter.mp h).2

@[simp] theorem mem_college_roster_ofOneToOne_iff
    {Applicants Colleges : Type*} [Fintype Applicants] [DecidableEq Colleges]
    (mu : Assignment Applicants Colleges) (a : Applicants) (c : Colleges) :
    a ∈ (ofOneToOne mu).college_roster c ↔ mu.m_match a = some c := by
  simp [ofOneToOne]

/-- A one-to-one assignment satisfies quota one when viewed as many-to-one. -/
theorem ofOneToOne_respects_quota_one
    {Applicants Colleges : Type*}
    [Fintype Applicants] [DecidableEq Applicants] [DecidableEq Colleges]
    (mu : Assignment Applicants Colleges) :
    RespectsQuota (fun _ : Colleges => 1) (ofOneToOne mu) := by
  classical
  intro c
  exact Finset.card_le_one_iff.2 (by
    intro a b ha hb
    have ha_match : mu.m_match a = some c :=
      (mem_college_roster_ofOneToOne_iff mu a c).1 ha
    have hb_match : mu.m_match b = some c :=
      (mem_college_roster_ofOneToOne_iff mu b c).1 hb
    have hwa : mu.w_match c = some a := (mu.consistent_m a c).1 ha_match
    have hwb : mu.w_match c = some b := (mu.consistent_m b c).1 hb_match
    exact Option.some.inj (hwa.symm.trans hwb))

/-- Seat copies used to reduce a capacity-constrained college to one-to-one slots. -/
abbrev CollegeSeat {Colleges : Type*} (quota : Colleges → ℕ) :=
  Σ c, Fin (quota c)

/-- The college owning a cloned seat. -/
def CollegeSeat.college {Colleges : Type*} {quota : Colleges → ℕ}
    (seat : CollegeSeat quota) : Colleges :=
  seat.1

noncomputable instance instFintypeCollegeSeat {Colleges : Type*}
    [Fintype Colleges] (quota : Colleges → ℕ) :
    Fintype (CollegeSeat quota) := by
  classical
  infer_instance

noncomputable instance instDecidableEqCollegeSeat {Colleges : Type*}
    [DecidableEq Colleges] (quota : Colleges → ℕ) :
    DecidableEq (CollegeSeat quota) := by
  classical
  infer_instance

/-- Applicant values for cloned seats: all seats of a college have the college value. -/
def applicantSeatValue {Applicants Colleges : Type*} {quota : Colleges → ℕ}
    (val_applicant : Applicants → Colleges → ℝ) :
    Applicants → CollegeSeat quota → ℝ :=
  fun a seat => val_applicant a seat.college

/-- College-side values for cloned seats: all seats of a college share its ranking. -/
def collegeSeatValue {Applicants Colleges : Type*} {quota : Colleges → ℕ}
    (val_college : Colleges → Applicants → ℝ) :
    CollegeSeat quota → Applicants → ℝ :=
  fun seat a => val_college seat.college a

/--
Collapse a one-to-one assignment between applicants and cloned college seats into
a many-to-one applicant/college assignment.
-/
noncomputable def ofSeatAssignment {Applicants Colleges : Type*}
    [Fintype Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (mu : Assignment Applicants (CollegeSeat quota)) :
    ManyToOneAssignment Applicants Colleges where
  app_match a := (mu.m_match a).map CollegeSeat.college
  college_roster c := (Finset.univ : Finset Applicants).filter fun a =>
    ∃ i : Fin (quota c), mu.m_match a = some ⟨c, i⟩
  consistent a c := by
    constructor
    · intro h
      cases hmatch : mu.m_match a with
      | none =>
          simp [hmatch] at h
      | some seat =>
          rcases seat with ⟨c0, i⟩
          simp [hmatch, CollegeSeat.college] at h
          subst c0
          simp [hmatch]
    · intro h
      rcases (Finset.mem_filter.mp h).2 with ⟨i, hi⟩
      simp [hi, CollegeSeat.college]

@[simp] theorem mem_college_roster_ofSeatAssignment_iff
    {Applicants Colleges : Type*}
    [Fintype Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (mu : Assignment Applicants (CollegeSeat quota))
    (a : Applicants) (c : Colleges) :
    a ∈ (ofSeatAssignment quota mu).college_roster c ↔
      ∃ i : Fin (quota c), mu.m_match a = some ⟨c, i⟩ := by
  simp [ofSeatAssignment]

/-- Collapsing cloned seats always respects the original college quotas. -/
theorem ofSeatAssignment_respects_quota
    {Applicants Colleges : Type*}
    [Fintype Applicants] [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (mu : Assignment Applicants (CollegeSeat quota)) :
    RespectsQuota quota (ofSeatAssignment quota mu) := by
  classical
  intro c
  let roster := (ofSeatAssignment quota mu).college_roster c
  let seatOfApplicant : {a // a ∈ roster} → Fin (quota c) := fun a =>
    Classical.choose
      ((mem_college_roster_ofSeatAssignment_iff quota mu a.1 c).1 a.2)
  have hseat_spec :
      ∀ a : {a // a ∈ roster},
        mu.m_match a.1 = some ⟨c, seatOfApplicant a⟩ := by
    intro a
    exact Classical.choose_spec
      ((mem_college_roster_ofSeatAssignment_iff quota mu a.1 c).1 a.2)
  have hinj : Function.Injective seatOfApplicant := by
    intro a b hseat
    have ha_match := hseat_spec a
    have hb_match := hseat_spec b
    have ha_w : mu.w_match ⟨c, seatOfApplicant a⟩ = some a.1 :=
      (mu.consistent_m a.1 ⟨c, seatOfApplicant a⟩).1 ha_match
    have hb_w : mu.w_match ⟨c, seatOfApplicant b⟩ = some b.1 :=
      (mu.consistent_m b.1 ⟨c, seatOfApplicant b⟩).1 hb_match
    rw [hseat] at ha_w
    exact Subtype.ext (Option.some.inj (ha_w.symm.trans hb_w))
  have hcard :
      Fintype.card {a // a ∈ roster} ≤ Fintype.card (Fin (quota c)) :=
    Fintype.card_le_of_injective seatOfApplicant hinj
  have hcardRoster : roster.card ≤ quota c := by
    simpa [Fintype.card_coe] using hcard
  change roster.card ≤ quota c
  exact hcardRoster

/--
If a collapsed college roster has room, then some cloned seat of that college is
empty in the one-to-one seat assignment.
-/
theorem exists_empty_seat_of_card_lt_quota
    {Applicants Colleges : Type*}
    [Fintype Applicants] [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (mu : Assignment Applicants (CollegeSeat quota))
    {c : Colleges}
    (hroom : ((ofSeatAssignment quota mu).college_roster c).card < quota c) :
    ∃ i : Fin (quota c), mu.w_match ⟨c, i⟩ = none := by
  classical
  by_contra hno
  have hsome :
      ∀ i : Fin (quota c), ∃ a : Applicants, mu.w_match ⟨c, i⟩ = some a := by
    intro i
    cases hmatch : mu.w_match ⟨c, i⟩ with
    | none =>
        exact False.elim (hno ⟨i, hmatch⟩)
    | some a =>
        exact ⟨a, rfl⟩
  let roster := (ofSeatAssignment quota mu).college_roster c
  let appOfSeat : Fin (quota c) → {a // a ∈ roster} := fun i =>
    let a := Classical.choose (hsome i)
    ⟨a, by
      have hwa : mu.w_match ⟨c, i⟩ = some a := Classical.choose_spec (hsome i)
      have ham : mu.m_match a = some ⟨c, i⟩ := (mu.consistent_m a ⟨c, i⟩).2 hwa
      exact (mem_college_roster_ofSeatAssignment_iff quota mu a c).2 ⟨i, ham⟩⟩
  have h_app_spec :
      ∀ i : Fin (quota c), mu.w_match ⟨c, i⟩ = some (appOfSeat i).1 := by
    intro i
    exact Classical.choose_spec (hsome i)
  have hinj : Function.Injective appOfSeat := by
    intro i j hij
    have hiw := h_app_spec i
    have hjw := h_app_spec j
    have him : mu.m_match (appOfSeat i).1 = some ⟨c, i⟩ :=
      (mu.consistent_m (appOfSeat i).1 ⟨c, i⟩).2 hiw
    have hjm : mu.m_match (appOfSeat j).1 = some ⟨c, j⟩ :=
      (mu.consistent_m (appOfSeat j).1 ⟨c, j⟩).2 hjw
    have happ : (appOfSeat i).1 = (appOfSeat j).1 :=
      congrArg Subtype.val hij
    rw [happ] at him
    have hseat : (⟨c, i⟩ : CollegeSeat quota) = ⟨c, j⟩ :=
      Option.some.inj (him.symm.trans hjm)
    cases hseat
    rfl
  have hle :
      Fintype.card (Fin (quota c)) ≤ Fintype.card {a // a ∈ roster} :=
    Fintype.card_le_of_injective appOfSeat hinj
  have hleRoster : quota c ≤ roster.card := by
    simpa [Fintype.card_coe] using hle
  exact (not_lt_of_ge hleRoster) hroom

end ManyToOneAssignment

namespace ManyToOne

/-- Applicant utility from an optional college assignment. -/
def valApplicant {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (a : Applicants) (c : Option Colleges) : ℝ :=
  match c with
  | none => 0
  | some c' => val_applicant a c'

@[simp] theorem valApplicant_ofSeatAssignment_app_match
    {Applicants Colleges : Type*}
    [Fintype Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (mu : Assignment Applicants (ManyToOneAssignment.CollegeSeat quota))
    (a : Applicants) :
    valApplicant val_applicant a ((ManyToOneAssignment.ofSeatAssignment quota mu).app_match a) =
      valM (ManyToOneAssignment.applicantSeatValue (quota := quota) val_applicant)
        a (mu.m_match a) := by
  cases hmatch : mu.m_match a with
  | none =>
      simp [ManyToOneAssignment.ofSeatAssignment, valApplicant, valM, hmatch]
  | some seat =>
      cases seat
      simp [ManyToOneAssignment.ofSeatAssignment, valApplicant, valM,
        ManyToOneAssignment.applicantSeatValue,
        ManyToOneAssignment.CollegeSeat.college, hmatch]

/--
College `c` would accept applicant `a` relative to roster `s`: either `c` has a
free acceptable seat or `c` strictly prefers `a` to some currently assigned
applicant.
-/
def CollegeWouldAccept {Applicants Colleges : Type*}
    (val_college : Colleges → Applicants → ℝ)
    (quota : Colleges → ℕ) (s : Finset Applicants)
    (a : Applicants) (c : Colleges) : Prop :=
  (0 < val_college c a ∧ s.card < quota c) ∨
    ∃ a' ∈ s, val_college c a' < val_college c a

/-- Stability for many-to-one college-admissions/hospital-resident assignments. -/
def IsStable {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (quota : Colleges → ℕ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  ManyToOneAssignment.RespectsQuota quota mu ∧
    (∀ a, 0 ≤ valApplicant val_applicant a (mu.app_match a)) ∧
    (∀ c a, a ∈ mu.college_roster c → 0 ≤ val_college c a) ∧
    (∀ a c,
      valApplicant val_applicant a (mu.app_match a) < val_applicant a c →
        CollegeWouldAccept val_college quota (mu.college_roster c) a c →
          False)

/--
Quota-one stability agrees with ordinary one-to-one stability under the
`ofOneToOne` embedding.
-/
theorem isStable_of_oneToOne_stable_quota_one
    {Applicants Colleges : Type*}
    [Fintype Applicants] [DecidableEq Applicants] [DecidableEq Colleges]
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : Assignment Applicants Colleges)
    (hstable : Matching.IsStable val_applicant val_college mu) :
    IsStable val_applicant val_college (fun _ : Colleges => 1)
      (ManyToOneAssignment.ofOneToOne mu) := by
  classical
  rcases hstable with ⟨happIR, hcollegeIR, hnoBlock⟩
  refine ⟨ManyToOneAssignment.ofOneToOne_respects_quota_one mu, ?_, ?_, ?_⟩
  · intro a
    simpa [valApplicant, ManyToOneAssignment.ofOneToOne, valM] using happIR a
  · intro c a ha
    have ha_match : mu.m_match a = some c :=
      (ManyToOneAssignment.mem_college_roster_ofOneToOne_iff mu a c).1 ha
    have hc_match : mu.w_match c = some a := (mu.consistent_m a c).1 ha_match
    simpa [valW, hc_match] using hcollegeIR c
  · intro a c happPref hcollegeAccept
    have happPref' : valM val_applicant a (mu.m_match a) < val_applicant a c := by
      simpa [valApplicant, ManyToOneAssignment.ofOneToOne, valM] using happPref
    have hcollegePref :
        valW val_college c (mu.w_match c) < val_college c a := by
      rcases hcollegeAccept with ⟨hpos, hroom⟩ | ⟨a', ha', hpref⟩
      · have hzero :
            ((ManyToOneAssignment.ofOneToOne mu).college_roster c).card = 0 :=
          Nat.lt_one_iff.mp (by simpa using hroom)
        have hrosterEmpty :
            (ManyToOneAssignment.ofOneToOne mu).college_roster c = ∅ :=
          Finset.card_eq_zero.mp hzero
        have hw_none : mu.w_match c = none := by
          apply Assignment.w_match_eq_none_of_forall_m_match_ne_some
          intro b hb
          have hb_mem :
              b ∈ (ManyToOneAssignment.ofOneToOne mu).college_roster c :=
            (ManyToOneAssignment.mem_college_roster_ofOneToOne_iff mu b c).2 hb
          simpa [hrosterEmpty] using hb_mem
        simpa [valW, hw_none] using hpos
      · have ha'_match : mu.m_match a' = some c :=
          (ManyToOneAssignment.mem_college_roster_ofOneToOne_iff mu a' c).1 ha'
        have hc_match : mu.w_match c = some a' := (mu.consistent_m a' c).1 ha'_match
        simpa [valW, hc_match] using hpref
    exact hnoBlock a c happPref' hcollegePref

/--
If a one-to-one matching over cloned college seats is stable, then the collapsed
many-to-one college assignment is stable.
-/
theorem isStable_of_seatAssignment_stable
    {Applicants Colleges : Type*}
    [Fintype Applicants] [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : Assignment Applicants (ManyToOneAssignment.CollegeSeat quota))
    (hstable :
      Matching.IsStable
        (ManyToOneAssignment.applicantSeatValue (quota := quota) val_applicant)
        (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
        mu) :
    IsStable val_applicant val_college quota
      (ManyToOneAssignment.ofSeatAssignment quota mu) := by
  classical
  rcases hstable with ⟨happIR, hcollegeIR, hnoBlock⟩
  refine ⟨ManyToOneAssignment.ofSeatAssignment_respects_quota quota mu, ?_, ?_, ?_⟩
  · intro a
    simpa using
      (happIR a)
  · intro c a ha
    rcases
      (ManyToOneAssignment.mem_college_roster_ofSeatAssignment_iff quota mu a c).1 ha
      with ⟨i, hai⟩
    have hseatMatch : mu.w_match ⟨c, i⟩ = some a :=
      (mu.consistent_m a ⟨c, i⟩).1 hai
    simpa [valW, ManyToOneAssignment.collegeSeatValue,
      ManyToOneAssignment.CollegeSeat.college, hseatMatch] using
      hcollegeIR ⟨c, i⟩
  · intro a c happPref hcollegeAccept
    have happPrefSeatBase :
        valM (ManyToOneAssignment.applicantSeatValue (quota := quota) val_applicant)
            a (mu.m_match a) < val_applicant a c := by
      simpa [valApplicant_ofSeatAssignment_app_match] using
        happPref
    rcases hcollegeAccept with ⟨hpos, hroom⟩ | ⟨a', ha', hpref⟩
    · rcases
        ManyToOneAssignment.exists_empty_seat_of_card_lt_quota quota mu hroom
        with ⟨i, hseatEmpty⟩
      have happPrefSeat :
          valM (ManyToOneAssignment.applicantSeatValue (quota := quota) val_applicant)
              a (mu.m_match a) <
            ManyToOneAssignment.applicantSeatValue (quota := quota) val_applicant
              a ⟨c, i⟩ := by
        simpa [ManyToOneAssignment.applicantSeatValue,
          ManyToOneAssignment.CollegeSeat.college] using happPrefSeatBase
      have hcollegePrefSeat :
          valW (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
              ⟨c, i⟩ (mu.w_match ⟨c, i⟩) <
            ManyToOneAssignment.collegeSeatValue (quota := quota) val_college
              ⟨c, i⟩ a := by
        simpa [valW, ManyToOneAssignment.collegeSeatValue,
          ManyToOneAssignment.CollegeSeat.college, hseatEmpty] using hpos
      exact hnoBlock a ⟨c, i⟩ happPrefSeat hcollegePrefSeat
    · rcases
        (ManyToOneAssignment.mem_college_roster_ofSeatAssignment_iff quota mu a' c).1 ha'
        with ⟨i, ha'i⟩
      have hseatMatch : mu.w_match ⟨c, i⟩ = some a' :=
        (mu.consistent_m a' ⟨c, i⟩).1 ha'i
      have happPrefSeat :
          valM (ManyToOneAssignment.applicantSeatValue (quota := quota) val_applicant)
              a (mu.m_match a) <
            ManyToOneAssignment.applicantSeatValue (quota := quota) val_applicant
              a ⟨c, i⟩ := by
        simpa [ManyToOneAssignment.applicantSeatValue,
          ManyToOneAssignment.CollegeSeat.college] using happPrefSeatBase
      have hcollegePrefSeat :
          valW (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
              ⟨c, i⟩ (mu.w_match ⟨c, i⟩) <
            ManyToOneAssignment.collegeSeatValue (quota := quota) val_college
              ⟨c, i⟩ a := by
        simpa [valW, ManyToOneAssignment.collegeSeatValue,
          ManyToOneAssignment.CollegeSeat.college, hseatMatch] using hpref
      exact hnoBlock a ⟨c, i⟩ happPrefSeat hcollegePrefSeat

/--
Many-to-one deferred acceptance via cloned college seats.

Each college `c` is replaced by `quota c` one-to-one seats, all sharing the
college's applicant ranking. The resulting one-to-one DA assignment is collapsed
back to a college roster assignment.
-/
noncomputable def deferredAcceptanceManyToOne
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ) :
    ManyToOneAssignment Applicants Colleges :=
  ManyToOneAssignment.ofSeatAssignment quota
    (deferredAcceptance
      (ManyToOneAssignment.applicantSeatValue (quota := quota) val_applicant)
      (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college))

/-- The cloned-seat many-to-one deferred-acceptance assignment is stable. -/
theorem deferredAcceptanceManyToOne_stable
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ) :
    IsStable val_applicant val_college quota
      (deferredAcceptanceManyToOne quota val_applicant val_college) := by
  unfold deferredAcceptanceManyToOne
  exact isStable_of_seatAssignment_stable quota val_applicant val_college
    (deferredAcceptance
      (ManyToOneAssignment.applicantSeatValue (quota := quota) val_applicant)
      (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college))
    (da_produces_stable_matching
      (ManyToOneAssignment.applicantSeatValue (quota := quota) val_applicant)
      (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college))

end ManyToOne

end Matching
end AppliedModelingLib
