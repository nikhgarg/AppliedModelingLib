import GS62CollegeAdmissions.SourceCompletion
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Prod.Lex

/-!
# Arbitrary-quota applicant optimality

This module proves Gale--Shapley Theorem 2.  The technical device is a strict
refinement of the cloned seats of each college.  The refinement preserves every
strict comparison between colleges and places the outside option at zero; it
only orders the otherwise identical seats of one college.  Every stable
many-to-one assignment is then lifted to a stable refined-seat assignment.
-/

namespace GS62CollegeAdmissions
open AppliedModelingLib.Matching
open scoped BigOperators

namespace ManyToOneOptimality

variable {Applicants Colleges : Type*}
  [Fintype Applicants] [Fintype Colleges]
  [DecidableEq Applicants] [DecidableEq Colleges]

abbrev Seat (quota : Colleges → ℕ) :=
  ManyToOneAssignment.CollegeSeat quota

/-- The properties needed of a strict refinement of cloned-seat values. -/
structure IsApplicantSeatRefinement
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (refined : Applicants → Seat quota → ℝ) : Prop where
  strict : ∀ a s t, refined a s = refined a t → s = t
  source_lt : ∀ a s t,
    val_applicant a s.1 < val_applicant a t.1 → refined a s < refined a t
  positive_iff : ∀ a s, 0 < refined a s ↔ 0 < val_applicant a s.1
  nonzero : ∀ a s, refined a s ≠ 0

private theorem exists_applicant_refinement_one
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (hnozero : ∀ a c, val_applicant a c ≠ 0)
    (a : Applicants) :
    ∃ refined : Seat quota → ℝ,
      (∀ s t, refined s = refined t → s = t) ∧
      (∀ s t, val_applicant a s.1 < val_applicant a t.1 →
        refined s < refined t) ∧
      (∀ s, 0 < refined s ↔ 0 < val_applicant a s.1) ∧
      ∀ s, refined s ≠ 0 := by
  classical
  let codeEquiv := Fintype.equivFin (Seat quota)
  let code : Option (Seat quota) → Fin (Fintype.card (Seat quota) + 1)
    | none => ⟨0, Nat.zero_lt_succ _⟩
    | some s => ⟨(codeEquiv s).1 + 1, Nat.succ_lt_succ (codeEquiv s).2⟩
  have hcode : Function.Injective code := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some y =>
            have hval := congrArg Fin.val hxy
            simp [code] at hval
    | some x =>
        cases y with
        | none =>
            have hval := congrArg Fin.val hxy
            simp [code] at hval
        | some y =>
            have hval : (codeEquiv x).1 = (codeEquiv y).1 := by
              have := congrArg Fin.val hxy
              simpa [code] using Nat.succ.inj this
            have hfin : codeEquiv x = codeEquiv y := Fin.ext hval
            exact congrArg some (codeEquiv.injective hfin)
  let base : Option (Seat quota) → ℝ
    | none => 0
    | some s => val_applicant a s.1
  let key : Option (Seat quota) →
      (ℝ ×ₗ Fin (Fintype.card (Seat quota) + 1)) :=
    fun x => toLex (base x, code x)
  have hkey : Function.Injective key := by
    intro x y hxy
    exact hcode (congrArg Prod.snd hxy)
  letI : LinearOrder (Option (Seat quota)) := LinearOrder.lift' key hkey
  let finToNat : Fin (Fintype.card (Option (Seat quota))) ↪o ℕ :=
    { toFun := fun i => i.1
      inj' := fun _ _ h => Fin.ext h
      map_rel_iff' := Iff.rfl }
  let embedding : Option (Seat quota) ↪o ℝ :=
    ((Fintype.orderIsoFinOfCardEq (Option (Seat quota)) rfl).symm.toOrderEmbedding).trans
      (finToNat.trans Nat.castOrderEmbedding)
  let refined : Seat quota → ℝ :=
    fun s => embedding (some s) - embedding none
  refine ⟨refined, ?_, ?_, ?_, ?_⟩
  · intro s t heq
    have hembed : embedding (some s) = embedding (some t) := by
      dsimp [refined] at heq
      linarith
    exact Option.some.inj (embedding.injective hembed)
  · intro s t hsource
    have hkeylt : key (some s) < key (some t) := by
      change toLex (val_applicant a s.1, code (some s)) <
        toLex (val_applicant a t.1, code (some t))
      exact Prod.Lex.left _ _ hsource
    have hoption : (some s : Option (Seat quota)) < some t := hkeylt
    have hembed : embedding (some s) < embedding (some t) :=
      embedding.lt_iff_lt.mpr hoption
    dsimp [refined]
    linarith
  · intro s
    constructor
    · intro hrefined
      by_contra hnot
      have hneg : val_applicant a s.1 < 0 :=
        lt_of_le_of_ne (le_of_not_gt hnot) (hnozero a s.1)
      have hkeylt : key (some s) < key none := by
        change toLex (val_applicant a s.1, code (some s)) <
          toLex (0, code none)
        exact Prod.Lex.left _ _ hneg
      have hoption : (some s : Option (Seat quota)) < none := hkeylt
      have hembed : embedding (some s) < embedding none :=
        embedding.lt_iff_lt.mpr hoption
      dsimp [refined] at hrefined
      linarith
    · intro hpositive
      have hkeylt : key none < key (some s) := by
        change toLex (0, code none) <
          toLex (val_applicant a s.1, code (some s))
        exact Prod.Lex.left _ _ hpositive
      have hoption : (none : Option (Seat quota)) < some s := hkeylt
      have hembed : embedding none < embedding (some s) :=
        embedding.lt_iff_lt.mpr hoption
      dsimp [refined]
      linarith
  · intro s hzero
    have hsign := hnozero a s.1
    rcases lt_or_gt_of_ne hsign with hneg | hpos
    · have hkeylt : key (some s) < key none := by
        change toLex (val_applicant a s.1, code (some s)) <
          toLex (0, code none)
        exact Prod.Lex.left _ _ hneg
      have hoption : (some s : Option (Seat quota)) < none := hkeylt
      have hembed : embedding (some s) < embedding none :=
        embedding.lt_iff_lt.mpr hoption
      dsimp [refined] at hzero
      linarith
    · exact (show 0 < refined s from
        (by
          apply (show 0 < refined s ↔ 0 < val_applicant a s.1 from ?_).2 hpos
          constructor
          · intro hrefined
            exact hpos
          · intro _
            have hkeylt : key none < key (some s) := by
              change toLex (0, code none) <
                toLex (val_applicant a s.1, code (some s))
              exact Prod.Lex.left _ _ hpos
            have hoption : (none : Option (Seat quota)) < some s := hkeylt
            have hembed : embedding none < embedding (some s) :=
              embedding.lt_iff_lt.mpr hoption
            dsimp [refined]
            linarith)) |>.ne' hzero

theorem exists_applicant_seat_refinement
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (hnozero : ∀ a c, val_applicant a c ≠ 0) :
    ∃ refined : Applicants → Seat quota → ℝ,
      IsApplicantSeatRefinement quota val_applicant refined := by
  classical
  choose refined hrefined using fun a =>
    exists_applicant_refinement_one quota val_applicant hnozero a
  refine ⟨refined, ?_⟩
  constructor
  · intro a
    exact (hrefined a).1
  · intro a
    exact (hrefined a).2.1
  · intro a
    exact (hrefined a).2.2.1
  · intro a
    exact (hrefined a).2.2.2

/-- A canonical choice of strict seat refinement. -/
noncomputable def refinedApplicantSeatValue
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (hnozero : ∀ a c, val_applicant a c ≠ 0) :
    Applicants → Seat quota → ℝ :=
  Classical.choose
    (exists_applicant_seat_refinement quota val_applicant hnozero)

theorem refinedApplicantSeatValue_spec
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (hnozero : ∀ a c, val_applicant a c ≠ 0) :
    IsApplicantSeatRefinement quota val_applicant
      (refinedApplicantSeatValue quota val_applicant hnozero) :=
  Classical.choose_spec
    (exists_applicant_seat_refinement quota val_applicant hnozero)

theorem source_lt_of_refined_lt_of_college_ne
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (refined : Applicants → Seat quota → ℝ)
    (hrefinement : IsApplicantSeatRefinement quota val_applicant refined)
    (hstrict : ∀ a c c', val_applicant a c = val_applicant a c' → c = c')
    (a : Applicants) (s t : Seat quota)
    (hne : s.1 ≠ t.1)
    (hrefined : refined a s < refined a t) :
    val_applicant a s.1 < val_applicant a t.1 := by
  rcases lt_trichotomy (val_applicant a s.1) (val_applicant a t.1) with
    hlt | heq | hgt
  · exact hlt
  · exact False.elim (hne (hstrict a s.1 t.1 heq))
  · have hreverse : refined a t < refined a s :=
      hrefinement.source_lt a t s hgt
    exact False.elim ((not_lt_of_ge (le_of_lt hreverse)) hrefined)

theorem refined_nonnegative_iff
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (hnozero : ∀ a c, val_applicant a c ≠ 0)
    (a : Applicants) (s : Seat quota) :
    0 ≤ refinedApplicantSeatValue quota val_applicant hnozero a s ↔
      0 ≤ val_applicant a s.1 := by
  have hspec := refinedApplicantSeatValue_spec quota val_applicant hnozero
  constructor
  · intro hrefined
    have hrefinedPos : 0 <
        refinedApplicantSeatValue quota val_applicant hnozero a s :=
      lt_of_le_of_ne hrefined (hspec.nonzero a s).symm
    exact le_of_lt ((hspec.positive_iff a s).1 hrefinedPos)
  · intro hsource
    have hsourcePos : 0 < val_applicant a s.1 :=
      lt_of_le_of_ne hsource (hnozero a s.1).symm
    exact le_of_lt ((hspec.positive_iff a s).2 hsourcePos)

theorem refined_men_strict
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (hnozero : ∀ a c, val_applicant a c ≠ 0) :
    MenStrictPreferenceProfile
      (refinedApplicantSeatValue quota val_applicant hnozero) :=
  (refinedApplicantSeatValue_spec quota val_applicant hnozero).strict

theorem refined_men_acceptably_strict
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (hnozero : ∀ a c, val_applicant a c ≠ 0) :
    MenAcceptableStrictPreferenceProfile
      (refinedApplicantSeatValue quota val_applicant hnozero) := by
  intro a s t _ _ heq
  exact (refinedApplicantSeatValue_spec quota val_applicant hnozero).strict
    a s t heq

theorem refined_men_no_outside_tie
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (hnozero : ∀ a c, val_applicant a c ≠ 0) :
    MenNoOutsideTie
      (refinedApplicantSeatValue quota val_applicant hnozero) :=
  (refinedApplicantSeatValue_spec quota val_applicant hnozero).nonzero

theorem college_seat_women_strict
    (quota : Colleges → ℕ)
    (val_college : Colleges → Applicants → ℝ)
    (hstrict : ∀ c a a', val_college c a = val_college c a' → a = a') :
    WomenStrictPreferenceProfile
      (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college) := by
  intro s a a' heq
  exact hstrict s.1 a a' heq

/-- Applicant-proposing DA in a strict refinement of the cloned-seat market. -/
noncomputable def refinedSeatDeferredAcceptance
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hnozero : ∀ a c, val_applicant a c ≠ 0) :
    Assignment Applicants (Seat quota) :=
  deferredAcceptance
    (refinedApplicantSeatValue quota val_applicant hnozero)
    (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)

/-- Collapse the strict-seat DA outcome back to college rosters. -/
noncomputable def refinedDeferredAcceptanceManyToOne
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hnozero : ∀ a c, val_applicant a c ≠ 0) :
    ManyToOneAssignment Applicants Colleges :=
  ManyToOneAssignment.ofSeatAssignment quota
    (refinedSeatDeferredAcceptance quota val_applicant val_college hnozero)

theorem refinedSeatDeferredAcceptance_stable
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hnozero : ∀ a c, val_applicant a c ≠ 0) :
    IsStable
      (refinedApplicantSeatValue quota val_applicant hnozero)
      (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
      (refinedSeatDeferredAcceptance quota val_applicant val_college hnozero) :=
  da_produces_stable_matching _ _

private theorem stable_refined_seats_implies_stable_source_seats
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hstrict : ∀ a c c', val_applicant a c = val_applicant a c' → c = c')
    (hnozero : ∀ a c, val_applicant a c ≠ 0)
    (mu : Assignment Applicants (Seat quota))
    (hstable : IsStable
      (refinedApplicantSeatValue quota val_applicant hnozero)
      (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college) mu) :
    IsStable
      (ManyToOneAssignment.applicantSeatValue (quota := quota) val_applicant)
      (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college) mu := by
  rcases hstable with ⟨happIR, hcollegeIR, hnoBlock⟩
  refine ⟨?_, hcollegeIR, ?_⟩
  · intro a
    cases hmatch : mu.m_match a with
    | none => simp [valM, hmatch]
    | some s =>
        have hrefined : 0 ≤
            refinedApplicantSeatValue quota val_applicant hnozero a s := by
          simpa [valM, hmatch] using happIR a
        have hsource := (refined_nonnegative_iff quota val_applicant hnozero a s).1
          hrefined
        simpa [valM, hmatch, ManyToOneAssignment.applicantSeatValue] using hsource
  · intro a t happPref hcollegePref
    have hrefinedPref :
        valM (refinedApplicantSeatValue quota val_applicant hnozero)
            a (mu.m_match a) <
          refinedApplicantSeatValue quota val_applicant hnozero a t := by
      cases hmatch : mu.m_match a with
      | none =>
          have hsourcePos : 0 < val_applicant a t.1 := by
            simpa [valM, hmatch,
              ManyToOneAssignment.applicantSeatValue] using happPref
          have hrefinedPos :=
            ((refinedApplicantSeatValue_spec quota val_applicant hnozero).positive_iff
              a t).2 hsourcePos
          simpa [valM, hmatch] using hrefinedPos
      | some s =>
          have hsourceLt : val_applicant a s.1 < val_applicant a t.1 := by
            simpa [valM, hmatch,
              ManyToOneAssignment.applicantSeatValue] using happPref
          have hrefinedLt :=
            (refinedApplicantSeatValue_spec quota val_applicant hnozero).source_lt
              a s t hsourceLt
          simpa [valM, hmatch] using hrefinedLt
    exact hnoBlock a t hrefinedPref hcollegePref

theorem refinedDeferredAcceptanceManyToOne_stable
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hstrict : ∀ a c c', val_applicant a c = val_applicant a c' → c = c')
    (hnozero : ∀ a c, val_applicant a c ≠ 0) :
    ManyToOne.IsStable val_applicant val_college quota
      (refinedDeferredAcceptanceManyToOne quota val_applicant val_college hnozero) := by
  unfold refinedDeferredAcceptanceManyToOne
  apply ManyToOne.isStable_of_seatAssignment_stable
  exact stable_refined_seats_implies_stable_source_seats
    quota val_applicant val_college hstrict hnozero _
      (refinedSeatDeferredAcceptance_stable
        quota val_applicant val_college hnozero)

theorem refinedSeatDeferredAcceptance_applicant_optimal
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (hcollegeStrict : ∀ c a a',
      val_college c a = val_college c a' → a = a') :
    ∀ nu : Assignment Applicants (Seat quota),
      IsStable
        (refinedApplicantSeatValue quota val_applicant happNoZero)
        (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college) nu →
      ∀ a,
        valM (refinedApplicantSeatValue quota val_applicant happNoZero)
            a (nu.m_match a) ≤
          valM (refinedApplicantSeatValue quota val_applicant happNoZero)
            a ((refinedSeatDeferredAcceptance quota val_applicant val_college
              happNoZero).m_match a) := by
  let refined := refinedApplicantSeatValue quota val_applicant happNoZero
  let seatCollege :=
    ManyToOneAssignment.collegeSeatValue (quota := quota) val_college
  have hrejected : DARejectedPairImpossibleInvariant refined seatCollege
      (deferredAcceptanceState refined seatCollege) :=
    deferredAcceptanceState_satisfies_rejected_pair_impossible_no_outside_tie
      refined seatCollege
      (refined_men_acceptably_strict quota val_applicant happNoZero)
      (college_seat_women_strict quota val_college hcollegeStrict).acceptablyStrict
      (refined_men_no_outside_tie quota val_applicant happNoZero)
  exact da_is_men_optimal_of_rejected_pair_impossible refined seatCollege
    (deferredAcceptanceState_satisfies_invariants_closed refined seatCollege)
    (deferredAcceptanceState_terminated refined seatCollege)
    hrejected

/-! ## Stable lifts of arbitrary many-to-one assignments -/

/-- Build a two-sided assignment from an injective partial proposer match. -/
noncomputable def assignmentOfPartialInjection
    {A B : Type*} (f : A → Option B)
    (hinjective : ∀ a a' b, f a = some b → f a' = some b → a = a') :
    Assignment A B := by
  classical
  exact
    { m_match := f
      w_match := fun b =>
        if h : ∃ a, f a = some b then some (Classical.choose h) else none
      consistent_m := by
        intro a b
        constructor
        · intro hab
          have hex : ∃ a', f a' = some b := ⟨a, hab⟩
          rw [dif_pos hex]
          have hchosen : f (Classical.choose hex) = some b :=
            Classical.choose_spec hex
          exact congrArg some (hinjective _ _ b hchosen hab)
        · intro hab
          by_cases hex : ∃ a', f a' = some b
          · rw [dif_pos hex] at hab
            have ha : Classical.choose hex = a := Option.some.inj hab
            simpa [ha] using Classical.choose_spec hex
          · rw [dif_neg hex] at hab
            cases hab }

abbrev Roster
    (nu : ManyToOneAssignment Applicants Colleges) (c : Colleges) :=
  {a : Applicants // a ∈ nu.college_roster c}

def localApplicantValue
    (quota : Colleges → ℕ)
    (refined : Applicants → Seat quota → ℝ)
    (nu : ManyToOneAssignment Applicants Colleges) (c : Colleges) :
    Roster nu c → Fin (quota c) → ℝ :=
  fun a i => refined a.1 ⟨c, i⟩

def localCollegeValue
    (quota : Colleges → ℕ)
    (val_college : Colleges → Applicants → ℝ)
    (nu : ManyToOneAssignment Applicants Colleges) (c : Colleges) :
    Fin (quota c) → Roster nu c → ℝ :=
  fun _i a => val_college c a.1

/-- A stable internal assignment of one college's roster to its cloned seats. -/
noncomputable def localRosterSeatAssignment
    (quota : Colleges → ℕ)
    (refined : Applicants → Seat quota → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (nu : ManyToOneAssignment Applicants Colleges) (c : Colleges) :
    Assignment (Roster nu c) (Fin (quota c)) :=
  deferredAcceptance
    (localApplicantValue quota refined nu c)
    (localCollegeValue (quota := quota) val_college nu c)

theorem localRosterSeatAssignment_stable
    (quota : Colleges → ℕ)
    (refined : Applicants → Seat quota → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (nu : ManyToOneAssignment Applicants Colleges) (c : Colleges) :
    IsStable
      (localApplicantValue quota refined nu c)
      (localCollegeValue (quota := quota) val_college nu c)
      (localRosterSeatAssignment quota refined val_college nu c) :=
  da_produces_stable_matching _ _

theorem localRosterSeatAssignment_applicant_complete
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (hcollegeNoZero : ∀ c a, val_college c a ≠ 0)
    (refined : Applicants → Seat quota → ℝ)
    (hrefined : IsApplicantSeatRefinement quota val_applicant refined)
    (nu : ManyToOneAssignment Applicants Colleges)
    (hnu : ManyToOne.IsStable val_applicant val_college quota nu)
    (c : Colleges) :
    ∀ a : Roster nu c, ∃ i,
      (localRosterSeatAssignment quota refined val_college nu c).m_match a =
        some i := by
  have hcard : Fintype.card (Roster nu c) ≤ Fintype.card (Fin (quota c)) := by
    simpa [Roster, Fintype.card_coe] using hnu.1 c
  have hallAcceptable : AllPairsAcceptable
      (localApplicantValue quota refined nu c)
      (localCollegeValue (quota := quota) val_college nu c) := by
    constructor
    · intro a i
      have hamatch : nu.app_match a.1 = some c := (nu.consistent a.1 c).2 a.2
      have happNonneg : 0 ≤ val_applicant a.1 c := by
        simpa [ManyToOne.valApplicant, hamatch] using hnu.2.1 a.1
      have happPos : 0 < val_applicant a.1 c :=
        lt_of_le_of_ne happNonneg (happNoZero a.1 c).symm
      exact hrefined.positive_iff a.1 ⟨c, i⟩ |>.2 happPos
    · intro i a
      have hcollegeNonneg : 0 ≤ val_college c a.1 :=
        hnu.2.2.1 c a.1 a.2
      exact lt_of_le_of_ne hcollegeNonneg (hcollegeNoZero c a.1).symm
  exact stable_left_complete_of_card_le_all_pairs_acceptable
    (localApplicantValue quota refined nu c)
    (localCollegeValue (quota := quota) val_college nu c)
    (localRosterSeatAssignment quota refined val_college nu c)
    hcard hallAcceptable
    (localRosterSeatAssignment_stable quota refined val_college nu c)

/-- Partial applicant-to-seat map obtained by internally seating every roster. -/
noncomputable def stableLiftMMatch
    (quota : Colleges → ℕ)
    (refined : Applicants → Seat quota → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (nu : ManyToOneAssignment Applicants Colleges) :
    Applicants → Option (Seat quota) :=
  fun a => (nu.app_match a).bind fun c =>
    if ha : a ∈ nu.college_roster c then
      Option.map (fun i => ⟨c, i⟩)
        ((localRosterSeatAssignment quota refined val_college nu c).m_match
          ⟨a, ha⟩)
    else none

private theorem stableLiftMMatch_injective
    (quota : Colleges → ℕ)
    (refined : Applicants → Seat quota → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (nu : ManyToOneAssignment Applicants Colleges) :
    ∀ a a' s,
      stableLiftMMatch quota refined val_college nu a = some s →
      stableLiftMMatch quota refined val_college nu a' = some s →
      a = a' := by
  classical
  intro a a' s ha ha'
  cases hmatch : nu.app_match a with
  | none =>
      simp [stableLiftMMatch, hmatch] at ha
  | some c =>
      cases hmatch' : nu.app_match a' with
      | none =>
          simp [stableLiftMMatch, hmatch'] at ha'
      | some c' =>
          have hac : a ∈ nu.college_roster c := (nu.consistent a c).1 hmatch
          have hac' : a' ∈ nu.college_roster c' := (nu.consistent a' c').1 hmatch'
          let ac : Roster nu c := ⟨a, hac⟩
          let ac' : Roster nu c' := ⟨a', hac'⟩
          cases hlocal :
              (localRosterSeatAssignment quota refined val_college nu c).m_match ac with
          | none => simp [stableLiftMMatch, hmatch, hac, ac, hlocal] at ha
          | some i =>
              cases hlocal' :
                  (localRosterSeatAssignment quota refined val_college nu c').m_match ac' with
              | none =>
                  simp [stableLiftMMatch, hmatch', hac', ac', hlocal'] at ha'
              | some i' =>
                  have hs : (⟨c, i⟩ : Seat quota) = ⟨c', i'⟩ := by
                    have has : (⟨c, i⟩ : Seat quota) = s := by
                      simpa [stableLiftMMatch, hmatch, hac, ac, hlocal] using ha
                    have ha's : (⟨c', i'⟩ : Seat quota) = s := by
                      simpa [stableLiftMMatch, hmatch', hac', ac', hlocal'] using ha'
                    exact has.trans ha's.symm
                  cases hs
                  have hw :=
                    ((localRosterSeatAssignment quota refined val_college nu c).consistent_m
                      ac i).1 hlocal
                  have hw' :=
                    ((localRosterSeatAssignment quota refined val_college nu c).consistent_m
                      ac' i).1 hlocal'
                  have hsub : ac = ac' := Option.some.inj (hw.symm.trans hw')
                  exact congrArg Subtype.val hsub

/-- A one-to-one refined-seat lift of a many-to-one assignment. -/
noncomputable def stableSeatLift
    (quota : Colleges → ℕ)
    (refined : Applicants → Seat quota → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (nu : ManyToOneAssignment Applicants Colleges) :
    Assignment Applicants (Seat quota) :=
  assignmentOfPartialInjection
    (stableLiftMMatch quota refined val_college nu)
    (stableLiftMMatch_injective quota refined val_college nu)

@[simp] theorem stableSeatLift_m_match
    (quota : Colleges → ℕ)
    (refined : Applicants → Seat quota → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (nu : ManyToOneAssignment Applicants Colleges) (a : Applicants) :
    (stableSeatLift quota refined val_college nu).m_match a =
      stableLiftMMatch quota refined val_college nu a := rfl

theorem stableSeatLift_collapse_app_match
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (hcollegeNoZero : ∀ c a, val_college c a ≠ 0)
    (refined : Applicants → Seat quota → ℝ)
    (hrefined : IsApplicantSeatRefinement quota val_applicant refined)
    (nu : ManyToOneAssignment Applicants Colleges)
    (hnu : ManyToOne.IsStable val_applicant val_college quota nu)
    (a : Applicants) :
    (ManyToOneAssignment.ofSeatAssignment quota
      (stableSeatLift quota refined val_college nu)).app_match a =
        nu.app_match a := by
  classical
  cases hmatch : nu.app_match a with
  | none =>
      change Option.map ManyToOneAssignment.CollegeSeat.college
        (stableLiftMMatch quota refined val_college nu a) = none
      simp [stableLiftMMatch, hmatch]
  | some c =>
      have hac : a ∈ nu.college_roster c := (nu.consistent a c).1 hmatch
      let ac : Roster nu c := ⟨a, hac⟩
      rcases localRosterSeatAssignment_applicant_complete
        quota val_applicant val_college happNoZero hcollegeNoZero
        refined hrefined nu hnu c ac with ⟨i, hi⟩
      change Option.map ManyToOneAssignment.CollegeSeat.college
        (stableLiftMMatch quota refined val_college nu a) = some c
      simp [stableLiftMMatch, hmatch, hac, ac, hi,
        ManyToOneAssignment.CollegeSeat.college]

/-- A consistent many-to-one assignment is determined by applicant matches. -/
theorem manyToOneAssignment_eq_of_app_match
    {mu nu : ManyToOneAssignment Applicants Colleges}
    (happ : ∀ a, mu.app_match a = nu.app_match a) :
    mu = nu := by
  cases mu with
  | mk muApp muRoster muCons =>
      cases nu with
      | mk nuApp nuRoster nuCons =>
          simp only at happ
          have hApp : muApp = nuApp := funext happ
          subst nuApp
          have hRoster : muRoster = nuRoster := by
            funext c
            ext a
            constructor
            · intro ha
              exact (nuCons a c).1 ((muCons a c).2 ha)
            · intro ha
              exact (muCons a c).1 ((nuCons a c).2 ha)
          subst nuRoster
          rfl

/-- Every stable-seat lift collapses to the source many-to-one assignment. -/
theorem stableSeatLift_collapse
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (hcollegeNoZero : ∀ c a, val_college c a ≠ 0)
    (refined : Applicants → Seat quota → ℝ)
    (hrefined : IsApplicantSeatRefinement quota val_applicant refined)
    (nu : ManyToOneAssignment Applicants Colleges)
    (hnu : ManyToOne.IsStable val_applicant val_college quota nu) :
    ManyToOneAssignment.ofSeatAssignment quota
        (stableSeatLift quota refined val_college nu) = nu := by
  apply manyToOneAssignment_eq_of_app_match
  exact stableSeatLift_collapse_app_match quota val_applicant val_college
    happNoZero hcollegeNoZero refined hrefined nu hnu

theorem stableSeatLift_m_match_iff_local
    (quota : Colleges → ℕ)
    (refined : Applicants → Seat quota → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (nu : ManyToOneAssignment Applicants Colleges)
    (a : Applicants) (c : Colleges) (i : Fin (quota c)) :
    (stableSeatLift quota refined val_college nu).m_match a = some ⟨c, i⟩ ↔
      ∃ hac : a ∈ nu.college_roster c,
        (localRosterSeatAssignment quota refined val_college nu c).m_match
          ⟨a, hac⟩ = some i := by
  classical
  constructor
  · intro hlift
    change stableLiftMMatch quota refined val_college nu a = some ⟨c, i⟩ at hlift
    cases hmatch : nu.app_match a with
    | none => simp [stableLiftMMatch, hmatch] at hlift
    | some d =>
        have had : a ∈ nu.college_roster d := (nu.consistent a d).1 hmatch
        let ad : Roster nu d := ⟨a, had⟩
        cases hlocal :
            (localRosterSeatAssignment quota refined val_college nu d).m_match ad with
        | none => simp [stableLiftMMatch, hmatch, had, ad, hlocal] at hlift
        | some j =>
            have hs : (⟨d, j⟩ : Seat quota) = ⟨c, i⟩ := by
              simpa [stableLiftMMatch, hmatch, had, ad, hlocal] using hlift
            cases hs
            exact ⟨had, by simpa [ad]⟩
  · rintro ⟨hac, hlocal⟩
    have hmatch : nu.app_match a = some c := (nu.consistent a c).2 hac
    change stableLiftMMatch quota refined val_college nu a = some ⟨c, i⟩
    simp [stableLiftMMatch, hmatch, hac, hlocal]

theorem stableSeatLift_w_match_iff_local
    (quota : Colleges → ℕ)
    (refined : Applicants → Seat quota → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (nu : ManyToOneAssignment Applicants Colleges)
    (a : Applicants) (c : Colleges) (i : Fin (quota c)) :
    (stableSeatLift quota refined val_college nu).w_match ⟨c, i⟩ = some a ↔
      ∃ hac : a ∈ nu.college_roster c,
        (localRosterSeatAssignment quota refined val_college nu c).w_match i =
          some ⟨a, hac⟩ := by
  constructor
  · intro hw
    have hm := ((stableSeatLift quota refined val_college nu).consistent_m
      a ⟨c, i⟩).2 hw
    rcases (stableSeatLift_m_match_iff_local quota refined val_college nu
      a c i).1 hm with ⟨hac, hlocal⟩
    exact ⟨hac,
      ((localRosterSeatAssignment quota refined val_college nu c).consistent_m
        ⟨a, hac⟩ i).1 hlocal⟩
  · rintro ⟨hac, hw⟩
    have hm :=
      ((localRosterSeatAssignment quota refined val_college nu c).consistent_m
        ⟨a, hac⟩ i).2 hw
    have hlift := (stableSeatLift_m_match_iff_local quota refined val_college nu
      a c i).2 ⟨hac, hm⟩
    exact ((stableSeatLift quota refined val_college nu).consistent_m
      a ⟨c, i⟩).1 hlift

theorem stableSeatLift_w_match_none_iff_local
    (quota : Colleges → ℕ)
    (refined : Applicants → Seat quota → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (nu : ManyToOneAssignment Applicants Colleges)
    (c : Colleges) (i : Fin (quota c)) :
    (stableSeatLift quota refined val_college nu).w_match ⟨c, i⟩ = none ↔
      (localRosterSeatAssignment quota refined val_college nu c).w_match i = none := by
  constructor
  · intro hlift
    cases hlocal :
        (localRosterSeatAssignment quota refined val_college nu c).w_match i with
    | none => rfl
    | some a =>
        have hw := (stableSeatLift_w_match_iff_local quota refined val_college nu
          a.1 c i).2 ⟨a.2, by simpa using hlocal⟩
        rw [hlift] at hw
        cases hw
  · intro hlocal
    cases hlift : (stableSeatLift quota refined val_college nu).w_match ⟨c, i⟩ with
    | none => rfl
    | some a =>
        rcases (stableSeatLift_w_match_iff_local quota refined val_college nu
          a c i).1 hlift with ⟨hac, hw⟩
        rw [hlocal] at hw
        cases hw

theorem stableSeatLift_local_valM
    (quota : Colleges → ℕ)
    (refined : Applicants → Seat quota → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (nu : ManyToOneAssignment Applicants Colleges)
    (a : Applicants) (c : Colleges) (hac : a ∈ nu.college_roster c) :
    valM refined a ((stableSeatLift quota refined val_college nu).m_match a) =
      valM (localApplicantValue quota refined nu c) ⟨a, hac⟩
        ((localRosterSeatAssignment quota refined val_college nu c).m_match
          ⟨a, hac⟩) := by
  classical
  have hmatch : nu.app_match a = some c := (nu.consistent a c).2 hac
  cases hlocal :
      (localRosterSeatAssignment quota refined val_college nu c).m_match ⟨a, hac⟩ <;>
    simp [stableLiftMMatch, hmatch, hac, localApplicantValue, valM, hlocal]

theorem stableSeatLift_local_valW
    (quota : Colleges → ℕ)
    (refined : Applicants → Seat quota → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (nu : ManyToOneAssignment Applicants Colleges)
    (c : Colleges) (i : Fin (quota c)) :
    valW (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
        ⟨c, i⟩ ((stableSeatLift quota refined val_college nu).w_match ⟨c, i⟩) =
      valW (localCollegeValue quota val_college nu c) i
        ((localRosterSeatAssignment quota refined val_college nu c).w_match i) := by
  cases hlift : (stableSeatLift quota refined val_college nu).w_match ⟨c, i⟩ with
  | none =>
      have hlocal := (stableSeatLift_w_match_none_iff_local
        quota refined val_college nu c i).1 hlift
      simp [valW, hlift, hlocal]
  | some a =>
      rcases (stableSeatLift_w_match_iff_local quota refined val_college nu
        a c i).1 hlift with ⟨hac, hlocal⟩
      simp [valW, hlift, hlocal, ManyToOneAssignment.collegeSeatValue,
        ManyToOneAssignment.CollegeSeat.college, localCollegeValue]

/-- Every stable college assignment has a stable lift to the refined-seat market. -/
theorem stableSeatLift_stable
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happStrict : ∀ a c c', val_applicant a c = val_applicant a c' → c = c')
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (hcollegeNoZero : ∀ c a, val_college c a ≠ 0)
    (refined : Applicants → Seat quota → ℝ)
    (hrefined : IsApplicantSeatRefinement quota val_applicant refined)
    (nu : ManyToOneAssignment Applicants Colleges)
    (hnu : ManyToOne.IsStable val_applicant val_college quota nu) :
    IsStable refined
      (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
      (stableSeatLift quota refined val_college nu) := by
  classical
  let lift := stableSeatLift quota refined val_college nu
  refine ⟨?_, ?_, ?_⟩
  · intro a
    change 0 ≤ valM refined a (lift.m_match a)
    cases hmatch : nu.app_match a with
    | none =>
        have hlift : lift.m_match a = none := by
          change stableLiftMMatch quota refined val_college nu a = none
          simp [stableLiftMMatch, hmatch]
        rw [hlift]
        simp [valM]
    | some c =>
        have hac : a ∈ nu.college_roster c := (nu.consistent a c).1 hmatch
        let ac : Roster nu c := ⟨a, hac⟩
        rcases localRosterSeatAssignment_applicant_complete
          quota val_applicant val_college happNoZero hcollegeNoZero
          refined hrefined nu hnu c ac with ⟨i, hi⟩
        have hlift : lift.m_match a = some ⟨c, i⟩ := by
          exact (stableSeatLift_m_match_iff_local quota refined val_college nu
            a c i).2 ⟨hac, by simpa [ac] using hi⟩
        have happNonneg : 0 ≤ val_applicant a c := by
          simpa [ManyToOne.valApplicant, hmatch] using hnu.2.1 a
        have happPos : 0 < val_applicant a c :=
          lt_of_le_of_ne happNonneg (happNoZero a c).symm
        have hrefinedPos : 0 < refined a ⟨c, i⟩ :=
          (hrefined.positive_iff a ⟨c, i⟩).2 happPos
        rw [hlift]
        simpa [valM] using le_of_lt hrefinedPos
  · intro seat
    change 0 ≤ valW
      (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
      seat (lift.w_match seat)
    rcases seat with ⟨c, i⟩
    cases hlift : lift.w_match ⟨c, i⟩ with
    | none => simp [valW, hlift]
    | some a =>
        rcases (stableSeatLift_w_match_iff_local quota refined val_college nu
          a c i).1 hlift with ⟨hac, _hlocal⟩
        have hnonneg : 0 ≤ val_college c a := hnu.2.2.1 c a hac
        simpa [valW, ManyToOneAssignment.collegeSeatValue,
          ManyToOneAssignment.CollegeSeat.college] using hnonneg
  · intro a seat happPref hcollegePref
    rcases seat with ⟨c, i⟩
    by_cases hac : a ∈ nu.college_roster c
    · let ac : Roster nu c := ⟨a, hac⟩
      have happLocal :
          valM (localApplicantValue quota refined nu c) ac
              ((localRosterSeatAssignment quota refined val_college nu c).m_match ac) <
            localApplicantValue quota refined nu c ac i := by
        have hval := stableSeatLift_local_valM quota refined val_college nu a c hac
        rw [hval] at happPref
        simpa [ac, localApplicantValue] using happPref
      have hcollegeLocal :
          valW (localCollegeValue quota val_college nu c) i
              ((localRosterSeatAssignment quota refined val_college nu c).w_match i) <
            localCollegeValue quota val_college nu c i ac := by
        have hval := stableSeatLift_local_valW quota refined val_college nu c i
        rw [hval] at hcollegePref
        simpa [ac, localCollegeValue,
          ManyToOneAssignment.collegeSeatValue,
          ManyToOneAssignment.CollegeSeat.college] using hcollegePref
      exact (localRosterSeatAssignment_stable quota refined val_college nu c).2.2
        ac i happLocal hcollegeLocal
    · have hnotMatch : nu.app_match a ≠ some c := by
        intro hmatch
        exact hac ((nu.consistent a c).1 hmatch)
      have happSource :
          ManyToOne.valApplicant val_applicant a (nu.app_match a) <
            val_applicant a c := by
        cases hmatch : nu.app_match a with
        | none =>
            have hlift : stableLiftMMatch quota refined val_college nu a = none := by
              change stableLiftMMatch quota refined val_college nu a = none
              simp [stableLiftMMatch, hmatch]
            have hrefinedPos : 0 < refined a ⟨c, i⟩ := by
              simpa [valM, hlift] using happPref
            have hsourcePos := (hrefined.positive_iff a ⟨c, i⟩).1
              hrefinedPos
            simpa [ManyToOne.valApplicant, hmatch] using hsourcePos
        | some d =>
            have had : a ∈ nu.college_roster d := (nu.consistent a d).1 hmatch
            have hdc : d ≠ c := by
              intro heq
              subst d
              exact hnotMatch hmatch
            let ad : Roster nu d := ⟨a, had⟩
            rcases localRosterSeatAssignment_applicant_complete
              quota val_applicant val_college happNoZero hcollegeNoZero
              refined hrefined nu hnu d ad with ⟨j, hj⟩
            have hlift : stableLiftMMatch quota refined val_college nu a =
                some ⟨d, j⟩ := by
              change (stableSeatLift quota refined val_college nu).m_match a =
                some ⟨d, j⟩
              exact (stableSeatLift_m_match_iff_local quota refined val_college nu
                  a d j).2 ⟨had, by simpa [ad] using hj⟩
            have hrefinedLt : refined a ⟨d, j⟩ < refined a ⟨c, i⟩ := by
              simpa [valM, hlift] using happPref
            have hsourceLt := source_lt_of_refined_lt_of_college_ne
              quota val_applicant refined hrefined happStrict a
              ⟨d, j⟩ ⟨c, i⟩ hdc hrefinedLt
            simpa [ManyToOne.valApplicant, hmatch] using hsourceLt
      have hcollegeAccept :
          ManyToOne.CollegeWouldAccept val_college quota
            (nu.college_roster c) a c := by
        cases hliftW : lift.w_match ⟨c, i⟩ with
        | some b =>
            rcases (stableSeatLift_w_match_iff_local quota refined val_college nu
              b c i).1 hliftW with ⟨hbc, _hlocal⟩
            have hpref : val_college c b < val_college c a := by
              simpa [valW, lift, hliftW,
                ManyToOneAssignment.collegeSeatValue] using hcollegePref
            exact Or.inr ⟨b, hbc, hpref⟩
        | none =>
            have hlocalNone := (stableSeatLift_w_match_none_iff_local
              quota refined val_college nu c i).1 hliftW
            have hroom : (nu.college_roster c).card < quota c := by
              by_contra hnotRoom
              have heq : (nu.college_roster c).card = quota c :=
                Nat.le_antisymm (hnu.1 c) (le_of_not_gt hnotRoom)
              have hmComplete := localRosterSeatAssignment_applicant_complete
                quota val_applicant val_college happNoZero hcollegeNoZero
                refined hrefined nu hnu c
              have hcardLocal : Fintype.card (Roster nu c) =
                  Fintype.card (Fin (quota c)) := by
                simpa [Roster, Fintype.card_coe] using heq
              have hwComplete := Assignment.w_complete_of_m_complete_of_card_eq
                (localRosterSeatAssignment quota refined val_college nu c)
                hcardLocal hmComplete
              rcases hwComplete i with ⟨b, hb⟩
              rw [hlocalNone] at hb
              cases hb
            have hpositive : 0 < val_college c a := by
              simpa [valW, lift, hliftW,
                ManyToOneAssignment.collegeSeatValue] using hcollegePref
            exact Or.inl ⟨hpositive, hroom⟩
      exact hnu.2.2.2 a c happSource hcollegeAccept

theorem refined_negative_iff
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (refined : Applicants → Seat quota → ℝ)
    (hrefined : IsApplicantSeatRefinement quota val_applicant refined)
    (hsourceNoZero : ∀ a c, val_applicant a c ≠ 0)
    (a : Applicants) (s : Seat quota) :
    refined a s < 0 ↔ val_applicant a s.1 < 0 := by
  constructor
  · intro hrefinedNeg
    by_contra hnot
    have hsourcePos : 0 < val_applicant a s.1 :=
      lt_of_le_of_ne (le_of_not_gt hnot)
        (hsourceNoZero a s.1).symm
    have := (hrefined.positive_iff a s).2 hsourcePos
    linarith
  · intro hsourceNeg
    have hnotPositive : ¬ 0 < refined a s := by
      intro hpos
      have := (hrefined.positive_iff a s).1 hpos
      linarith
    exact lt_of_le_of_ne (le_of_not_gt hnotPositive)
      (hrefined.nonzero a s)

theorem refined_val_lt_of_source_collapse_lt
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (refined : Applicants → Seat quota → ℝ)
    (hrefined : IsApplicantSeatRefinement quota val_applicant refined)
    (hsourceNoZero : ∀ a c, val_applicant a c ≠ 0)
    (mu nu : Assignment Applicants (Seat quota)) (a : Applicants)
    (hsource :
      ManyToOne.valApplicant val_applicant a
          ((ManyToOneAssignment.ofSeatAssignment quota mu).app_match a) <
        ManyToOne.valApplicant val_applicant a
          ((ManyToOneAssignment.ofSeatAssignment quota nu).app_match a)) :
    valM refined a (mu.m_match a) < valM refined a (nu.m_match a) := by
  cases hmu : mu.m_match a with
  | none =>
      cases hnu : nu.m_match a with
      | none =>
          simp [ManyToOneAssignment.ofSeatAssignment, ManyToOne.valApplicant,
            hmu, hnu] at hsource
      | some t =>
          have hsourcePos : 0 < val_applicant a t.1 := by
            simpa [ManyToOneAssignment.ofSeatAssignment, ManyToOne.valApplicant,
              ManyToOneAssignment.CollegeSeat.college, hmu, hnu] using hsource
          have hrefinedPos := (hrefined.positive_iff a t).2 hsourcePos
          simpa [valM, hmu, hnu] using hrefinedPos
  | some s =>
      cases hnu : nu.m_match a with
      | none =>
          have hsourceNeg : val_applicant a s.1 < 0 := by
            simpa [ManyToOneAssignment.ofSeatAssignment, ManyToOne.valApplicant,
              ManyToOneAssignment.CollegeSeat.college, hmu, hnu] using hsource
          have hrefinedNeg :=
            (refined_negative_iff quota val_applicant refined hrefined
              hsourceNoZero a s).2 hsourceNeg
          simpa [valM, hmu, hnu] using hrefinedNeg
      | some t =>
          have hsourceLt : val_applicant a s.1 < val_applicant a t.1 := by
            simpa [ManyToOneAssignment.ofSeatAssignment, ManyToOne.valApplicant,
              ManyToOneAssignment.CollegeSeat.college, hmu, hnu] using hsource
          have hrefinedLt := hrefined.source_lt a s t hsourceLt
          simpa [valM, hmu, hnu] using hrefinedLt

/--
Gale--Shapley Theorem 2 for arbitrary finite college quotas: the
applicant-proposing outcome is applicant-optimal among every stable college
assignment.
-/
theorem paper_gs62_theorem2_arbitrary_quota_applicant_optimal
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : gs_strict_college_admissions_domain val_applicant val_college) :
    gs_applicant_optimal_college_assignment quota val_applicant val_college
      (refinedDeferredAcceptanceManyToOne quota val_applicant val_college
        hdomain.1.2) := by
  rcases hdomain with ⟨⟨happStrict, happNoZero⟩,
    ⟨hcollegeStrict, hcollegeNoZero⟩⟩
  let refined := refinedApplicantSeatValue quota val_applicant happNoZero
  let seatDA := refinedSeatDeferredAcceptance
    quota val_applicant val_college happNoZero
  let collegeDA := refinedDeferredAcceptanceManyToOne
    quota val_applicant val_college happNoZero
  have hrefined : IsApplicantSeatRefinement quota val_applicant refined :=
    refinedApplicantSeatValue_spec quota val_applicant happNoZero
  refine ⟨?_, ?_⟩
  · exact refinedDeferredAcceptanceManyToOne_stable
      quota val_applicant val_college happStrict happNoZero
  · intro nu hnu a
    let liftNu := stableSeatLift quota refined val_college nu
    have hliftStable : IsStable refined
        (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
        liftNu :=
      stableSeatLift_stable quota val_applicant val_college happStrict
        happNoZero hcollegeNoZero refined hrefined nu hnu
    have hopt : valM refined a (liftNu.m_match a) ≤
        valM refined a (seatDA.m_match a) := by
      exact refinedSeatDeferredAcceptance_applicant_optimal
        quota val_applicant val_college happNoZero hcollegeStrict
        liftNu hliftStable a
    by_contra hnot
    have hsourceGt :
        ManyToOne.valApplicant val_applicant a (collegeDA.app_match a) <
          ManyToOne.valApplicant val_applicant a (nu.app_match a) :=
      lt_of_not_ge hnot
    have hcollapseLift := stableSeatLift_collapse_app_match
      quota val_applicant val_college happNoZero hcollegeNoZero
      refined hrefined nu hnu a
    have hsourceSeats :
        ManyToOne.valApplicant val_applicant a
            ((ManyToOneAssignment.ofSeatAssignment quota seatDA).app_match a) <
          ManyToOne.valApplicant val_applicant a
            ((ManyToOneAssignment.ofSeatAssignment quota liftNu).app_match a) := by
      simpa [collegeDA, seatDA, refinedDeferredAcceptanceManyToOne,
        refinedSeatDeferredAcceptance, liftNu, hcollapseLift] using hsourceGt
    have hrefinedGt := refined_val_lt_of_source_collapse_lt
      quota val_applicant refined hrefined happNoZero
      seatDA liftNu a hsourceSeats
    exact (not_lt_of_ge hopt) hrefinedGt

/-! ## The inverted, college-proposing procedure -/

/-- In the cloned-seat market, strict college rankings are strict proposer rankings. -/
theorem college_seat_men_strict
    (quota : Colleges → ℕ)
    (val_college : Colleges → Applicants → ℝ)
    (hstrict : ∀ c a a', val_college c a = val_college c a' → a = a') :
    MenStrictPreferenceProfile
      (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college) := by
  intro s a a' heq
  exact hstrict s.1 a a' heq

/-- The weaker acceptable-region strictness needed by incomplete-list DA. -/
theorem college_seat_men_acceptably_strict
    (quota : Colleges → ℕ)
    (val_college : Colleges → Applicants → ℝ)
    (hstrict : ∀ c a a', val_college c a = val_college c a' → a = a') :
    MenAcceptableStrictPreferenceProfile
      (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college) := by
  intro s a a' _ _ heq
  exact hstrict s.1 a a' heq

/-- No cloned college seat ties an applicant with remaining empty. -/
theorem college_seat_men_no_outside_tie
    (quota : Colleges → ℕ)
    (val_college : Colleges → Applicants → ℝ)
    (hnozero : ∀ c a, val_college c a ≠ 0) :
    MenNoOutsideTie
      (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college) := by
  intro s a
  exact hnozero s.1 a

/-- A strict applicant seat refinement is strict on the receiver side as well. -/
theorem refined_women_strict
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (hnozero : ∀ a c, val_applicant a c ≠ 0) :
    WomenStrictPreferenceProfile
      (refinedApplicantSeatValue quota val_applicant hnozero) :=
  (refinedApplicantSeatValue_spec quota val_applicant hnozero).strict

/--
The paper's inverted procedure: cloned college seats propose to applicants,
and the resulting seat assignment is viewed in applicant--seat orientation.
Applicants' arbitrary strict ordering among seats of one college is only a
technical refinement of their strict college ranking.
-/
noncomputable def collegeProposingRefinedSeatDA
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0) :
    Assignment Applicants (Seat quota) :=
  (deferredAcceptance
    (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
    (refinedApplicantSeatValue quota val_applicant happNoZero)).swap

/--
Seat-responsive college optimality: the assignment is stable and every cloned
college seat weakly prefers its applicant to its applicant in any other stable
refined-seat assignment.  This is the standard cloned-seat meaning of college
optimality for responsive quota preferences.
-/
def IsCollegeOptimalRefinedSeatAssignment
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (mu : Assignment Applicants (Seat quota)) : Prop :=
  IsStable
      (refinedApplicantSeatValue quota val_applicant happNoZero)
      (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college) mu ∧
    ∀ nu, IsStable
        (refinedApplicantSeatValue quota val_applicant happNoZero)
        (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college) nu →
      ∀ s, valW
          (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
          s (nu.w_match s) ≤
        valW
          (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
          s (mu.w_match s)

/-- College-proposing DA is college-optimal in the responsive cloned-seat market. -/
theorem collegeProposingRefinedSeatDA_college_optimal
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (hcollegeStrict : ∀ c a a',
      val_college c a = val_college c a' → a = a')
    (hcollegeNoZero : ∀ c a, val_college c a ≠ 0) :
    IsCollegeOptimalRefinedSeatAssignment quota val_applicant val_college
      happNoZero
      (collegeProposingRefinedSeatDA quota val_applicant val_college
        happNoZero) := by
  let seatValue :=
    ManyToOneAssignment.collegeSeatValue (quota := quota) val_college
  let applicantValue :=
    refinedApplicantSeatValue quota val_applicant happNoZero
  let seatDA := deferredAcceptance seatValue applicantValue
  have hseatStrict : MenAcceptableStrictPreferenceProfile seatValue := by
    exact college_seat_men_acceptably_strict quota val_college hcollegeStrict
  have happStrict : WomenAcceptableStrictPreferenceProfile applicantValue := by
    exact (refined_women_strict quota val_applicant happNoZero).acceptablyStrict
  have hseatNoZero : MenNoOutsideTie seatValue := by
    exact college_seat_men_no_outside_tie quota val_college hcollegeNoZero
  have hrejected : DARejectedPairImpossibleInvariant seatValue applicantValue
      (deferredAcceptanceState seatValue applicantValue) :=
    deferredAcceptanceState_satisfies_rejected_pair_impossible_no_outside_tie
      seatValue applicantValue hseatStrict happStrict hseatNoZero
  have hoptimal : DaIsMenOptimalCertificate seatValue applicantValue :=
    da_is_men_optimal_of_rejected_pair_impossible seatValue applicantValue
      (deferredAcceptanceState_satisfies_invariants_closed
        seatValue applicantValue)
      (deferredAcceptanceState_terminated seatValue applicantValue)
      hrejected
  refine ⟨?_, ?_⟩
  · change IsStable applicantValue seatValue seatDA.swap
    exact (isStable_swap_iff seatValue applicantValue seatDA).2
      (da_produces_stable_matching seatValue applicantValue)
  · intro nu hnu s
    have hnuSwap : IsStable seatValue applicantValue nu.swap :=
      (isStable_swap_iff applicantValue seatValue nu).2 hnu
    have hs := hoptimal nu.swap hnuSwap s
    simpa [seatValue, applicantValue, seatDA,
      collegeProposingRefinedSeatDA, valM, valW] using hs

/-- The college-optimal refined-seat assignment is unique. -/
theorem college_optimal_refined_seat_assignment_unique
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (hcollegeStrict : ∀ c a a',
      val_college c a = val_college c a' → a = a')
    (hcollegeNoZero : ∀ c a, val_college c a ≠ 0)
    {mu nu : Assignment Applicants (Seat quota)}
    (hmu : IsCollegeOptimalRefinedSeatAssignment quota val_applicant
      val_college happNoZero mu)
    (hnu : IsCollegeOptimalRefinedSeatAssignment quota val_applicant
      val_college happNoZero nu) :
    mu = nu := by
  let seatValue :=
    ManyToOneAssignment.collegeSeatValue (quota := quota) val_college
  let applicantValue :=
    refinedApplicantSeatValue quota val_applicant happNoZero
  have hmuSwap : IsMenOptimalStable seatValue applicantValue mu.swap := by
    refine ⟨(isStable_swap_iff applicantValue seatValue mu |>.2 hmu.1), ?_⟩
    intro rho hrho s
    have hrhoSwap : IsStable applicantValue seatValue rho.swap :=
      (isStable_swap_iff seatValue applicantValue rho).2 hrho
    have hs := hmu.2 rho.swap hrhoSwap s
    simpa [seatValue, applicantValue, valM, valW] using hs
  have hnuSwap : IsMenOptimalStable seatValue applicantValue nu.swap := by
    refine ⟨(isStable_swap_iff applicantValue seatValue nu |>.2 hnu.1), ?_⟩
    intro rho hrho s
    have hrhoSwap : IsStable applicantValue seatValue rho.swap :=
      (isStable_swap_iff seatValue applicantValue rho).2 hrho
    have hs := hnu.2 rho.swap hrhoSwap s
    simpa [seatValue, applicantValue, valM, valW] using hs
  have hswap : mu.swap = nu.swap :=
    men_optimal_stable_matching_unique_of_no_outside_tie
      seatValue applicantValue
      (college_seat_men_strict quota val_college hcollegeStrict)
      (college_seat_men_no_outside_tie quota val_college hcollegeNoZero)
      hmuSwap hnuSwap
  simpa using congrArg Assignment.swap hswap

/--
A many-to-one outcome is college-optimal when it is the collapse of the
college-optimal responsive cloned-seat assignment.
-/
def gs_college_optimal_college_assignment
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  gs_stable_college_assignment quota val_applicant val_college mu ∧
    ∃ seatMu : Assignment Applicants (Seat quota),
      IsCollegeOptimalRefinedSeatAssignment quota val_applicant val_college
        happNoZero seatMu ∧
      ManyToOneAssignment.ofSeatAssignment quota seatMu = mu

/-- Collapse the output of the inverted college-proposing procedure. -/
noncomputable def collegeProposingManyToOne
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0) :
    ManyToOneAssignment Applicants Colleges :=
  ManyToOneAssignment.ofSeatAssignment quota
    (collegeProposingRefinedSeatDA quota val_applicant val_college
      happNoZero)

/--
The explicit responsive roster convention.  `mu` is weakly college-preferred
to `nu` when the two rosters can be placed into named cloned seats so that every
seat weakly prefers its `mu` applicant, with an empty seat valued at zero.  This
is the project-declared responsive extension of each college's strict applicant
ranking; the GS62 source itself does not spell out a roster order.
-/
def gs_colleges_weakly_prefer_assignment
    (quota : Colleges → ℕ)
    (val_college : Colleges → Applicants → ℝ)
    (mu nu : ManyToOneAssignment Applicants Colleges) : Prop :=
  ∃ muSeats nuSeats : Assignment Applicants (Seat quota),
    ManyToOneAssignment.ofSeatAssignment quota muSeats = mu ∧
      ManyToOneAssignment.ofSeatAssignment quota nuSeats = nu ∧
      ∀ s, valW
          (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
          s (nuSeats.w_match s) ≤
        valW
          (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
          s (muSeats.w_match s)

/-- Source-level college optimality under responsive quota preferences. -/
def gs_responsive_college_optimal_assignment
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  gs_stable_college_assignment quota val_applicant val_college mu ∧
    ∀ nu, gs_stable_college_assignment quota val_applicant val_college nu →
      gs_colleges_weakly_prefer_assignment quota val_college mu nu

/--
For a finite one-to-one assignment, summing receiver values over receivers is
the same as summing the corresponding values over proposers.  Empty partners
contribute zero on both sides.
-/
private theorem sum_valW_eq_sum_valM
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (v : B → A → ℝ) (sigma : Assignment A B) :
    (∑ b, valW v b (sigma.w_match b)) =
      ∑ a, valM (fun a b => v b a) a (sigma.m_match a) := by
  classical
  calc
    (∑ b, valW v b (sigma.w_match b)) =
        ∑ b, ∑ a, if sigma.m_match a = some b then v b a else 0 := by
          apply Finset.sum_congr rfl
          intro b _
          cases h : sigma.w_match b with
          | none =>
              have hnone : ∀ a, sigma.m_match a ≠ some b := by
                intro a ha
                have : sigma.w_match b = some a :=
                  (sigma.consistent_m a b).1 ha
                rw [h] at this
                cases this
              simp only [valW]
              exact (Finset.sum_eq_zero fun a _ => by simp [hnone a]).symm
          | some a0 =>
              simp only [valW]
              rw [Finset.sum_eq_single a0]
              · simp [(sigma.consistent_m a0 b).2 h]
              · intro a _ hne
                have hnot : sigma.m_match a ≠ some b := by
                  intro ha
                  have hw : sigma.w_match b = some a :=
                    (sigma.consistent_m a b).1 ha
                  rw [h] at hw
                  exact hne (Option.some.inj hw.symm)
                simp [hnot]
              · simp
    _ = ∑ a, ∑ b, if sigma.m_match a = some b then v b a else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ a, valM (fun a b => v b a) a (sigma.m_match a) := by
          apply Finset.sum_congr rfl
          intro a _
          cases h : sigma.m_match a with
          | none =>
              simp only [valM]
              exact Finset.sum_eq_zero fun b _ => by simp
          | some b0 =>
              simp only [valM]
              simpa [Option.some.injEq, eq_comm] using
                (Fintype.sum_ite_eq' b0 (fun b => v b a)).symm

/--
The sum of cloned-seat college values depends only on the collapsed roster
assignment, not on the arbitrary placement of each roster member into a seat.
-/
private theorem collegeSeatValue_sum_eq_of_collapse_eq
    (quota : Colleges → ℕ)
    (val_college : Colleges → Applicants → ℝ)
    (sigma tau : Assignment Applicants (Seat quota))
    (hcollapse : ManyToOneAssignment.ofSeatAssignment quota sigma =
      ManyToOneAssignment.ofSeatAssignment quota tau) :
    (∑ s, valW (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
      s (sigma.w_match s)) =
      ∑ s, valW (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
        s (tau.w_match s) := by
  have hpoint : ∀ (rho : Assignment Applicants (Seat quota)) (a : Applicants),
      valM (fun a (s : Seat quota) => val_college s.1 a) a (rho.m_match a) =
        ManyToOne.valApplicant (fun a c => val_college c a) a
          ((ManyToOneAssignment.ofSeatAssignment quota rho).app_match a) := by
    intro rho a
    cases h : rho.m_match a with
    | none =>
        change valM (fun a (s : Seat quota) => val_college s.1 a) a none =
          ManyToOne.valApplicant (fun a c => val_college c a) a
            (Option.map ManyToOneAssignment.CollegeSeat.college (rho.m_match a))
        rw [h]
        rfl
    | some s =>
        rcases s with ⟨c, i⟩
        change valM (fun a (s : Seat quota) => val_college s.1 a) a
          (some (⟨c, i⟩ : Seat quota)) =
          ManyToOne.valApplicant (fun a c => val_college c a) a
            (Option.map ManyToOneAssignment.CollegeSeat.college (rho.m_match a))
        rw [h]
        rfl
  calc
    (∑ s, valW (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
        s (sigma.w_match s)) =
        ∑ a, valM (fun a s => val_college s.1 a) a (sigma.m_match a) := by
          simpa [ManyToOneAssignment.collegeSeatValue] using
            sum_valW_eq_sum_valM
              (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college) sigma
    _ = ∑ a, ManyToOne.valApplicant (fun a c => val_college c a) a
          ((ManyToOneAssignment.ofSeatAssignment quota sigma).app_match a) := by
          apply Finset.sum_congr rfl
          intro a _
          exact hpoint sigma a
    _ = ∑ a, ManyToOne.valApplicant (fun a c => val_college c a) a
          ((ManyToOneAssignment.ofSeatAssignment quota tau).app_match a) := by
          rw [hcollapse]
    _ = ∑ a, valM (fun a s => val_college s.1 a) a (tau.m_match a) := by
          apply Finset.sum_congr rfl
          intro a _
          exact (hpoint tau a).symm
    _ = ∑ s, valW (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
          s (tau.w_match s) := by
          simpa [ManyToOneAssignment.collegeSeatValue] using
            (sum_valW_eq_sum_valM
              (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college) tau).symm

/--
The explicit responsive cloned-seat roster order is antisymmetric on the
strict source domain.  Thus it alone, rather than an auxiliary fixed-seat
certificate, determines a unique responsive college-optimal stable outcome.
-/
theorem gs_responsive_college_optimal_assignment_unique
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hcollegeStrict : ∀ c a a', val_college c a = val_college c a' → a = a')
    (hcollegeNoZero : ∀ c a, val_college c a ≠ 0)
    {mu nu : ManyToOneAssignment Applicants Colleges}
    (hmu : gs_responsive_college_optimal_assignment quota val_applicant val_college mu)
    (hnu : gs_responsive_college_optimal_assignment quota val_applicant val_college nu) :
    mu = nu := by
  classical
  let seatValue := ManyToOneAssignment.collegeSeatValue (quota := quota) val_college
  rcases hmu.2 nu hnu.1 with ⟨muSeats, nuSeats, hmuCollapse, hnuCollapse, hmuNu⟩
  rcases hnu.2 mu hmu.1 with ⟨nuSeats', muSeats', hnuCollapse', hmuCollapse', hnuMu⟩
  have hsumMuNu :
      (∑ s, valW seatValue s (nuSeats.w_match s)) ≤
        ∑ s, valW seatValue s (muSeats.w_match s) := by
    exact Finset.sum_le_sum fun s _ => hmuNu s
  have hsumNuMu :
      (∑ s, valW seatValue s (muSeats'.w_match s)) ≤
        ∑ s, valW seatValue s (nuSeats'.w_match s) := by
    exact Finset.sum_le_sum fun s _ => hnuMu s
  have hsumMuSame :
      (∑ s, valW seatValue s (muSeats.w_match s)) =
        ∑ s, valW seatValue s (muSeats'.w_match s) := by
    exact collegeSeatValue_sum_eq_of_collapse_eq quota val_college muSeats muSeats'
      (hmuCollapse.trans hmuCollapse'.symm)
  have hsumNuSame :
      (∑ s, valW seatValue s (nuSeats.w_match s)) =
        ∑ s, valW seatValue s (nuSeats'.w_match s) := by
    exact collegeSeatValue_sum_eq_of_collapse_eq quota val_college nuSeats nuSeats'
      (hnuCollapse.trans hnuCollapse'.symm)
  have hsum :
      (∑ s, valW seatValue s (nuSeats.w_match s)) =
        ∑ s, valW seatValue s (muSeats.w_match s) := by
    apply le_antisymm hsumMuNu
    calc
      (∑ s, valW seatValue s (muSeats.w_match s)) =
          ∑ s, valW seatValue s (muSeats'.w_match s) := hsumMuSame
      _ ≤ ∑ s, valW seatValue s (nuSeats'.w_match s) := hsumNuMu
      _ = ∑ s, valW seatValue s (nuSeats.w_match s) := hsumNuSame.symm
  have hdiff :
      (∑ s : Seat quota, (valW seatValue s (muSeats.w_match s) -
        valW seatValue s (nuSeats.w_match s))) = 0 := by
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hsum.symm
  have hnonnegative : ∀ s ∈ (Finset.univ : Finset (Seat quota)),
      0 ≤ valW seatValue s (muSeats.w_match s) -
        valW seatValue s (nuSeats.w_match s) := by
    intro s _
    exact sub_nonneg.mpr (hmuNu s)
  have hzero : ∀ s ∈ (Finset.univ : Finset (Seat quota)),
      valW seatValue s (muSeats.w_match s) -
        valW seatValue s (nuSeats.w_match s) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonnegative).1 hdiff
  have hvalue : ∀ s,
      valW seatValue s (muSeats.w_match s) =
        valW seatValue s (nuSeats.w_match s) := by
    intro s
    exact sub_eq_zero.mp (hzero s (Finset.mem_univ s))
  have hswap : muSeats.swap = nuSeats.swap := by
    apply assignment_eq_of_same_man_values_of_strict_no_outside_tie
      seatValue
      (college_seat_men_strict quota val_college hcollegeStrict)
      (college_seat_men_no_outside_tie quota val_college hcollegeNoZero)
    intro s
    simpa [seatValue] using hvalue s
  have hseats : muSeats = nuSeats := by
    simpa using congrArg Assignment.swap hswap
  calc
    mu = ManyToOneAssignment.ofSeatAssignment quota muSeats := hmuCollapse.symm
    _ = ManyToOneAssignment.ofSeatAssignment quota nuSeats := congrArg _ hseats
    _ = nu := hnuCollapse

/-- The inverted procedure's collapsed outcome is source-level stable. -/
theorem collegeProposingManyToOne_stable
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happStrict : ∀ a c c', val_applicant a c = val_applicant a c' → c = c')
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (hcollegeStrict : ∀ c a a',
      val_college c a = val_college c a' → a = a')
    (hcollegeNoZero : ∀ c a, val_college c a ≠ 0) :
    gs_stable_college_assignment quota val_applicant val_college
      (collegeProposingManyToOne quota val_applicant val_college
        happNoZero) := by
  let seatMu := collegeProposingRefinedSeatDA
    quota val_applicant val_college happNoZero
  have hseatOptimal : IsCollegeOptimalRefinedSeatAssignment
      quota val_applicant val_college happNoZero seatMu :=
    collegeProposingRefinedSeatDA_college_optimal quota val_applicant
      val_college happNoZero hcollegeStrict hcollegeNoZero
  have hsourceSeatStable : IsStable
      (ManyToOneAssignment.applicantSeatValue (quota := quota) val_applicant)
      (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
      seatMu :=
    stable_refined_seats_implies_stable_source_seats quota val_applicant
      val_college happStrict happNoZero seatMu hseatOptimal.1
  change ManyToOne.IsStable val_applicant val_college quota
    (ManyToOneAssignment.ofSeatAssignment quota seatMu)
  exact ManyToOne.isStable_of_seatAssignment_stable quota val_applicant
    val_college seatMu hsourceSeatStable

/--
Semantic bridge for the paper's quoted phrase "college optimal": the inverted
procedure weakly improves every cloned college seat relative to a lift of every
other source-stable roster assignment.
-/
theorem collegeProposingManyToOne_responsive_college_optimal
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : gs_strict_college_admissions_domain
      val_applicant val_college) :
    gs_responsive_college_optimal_assignment quota val_applicant val_college
      (collegeProposingManyToOne quota val_applicant val_college
        hdomain.1.2) := by
  rcases hdomain with ⟨⟨happStrict, happNoZero⟩,
    ⟨hcollegeStrict, hcollegeNoZero⟩⟩
  let refined := refinedApplicantSeatValue quota val_applicant happNoZero
  let seatMu := collegeProposingRefinedSeatDA
    quota val_applicant val_college happNoZero
  have hrefined : IsApplicantSeatRefinement quota val_applicant refined :=
    refinedApplicantSeatValue_spec quota val_applicant happNoZero
  have hseatOptimal : IsCollegeOptimalRefinedSeatAssignment
      quota val_applicant val_college happNoZero seatMu :=
    collegeProposingRefinedSeatDA_college_optimal quota val_applicant
      val_college happNoZero hcollegeStrict hcollegeNoZero
  refine ⟨?_, ?_⟩
  · exact collegeProposingManyToOne_stable quota val_applicant val_college
      happStrict happNoZero hcollegeStrict hcollegeNoZero
  · intro nu hnu
    let nuSeats := stableSeatLift quota refined val_college nu
    have hnuSeatsStable : IsStable refined
        (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
        nuSeats :=
      stableSeatLift_stable quota val_applicant val_college happStrict
        happNoZero hcollegeNoZero refined hrefined nu hnu
    refine ⟨seatMu, nuSeats, ?_, ?_, ?_⟩
    · rfl
    · exact stableSeatLift_collapse quota val_applicant val_college
        happNoZero hcollegeNoZero refined hrefined nu hnu
    · exact hseatOptimal.2 nuSeats hnuSeatsStable

/-- The inverted procedure's concrete collapsed output is college-optimal. -/
theorem collegeProposingManyToOne_college_optimal
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : gs_strict_college_admissions_domain
      val_applicant val_college) :
    gs_college_optimal_college_assignment quota val_applicant val_college
      hdomain.1.2
      (collegeProposingManyToOne quota val_applicant val_college
        hdomain.1.2) := by
  rcases hdomain with ⟨⟨happStrict, happNoZero⟩,
    ⟨hcollegeStrict, hcollegeNoZero⟩⟩
  let seatMu := collegeProposingRefinedSeatDA
    quota val_applicant val_college happNoZero
  have hseatOptimal : IsCollegeOptimalRefinedSeatAssignment
      quota val_applicant val_college happNoZero seatMu :=
    collegeProposingRefinedSeatDA_college_optimal quota val_applicant
      val_college happNoZero hcollegeStrict hcollegeNoZero
  have hstable := collegeProposingManyToOne_stable
    quota val_applicant val_college happStrict happNoZero
      hcollegeStrict hcollegeNoZero
  refine ⟨hstable, seatMu, hseatOptimal, ?_⟩
  rfl

/--
Under the explicitly declared responsive cloned-seat roster convention, the
inverted college-proposing procedure is the unique responsive
college-optimal stable assignment.  This is the source-facing optimality route:
it does not require a separate fixed-seat optimality certificate.
-/
theorem paper_gs62_inverted_college_proposing_unique_responsive_college_optimal
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : gs_strict_college_admissions_domain
      val_applicant val_college) :
    ∃! mu : ManyToOneAssignment Applicants Colleges,
      gs_responsive_college_optimal_assignment quota val_applicant
        val_college mu := by
  let mu := collegeProposingManyToOne
    quota val_applicant val_college hdomain.1.2
  have hmu : gs_responsive_college_optimal_assignment quota val_applicant
      val_college mu := by
    exact collegeProposingManyToOne_responsive_college_optimal
      quota val_applicant val_college hdomain
  rcases hdomain with ⟨⟨_happStrict, _happNoZero⟩,
    ⟨hcollegeStrict, hcollegeNoZero⟩⟩
  refine ⟨mu, hmu, ?_⟩
  intro nu hnu
  exact gs_responsive_college_optimal_assignment_unique
    quota val_applicant val_college hcollegeStrict hcollegeNoZero hnu hmu

/--
Internal compatibility strengthening: the same outcome also has a particular
fixed refined-seat optimality certificate.  This theorem is retained for the
Roth82 quota specialization; GS62's paper-facing endpoint uses the explicit
responsive roster convention above instead.
-/
theorem paper_gs62_inverted_college_proposing_unique_college_optimal
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : gs_strict_college_admissions_domain
      val_applicant val_college) :
    ∃! mu : ManyToOneAssignment Applicants Colleges,
      gs_college_optimal_college_assignment quota val_applicant val_college
          hdomain.1.2 mu ∧
        gs_responsive_college_optimal_assignment quota val_applicant
          val_college mu := by
  have hresponsive :=
    collegeProposingManyToOne_responsive_college_optimal
      quota val_applicant val_college hdomain
  rcases hdomain with ⟨⟨happStrict, happNoZero⟩,
    ⟨hcollegeStrict, hcollegeNoZero⟩⟩
  let seatMu := collegeProposingRefinedSeatDA
    quota val_applicant val_college happNoZero
  let mu := collegeProposingManyToOne
    quota val_applicant val_college happNoZero
  have hseatOptimal : IsCollegeOptimalRefinedSeatAssignment
      quota val_applicant val_college happNoZero seatMu :=
    collegeProposingRefinedSeatDA_college_optimal quota val_applicant
      val_college happNoZero hcollegeStrict hcollegeNoZero
  have hsourceSeatStable : IsStable
      (ManyToOneAssignment.applicantSeatValue (quota := quota) val_applicant)
      (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
      seatMu :=
    stable_refined_seats_implies_stable_source_seats quota val_applicant
      val_college happStrict happNoZero seatMu hseatOptimal.1
  have hmuStable : gs_stable_college_assignment quota val_applicant
      val_college mu := by
    change ManyToOne.IsStable val_applicant val_college quota mu
    change ManyToOne.IsStable val_applicant val_college quota
      (ManyToOneAssignment.ofSeatAssignment quota seatMu)
    exact ManyToOne.isStable_of_seatAssignment_stable quota val_applicant
      val_college seatMu hsourceSeatStable
  refine ⟨mu, ⟨⟨hmuStable, seatMu, hseatOptimal, rfl⟩, hresponsive⟩, ?_⟩
  intro nu hnu
  rcases hnu with ⟨⟨_nuStable, seatNu, hseatNuOptimal, rfl⟩,
    _nuResponsive⟩
  have hseatEq : seatNu = seatMu :=
    college_optimal_refined_seat_assignment_unique quota val_applicant
      val_college happNoZero hcollegeStrict hcollegeNoZero
      hseatNuOptimal hseatOptimal
  simpa [mu, seatMu, collegeProposingManyToOne, hseatEq]

/--
Source-shaped endpoint with the explicit responsive cloned-seat roster order:
the concrete inverted procedure output is responsive-college-optimal, and no
other responsive-college-optimal stable assignment differs from it.
-/
theorem paper_gs62_inverted_college_proposing_responsive_outcome_unique
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : gs_strict_college_admissions_domain
      val_applicant val_college) :
    let mu := collegeProposingManyToOne
      quota val_applicant val_college hdomain.1.2
    gs_responsive_college_optimal_assignment quota val_applicant
      val_college mu ∧
      ∀ nu, gs_responsive_college_optimal_assignment quota val_applicant
        val_college nu → nu = mu := by
  let mu := collegeProposingManyToOne
    quota val_applicant val_college hdomain.1.2
  have hmu : gs_responsive_college_optimal_assignment quota val_applicant
      val_college mu := by
    exact collegeProposingManyToOne_responsive_college_optimal
      quota val_applicant val_college hdomain
  refine ⟨hmu, ?_⟩
  intro nu hnu
  rcases hdomain with ⟨⟨_happStrict, _happNoZero⟩,
    ⟨hcollegeStrict, hcollegeNoZero⟩⟩
  exact gs_responsive_college_optimal_assignment_unique
    quota val_applicant val_college hcollegeStrict hcollegeNoZero hnu hmu

end ManyToOneOptimality
end GS62CollegeAdmissions
