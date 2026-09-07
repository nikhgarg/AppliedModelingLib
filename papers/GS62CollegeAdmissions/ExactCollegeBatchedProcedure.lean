import GS62CollegeAdmissions.ManyToOneOptimality
import AppliedModelingLib.Foundations.Math.FiniteChoice

/-!
# The literal Section 4 college waiting-list procedure

This module gives the college-admissions procedure on the state space used in
the paper.  A state records the applications received by each college.  In one
round every currently unmatched applicant with an untried mutually acceptable
college applies to the best such college, and each college replaces its waiting
list by the top `q` applicants from its old waiting list together with the new
applications.

The waiting list is defined directly by top-`q` selection.  Cloned seats are
not part of the procedure semantics; they enter only in the terminal-output
comparison with the repository's applicant-proposing many-to-one DA.
-/

namespace GS62CollegeAdmissions
namespace ExactCollegeBatchedProcedure

open AppliedModelingLib.Matching
open AppliedModelingLib.FiniteChoice

variable {Applicants Colleges : Type*}
  [Fintype Applicants] [Fintype Colleges]
  [DecidableEq Applicants] [DecidableEq Colleges]

/-- A pair may occur in the source procedure exactly when both sides list it. -/
def sourceEligible
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (a : Applicants) (c : Colleges) : Prop :=
  0 < val_applicant a c /\ 0 < val_college c a

/-- Higher college scores occur first in the induced applicant order. -/
@[reducible] noncomputable def collegeOrder
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (c : Colleges) : LinearOrder Applicants :=
  LinearOrder.lift' (α := Applicants) (β := OrderDual Real)
    (fun a => OrderDual.toDual (val_college c a))
    (by
      intro a b h
      exact hcollegeStrict c a b h)

/-- The literal top-`q` waiting-list selection at one college. -/
noncomputable def collegeTopQ
    (quota : Colleges -> Nat)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (c : Colleges) (pool : Finset Applicants) : Finset Applicants :=
  letI : LinearOrder Applicants := collegeOrder val_college hcollegeStrict c
  linearTopQChoice (quota c) pool

theorem collegeTopQ_subset
    (quota : Colleges -> Nat)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (c : Colleges) (pool : Finset Applicants) :
    collegeTopQ quota val_college hcollegeStrict c pool <= pool := by
  classical
  letI : LinearOrder Applicants := collegeOrder val_college hcollegeStrict c
  exact linearTopQChoice_feasible (α := Applicants) (quota c) pool

theorem collegeTopQ_card
    (quota : Colleges -> Nat)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (c : Colleges) (pool : Finset Applicants) :
    (collegeTopQ quota val_college hcollegeStrict c pool).card =
      min (quota c) pool.card := by
  classical
  letI : LinearOrder Applicants := collegeOrder val_college hcollegeStrict c
  exact linearTopQChoice_qAcceptant (α := Applicants) (quota c) pool

theorem collegeTopQ_priority
    (quota : Colleges -> Nat)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (c : Colleges) (pool : Finset Applicants) {chosen rejected : Applicants}
    (hchosen : chosen ∈ collegeTopQ quota val_college hcollegeStrict c pool)
    (hrejectedPool : rejected ∈ pool)
    (hrejected : rejected ∉ collegeTopQ quota val_college hcollegeStrict c pool) :
    val_college c rejected < val_college c chosen := by
  classical
  letI : LinearOrder Applicants := collegeOrder val_college hcollegeStrict c
  have hpriority := linearTopQChoice_priority
    (α := Applicants) (quota c) hchosen hrejectedPool hrejected
  exact hpriority

private theorem collegeTopQ_substitutable
    (quota : Colleges -> Nat)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (c : Colleges) :
    Substitutable (collegeTopQ quota val_college hcollegeStrict c) := by
  classical
  letI : LinearOrder Applicants := collegeOrder val_college hcollegeStrict c
  unfold collegeTopQ
  have hsub : Substitutable (linearTopQChoice (α := Applicants) (quota c)) :=
    substitutable_of_feasible_of_qRepresentative
    (C := linearTopQChoice (α := Applicants) (quota c))
    (q := quota c)
    (linearTopQChoice_feasible (α := Applicants) (quota c))
    (linearTopQChoice_qRepresentative (α := Applicants) (quota c))
  intro X1 X2 hsubset x hx
  exact hsub hsubset hx

/-- Top-`q` selection can discard old rejections before adding a fresh batch. -/
theorem collegeTopQ_union_choice
    (quota : Colleges -> Nat)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (c : Colleges) (old fresh : Finset Applicants) :
    collegeTopQ quota val_college hcollegeStrict c (old ∪ fresh) =
      collegeTopQ quota val_college hcollegeStrict c
        (collegeTopQ quota val_college hcollegeStrict c old ∪ fresh) := by
  classical
  let C := collegeTopQ quota val_college hcollegeStrict c
  have hfeasible : Feasible C :=
    collegeTopQ_subset quota val_college hcollegeStrict c
  have haccept : QAcceptant (quota c) C :=
    collegeTopQ_card quota val_college hcollegeStrict c
  have hsub : Substitutable C :=
    collegeTopQ_substitutable quota val_college hcollegeStrict c
  have hconsistent : Consistent C :=
    consistent_of_qAcceptant_of_substitutable haccept hsub
  apply hconsistent
  · intro a ha
    have haPool : a ∈ old ∪ fresh := hfeasible _ ha
    rcases Finset.mem_union.mp haPool with haOld | haFresh
    · exact Finset.mem_union_left _
        (hsub (Finset.subset_union_left) (Finset.mem_inter.mpr ⟨haOld, ha⟩))
    · exact Finset.mem_union_right _ haFresh
  · exact Finset.union_subset_union_left (hfeasible old)

/-- Direct source state: cumulative applications received by every college. -/
structure SourceWaitingListState (Applicants Colleges : Type*)
    [DecidableEq Applicants] where
  applications : Colleges -> Finset Applicants

/-- A college's current waiting list is the top quota-many applications seen. -/
noncomputable def waitingList
    (quota : Colleges -> Nat)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges) (c : Colleges) :
    Finset Applicants :=
  collegeTopQ quota val_college hcollegeStrict c (s.applications c)

/-- The source states reachable from the empty application history. -/
def SourceStateInvariant
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges) : Prop :=
  (forall a c d,
      a ∈ waitingList quota val_college hcollegeStrict s c ->
      a ∈ waitingList quota val_college hcollegeStrict s d -> c = d) /\
    (forall a c, a ∈ s.applications c ->
      sourceEligible val_applicant val_college a c) /\
    forall a c d, a ∈ s.applications c ->
      sourceEligible val_applicant val_college a d ->
      a ∉ s.applications d ->
      val_applicant a d <= val_applicant a c

/-- The unique college whose waiting list currently contains an applicant. -/
noncomputable def assignedCollege
    (quota : Colleges -> Nat)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges) (a : Applicants) :
    Option Colleges := by
  classical
  exact if h : exists c,
      a ∈ waitingList quota val_college hcollegeStrict s c then
    some (Classical.choose h)
  else none

theorem assignedCollege_eq_some_iff
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges)
    (hinv : SourceStateInvariant quota val_applicant val_college
      hcollegeStrict s)
    (a : Applicants) (c : Colleges) :
    assignedCollege quota val_college hcollegeStrict s a = some c <->
      a ∈ waitingList quota val_college hcollegeStrict s c := by
  classical
  unfold assignedCollege
  by_cases h : exists d,
      a ∈ waitingList quota val_college hcollegeStrict s d
  · rw [dif_pos h]
    constructor
    · intro heq
      have hc : Classical.choose h = c := Option.some.inj heq
      simpa [hc] using Classical.choose_spec h
    · intro hac
      have hc : Classical.choose h = c :=
        hinv.1 a (Classical.choose h) c (Classical.choose_spec h) hac
      simp [hc]
  · rw [dif_neg h]
    constructor
    · intro hnone
      cases hnone
    · intro hac
      exact False.elim (h ⟨c, hac⟩)

/-- Mutually acceptable colleges to which this applicant has not yet applied. -/
noncomputable def untriedEligibleColleges
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (s : SourceWaitingListState Applicants Colleges) (a : Applicants) :
    Finset Colleges := by
  classical
  exact Finset.univ.filter fun c =>
    sourceEligible val_applicant val_college a c /\ a ∉ s.applications c

/-- An applicant acts in a round iff unmatched and an eligible target remains. -/
def SourceActive
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges) (a : Applicants) : Prop :=
  assignedCollege quota val_college hcollegeStrict s a = none /\
    (untriedEligibleColleges val_applicant val_college s a).Nonempty

private theorem exists_best_untried
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (s : SourceWaitingListState Applicants Colleges) (a : Applicants)
    (h : (untriedEligibleColleges val_applicant val_college s a).Nonempty) :
    exists c,
      c ∈ untriedEligibleColleges val_applicant val_college s a /\
        forall d, d ∈ untriedEligibleColleges val_applicant val_college s a ->
          val_applicant a d <= val_applicant a c := by
  exact Finset.exists_max_image _ _ h

/-- Best currently available source-level application target. -/
noncomputable def nextCollege
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges) (a : Applicants) :
    Option Colleges := by
  classical
  if hactive : SourceActive quota val_applicant val_college
      hcollegeStrict s a then
    exact some (Classical.choose
      (exists_best_untried val_applicant val_college s a hactive.2))
  else exact none

theorem nextCollege_eq_some_of_active
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges) (a : Applicants)
    (hactive : SourceActive quota val_applicant val_college
      hcollegeStrict s a) :
    exists c,
      nextCollege quota val_applicant val_college hcollegeStrict s a = some c /\
      c ∈ untriedEligibleColleges val_applicant val_college s a /\
      forall d, d ∈ untriedEligibleColleges val_applicant val_college s a ->
        val_applicant a d <= val_applicant a c := by
  classical
  let hexists := exists_best_untried val_applicant val_college s a hactive.2
  let c := Classical.choose hexists
  have hspec := Classical.choose_spec hexists
  refine ⟨c, ?_, hspec.1, hspec.2⟩
  simp [nextCollege, hactive, c, hexists]

theorem nextCollege_eq_none_of_not_active
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges) (a : Applicants)
    (hnot : ¬ SourceActive quota val_applicant val_college
      hcollegeStrict s a) :
    nextCollege quota val_applicant val_college hcollegeStrict s a = none := by
  simp [nextCollege, hnot]

/-- New applications received by one college in the current source round. -/
noncomputable def newApplications
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges) (c : Colleges) :
    Finset Applicants := by
  classical
  exact Finset.univ.filter fun a =>
    nextCollege quota val_applicant val_college hcollegeStrict s a = some c

/-- One literal source round: add every unmatched applicant's next application. -/
noncomputable def sourceStep
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges) :
    SourceWaitingListState Applicants Colleges where
  applications c := s.applications c ∪
    newApplications quota val_applicant val_college hcollegeStrict s c

/-- The step's waiting list is exactly top-`q` of old holders and new applicants. -/
theorem waitingList_sourceStep
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges) (c : Colleges) :
    waitingList quota val_college hcollegeStrict
        (sourceStep quota val_applicant val_college hcollegeStrict s) c =
      collegeTopQ quota val_college hcollegeStrict c
        (waitingList quota val_college hcollegeStrict s c ∪
          newApplications quota val_applicant val_college hcollegeStrict s c) := by
  simpa [waitingList, sourceStep] using
    collegeTopQ_union_choice quota val_college hcollegeStrict c
      (s.applications c)
      (newApplications quota val_applicant val_college hcollegeStrict s c)

theorem sourceActive_of_nextCollege_eq_some
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges) (a : Applicants)
    {c : Colleges}
    (hnext : nextCollege quota val_applicant val_college
      hcollegeStrict s a = some c) :
    SourceActive quota val_applicant val_college hcollegeStrict s a := by
  by_contra hnot
  have hnone := nextCollege_eq_none_of_not_active
    quota val_applicant val_college hcollegeStrict s a hnot
  rw [hnone] at hnext
  cases hnext

theorem mem_newApplications_iff
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges)
    (a : Applicants) (c : Colleges) :
    a ∈ newApplications quota val_applicant val_college hcollegeStrict s c <->
      nextCollege quota val_applicant val_college hcollegeStrict s a = some c := by
  classical
  simp [newApplications]

theorem mem_newApplications_spec
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges)
    {a : Applicants} {c : Colleges}
    (hnew : a ∈ newApplications quota val_applicant val_college
      hcollegeStrict s c) :
    SourceActive quota val_applicant val_college hcollegeStrict s a /\
      c ∈ untriedEligibleColleges val_applicant val_college s a /\
      forall d, d ∈ untriedEligibleColleges val_applicant val_college s a ->
        val_applicant a d <= val_applicant a c := by
  have hnext := (mem_newApplications_iff quota val_applicant val_college
    hcollegeStrict s a c).1 hnew
  have hactive := sourceActive_of_nextCollege_eq_some
    quota val_applicant val_college hcollegeStrict s a hnext
  rcases nextCollege_eq_some_of_active quota val_applicant val_college
      hcollegeStrict s a hactive with ⟨c', hc', hmem, hbest⟩
  have hcc : c' = c := Option.some.inj (hc'.symm.trans hnext)
  subst c'
  exact ⟨hactive, hmem, hbest⟩

/-- No chosen applicant is newly created except at the college applied to. -/
theorem waitingList_sourceStep_subset_old_union_new
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges) (c : Colleges) :
    waitingList quota val_college hcollegeStrict
        (sourceStep quota val_applicant val_college hcollegeStrict s) c <=
      waitingList quota val_college hcollegeStrict s c ∪
        newApplications quota val_applicant val_college hcollegeStrict s c := by
  classical
  intro a ha
  have haPool : a ∈ s.applications c ∪
      newApplications quota val_applicant val_college hcollegeStrict s c := by
    exact collegeTopQ_subset quota val_college hcollegeStrict c _
      (by simpa [waitingList, sourceStep] using ha)
  rcases Finset.mem_union.mp haPool with haOld | haNew
  · apply Finset.mem_union_left
    have hsub : Substitutable
        (collegeTopQ quota val_college hcollegeStrict c) :=
      collegeTopQ_substitutable quota val_college hcollegeStrict c
    exact hsub (X₁ := s.applications c)
      (X₂ := s.applications c ∪
        newApplications quota val_applicant val_college hcollegeStrict s c)
      Finset.subset_union_left
      (Finset.mem_inter.mpr ⟨haOld, by simpa [waitingList, sourceStep] using ha⟩)
  · exact Finset.mem_union_right _ haNew

theorem sourceStep_preserves_invariant
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges)
    (hinv : SourceStateInvariant quota val_applicant val_college
      hcollegeStrict s) :
    SourceStateInvariant quota val_applicant val_college hcollegeStrict
      (sourceStep quota val_applicant val_college hcollegeStrict s) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro a c d hac had
    have hac' := waitingList_sourceStep_subset_old_union_new
      quota val_applicant val_college hcollegeStrict s c hac
    have had' := waitingList_sourceStep_subset_old_union_new
      quota val_applicant val_college hcollegeStrict s d had
    rcases Finset.mem_union.mp hac' with hacOld | hacNew
    · rcases Finset.mem_union.mp had' with hadOld | hadNew
      · exact hinv.1 a c d hacOld hadOld
      · have hactive := (mem_newApplications_spec quota val_applicant
          val_college hcollegeStrict s hadNew).1
        have hassigned := (assignedCollege_eq_some_iff quota val_applicant
          val_college hcollegeStrict s hinv a c).2 hacOld
        rw [hactive.1] at hassigned
        cases hassigned
    · rcases Finset.mem_union.mp had' with hadOld | hadNew
      · have hactive := (mem_newApplications_spec quota val_applicant
          val_college hcollegeStrict s hacNew).1
        have hassigned := (assignedCollege_eq_some_iff quota val_applicant
          val_college hcollegeStrict s hinv a d).2 hadOld
        rw [hactive.1] at hassigned
        cases hassigned
      · have hcNext := (mem_newApplications_iff quota val_applicant
          val_college hcollegeStrict s a c).1 hacNew
        have hdNext := (mem_newApplications_iff quota val_applicant
          val_college hcollegeStrict s a d).1 hadNew
        exact Option.some.inj (hcNext.symm.trans hdNext)
  · intro a c hac
    rcases Finset.mem_union.mp (by simpa [sourceStep] using hac) with
      hacOld | hacNew
    · exact hinv.2.1 a c hacOld
    · have hmem := (mem_newApplications_spec quota val_applicant
        val_college hcollegeStrict s hacNew).2.1
      exact (Finset.mem_filter.mp hmem).2.1
  · intro a c d hac hdEligible hdNot
    have hdNotOld : a ∉ s.applications d := by
      intro hdOld
      apply hdNot
      simp [sourceStep, hdOld]
    rcases Finset.mem_union.mp (by simpa [sourceStep] using hac) with
      hacOld | hacNew
    · exact hinv.2.2 a c d hacOld hdEligible hdNotOld
    · have hspec := mem_newApplications_spec quota val_applicant
        val_college hcollegeStrict s hacNew
      have hdMem : d ∈ untriedEligibleColleges
          val_applicant val_college s a := by
        simp [untriedEligibleColleges, hdEligible, hdNotOld]
      exact hspec.2.2 d hdMem

/-- Empty source application history. -/
def initialSourceState : SourceWaitingListState Applicants Colleges where
  applications _ := ∅

theorem initialSourceState_invariant
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a') :
    SourceStateInvariant quota val_applicant val_college hcollegeStrict
      (initialSourceState (Applicants := Applicants) (Colleges := Colleges)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro a c d hac
    have hfalse : a ∈ (∅ : Finset Applicants) :=
      collegeTopQ_subset quota val_college hcollegeStrict c ∅
        (by simpa [waitingList, initialSourceState] using hac)
    simp at hfalse
  · simp [initialSourceState]
  · simp [initialSourceState]

/-- One literal Section 4 round, exposed as a relation for source-facing paths. -/
def SourceStepRelation
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (before after : SourceWaitingListState Applicants Colleges) : Prop :=
  after = sourceStep quota val_applicant val_college hcollegeStrict before

/-- States reachable from the empty application history by literal rounds. -/
def SourceReachable
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges) : Prop :=
  Relation.ReflTransGen
    (SourceStepRelation quota val_applicant val_college hcollegeStrict)
    (initialSourceState (Applicants := Applicants) (Colleges := Colleges)) s

/-- The finite measure of eligible applicant-college pairs not yet tried. -/
noncomputable def untriedEligiblePairs
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (s : SourceWaitingListState Applicants Colleges) :
    Finset (Applicants × Colleges) := by
  classical
  exact Finset.univ.filter fun p =>
    sourceEligible val_applicant val_college p.1 p.2 /\
      p.1 ∉ s.applications p.2

theorem mem_untriedEligiblePairs_iff
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (s : SourceWaitingListState Applicants Colleges)
    (a : Applicants) (c : Colleges) :
    (a, c) ∈ untriedEligiblePairs val_applicant val_college s <->
      c ∈ untriedEligibleColleges val_applicant val_college s a := by
  classical
  simp [untriedEligiblePairs, untriedEligibleColleges]

theorem untriedEligiblePairs_sourceStep_subset
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges) :
    untriedEligiblePairs val_applicant val_college
        (sourceStep quota val_applicant val_college hcollegeStrict s) <=
      untriedEligiblePairs val_applicant val_college s := by
  classical
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨_hpUniv, hpEligible, hpNot⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ p, hpEligible, ?_⟩
  intro hpOld
  apply hpNot
  simp [sourceStep, hpOld]

theorem untriedEligiblePairs_sourceStep_ssubset_of_active
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges)
    (hactive : exists a, SourceActive quota val_applicant val_college
      hcollegeStrict s a) :
    untriedEligiblePairs val_applicant val_college
        (sourceStep quota val_applicant val_college hcollegeStrict s) <
      untriedEligiblePairs val_applicant val_college s := by
  classical
  refine Finset.ssubset_iff_subset_ne.mpr
    ⟨untriedEligiblePairs_sourceStep_subset quota val_applicant
      val_college hcollegeStrict s, ?_⟩
  rcases hactive with ⟨a, ha⟩
  rcases nextCollege_eq_some_of_active quota val_applicant val_college
      hcollegeStrict s a ha with ⟨c, hcNext, hcUntried, _hcBest⟩
  intro heq
  have hpairOld : (a, c) ∈ untriedEligiblePairs
      val_applicant val_college s :=
    (mem_untriedEligiblePairs_iff val_applicant val_college s a c).2 hcUntried
  have hpairNew : (a, c) ∈ untriedEligiblePairs val_applicant val_college
      (sourceStep quota val_applicant val_college hcollegeStrict s) := by
    rw [heq]
    exact hpairOld
  have hnotApplied := (Finset.mem_filter.mp hpairNew).2.2
  apply hnotApplied
  have hnew : a ∈ newApplications quota val_applicant val_college
      hcollegeStrict s c :=
    (mem_newApplications_iff quota val_applicant val_college
      hcollegeStrict s a c).2 hcNext
  simp [sourceStep, hnew]

theorem untriedEligiblePairs_card_sourceStep_lt_of_active
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges)
    (hactive : exists a, SourceActive quota val_applicant val_college
      hcollegeStrict s a) :
    (untriedEligiblePairs val_applicant val_college
      (sourceStep quota val_applicant val_college hcollegeStrict s)).card <
      (untriedEligiblePairs val_applicant val_college s).card :=
  Finset.card_lt_card
    (untriedEligiblePairs_sourceStep_ssubset_of_active quota val_applicant
      val_college hcollegeStrict s hactive)

/-- Run source rounds until no unmatched applicant can make another application. -/
noncomputable def sourceRunToTerminal
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a') :
    SourceWaitingListState Applicants Colleges ->
      SourceWaitingListState Applicants Colleges
  | s => by
      classical
      exact if hactive : exists a, SourceActive quota val_applicant val_college
            hcollegeStrict s a then
          sourceRunToTerminal quota val_applicant val_college hcollegeStrict
            (sourceStep quota val_applicant val_college hcollegeStrict s)
        else s
termination_by s =>
  (untriedEligiblePairs val_applicant val_college s).card
decreasing_by
  apply untriedEligiblePairs_card_sourceStep_lt_of_active
  assumption

/-- The terminating recursive evaluator realizes a path of literal rounds. -/
theorem sourceRunToTerminal_reachable
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges) :
    Relation.ReflTransGen
      (SourceStepRelation quota val_applicant val_college hcollegeStrict)
      s (sourceRunToTerminal quota val_applicant val_college hcollegeStrict s) := by
  rw [sourceRunToTerminal]
  split
  next hactive =>
    exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (by rfl))
      (sourceRunToTerminal_reachable quota val_applicant val_college
        hcollegeStrict
        (sourceStep quota val_applicant val_college hcollegeStrict s))
  next hnot =>
    exact Relation.ReflTransGen.refl
termination_by
  (untriedEligiblePairs val_applicant val_college s).card
decreasing_by
  apply untriedEligiblePairs_card_sourceStep_lt_of_active
  assumption

theorem sourceRunToTerminal_terminated
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges) :
    ¬ (exists a, SourceActive quota val_applicant val_college
      hcollegeStrict
      (sourceRunToTerminal quota val_applicant val_college
        hcollegeStrict s) a) := by
  rw [sourceRunToTerminal]
  split
  next hactive =>
    exact sourceRunToTerminal_terminated quota val_applicant val_college
      hcollegeStrict
      (sourceStep quota val_applicant val_college hcollegeStrict s)
  next hnot =>
    exact hnot
termination_by
  (untriedEligiblePairs val_applicant val_college s).card
decreasing_by
  apply untriedEligiblePairs_card_sourceStep_lt_of_active
  assumption

theorem sourceRunToTerminal_preserves_invariant
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges)
    (hinv : SourceStateInvariant quota val_applicant val_college
      hcollegeStrict s) :
    SourceStateInvariant quota val_applicant val_college hcollegeStrict
      (sourceRunToTerminal quota val_applicant val_college
        hcollegeStrict s) := by
  rw [sourceRunToTerminal]
  split
  next hactive =>
    exact sourceRunToTerminal_preserves_invariant quota val_applicant
      val_college hcollegeStrict
      (sourceStep quota val_applicant val_college hcollegeStrict s)
      (sourceStep_preserves_invariant quota val_applicant val_college
        hcollegeStrict s hinv)
  next hnot =>
    exact hinv
termination_by
  (untriedEligiblePairs val_applicant val_college s).card
decreasing_by
  apply untriedEligiblePairs_card_sourceStep_lt_of_active
  assumption

/-- Terminal direct source state from the empty application history on strict applicant lists. -/
noncomputable def sourceWaitingListFinalState
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (happlicantStrict : forall a c c',
      val_applicant a c = val_applicant a c' -> c = c') :
    SourceWaitingListState Applicants Colleges :=
  sourceRunToTerminal quota val_applicant val_college hcollegeStrict
    (initialSourceState (Applicants := Applicants) (Colleges := Colleges))

theorem sourceWaitingListFinalState_reachable
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (happlicantStrict : forall a c c',
      val_applicant a c = val_applicant a c' -> c = c') :
    SourceReachable quota val_applicant val_college hcollegeStrict
      (sourceWaitingListFinalState quota val_applicant val_college
        hcollegeStrict happlicantStrict) :=
  sourceRunToTerminal_reachable quota val_applicant val_college
    hcollegeStrict _

theorem sourceWaitingListFinalState_invariant
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (happlicantStrict : forall a c c',
      val_applicant a c = val_applicant a c' -> c = c') :
    SourceStateInvariant quota val_applicant val_college hcollegeStrict
      (sourceWaitingListFinalState quota val_applicant val_college
        hcollegeStrict happlicantStrict) :=
  sourceRunToTerminal_preserves_invariant quota val_applicant val_college
    hcollegeStrict _
    (initialSourceState_invariant quota val_applicant val_college hcollegeStrict)

theorem sourceWaitingListFinalState_terminated
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (happlicantStrict : forall a c c',
      val_applicant a c = val_applicant a c' -> c = c') :
    ¬ (exists a, SourceActive quota val_applicant val_college
      hcollegeStrict
      (sourceWaitingListFinalState quota val_applicant val_college
        hcollegeStrict happlicantStrict) a) :=
  sourceRunToTerminal_terminated quota val_applicant val_college
    hcollegeStrict _

theorem waitingList_subset_applications
    (quota : Colleges -> Nat)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges) (c : Colleges) :
    waitingList quota val_college hcollegeStrict s c <= s.applications c :=
  collegeTopQ_subset quota val_college hcollegeStrict c (s.applications c)

theorem collegeTopQ_card_eq_quota_of_rejected
    (quota : Colleges -> Nat)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (c : Colleges) (pool : Finset Applicants) {a : Applicants}
    (haPool : a ∈ pool)
    (haRejected : a ∉ collegeTopQ quota val_college hcollegeStrict c pool) :
    (collegeTopQ quota val_college hcollegeStrict c pool).card = quota c := by
  classical
  have hqle : quota c <= pool.card := by
    by_contra hnot
    have hcardle : pool.card <= quota c := Nat.le_of_lt (Nat.lt_of_not_ge hnot)
    let C := collegeTopQ quota val_college hcollegeStrict c
    have heq : C pool = pool :=
      QAcceptant.eq_of_card_le
        (collegeTopQ_subset quota val_college hcollegeStrict c)
        (collegeTopQ_card quota val_college hcollegeStrict c)
        hcardle
    exact haRejected (by simpa [C, heq] using haPool)
  rw [collegeTopQ_card]
  exact Nat.min_eq_left hqle

theorem waitingList_card_eq_quota_of_rejected_application
    (quota : Colleges -> Nat)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges)
    {a : Applicants} {c : Colleges}
    (haApplied : a ∈ s.applications c)
    (haRejected : a ∉ waitingList quota val_college hcollegeStrict s c) :
    (waitingList quota val_college hcollegeStrict s c).card = quota c :=
  collegeTopQ_card_eq_quota_of_rejected quota val_college hcollegeStrict
    c (s.applications c) haApplied haRejected

/-- Every rejected application is impossible in every stable assignment. -/
def SourceRejectedPairImpossible
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges) : Prop :=
  forall nu : ManyToOneAssignment Applicants Colleges,
    ManyToOne.IsStable val_applicant val_college quota nu ->
    forall a c, a ∈ s.applications c ->
      a ∉ waitingList quota val_college hcollegeStrict s c ->
      nu.app_match a ≠ some c

theorem initialSourceState_rejected_pair_impossible
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a') :
    SourceRejectedPairImpossible quota val_applicant val_college
      hcollegeStrict
      (initialSourceState (Applicants := Applicants) (Colleges := Colleges)) := by
  intro nu hstable a c ha
  simp [initialSourceState] at ha

private theorem selected_after_step_prefers_college_to_other_stable_match
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (happStrict : forall a c c',
      val_applicant a c = val_applicant a c' -> c = c')
    (happNoZero : forall a c, val_applicant a c ≠ 0)
    (hcollegeNoZero : forall c a, val_college c a ≠ 0)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges)
    (hinv : SourceStateInvariant quota val_applicant val_college
      hcollegeStrict s)
    (hrejected : SourceRejectedPairImpossible quota val_applicant val_college
      hcollegeStrict s)
    (nu : ManyToOneAssignment Applicants Colleges)
    (hnu : ManyToOne.IsStable val_applicant val_college quota nu)
    {a : Applicants} {c : Colleges}
    (haSelected : a ∈ waitingList quota val_college hcollegeStrict
      (sourceStep quota val_applicant val_college hcollegeStrict s) c)
    (haNotC : nu.app_match a ≠ some c) :
    ManyToOne.valApplicant val_applicant a (nu.app_match a) <
      val_applicant a c := by
  classical
  have hstepInv := sourceStep_preserves_invariant quota val_applicant
    val_college hcollegeStrict s hinv
  have hacApplied : a ∈
      (sourceStep quota val_applicant val_college hcollegeStrict s).applications c :=
    waitingList_subset_applications quota val_college hcollegeStrict _ c haSelected
  have hcEligible : sourceEligible val_applicant val_college a c :=
    hstepInv.2.1 a c hacApplied
  have haOrigin := waitingList_sourceStep_subset_old_union_new
    quota val_applicant val_college hcollegeStrict s c haSelected
  rcases Finset.mem_union.mp haOrigin with haOldSelected | haNew
  · have hacOld : a ∈ s.applications c :=
      waitingList_subset_applications quota val_college hcollegeStrict s c
        haOldSelected
    cases hmatch : nu.app_match a with
    | none =>
        simpa [ManyToOne.valApplicant, hmatch] using hcEligible.1
    | some d =>
        have hdc : d ≠ c := by
          intro hdc
          subst d
          exact haNotC hmatch
        have hadRoster : a ∈ nu.college_roster d :=
          (nu.consistent a d).1 hmatch
        have hdAppNonneg : 0 <= val_applicant a d := by
          simpa [ManyToOne.valApplicant, hmatch] using hnu.2.1 a
        have hdCollegeNonneg : 0 <= val_college d a :=
          hnu.2.2.1 d a hadRoster
        have hdEligible : sourceEligible val_applicant val_college a d :=
          ⟨lt_of_le_of_ne hdAppNonneg (happNoZero a d).symm,
            lt_of_le_of_ne hdCollegeNonneg (hcollegeNoZero d a).symm⟩
        by_cases hadApplied : a ∈ s.applications d
        · have haNotWaitingD : a ∉
              waitingList quota val_college hcollegeStrict s d := by
            intro haWaitingD
            exact hdc (hinv.1 a d c haWaitingD haOldSelected)
          exact False.elim
            (hrejected nu hnu a d hadApplied haNotWaitingD hmatch)
        · have hle := hinv.2.2 a c d hacOld hdEligible hadApplied
          have hne : val_applicant a d ≠ val_applicant a c := by
            intro heq
            exact hdc (happStrict a d c heq)
          have hlt : val_applicant a d < val_applicant a c :=
            lt_of_le_of_ne hle hne
          simpa [ManyToOne.valApplicant, hmatch] using hlt
  · have hnewSpec := mem_newApplications_spec quota val_applicant
      val_college hcollegeStrict s haNew
    cases hmatch : nu.app_match a with
    | none =>
        simpa [ManyToOne.valApplicant, hmatch] using hcEligible.1
    | some d =>
        have hdc : d ≠ c := by
          intro hdc
          subst d
          exact haNotC hmatch
        have hadRoster : a ∈ nu.college_roster d :=
          (nu.consistent a d).1 hmatch
        have hdAppNonneg : 0 <= val_applicant a d := by
          simpa [ManyToOne.valApplicant, hmatch] using hnu.2.1 a
        have hdCollegeNonneg : 0 <= val_college d a :=
          hnu.2.2.1 d a hadRoster
        have hdEligible : sourceEligible val_applicant val_college a d :=
          ⟨lt_of_le_of_ne hdAppNonneg (happNoZero a d).symm,
            lt_of_le_of_ne hdCollegeNonneg (hcollegeNoZero d a).symm⟩
        by_cases hadApplied : a ∈ s.applications d
        · have haNotWaitingD : a ∉
              waitingList quota val_college hcollegeStrict s d := by
            intro haWaitingD
            have hassigned := (assignedCollege_eq_some_iff quota val_applicant
              val_college hcollegeStrict s hinv a d).2 haWaitingD
            rw [hnewSpec.1.1] at hassigned
            cases hassigned
          exact False.elim
            (hrejected nu hnu a d hadApplied haNotWaitingD hmatch)
        · have hdUntried : d ∈ untriedEligibleColleges
              val_applicant val_college s a := by
            simp [untriedEligibleColleges, hdEligible, hadApplied]
          have hle := hnewSpec.2.2 d hdUntried
          have hne : val_applicant a d ≠ val_applicant a c := by
            intro heq
            exact hdc (happStrict a d c heq)
          have hlt : val_applicant a d < val_applicant a c :=
            lt_of_le_of_ne hle hne
          simpa [ManyToOne.valApplicant, hmatch] using hlt

theorem sourceStep_preserves_rejected_pair_impossible
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (happStrict : forall a c c',
      val_applicant a c = val_applicant a c' -> c = c')
    (happNoZero : forall a c, val_applicant a c ≠ 0)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (hcollegeNoZero : forall c a, val_college c a ≠ 0)
    (s : SourceWaitingListState Applicants Colleges)
    (hinv : SourceStateInvariant quota val_applicant val_college
      hcollegeStrict s)
    (hrejected : SourceRejectedPairImpossible quota val_applicant val_college
      hcollegeStrict s) :
    SourceRejectedPairImpossible quota val_applicant val_college
      hcollegeStrict
      (sourceStep quota val_applicant val_college hcollegeStrict s) := by
  classical
  intro nu hnu a c haApplied haNotSelected haNuC
  have hfull : (waitingList quota val_college hcollegeStrict
      (sourceStep quota val_applicant val_college hcollegeStrict s) c).card =
      quota c :=
    waitingList_card_eq_quota_of_rejected_application quota val_college
      hcollegeStrict _ haApplied haNotSelected
  have haNuRoster : a ∈ nu.college_roster c :=
    (nu.consistent a c).1 haNuC
  have hnotSubset : ¬ (waitingList quota val_college hcollegeStrict
      (sourceStep quota val_applicant val_college hcollegeStrict s) c <=
      nu.college_roster c) := by
    intro hsubset
    have hinsert : insert a (waitingList quota val_college hcollegeStrict
        (sourceStep quota val_applicant val_college hcollegeStrict s) c) <=
        nu.college_roster c := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact haNuRoster
      · exact hsubset hx
    have hcardInsert := Finset.card_le_card hinsert
    rw [Finset.card_insert_of_notMem haNotSelected, hfull] at hcardInsert
    have hquota := hnu.1 c
    omega
  rcases Finset.not_subset.mp hnotSubset with
    ⟨beta, hbetaSelected, hbetaNotNu⟩
  have hbetaPrefCollege : val_college c a < val_college c beta :=
    collegeTopQ_priority quota val_college hcollegeStrict c
      ((sourceStep quota val_applicant val_college hcollegeStrict s).applications c)
      hbetaSelected haApplied haNotSelected
  have hbetaNotC : nu.app_match beta ≠ some c := by
    intro hbetaC
    exact hbetaNotNu ((nu.consistent beta c).1 hbetaC)
  have hbetaPrefApplicant :=
    selected_after_step_prefers_college_to_other_stable_match
      quota val_applicant val_college happStrict happNoZero
      hcollegeNoZero hcollegeStrict s hinv hrejected nu hnu
      hbetaSelected hbetaNotC
  exact hnu.2.2.2 beta c hbetaPrefApplicant
    (Or.inr ⟨a, haNuRoster, hbetaPrefCollege⟩)

/-- Invariants and rejection impossibility propagate along literal round paths. -/
theorem sourcePath_preserves_invariant_and_rejections
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (happStrict : forall a c c',
      val_applicant a c = val_applicant a c' -> c = c')
    (happNoZero : forall a c, val_applicant a c ≠ 0)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (hcollegeNoZero : forall c a, val_college c a ≠ 0)
    {before after : SourceWaitingListState Applicants Colleges}
    (hpath : Relation.ReflTransGen
      (SourceStepRelation quota val_applicant val_college hcollegeStrict)
      before after) :
    SourceStateInvariant quota val_applicant val_college
        hcollegeStrict before ->
      SourceRejectedPairImpossible quota val_applicant val_college
        hcollegeStrict before ->
      SourceStateInvariant quota val_applicant val_college
          hcollegeStrict after /\
        SourceRejectedPairImpossible quota val_applicant val_college
          hcollegeStrict after := by
  induction hpath using Relation.ReflTransGen.trans_induction_on with
  | refl =>
      intro hinv hrejected
      exact ⟨hinv, hrejected⟩
  | single hstep =>
      intro hinv hrejected
      unfold SourceStepRelation at hstep
      rcases hstep with rfl
      exact
        ⟨sourceStep_preserves_invariant quota val_applicant val_college
            hcollegeStrict _ hinv,
          sourceStep_preserves_rejected_pair_impossible quota val_applicant
            val_college happStrict happNoZero hcollegeStrict hcollegeNoZero
            _ hinv hrejected⟩
  | trans _ _ hleft hright =>
      intro hinv hrejected
      rcases hleft hinv hrejected with ⟨hmiddleInv, hmiddleRejected⟩
      exact hright hmiddleInv hmiddleRejected

/-- Every state reachable by literal rounds carries both proof invariants. -/
theorem sourceReachable_invariant_and_rejections
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hdomain : gs_strict_college_admissions_domain
      val_applicant val_college)
    {s : SourceWaitingListState Applicants Colleges}
    (hreachable : SourceReachable quota val_applicant val_college
      hdomain.2.1 s) :
    SourceStateInvariant quota val_applicant val_college hdomain.2.1 s /\
      SourceRejectedPairImpossible quota val_applicant val_college
        hdomain.2.1 s :=
  sourcePath_preserves_invariant_and_rejections quota val_applicant
    val_college hdomain.1.1 hdomain.1.2 hdomain.2.1 hdomain.2.2 hreachable
    (initialSourceState_invariant quota val_applicant val_college hdomain.2.1)
    (initialSourceState_rejected_pair_impossible quota val_applicant
      val_college hdomain.2.1)

theorem sourceRunToTerminal_preserves_rejected_pair_impossible
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (happStrict : forall a c c',
      val_applicant a c = val_applicant a c' -> c = c')
    (happNoZero : forall a c, val_applicant a c ≠ 0)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (hcollegeNoZero : forall c a, val_college c a ≠ 0)
    (s : SourceWaitingListState Applicants Colleges)
    (hinv : SourceStateInvariant quota val_applicant val_college
      hcollegeStrict s)
    (hrejected : SourceRejectedPairImpossible quota val_applicant val_college
      hcollegeStrict s) :
    SourceRejectedPairImpossible quota val_applicant val_college
      hcollegeStrict
      (sourceRunToTerminal quota val_applicant val_college
        hcollegeStrict s) := by
  rw [sourceRunToTerminal]
  split
  next hactive =>
    exact sourceRunToTerminal_preserves_rejected_pair_impossible
      quota val_applicant val_college happStrict happNoZero
      hcollegeStrict hcollegeNoZero
      (sourceStep quota val_applicant val_college hcollegeStrict s)
      (sourceStep_preserves_invariant quota val_applicant val_college
        hcollegeStrict s hinv)
      (sourceStep_preserves_rejected_pair_impossible quota val_applicant
        val_college happStrict happNoZero hcollegeStrict hcollegeNoZero
        s hinv hrejected)
  next hnot =>
    exact hrejected
termination_by
  (untriedEligiblePairs val_applicant val_college s).card
decreasing_by
  apply untriedEligiblePairs_card_sourceStep_lt_of_active
  assumption

theorem sourceWaitingListFinalState_rejected_pair_impossible
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hdomain : gs_strict_college_admissions_domain
      val_applicant val_college) :
    SourceRejectedPairImpossible quota val_applicant val_college
      hdomain.2.1
      (sourceWaitingListFinalState quota val_applicant val_college
        hdomain.2.1 hdomain.1.1) := by
  exact sourceRunToTerminal_preserves_rejected_pair_impossible
    quota val_applicant val_college hdomain.1.1 hdomain.1.2
    hdomain.2.1 hdomain.2.2
    (initialSourceState (Applicants := Applicants) (Colleges := Colleges))
    (initialSourceState_invariant quota val_applicant val_college hdomain.2.1)
    (initialSourceState_rejected_pair_impossible quota val_applicant
      val_college hdomain.2.1)

private theorem manyToOneAssignment_eq_of_app_match
    {mu nu : ManyToOneAssignment Applicants Colleges}
    (happ : mu.app_match = nu.app_match) :
    mu = nu := by
  cases mu with
  | mk muMatch muRoster muConsistent =>
      cases nu with
      | mk nuMatch nuRoster nuConsistent =>
          dsimp at happ
          subst nuMatch
          have hroster : muRoster = nuRoster := by
            funext c
            ext a
            rw [← muConsistent a c, ← nuConsistent a c]
          subst nuRoster
          rfl

/-- Convert an invariant direct waiting-list state into a many-to-one assignment. -/
noncomputable def sourceAssignmentFromState
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges)
    (hinv : SourceStateInvariant quota val_applicant val_college
      hcollegeStrict s) : ManyToOneAssignment Applicants Colleges where
  app_match := assignedCollege quota val_college hcollegeStrict s
  college_roster := waitingList quota val_college hcollegeStrict s
  consistent a c :=
    assignedCollege_eq_some_iff quota val_applicant val_college
      hcollegeStrict s hinv a c

/--
Proof-free assignment view of a source state. On reachable states its rosters
are exactly the waiting lists; defining consistency through `assignedCollege`
keeps the source-facing result independent of an invariant proof term.
-/
noncomputable def sourceAssignmentView
    (quota : Colleges -> Nat)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges) :
    ManyToOneAssignment Applicants Colleges where
  app_match := assignedCollege quota val_college hcollegeStrict s
  college_roster c := (Finset.univ : Finset Applicants).filter fun a =>
    assignedCollege quota val_college hcollegeStrict s a = some c
  consistent a c := by simp

theorem sourceAssignmentView_eq_sourceAssignmentFromState
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges)
    (hinv : SourceStateInvariant quota val_applicant val_college
      hcollegeStrict s) :
    sourceAssignmentView quota val_college hcollegeStrict s =
      sourceAssignmentFromState quota val_applicant val_college
        hcollegeStrict s hinv := by
  apply manyToOneAssignment_eq_of_app_match
  rfl

/-- The assignment returned by the literal Section 4 runner on strict applicant lists. -/
noncomputable def sourceWaitingListFinalAssignment
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (happlicantStrict : forall a c c',
      val_applicant a c = val_applicant a c' -> c = c') :
    ManyToOneAssignment Applicants Colleges :=
  sourceAssignmentFromState quota val_applicant val_college hcollegeStrict
    (sourceWaitingListFinalState quota val_applicant val_college hcollegeStrict
      happlicantStrict)
    (sourceWaitingListFinalState_invariant quota val_applicant
      val_college hcollegeStrict happlicantStrict)

theorem sourceAssignmentFromState_respects_quota
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges)
    (hinv : SourceStateInvariant quota val_applicant val_college
      hcollegeStrict s) :
    ManyToOneAssignment.RespectsQuota quota
      (sourceAssignmentFromState quota val_applicant val_college
        hcollegeStrict s hinv) := by
  intro c
  change (waitingList quota val_college hcollegeStrict s c).card <= quota c
  unfold waitingList
  rw [collegeTopQ_card]
  exact Nat.min_le_left _ _

theorem sourceAssignmentFromState_applicant_ir
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges)
    (hinv : SourceStateInvariant quota val_applicant val_college
      hcollegeStrict s) :
    forall a, 0 <= ManyToOne.valApplicant val_applicant a
      ((sourceAssignmentFromState quota val_applicant val_college
        hcollegeStrict s hinv).app_match a) := by
  intro a
  cases hmatch : (sourceAssignmentFromState quota val_applicant val_college
      hcollegeStrict s hinv).app_match a with
  | none => simp [ManyToOne.valApplicant, hmatch]
  | some c =>
      have haWaiting : a ∈ waitingList quota val_college hcollegeStrict s c :=
        (sourceAssignmentFromState quota val_applicant val_college
          hcollegeStrict s hinv).consistent a c |>.mp hmatch
      have haApplied := waitingList_subset_applications quota val_college
        hcollegeStrict s c haWaiting
      exact le_of_lt (hinv.2.1 a c haApplied).1

theorem sourceAssignmentFromState_college_ir
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges)
    (hinv : SourceStateInvariant quota val_applicant val_college
      hcollegeStrict s) :
    forall c a,
      a ∈ (sourceAssignmentFromState quota val_applicant val_college
        hcollegeStrict s hinv).college_roster c ->
      0 <= val_college c a := by
  intro c a ha
  have haApplied := waitingList_subset_applications quota val_college
    hcollegeStrict s c ha
  exact le_of_lt (hinv.2.1 a c haApplied).2

private theorem preferred_college_was_applied_of_terminated
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges)
    (hinv : SourceStateInvariant quota val_applicant val_college
      hcollegeStrict s)
    (hterm : ¬ (exists a, SourceActive quota val_applicant val_college
      hcollegeStrict s a))
    (a : Applicants) (c : Colleges)
    (happPref : ManyToOne.valApplicant val_applicant a
        ((sourceAssignmentFromState quota val_applicant val_college
          hcollegeStrict s hinv).app_match a) < val_applicant a c)
    (hcollegeAccept : ManyToOne.CollegeWouldAccept val_college quota
      ((sourceAssignmentFromState quota val_applicant val_college
        hcollegeStrict s hinv).college_roster c) a c) :
    a ∈ s.applications c := by
  classical
  let mu := sourceAssignmentFromState quota val_applicant val_college
    hcollegeStrict s hinv
  have happIR := sourceAssignmentFromState_applicant_ir quota val_applicant
    val_college hcollegeStrict s hinv a
  have hcAppPositive : 0 < val_applicant a c :=
    lt_of_le_of_lt happIR happPref
  have hcCollegePositive : 0 < val_college c a := by
    rcases hcollegeAccept with hroom | hreplace
    · exact hroom.1
    · rcases hreplace with ⟨b, hbRoster, hba⟩
      have hbNonnegative := sourceAssignmentFromState_college_ir
        quota val_applicant val_college hcollegeStrict s hinv c b hbRoster
      linarith
  have hcEligible : sourceEligible val_applicant val_college a c :=
    ⟨hcAppPositive, hcCollegePositive⟩
  by_contra hcNotApplied
  have hcUntried : c ∈ untriedEligibleColleges val_applicant val_college s a := by
    simp [untriedEligibleColleges, hcEligible, hcNotApplied]
  cases hmatch : mu.app_match a with
  | none =>
      apply hterm
      refine ⟨a, ?_, ⟨c, hcUntried⟩⟩
      simpa [mu, sourceAssignmentFromState] using hmatch
  | some d =>
      have hdWaiting : a ∈ waitingList quota val_college hcollegeStrict s d :=
        mu.consistent a d |>.mp hmatch
      have hdApplied := waitingList_subset_applications quota val_college
        hcollegeStrict s d hdWaiting
      have hle := hinv.2.2 a d c hdApplied hcEligible hcNotApplied
      have hlt : val_applicant a d < val_applicant a c := by
        simpa [ManyToOne.valApplicant, mu, hmatch] using happPref
      linarith

theorem sourceAssignmentFromState_stable_of_terminated
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hcollegeStrict : forall c a a',
      val_college c a = val_college c a' -> a = a')
    (s : SourceWaitingListState Applicants Colleges)
    (hinv : SourceStateInvariant quota val_applicant val_college
      hcollegeStrict s)
    (hterm : ¬ (exists a, SourceActive quota val_applicant val_college
      hcollegeStrict s a)) :
    ManyToOne.IsStable val_applicant val_college quota
      (sourceAssignmentFromState quota val_applicant val_college
        hcollegeStrict s hinv) := by
  classical
  refine ⟨sourceAssignmentFromState_respects_quota quota val_applicant
      val_college hcollegeStrict s hinv,
    sourceAssignmentFromState_applicant_ir quota val_applicant
      val_college hcollegeStrict s hinv,
    sourceAssignmentFromState_college_ir quota val_applicant
      val_college hcollegeStrict s hinv, ?_⟩
  intro a c happPref hcollegeAccept
  have haApplied := preferred_college_was_applied_of_terminated
    quota val_applicant val_college hcollegeStrict s hinv hterm
    a c happPref hcollegeAccept
  by_cases haSelected : a ∈ waitingList quota val_college hcollegeStrict s c
  · have haMatch :
        (sourceAssignmentFromState quota val_applicant val_college
          hcollegeStrict s hinv).app_match a = some c :=
      (sourceAssignmentFromState quota val_applicant val_college
        hcollegeStrict s hinv).consistent a c |>.mpr haSelected
    simpa [ManyToOne.valApplicant, haMatch] using happPref
  · have hfull := waitingList_card_eq_quota_of_rejected_application
      quota val_college hcollegeStrict s haApplied haSelected
    rcases hcollegeAccept with hroom | hreplace
    · have hroomCard := hroom.2
      change (waitingList quota val_college hcollegeStrict s c).card <
          quota c at hroomCard
      omega
    · rcases hreplace with ⟨b, hbSelected, hcollegePref⟩
      have hpriority : val_college c a < val_college c b :=
        collegeTopQ_priority quota val_college hcollegeStrict c
          (s.applications c) hbSelected haApplied haSelected
      linarith

/-- The literal source waiting-list runner returns a stable assignment. -/
theorem paper_gs62_source_waiting_list_assignment_stable
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hdomain : gs_strict_college_admissions_domain
      val_applicant val_college) :
    ManyToOne.IsStable val_applicant val_college quota
      (sourceWaitingListFinalAssignment quota val_applicant val_college
        hdomain.2.1 hdomain.1.1) := by
  exact sourceAssignmentFromState_stable_of_terminated quota val_applicant
    val_college hdomain.2.1
    (sourceWaitingListFinalState quota val_applicant val_college hdomain.2.1
      hdomain.1.1)
    (sourceWaitingListFinalState_invariant quota val_applicant
      val_college hdomain.2.1 hdomain.1.1)
    (sourceWaitingListFinalState_terminated quota val_applicant
      val_college hdomain.2.1 hdomain.1.1)

theorem sourceAssignmentFromState_applicant_optimal_of_terminated_rejections
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hdomain : gs_strict_college_admissions_domain
      val_applicant val_college)
    (s : SourceWaitingListState Applicants Colleges)
    (hinv : SourceStateInvariant quota val_applicant val_college
      hdomain.2.1 s)
    (hterm : ¬ (exists a, SourceActive quota val_applicant val_college
      hdomain.2.1 s a))
    (hrejected : SourceRejectedPairImpossible quota val_applicant val_college
      hdomain.2.1 s) :
    gs_applicant_optimal_college_assignment quota val_applicant val_college
      (sourceAssignmentFromState quota val_applicant val_college
        hdomain.2.1 s hinv) := by
  classical
  let mu := sourceAssignmentFromState quota val_applicant val_college
    hdomain.2.1 s hinv
  refine ⟨sourceAssignmentFromState_stable_of_terminated quota val_applicant
      val_college hdomain.2.1 s hinv hterm, ?_⟩
  intro nu hnu a
  by_contra hnot
  have hbetter : ManyToOne.valApplicant val_applicant a (mu.app_match a) <
      ManyToOne.valApplicant val_applicant a (nu.app_match a) :=
    lt_of_not_ge hnot
  cases hnuMatch : nu.app_match a with
  | none =>
      have hmuIR := sourceAssignmentFromState_applicant_ir quota val_applicant
        val_college hdomain.2.1 s hinv a
      change 0 <= ManyToOne.valApplicant val_applicant a (mu.app_match a) at hmuIR
      simp [ManyToOne.valApplicant, hnuMatch] at hbetter
      exact (not_lt_of_ge hmuIR) hbetter
  | some c =>
      have haNuRoster : a ∈ nu.college_roster c :=
        (nu.consistent a c).1 hnuMatch
      have hcAppNonnegative : 0 <= val_applicant a c := by
        simpa [ManyToOne.valApplicant, hnuMatch] using hnu.2.1 a
      have hcCollegeNonnegative : 0 <= val_college c a :=
        hnu.2.2.1 c a haNuRoster
      have hcEligible : sourceEligible val_applicant val_college a c :=
        ⟨lt_of_le_of_ne hcAppNonnegative (hdomain.1.2 a c).symm,
          lt_of_le_of_ne hcCollegeNonnegative (hdomain.2.2 c a).symm⟩
      have hcApplied : a ∈ s.applications c := by
        by_contra hcNotApplied
        have hcUntried : c ∈ untriedEligibleColleges
            val_applicant val_college s a := by
          simp [untriedEligibleColleges, hcEligible, hcNotApplied]
        cases hmuMatch : mu.app_match a with
        | none =>
            apply hterm
            refine ⟨a, ?_, ⟨c, hcUntried⟩⟩
            simpa [mu, sourceAssignmentFromState] using hmuMatch
        | some d =>
            have hdWaiting : a ∈ waitingList quota val_college
                hdomain.2.1 s d := mu.consistent a d |>.mp hmuMatch
            have hdApplied := waitingList_subset_applications quota
              val_college hdomain.2.1 s d hdWaiting
            have hle := hinv.2.2 a d c hdApplied hcEligible hcNotApplied
            have hlt : val_applicant a d < val_applicant a c := by
              simpa [ManyToOne.valApplicant, mu, hmuMatch, hnuMatch] using hbetter
            linarith
      have hcNotWaiting : a ∉ waitingList quota val_college
          hdomain.2.1 s c := by
        intro hcWaiting
        have hmuC : mu.app_match a = some c := mu.consistent a c |>.mpr hcWaiting
        simp [ManyToOne.valApplicant, hmuC, hnuMatch] at hbetter
      exact hrejected nu hnu a c hcApplied hcNotWaiting hnuMatch

/-- Every reachable terminal state realizes the source's applicant-optimal assignment. -/
theorem paper_gs62_source_reachable_terminal_assignment_applicant_optimal
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hdomain : gs_strict_college_admissions_domain
      val_applicant val_college)
    (s : SourceWaitingListState Applicants Colleges)
    (hreachable : SourceReachable quota val_applicant val_college
      hdomain.2.1 s)
    (hterm : ¬ (exists a, SourceActive quota val_applicant val_college
      hdomain.2.1 s a)) :
    gs_applicant_optimal_college_assignment quota val_applicant val_college
      (sourceAssignmentView quota val_college hdomain.2.1 s) := by
  rcases sourceReachable_invariant_and_rejections quota val_applicant
    val_college hdomain hreachable with ⟨hinv, hrejected⟩
  rw [sourceAssignmentView_eq_sourceAssignmentFromState quota val_applicant
    val_college hdomain.2.1 s hinv]
  exact sourceAssignmentFromState_applicant_optimal_of_terminated_rejections
    quota val_applicant val_college hdomain s hinv hterm hrejected

/-- The exact source runner satisfies Gale--Shapley applicant optimality. -/
theorem paper_gs62_source_waiting_list_assignment_applicant_optimal
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hdomain : gs_strict_college_admissions_domain
      val_applicant val_college) :
    gs_applicant_optimal_college_assignment quota val_applicant val_college
      (sourceWaitingListFinalAssignment quota val_applicant val_college
        hdomain.2.1 hdomain.1.1) := by
  exact sourceAssignmentFromState_applicant_optimal_of_terminated_rejections
    quota val_applicant val_college hdomain
    (sourceWaitingListFinalState quota val_applicant val_college hdomain.2.1
      hdomain.1.1)
    (sourceWaitingListFinalState_invariant quota val_applicant
      val_college hdomain.2.1 hdomain.1.1)
    (sourceWaitingListFinalState_terminated quota val_applicant
      val_college hdomain.2.1 hdomain.1.1)
    (sourceWaitingListFinalState_rejected_pair_impossible quota
      val_applicant val_college hdomain)

private theorem option_college_eq_of_same_value
    (val_applicant : Applicants -> Colleges -> Real)
    (happStrict : forall a c c',
      val_applicant a c = val_applicant a c' -> c = c')
    (happNoZero : forall a c, val_applicant a c ≠ 0)
    (a : Applicants) {x y : Option Colleges}
    (hvalue : ManyToOne.valApplicant val_applicant a x =
      ManyToOne.valApplicant val_applicant a y) :
    x = y := by
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some c =>
          have hzero : val_applicant a c = 0 := by
            simpa [ManyToOne.valApplicant] using hvalue.symm
          exact False.elim (happNoZero a c hzero)
  | some c =>
      cases y with
      | none =>
          have hzero : val_applicant a c = 0 := by
            simpa [ManyToOne.valApplicant] using hvalue
          exact False.elim (happNoZero a c hzero)
      | some d =>
          have hcd : c = d := happStrict a c d (by
            simpa [ManyToOne.valApplicant] using hvalue)
          simp [hcd]

/-
Applicant-positive but college-negative cloned-seat proposals do not require a
source application.  They are rejected by college individual rationality, so
the common applicant-optimal stable assignment still identifies the outcomes.
-/
/-- The literal top-`q` runner has exactly the repository applicant-DA outcome. -/
theorem paper_gs62_source_waiting_list_assignment_eq_applicant_da
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (hdomain : gs_strict_college_admissions_domain
      val_applicant val_college) :
    sourceWaitingListFinalAssignment quota val_applicant val_college
        hdomain.2.1 hdomain.1.1 =
      ManyToOneOptimality.refinedDeferredAcceptanceManyToOne
        quota val_applicant val_college hdomain.1.2 := by
  let sourceMu := sourceWaitingListFinalAssignment
    quota val_applicant val_college hdomain.2.1 hdomain.1.1
  let daMu := ManyToOneOptimality.refinedDeferredAcceptanceManyToOne
    quota val_applicant val_college hdomain.1.2
  have hsource : gs_applicant_optimal_college_assignment quota
      val_applicant val_college sourceMu :=
    paper_gs62_source_waiting_list_assignment_applicant_optimal
      quota val_applicant val_college hdomain
  have hda : gs_applicant_optimal_college_assignment quota
      val_applicant val_college daMu :=
    ManyToOneOptimality.paper_gs62_theorem2_arbitrary_quota_applicant_optimal
      quota val_applicant val_college hdomain
  apply manyToOneAssignment_eq_of_app_match
  funext a
  apply option_college_eq_of_same_value val_applicant hdomain.1.1
    hdomain.1.2 a
  exact le_antisymm
    (hda.2 sourceMu hsource.1 a)
    (hsource.2 daMu hda.1 a)

end ExactCollegeBatchedProcedure
end GS62CollegeAdmissions
