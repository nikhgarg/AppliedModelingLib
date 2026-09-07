import GS62CollegeAdmissions.SourceCompletion

/-!
# Literal college-stability definition in Gale--Shapley 1962

The displayed definition on printed page 10 calls an assignment unstable when
one *currently assigned* applicant can replace another currently assigned
applicant at a college that prefers the former.  It does not itself mention
individual rationality, vacant seats, or an unmatched applicant's ability to
displace a current assignee.  The shared many-to-one API uses the standard
stronger definition containing all of those conditions.

This file keeps the two predicates separate and proves their exact relation.
It deliberately does not infer the missing clauses from a predicate name or
from the later deferred-acceptance construction.
-/

namespace GS62CollegeAdmissions

open AppliedModelingLib.Matching

/--
The replacement-pair condition displayed in the first definition on printed
page 10: applicant `beta`, currently assigned to `B`, and college `A` prefer
one another to `beta`'s current college and a currently assigned applicant
`alpha` of `A`, respectively.

This is a literal transcription of the displayed condition.  In particular,
it has no implicit individual-rationality, vacancy, or unmatched-applicant
clause.
-/
def gs62ReplacementPair {Applicants Colleges : Type*}
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  exists alpha beta A B,
    mu.app_match alpha = some A /\
      mu.app_match beta = some B /\
        val_applicant beta B < val_applicant beta A /\
          val_college A alpha < val_college A beta

/--
The literal negation of the displayed page-10 replacement-pair condition.
This is the paper's first stated requirement on an assignment, before adding
the standard matching-theory completion conditions.
-/
def gs62LiteralStableCollegeAssignment {Applicants Colleges : Type*}
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  Not (gs62ReplacementPair val_applicant val_college mu)

/-- The page-10 replacement-pair definition unfolds exactly as displayed. -/
theorem gs62ReplacementPair_iff_source_definition {Applicants Colleges : Type*}
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (mu : ManyToOneAssignment Applicants Colleges) :
    gs62ReplacementPair val_applicant val_college mu <->
      exists alpha beta A B,
        mu.app_match alpha = some A /\
          mu.app_match beta = some B /\
            val_applicant beta B < val_applicant beta A /\
              val_college A alpha < val_college A beta := by
  rfl

/-- The literal source-stability predicate is precisely no replacement pair. -/
theorem gs62LiteralStableCollegeAssignment_iff_source_definition
    {Applicants Colleges : Type*}
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (mu : ManyToOneAssignment Applicants Colleges) :
    gs62LiteralStableCollegeAssignment val_applicant val_college mu <->
      Not (exists alpha beta A B,
        mu.app_match alpha = some A /\
          mu.app_match beta = some B /\
            val_applicant beta B < val_applicant beta A /\
              val_college A alpha < val_college A beta) := by
  rfl

/--
The reusable, standard many-to-one matching-theory notion used by the existing
runner and optimality proofs.  It is intentionally named separately from the
literal page-10 predicate.
-/
def gs62StandardStableCollegeAssignment {Applicants Colleges : Type*}
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  ManyToOne.IsStable val_applicant val_college quota mu

/-- The standard operational predicate is the shared many-to-one predicate. -/
theorem gs62StandardStableCollegeAssignment_iff_standard_definition
    {Applicants Colleges : Type*}
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (mu : ManyToOneAssignment Applicants Colleges) :
    gs62StandardStableCollegeAssignment quota val_applicant val_college mu <->
      ManyToOne.IsStable val_applicant val_college quota mu := by
  rfl

/--
Standard many-to-one stability rules out every literal source replacement
pair.  This direction needs no fullness, acceptability, or completeness
assumption: a source replacement pair is already a standard blocking pair
through its currently assigned displaced applicant.
-/
theorem gs62LiteralStable_of_standardStable {Applicants Colleges : Type*}
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (mu : ManyToOneAssignment Applicants Colleges)
    (hstable : gs62StandardStableCollegeAssignment
      quota val_applicant val_college mu) :
    gs62LiteralStableCollegeAssignment val_applicant val_college mu := by
  intro hreplacement
  rcases hreplacement with ⟨alpha, beta, A, B, halpha, hbeta, hbetaPref, hcollegePref⟩
  have hbetaPref' :
      ManyToOne.valApplicant val_applicant beta (mu.app_match beta) <
        val_applicant beta A := by
    simpa [ManyToOne.valApplicant, hbeta] using hbetaPref
  have hcollegeAccept :
      ManyToOne.CollegeWouldAccept val_college quota (mu.college_roster A) beta A :=
    Or.inr ⟨alpha, (mu.consistent alpha A).1 halpha, hcollegePref⟩
  exact hstable.2.2.2 beta A hbetaPref' hcollegeAccept

/--
An explicit full-assignment regime under which the literal replacement-pair
condition has all the missing standard-stability cases available.  The clauses
are kept separate in the bridge theorem below so callers cannot mistake this
for the general Section 4 model: page 9 only says every quota is filled when
there are enough applicants, while page 13 permits an applicant to exhaust all
colleges to which they are willing and permitted to apply.
-/
def gs62CompleteFullAcceptableAssignment {Applicants Colleges : Type*}
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  ManyToOneAssignment.RespectsQuota quota mu /\
    (forall a, exists c, mu.app_match a = some c) /\
      (forall c, (mu.college_roster c).card = quota c) /\
        (forall a c, mu.app_match a = some c -> 0 <= val_applicant a c) /\
          forall c a, a ∈ mu.college_roster c -> 0 <= val_college c a

/--
In the explicit complete, full-quota, individually-rational regime, the
literal source definition and standard many-to-one stability agree.  This is
not applied to the general arbitrary-quota source procedure, which may leave
applicants unmatched or quotas unfilled.
-/
theorem gs62StandardStable_of_literalStable_of_completeFullAcceptable
    {Applicants Colleges : Type*}
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (mu : ManyToOneAssignment Applicants Colleges)
    (hliteral : gs62LiteralStableCollegeAssignment val_applicant val_college mu)
    (hcomplete : gs62CompleteFullAcceptableAssignment
      quota val_applicant val_college mu) :
    gs62StandardStableCollegeAssignment quota val_applicant val_college mu := by
  rcases hcomplete with ⟨hquota, hassigned, hfull, happIR, hcollegeIR⟩
  refine ⟨hquota, ?_, ?_, ?_⟩
  · intro a
    rcases hassigned a with ⟨c, hmatch⟩
    simpa [ManyToOne.valApplicant, hmatch] using happIR a c hmatch
  · exact hcollegeIR
  · intro beta A hbetaPref hcollegeAccept
    rcases hassigned beta with ⟨B, hbeta⟩
    have hbetaPref' : val_applicant beta B < val_applicant beta A := by
      simpa [ManyToOne.valApplicant, hbeta] using hbetaPref
    rcases hcollegeAccept with hfree | hreplace
    · have hnotLt : Not ((mu.college_roster A).card < quota A) := by
        rw [hfull A]
        exact lt_irrefl _
      exact False.elim (hnotLt hfree.2)
    · rcases hreplace with ⟨alpha, halpha, hcollegePref⟩
      exact hliteral ⟨alpha, beta, A, B,
        (mu.consistent alpha A).2 halpha, hbeta, hbetaPref', hcollegePref⟩

/--
The exact bridge statement: standard stability always implies the literal
source condition, and the converse needs the explicit complete/full/acceptable
regime above.
-/
theorem gs62StandardStable_iff_literalStable_of_completeFullAcceptable
    {Applicants Colleges : Type*}
    (quota : Colleges -> Nat)
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (mu : ManyToOneAssignment Applicants Colleges)
    (hcomplete : gs62CompleteFullAcceptableAssignment
      quota val_applicant val_college mu) :
    gs62StandardStableCollegeAssignment quota val_applicant val_college mu <->
      gs62LiteralStableCollegeAssignment val_applicant val_college mu := by
  constructor
  · exact gs62LiteralStable_of_standardStable quota val_applicant val_college mu
  · intro hliteral
    exact gs62StandardStable_of_literalStable_of_completeFullAcceptable
      quota val_applicant val_college mu hliteral hcomplete

/-! ## Boundary witness for the raw displayed predicate -/

/-- A one-seat, two-applicant market used to expose the unmatched-applicant gap. -/
def gs62RawLiteralBoundaryApplicantValue : Fin 2 -> Fin 1 -> Real :=
  fun _ _ => 1

/-- The college ranks applicant `1` strictly above applicant `0`. -/
def gs62RawLiteralBoundaryCollegeValue : Fin 1 -> Fin 2 -> Real :=
  fun _ a => if a = 0 then 1 else 2

/-- The single college has one seat. -/
def gs62RawLiteralBoundaryQuota : Fin 1 -> Nat := fun _ => 1

/--
The boundary market satisfies the paper's own strict-list domain: every listed
pair is mutually acceptable and the college strictly ranks the two applicants.
-/
theorem gs62RawLiteralBoundary_strictCollegeAdmissionsDomain :
    gs_strict_college_admissions_domain
      gs62RawLiteralBoundaryApplicantValue
      gs62RawLiteralBoundaryCollegeValue := by
  constructor
  · constructor
    · intro a c c' _
      fin_cases c
      fin_cases c'
      rfl
    · intro a c
      fin_cases a <;> fin_cases c <;>
        norm_num [gs62RawLiteralBoundaryApplicantValue]
  · constructor
    · intro c a a' h
      fin_cases c
      fin_cases a
      · fin_cases a'
        · rfl
        · norm_num [gs62RawLiteralBoundaryCollegeValue] at h
      · fin_cases a'
        · norm_num [gs62RawLiteralBoundaryCollegeValue] at h
        · rfl
    · intro c a
      fin_cases c
      fin_cases a <;> norm_num [gs62RawLiteralBoundaryCollegeValue]

/--
The raw literal candidate assigns applicant `0` to the college and leaves the
higher-ranked applicant `1` unmatched.  Both applicants and the college find
each other acceptable; the failure is solely that the printed condition needs
two currently assigned applicants.
-/
def gs62RawLiteralBoundaryAssignment : ManyToOneAssignment (Fin 2) (Fin 1) where
  app_match a := if a = 0 then some 0 else none
  college_roster _ := {0}
  consistent a c := by
    fin_cases a <;> fin_cases c <;> simp

/--
The raw printed replacement-pair predicate calls the boundary assignment
stable, because it has only one assigned applicant.
-/
theorem gs62RawLiteralBoundaryAssignment_literalStable :
    gs62LiteralStableCollegeAssignment
      gs62RawLiteralBoundaryApplicantValue
      gs62RawLiteralBoundaryCollegeValue
      gs62RawLiteralBoundaryAssignment := by
  intro hreplacement
  rcases hreplacement with ⟨alpha, beta, A, B, halpha, hbeta, _hbetaPref, hcollegePref⟩
  fin_cases alpha <;> fin_cases beta <;> fin_cases A <;> fin_cases B <;>
    simp [gs62RawLiteralBoundaryAssignment,
      gs62RawLiteralBoundaryCollegeValue] at *

/--
The same assignment is not standard-stable: the unmatched higher-ranked
applicant and the college form a blocking pair.  Thus the raw displayed
predicate cannot be substituted for standard stability in the general
arbitrary-quota model or in Theorem 2's comparison class.
-/
theorem gs62RawLiteralBoundaryAssignment_not_standardStable :
    Not (gs62StandardStableCollegeAssignment gs62RawLiteralBoundaryQuota
      gs62RawLiteralBoundaryApplicantValue
      gs62RawLiteralBoundaryCollegeValue
      gs62RawLiteralBoundaryAssignment) := by
  intro hstable
  have happPref :
      ManyToOne.valApplicant gs62RawLiteralBoundaryApplicantValue 1
          (gs62RawLiteralBoundaryAssignment.app_match 1) <
        gs62RawLiteralBoundaryApplicantValue 1 0 := by
    norm_num [ManyToOne.valApplicant, gs62RawLiteralBoundaryAssignment,
      gs62RawLiteralBoundaryApplicantValue]
  have hcollegeAccept : ManyToOne.CollegeWouldAccept
      gs62RawLiteralBoundaryCollegeValue gs62RawLiteralBoundaryQuota
      (gs62RawLiteralBoundaryAssignment.college_roster 0) 1 0 := by
    right
    refine ⟨0, ?_, ?_⟩
    · simp [gs62RawLiteralBoundaryAssignment]
    · norm_num [gs62RawLiteralBoundaryCollegeValue]
  exact hstable.2.2.2 1 0 happPref hcollegeAccept

/--
The second displayed definition on printed page 10: an assignment is
applicant-optimal when it is literally stable and no applicant prefers that
applicant's assignment in any other literally stable assignment.  This keeps
the source comparison class separate from the completed standard convention
used by the checked Theorem 2 route.
-/
def gs62LiteralApplicantOptimalCollegeAssignment {Applicants Colleges : Type*}
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  gs62LiteralStableCollegeAssignment val_applicant val_college mu /\
    forall nu, gs62LiteralStableCollegeAssignment val_applicant val_college nu ->
      forall a,
        ManyToOne.valApplicant val_applicant a (nu.app_match a) <=
          ManyToOne.valApplicant val_applicant a (mu.app_match a)

/--
Exact unfolding of the page-10 applicant-optimality definition over the
literal no-replacement notion of stability.
-/
theorem gs62LiteralApplicantOptimalCollegeAssignment_iff_source_definition
    {Applicants Colleges : Type*}
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (mu : ManyToOneAssignment Applicants Colleges) :
    gs62LiteralApplicantOptimalCollegeAssignment val_applicant val_college mu <->
      gs62LiteralStableCollegeAssignment val_applicant val_college mu /\
        forall nu, gs62LiteralStableCollegeAssignment val_applicant val_college nu ->
          forall a,
            ManyToOne.valApplicant val_applicant a (nu.app_match a) <=
              ManyToOne.valApplicant val_applicant a (mu.app_match a) := by
  rfl

/--
Backward-compatible name for the literal source predicate used by the
boundary witness below.
-/
abbrev gs62RawLiteralApplicantOptimal {Applicants Colleges : Type*}
    (val_applicant : Applicants -> Colleges -> Real)
    (val_college : Colleges -> Applicants -> Real)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  gs62LiteralApplicantOptimalCollegeAssignment val_applicant val_college mu

/--
The competing one-seat assignment gives the college to its preferred applicant
`1` and leaves applicant `0` unmatched.
-/
def gs62RawLiteralBoundaryPreferredAssignment :
    ManyToOneAssignment (Fin 2) (Fin 1) where
  app_match a := if a = 1 then some 0 else none
  college_roster _ := {1}
  consistent a c := by
    fin_cases a <;> fin_cases c <;> simp

/-- The preferred-assignee outcome also has no raw literal replacement pair. -/
theorem gs62RawLiteralBoundaryPreferredAssignment_literalStable :
    gs62LiteralStableCollegeAssignment
      gs62RawLiteralBoundaryApplicantValue
      gs62RawLiteralBoundaryCollegeValue
      gs62RawLiteralBoundaryPreferredAssignment := by
  intro hreplacement
  rcases hreplacement with ⟨alpha, beta, A, B, halpha, hbeta, _hbetaPref, hcollegePref⟩
  fin_cases alpha <;> fin_cases beta <;> fin_cases A <;> fin_cases B <;>
    simp [gs62RawLiteralBoundaryPreferredAssignment,
      gs62RawLiteralBoundaryCollegeValue] at *

/--
The raw literal page-10 stability predicate is too weak for the page-14
applicant-optimality comparison: the preferred-assignee outcome is not optimal
against the other raw-literal-stable assignment, which improves applicant `0`.
This is a boundary theorem about the uncompleted reading, not a claim that the
paper's completed theorem is false.
-/
theorem gs62RawLiteralBoundaryPreferredAssignment_not_rawLiteralApplicantOptimal :
    Not (gs62RawLiteralApplicantOptimal
      gs62RawLiteralBoundaryApplicantValue
      gs62RawLiteralBoundaryCollegeValue
      gs62RawLiteralBoundaryPreferredAssignment) := by
  intro hoptimal
  have hcomparison := hoptimal.2 gs62RawLiteralBoundaryAssignment
    gs62RawLiteralBoundaryAssignment_literalStable 0
  norm_num [ManyToOne.valApplicant,
    gs62RawLiteralBoundaryApplicantValue,
    gs62RawLiteralBoundaryAssignment,
    gs62RawLiteralBoundaryPreferredAssignment] at hcomparison

end GS62CollegeAdmissions
