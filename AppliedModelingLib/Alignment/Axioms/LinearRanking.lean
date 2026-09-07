import AppliedModelingLib.SocialChoice.Ranking.Basic

/-!
# Finite linear rank-aggregation axioms

This module separates the source paper's finite ranking/profile vocabulary
from any particular feature embedding or aggregation algorithm.  A caller
supplies the predicate identifying rankings feasible for its linear-feature
model.  The module then states the four paper-independent social-choice
axioms in terms of that predicate.

The public primitives intentionally use `Ranking.Candidate n`, whose universe
has at least two alternatives, and `Ranking.Ranking n`, which is a total
ranking represented by a permutation.

## Main declarations

- `RankingProfile`
- `LinearRankAggregationRule`
- `ParetoOptimal`
- `PairwiseMajorityConsistent`
- `MajorityConsistent`
- `WinnerMonotonic`
-/

namespace AppliedModelingLib
namespace Alignment
namespace Axioms

open SocialChoice.Ranking

/-- A profile assigns one complete ranking to each voter. -/
abbrev RankingProfile (Voter : Type*) (n : ℕ) := Voter → Ranking n

/-- Candidate `first` is strictly above `second` in a ranking. -/
def StrictlyPrefers {n : ℕ} (ranking : Ranking n)
    (first second : Candidate n) : Prop :=
  rankOf ranking first < rankOf ranking second

/-- Strict preference in a finite ranking is decidable. -/
instance instDecidableStrictlyPrefers {n : ℕ} (ranking : Ranking n)
    (first second : Candidate n) : Decidable (StrictlyPrefers ranking first second) :=
  inferInstanceAs (Decidable (rankOf ranking first < rankOf ranking second))

/-- The finite set of voters satisfying a decidable predicate. -/
def votersSatisfying {Voter : Type*} [Fintype Voter]
    (predicate : Voter → Prop) [DecidablePred predicate] : Finset Voter :=
  Finset.univ.filter predicate

/-- More than half of the finite voter population satisfies `predicate`. -/
def StrictMajority {Voter : Type*} [Fintype Voter]
    (predicate : Voter → Prop) [DecidablePred predicate] : Prop :=
  Fintype.card Voter < 2 * (votersSatisfying predicate).card

/-- A strict majority ranks `first` above `second`. -/
def StrictMajorityPrefers {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (first second : Candidate n) : Prop :=
  StrictMajority (fun voter => StrictlyPrefers (profile voter) first second)

/-- Strict-majority preference is decidable when the voter carrier is finite. -/
instance instDecidableStrictMajorityPrefers {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (first second : Candidate n) :
    Decidable (StrictMajorityPrefers profile first second) := by
  unfold StrictMajorityPrefers StrictMajority votersSatisfying
  infer_instance

/-- Every voter ranks `first` above `second`. -/
def UniversallyPreferred {Voter : Type*} {n : ℕ}
    (profile : RankingProfile Voter n) (first second : Candidate n) : Prop :=
  ∀ voter, StrictlyPrefers (profile voter) first second

/-- Universal finite-profile preference is decidable from the submitted rankings. -/
instance instDecidableUniversallyPreferred {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (first second : Candidate n) :
    Decidable (UniversallyPreferred profile first second) := by
  unfold UniversallyPreferred
  exact Fintype.decidableForallFintype

/-- A profile whose submitted rankings all belong to a supplied feasible set. -/
def FeasibleProfile {Voter : Type*} {n : ℕ}
    (feasible : Ranking n → Prop) (profile : RankingProfile Voter n) : Prop :=
  ∀ voter, feasible (profile voter)

/--
A linear-rank-aggregation rule with an explicit output-feasibility guarantee.
The feature vectors/parameters which justify `feasible` stay external to this
generic social-choice interface.
-/
structure LinearRankAggregationRule (Voter : Type*) (n : ℕ)
    (feasible : Ranking n → Prop) where
  run : RankingProfile Voter n → Ranking n
  output_feasible : ∀ profile, feasible (run profile)

/-- Two profiles induce the same directed strict-pairwise-majority relation. -/
def SamePairwiseMajorityRelation {Voter : Type*} [Fintype Voter] {n : ℕ}
    (firstProfile secondProfile : RankingProfile Voter n) : Prop :=
  ∀ first second,
    StrictMajorityPrefers firstProfile first second ↔
      StrictMajorityPrefers secondProfile first second

/--
The paper's `C1` condition: a rule's output depends only on the directed
strict-pairwise-majority relation of its input profile.
-/
def C1LinearRankAggregationRule {Voter : Type*} [Fintype Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (rule : LinearRankAggregationRule Voter n feasible) : Prop :=
  ∀ firstProfile secondProfile,
    SamePairwiseMajorityRelation firstProfile secondProfile →
      rule.run firstProfile = rule.run secondProfile

/-- Equality of profiles is a trivial same-majority-relation witness. -/
theorem samePairwiseMajorityRelation_refl {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) :
    SamePairwiseMajorityRelation profile profile := by
  intro first second
  rfl

/-- A ranking precisely follows every strict pairwise majority in a profile. -/
def IsPairwiseMajorityRanking {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (ranking : Ranking n) : Prop :=
  ∀ first second,
    StrictlyPrefers ranking first second ↔ StrictMajorityPrefers profile first second

/--
Definition 2.1 of Ge et al. (2024), specialized to finite ranking profiles:
unanimously preferred candidates remain ordered that way by the rule.
-/
def ParetoOptimal {Voter : Type*} {n : ℕ} (feasible : Ranking n → Prop)
    (rule : LinearRankAggregationRule Voter n feasible) : Prop :=
  ∀ profile first second,
    FeasibleProfile feasible profile → UniversallyPreferred profile first second →
      StrictlyPrefers (rule.run profile) first second

/--
Definition 2.2 of Ge et al. (2024), specialized to finite ranking profiles:
when a feasible ranking realizes all strict pairwise majorities, the rule
returns that ranking.
-/
def PairwiseMajorityConsistent {Voter : Type*} [Fintype Voter] {n : ℕ}
    (feasible : Ranking n → Prop)
    (rule : LinearRankAggregationRule Voter n feasible) : Prop :=
  ∀ profile majorityRanking,
    FeasibleProfile feasible profile → feasible majorityRanking →
      IsPairwiseMajorityRanking profile majorityRanking → rule.run profile = majorityRanking

/-- Candidate `candidate` is ranked first by a strict majority of voters. -/
noncomputable def MajorityTopChoice {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (candidate : Candidate n) : Prop := by
  classical
  exact StrictMajority (fun voter => firstChoice (profile voter) = candidate)

/--
Definition 4.1 of Ge et al. (2024), specialized to finite ranking profiles.
-/
def MajorityConsistent {Voter : Type*} [Fintype Voter] {n : ℕ}
    (feasible : Ranking n → Prop)
    (rule : LinearRankAggregationRule Voter n feasible) : Prop :=
  ∀ profile candidate,
    FeasibleProfile feasible profile → MajorityTopChoice profile candidate →
      firstChoice (rule.run profile) = candidate

/--
`updated` elevates `candidate` relative to `original`, while preserving all
pairwise comparisons between the other candidates.
-/
def ElevatesCandidate {n : ℕ} (original updated : Ranking n)
    (candidate : Candidate n) : Prop :=
  rankOf updated candidate ≤ rankOf original candidate ∧
    ∀ first second, first ≠ candidate → second ≠ candidate →
      (StrictlyPrefers original first second ↔ StrictlyPrefers updated first second)

/-- A profile update changes one voter's ranking by elevating one candidate. -/
def ProfileElevatesCandidate {Voter : Type*} {n : ℕ}
    (original updated : RankingProfile Voter n) (voter : Voter)
    (candidate : Candidate n) : Prop :=
  ElevatesCandidate (original voter) (updated voter) candidate ∧
    ∀ otherVoter, otherVoter ≠ voter → updated otherVoter = original otherVoter

/--
Definition 4.2 of Ge et al. (2024), specialized to feasible finite profiles.
Elevating an output winner in one submitted ranking leaves it the output
winner after the update.
-/
def WinnerMonotonic {Voter : Type*} {n : ℕ} (feasible : Ranking n → Prop)
    (rule : LinearRankAggregationRule Voter n feasible) : Prop :=
  ∀ original updated voter candidate,
    FeasibleProfile feasible original → FeasibleProfile feasible updated →
      firstChoice (rule.run original) = candidate →
      ProfileElevatesCandidate original updated voter candidate →
        firstChoice (rule.run updated) = candidate

@[simp] theorem not_strictlyPrefers_self {n : ℕ} (ranking : Ranking n)
    (candidate : Candidate n) : ¬ StrictlyPrefers ranking candidate candidate := by
  exact lt_irrefl _

/-- Every two distinct candidates are strictly ordered in a finite ranking. -/
theorem strictlyPrefers_or_reverse_of_ne {n : ℕ} (ranking : Ranking n)
    {first second : Candidate n} (hdistinct : first ≠ second) :
    StrictlyPrefers ranking first second ∨ StrictlyPrefers ranking second first := by
  have hrank_distinct : rankOf ranking first ≠ rankOf ranking second := by
    intro hranks
    apply hdistinct
    exact ranking.symm.injective hranks
  rcases lt_or_gt_of_ne hrank_distinct with hforward | hreverse
  · exact Or.inl hforward
  · exact Or.inr hreverse

/-- The first-ranked candidate is strictly preferred to every distinct candidate. -/
theorem strictlyPrefers_firstChoice_of_ne {n : ℕ} (ranking : Ranking n)
    {candidate : Candidate n} (hdistinct : candidate ≠ firstChoice ranking) :
    StrictlyPrefers ranking (firstChoice ranking) candidate := by
  unfold StrictlyPrefers
  rw [rankOf_firstChoice]
  apply Fin.pos_iff_ne_zero.mpr
  intro hzero
  apply hdistinct
  calc
    candidate = ranking (rankOf ranking candidate) := by simp [rankOf]
    _ = ranking 0 := congrArg ranking hzero
    _ = firstChoice ranking := rfl

theorem elevatesCandidate_refl {n : ℕ} (ranking : Ranking n)
    (candidate : Candidate n) : ElevatesCandidate ranking ranking candidate := by
  refine ⟨le_rfl, ?_⟩
  intro first second _hfirst _hsecond
  rfl

theorem profileElevatesCandidate_refl {Voter : Type*} {n : ℕ}
    (profile : RankingProfile Voter n) (voter : Voter) (candidate : Candidate n) :
    ProfileElevatesCandidate profile profile voter candidate := by
  refine ⟨elevatesCandidate_refl (profile voter) candidate, ?_⟩
  intro otherVoter _h
  rfl

end Axioms
end Alignment
end AppliedModelingLib
