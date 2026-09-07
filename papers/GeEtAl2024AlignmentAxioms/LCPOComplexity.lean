import GeEtAl2024AlignmentAxioms.LCPO

/-!
# The quadratic linear-feasibility implementation of LCPO

The implementation paragraph after Theorem 4.3 checks, at every rank position,
whether each candidate can extend the selected prefix while respecting the
linear-feasibility and Pareto constraints.  This file exposes that query as an
existential system over a linear parameter and records the exact square-size
position-by-candidate query schedule.  Thus the formal statement counts the
paper's LP-feasibility calls rather than assigning a fictitious cost to Lean's
noncomputable finite maximizer.
-/

namespace GeEtAl2024AlignmentAxioms

open AppliedModelingLib.Alignment.Axioms
open AppliedModelingLib.SocialChoice.Ranking

/--
The source feasibility query at one LCPO step.  A successful query supplies a
linear parameter whose induced complete ranking extends the current prefix,
respects every unanimous comparison, and places `candidate` at `position`.
-/
def LCPOLinearFeasibilityQuery {Voter : Type*} {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (selectedPrefix : Ranking n)
    (position candidate : Candidate n) : Prop :=
  ∃ contender : Ranking n, ∃ parameter : LinearRewardParameter dimension,
    NondegenerateParameter features parameter ∧
      InducesRanking features parameter contender ∧
      RespectsPareto profile contender ∧
      AgreesBefore selectedPrefix contender position ∧
      contender position = candidate

/-- The linear-parameter query is exactly the `CanPlaceAt` query used by LCPO. -/
theorem lcpoLinearFeasibilityQuery_iff_canPlaceAt
    {Voter : Type*} {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (selectedPrefix : Ranking n)
    (position candidate : Candidate n) :
    LCPOLinearFeasibilityQuery features profile selectedPrefix position candidate ↔
      CanPlaceAt (LinearFeasibleRanking features) profile selectedPrefix position candidate := by
  constructor
  · rintro ⟨contender, parameter, hnondegenerate, hinduced, hpareto, hprefix, hposition⟩
    exact ⟨contender, ⟨⟨parameter, hnondegenerate, hinduced⟩, hpareto⟩,
      hprefix, hposition⟩
  · rintro ⟨contender, ⟨⟨parameter, hnondegenerate, hinduced⟩, hpareto⟩,
      hprefix, hposition⟩
    exact ⟨contender, parameter, hnondegenerate, hinduced, hpareto, hprefix, hposition⟩

/-- All position-by-candidate feasibility checks made by the source algorithm. -/
def lcpoLinearFeasibilityQuerySchedule (n : ℕ) :
    Finset (Candidate n × Candidate n) :=
  Finset.univ.product Finset.univ

/-- The schedule has exactly `|C|²` entries. -/
theorem card_lcpoLinearFeasibilityQuerySchedule (n : ℕ) :
    (lcpoLinearFeasibilityQuerySchedule n).card =
      Fintype.card (Candidate n) ^ 2 := by
  simp [lcpoLinearFeasibilityQuerySchedule, pow_two]

/-- Every position/candidate feasibility query belongs to the square schedule. -/
theorem mem_lcpoLinearFeasibilityQuerySchedule (n : ℕ)
    (position candidate : Candidate n) :
    (position, candidate) ∈ lcpoLinearFeasibilityQuerySchedule n := by
  simp [lcpoLinearFeasibilityQuerySchedule]

/--
The fixed-tie LCPO construction realizes the source implementation rule using
exactly the square position-by-candidate schedule.  At each scheduled query,
no candidate that can extend the prefix through the displayed linear-parameter
system has a better Copeland key than the selected candidate.
-/
theorem fixedTieLCPOOutcome_has_quadratic_linearFeasibilityQuerySchedule
    {Voter : Type*} [Fintype Voter] [Nonempty Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n)
    (hprofile : FeasibleProfile (LinearFeasibleRanking features) profile) :
    (lcpoLinearFeasibilityQuerySchedule n).card =
        Fintype.card (Candidate n) ^ 2 ∧
      ∀ position candidate,
        (position, candidate) ∈ lcpoLinearFeasibilityQuerySchedule n ∧
          (LCPOLinearFeasibilityQuery features profile
              (fixedTieLCPOOutcome (LinearFeasibleRanking features) profile hprofile)
              position candidate →
            ¬ CopelandBetter profile candidate
              (fixedTieLCPOOutcome (LinearFeasibleRanking features) profile hprofile position)) := by
  refine ⟨card_lcpoLinearFeasibilityQuerySchedule n, ?_⟩
  intro position candidate
  refine ⟨mem_lcpoLinearFeasibilityQuerySchedule n position candidate, ?_⟩
  intro hquery
  exact (fixedTieLCPOOutcome_isFixedTieLCPOOutcome
    (LinearFeasibleRanking features) profile hprofile).2 position candidate
      ((lcpoLinearFeasibilityQuery_iff_canPlaceAt
        features profile
        (fixedTieLCPOOutcome (LinearFeasibleRanking features) profile hprofile)
        position candidate).mp hquery)

end GeEtAl2024AlignmentAxioms
