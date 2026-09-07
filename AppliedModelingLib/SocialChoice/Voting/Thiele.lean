import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Thiele Committee Scores

Reusable finite approval-ballot and committee-score primitives for
multi-member voting rules.

The module is intentionally score-agnostic: PAV, Thiele-squared, and other
rules should instantiate `thieleScore` with the relevant weight sequence.
-/

namespace AppliedModelingLib
namespace SocialChoice
namespace Voting

/-- A finite approval ballot over candidates. -/
abbrev ApprovalBallot (Candidate : Type*) := Finset Candidate

/-- The number of approved committee members on one ballot. -/
def approvedCommitteeCount {Candidate : Type*} [DecidableEq Candidate]
    (committee ballot : Finset Candidate) : ℕ :=
  (committee ∩ ballot).card

/--
Generic Thiele-style committee score for a finite profile of approval ballots.

The weight function maps the number of approved committee members on a ballot
to that ballot's score contribution.
-/
def thieleScore {Candidate Score : Type*} [DecidableEq Candidate] [AddMonoid Score]
    (weight : ℕ → Score) (committee : Finset Candidate)
    (profile : List (ApprovalBallot Candidate)) : Score :=
  (profile.map fun ballot => weight (approvedCommitteeCount committee ballot)).sum

@[simp] theorem thieleScore_nil {Candidate Score : Type*}
    [DecidableEq Candidate] [AddMonoid Score]
    (weight : ℕ → Score) (committee : Finset Candidate) :
    thieleScore weight committee ([] : List (ApprovalBallot Candidate)) = 0 := rfl

/--
PAV marginal weight as a total function on natural counts.

The zero-count contribution is set to zero; positive counts receive weight
`1 / approved`.
-/
noncomputable def pavWeight (approved : ℕ) : ℝ :=
  if approved = 0 then 0 else (approved : ℝ)⁻¹

/-- Proportional approval voting is the Thiele score with harmonic weights. -/
noncomputable def pavScore {Candidate : Type*} [DecidableEq Candidate]
    (committee : Finset Candidate) (profile : List (ApprovalBallot Candidate)) : ℝ :=
  thieleScore pavWeight committee profile

@[simp] theorem pavWeight_zero : pavWeight 0 = 0 := by
  simp [pavWeight]

theorem pavWeight_of_pos {approved : ℕ} (h : 0 < approved) :
    pavWeight approved = (approved : ℝ)⁻¹ := by
  simp [pavWeight, Nat.ne_of_gt h]

@[simp] theorem pavScore_nil {Candidate : Type*} [DecidableEq Candidate]
    (committee : Finset Candidate) :
    pavScore committee ([] : List (ApprovalBallot Candidate)) = 0 := rfl

/-- Harmonic PAV score contribution for `n` approved winners. -/
noncomputable def pavHarmonicSum : ℕ → ℝ
  | 0 => 0
  | n + 1 => pavHarmonicSum n + pavWeight (n + 1)

@[simp] theorem pavHarmonicSum_zero : pavHarmonicSum 0 = 0 := rfl

@[simp] theorem pavHarmonicSum_succ (n : ℕ) :
    pavHarmonicSum (n + 1) = pavHarmonicSum n + pavWeight (n + 1) := rfl

/--
Two-party PAV score as a function of one party's seat count.

The other party receives `seats - seatCount` seats.
-/
noncomputable def twoPartyPAVSeatScore (partyShare : ℝ) (seats seatCount : ℕ) : ℝ :=
  partyShare * pavHarmonicSum seatCount +
    (1 - partyShare) * pavHarmonicSum (seats - seatCount)

/--
`choice` is a score-maximizing natural number up to `upper`, with ties broken
toward the smallest maximizing value.
-/
def IsMinArgmaxOn (score : ℕ → ℝ) (choice upper : ℕ) : Prop :=
  choice ≤ upper ∧
    (∀ candidate, candidate ≤ upper → score candidate ≤ score choice) ∧
    (∀ candidate, candidate ≤ upper → score candidate = score choice → choice ≤ candidate)

/-- A finite natural score domain has a leftmost maximizing choice. -/
theorem exists_isMinArgmaxOn (score : ℕ → ℝ) (upper : ℕ) :
    ∃ choice, IsMinArgmaxOn score choice upper := by
  classical
  let candidates := Finset.range (upper + 1)
  have hcandidates : candidates.Nonempty := by
    exact ⟨0, by simp [candidates]⟩
  obtain ⟨maximizer, hmaximizer, hmax⟩ :=
    Finset.exists_max_image candidates score hcandidates
  let maximizers := candidates.filter (fun candidate => score candidate = score maximizer)
  have hmaximizerMem : maximizer ∈ maximizers := by
    simp [maximizers, hmaximizer]
  let choice := maximizers.min' ⟨maximizer, hmaximizerMem⟩
  have hchoiceMem : choice ∈ maximizers := by
    exact Finset.min'_mem maximizers ⟨maximizer, hmaximizerMem⟩
  have hchoiceCandidates : choice ∈ candidates :=
    (Finset.mem_filter.mp hchoiceMem).1
  have hchoiceScore : score choice = score maximizer :=
    (Finset.mem_filter.mp hchoiceMem).2
  refine ⟨choice, ?_, ?_, ?_⟩
  · exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hchoiceCandidates)
  · intro candidate hcandidate
    have hcandidateMem : candidate ∈ candidates := by
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hcandidate)
    calc
      score candidate ≤ score maximizer := hmax candidate hcandidateMem
      _ = score choice := hchoiceScore.symm
  · intro candidate hcandidate heq
    have hcandidateMem : candidate ∈ candidates := by
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hcandidate)
    have hcandidateMax : candidate ∈ maximizers := by
      apply Finset.mem_filter.mpr
      refine ⟨hcandidateMem, ?_⟩
      exact heq.trans hchoiceScore
    exact Finset.min'_le maximizers candidate hcandidateMax

/--
Generic floor/ceiling seat-share target used by proportional multi-member
voting statements.
-/
def roundedSeatShare (seatCount : ℕ) (partyShare : ℝ) (seats : ℕ) : Prop :=
  seatCount = ⌊partyShare * (seats : ℝ)⌋₊ ∨
    seatCount = ⌈partyShare * (seats : ℝ)⌉₊

/--
Any natural seat count between the floor and ceiling of the fractional target
is a rounded seat share.
-/
theorem roundedSeatShare_of_floor_le_of_le_ceil {seatCount seats : ℕ}
    {partyShare : ℝ}
    (hlower : ⌊partyShare * (seats : ℝ)⌋₊ ≤ seatCount)
    (hupper : seatCount ≤ ⌈partyShare * (seats : ℝ)⌉₊) :
    roundedSeatShare seatCount partyShare seats := by
  by_cases h_eq_floor : seatCount = ⌊partyShare * (seats : ℝ)⌋₊
  · exact Or.inl h_eq_floor
  · right
    have hfloor_lt : ⌊partyShare * (seats : ℝ)⌋₊ < seatCount :=
      lt_of_le_of_ne hlower (Ne.symm h_eq_floor)
    have hfloor_add_le : ⌊partyShare * (seats : ℝ)⌋₊ + 1 ≤ seatCount :=
      Nat.succ_le_of_lt hfloor_lt
    have hceil_le_floor_add :
        ⌈partyShare * (seats : ℝ)⌉₊ ≤
          ⌊partyShare * (seats : ℝ)⌋₊ + 1 :=
      Nat.ceil_le_floor_add_one (partyShare * (seats : ℝ))
    exact le_antisymm hupper (le_trans hceil_le_floor_add hfloor_add_le)

/--
An interval characterization for a PAV party seat count.
-/
def pavSeatInterval (seatCount : ℕ) (partyShare : ℝ) (seats : ℕ) : Prop :=
  partyShare * ((seats + 1 : ℕ) : ℝ) - 1 ≤ (seatCount : ℝ) ∧
    (seatCount : ℝ) < partyShare * ((seats + 1 : ℕ) : ℝ)

/--
Multiplied adjacent-marginal optimality conditions for a PAV two-party seat
allocation.

The first condition says the selected party's last chosen seat has strictly
higher marginal value than the other party's next relevant seat. The second
condition says the selected party's next seat has no higher marginal value than
the other party's last relevant seat.
-/
def pavSeatMarginalConditions (seatCount : ℕ) (partyShare : ℝ) (seats : ℕ) : Prop :=
  (1 ≤ seatCount →
      partyShare * ((seats - seatCount + 1 : ℕ) : ℝ) >
        (1 - partyShare) * (seatCount : ℝ)) ∧
    (seatCount < seats →
      partyShare * ((seats - seatCount : ℕ) : ℝ) ≤
        (1 - partyShare) * ((seatCount + 1 : ℕ) : ℝ))

/--
Adjacent PAV marginal optimality conditions in their harmonic-weight form.
-/
def pavSeatMarginalWeightConditions (seatCount : ℕ) (partyShare : ℝ)
    (seats : ℕ) : Prop :=
  (1 ≤ seatCount →
      partyShare * pavWeight seatCount >
        (1 - partyShare) * pavWeight (seats - seatCount + 1)) ∧
    (seatCount < seats →
      partyShare * pavWeight (seatCount + 1) ≤
        (1 - partyShare) * pavWeight (seats - seatCount))

/--
If moving from `k` to `k + 1` seats improves the two-party PAV score, then the
previous seat's PAV marginal comparison is strict.
-/
theorem prevSeatMarginalWeight_lt_of_score_lt {partyShare : ℝ} {seats k : ℕ}
    (hk : k + 1 ≤ seats) :
    twoPartyPAVSeatScore partyShare seats k <
        twoPartyPAVSeatScore partyShare seats (k + 1) →
      (1 - partyShare) * pavWeight (seats - (k + 1) + 1) <
        partyShare * pavWeight (k + 1) := by
  intro h
  have hsub : seats - k = seats - (k + 1) + 1 := by
    omega
  have hscore :
      twoPartyPAVSeatScore partyShare seats k =
        partyShare * pavHarmonicSum k +
          (1 - partyShare) *
            (pavHarmonicSum (seats - (k + 1)) +
              pavWeight (seats - (k + 1) + 1)) := by
    simp [twoPartyPAVSeatScore, hsub]
  rw [hscore] at h
  simp [twoPartyPAVSeatScore] at h
  have hlt :
      (1 - partyShare) * pavWeight (seats - (k + 1) + 1) <
        partyShare * pavWeight (k + 1) := by
    linarith
  exact hlt

/--
If moving from `k` to `k + 1` seats does not improve the two-party PAV score,
then the next seat's PAV marginal comparison is non-strict.
-/
theorem nextSeatMarginalWeight_le_of_score_le {partyShare : ℝ} {seats k : ℕ}
    (hk : k < seats) :
    twoPartyPAVSeatScore partyShare seats (k + 1) ≤
        twoPartyPAVSeatScore partyShare seats k →
      partyShare * pavWeight (k + 1) ≤
        (1 - partyShare) * pavWeight (seats - k) := by
  intro h
  have hsub : seats - k = seats - (k + 1) + 1 := by
    omega
  have hscore :
      twoPartyPAVSeatScore partyShare seats k =
        partyShare * pavHarmonicSum k +
          (1 - partyShare) *
            (pavHarmonicSum (seats - (k + 1)) +
              pavWeight (seats - (k + 1) + 1)) := by
    simp [twoPartyPAVSeatScore, hsub]
  rw [hscore] at h
  simp [twoPartyPAVSeatScore] at h
  have hle :
      partyShare * pavWeight (k + 1) ≤
        (1 - partyShare) * pavWeight (seats - (k + 1) + 1) := by
    linarith
  simpa [hsub] using hle

/--
A leftmost maximizer of the two-party PAV seat score satisfies the adjacent
marginal optimality conditions.
-/
theorem pavSeatMarginalWeightConditions_of_isMinArgmaxOn {seatCount seats : ℕ}
    {partyShare : ℝ}
    (hmin : IsMinArgmaxOn (twoPartyPAVSeatScore partyShare seats) seatCount seats) :
    pavSeatMarginalWeightConditions seatCount partyShare seats := by
  rcases hmin with ⟨hseat, hmax, hminChoice⟩
  constructor
  · intro hposSeat
    cases seatCount with
    | zero =>
        omega
    | succ k =>
        have hk : k + 1 ≤ seats := hseat
        have hk_pred_le : k ≤ seats := Nat.le_trans (Nat.le_succ k) hk
        have hscore_le :
            twoPartyPAVSeatScore partyShare seats k ≤
              twoPartyPAVSeatScore partyShare seats (k + 1) :=
          hmax k hk_pred_le
        have hscore_ne :
            twoPartyPAVSeatScore partyShare seats k ≠
              twoPartyPAVSeatScore partyShare seats (k + 1) := by
          intro heq
          have hle_choice : k + 1 ≤ k := hminChoice k hk_pred_le heq
          omega
        have hscore_lt :
            twoPartyPAVSeatScore partyShare seats k <
              twoPartyPAVSeatScore partyShare seats (k + 1) :=
          lt_of_le_of_ne hscore_le hscore_ne
        exact prevSeatMarginalWeight_lt_of_score_lt hk hscore_lt
  · intro hltSeat
    have hsucc_le : seatCount + 1 ≤ seats := Nat.succ_le_of_lt hltSeat
    have hscore_le :
        twoPartyPAVSeatScore partyShare seats (seatCount + 1) ≤
          twoPartyPAVSeatScore partyShare seats seatCount :=
      hmax (seatCount + 1) hsucc_le
    exact nextSeatMarginalWeight_le_of_score_le hltSeat hscore_le

/--
The harmonic-weight adjacent marginal conditions are equivalent to the cleared
adjacent marginal inequalities used for interval arithmetic.
-/
theorem pavSeatMarginalConditions_of_weightConditions {seatCount seats : ℕ}
    {partyShare : ℝ}
    (hweight : pavSeatMarginalWeightConditions seatCount partyShare seats) :
    pavSeatMarginalConditions seatCount partyShare seats := by
  rcases hweight with ⟨hprev, hnext⟩
  constructor
  · intro hposSeat
    have h := hprev hposSeat
    have hmpos_nat : 0 < seats - seatCount + 1 := Nat.succ_pos _
    have hnpos : (0 : ℝ) < seatCount := Nat.cast_pos.mpr hposSeat
    have hmpos : (0 : ℝ) < (seats - seatCount + 1 : ℕ) :=
      Nat.cast_pos.mpr hmpos_nat
    rw [pavWeight_of_pos hposSeat, pavWeight_of_pos hmpos_nat] at h
    have hmul := mul_lt_mul_of_pos_right h (mul_pos hnpos hmpos)
    field_simp [hnpos.ne', hmpos.ne'] at hmul
    nlinarith
  · intro hltSeat
    have h := hnext hltSeat
    have hmpos_nat : 0 < seats - seatCount := Nat.sub_pos_of_lt hltSeat
    have hnpos_nat : 0 < seatCount + 1 := Nat.succ_pos _
    have hmpos : (0 : ℝ) < (seats - seatCount : ℕ) :=
      Nat.cast_pos.mpr hmpos_nat
    have hnpos : (0 : ℝ) < (seatCount + 1 : ℕ) :=
      Nat.cast_pos.mpr hnpos_nat
    rw [pavWeight_of_pos hnpos_nat, pavWeight_of_pos hmpos_nat] at h
    have hmul := mul_le_mul_of_nonneg_right h (mul_nonneg hnpos.le hmpos.le)
    field_simp [hnpos.ne', hmpos.ne'] at hmul
    nlinarith

/--
A leftmost maximizer of the two-party PAV seat score satisfies the cleared
adjacent marginal inequalities.
-/
theorem pavSeatMarginalConditions_of_isMinArgmaxOn {seatCount seats : ℕ}
    {partyShare : ℝ}
    (hmin : IsMinArgmaxOn (twoPartyPAVSeatScore partyShare seats) seatCount seats) :
    pavSeatMarginalConditions seatCount partyShare seats :=
  pavSeatMarginalConditions_of_weightConditions <|
    pavSeatMarginalWeightConditions_of_isMinArgmaxOn hmin

/--
The adjacent PAV marginal conditions imply the corresponding interval
characterization of the selected party's seat count.
-/
theorem pavSeatInterval_of_marginalConditions {seatCount seats : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1) (hseat : seatCount ≤ seats)
    (hmarg : pavSeatMarginalConditions seatCount partyShare seats) :
    pavSeatInterval seatCount partyShare seats := by
  rcases hmarg with ⟨hprev, hnext⟩
  constructor
  · by_cases hlt : seatCount < seats
    · have h := hnext hlt
      have hcast :
          ((seats - seatCount : ℕ) : ℝ) = (seats : ℝ) - (seatCount : ℝ) :=
        Nat.cast_sub hseat
      rw [hcast] at h
      norm_num [Nat.cast_add, Nat.cast_one] at h ⊢
      linarith
    · have hge : seats ≤ seatCount := Nat.le_of_not_gt hlt
      have hsc : seatCount = seats := le_antisymm hseat hge
      subst seatCount
      norm_num [Nat.cast_add, Nat.cast_one]
      have hs : partyShare * (seats : ℝ) ≤ (seats : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg seats)]
      linarith
  · by_cases hzero : seatCount = 0
    · subst seatCount
      norm_num [Nat.cast_add, Nat.cast_one]
      have hseats_nonneg : (0 : ℝ) ≤ seats := Nat.cast_nonneg seats
      nlinarith
    · have hpos_count : 1 ≤ seatCount := Nat.one_le_iff_ne_zero.mpr hzero
      have h := hprev hpos_count
      have hcast :
          ((seats - seatCount + 1 : ℕ) : ℝ) =
            (seats : ℝ) - (seatCount : ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
        congr 1
        exact Nat.cast_sub hseat
      rw [hcast] at h
      norm_num [Nat.cast_add, Nat.cast_one] at h ⊢
      linarith

/--
A leftmost maximizer of the two-party PAV seat score satisfies the PAV interval
characterization.
-/
theorem pavSeatInterval_of_isMinArgmaxOn {seatCount seats : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hmin : IsMinArgmaxOn (twoPartyPAVSeatScore partyShare seats) seatCount seats) :
    pavSeatInterval seatCount partyShare seats :=
  pavSeatInterval_of_marginalConditions hpos hle hmin.1 <|
    pavSeatMarginalConditions_of_isMinArgmaxOn hmin

/--
The PAV interval characterization implies the coarser floor/ceiling
seat-share boundary.
-/
theorem pavSeatInterval_roundedSeatShare {seatCount seats : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hinterval : pavSeatInterval seatCount partyShare seats) :
    roundedSeatShare seatCount partyShare seats := by
  rcases hinterval with ⟨hlower, hupper⟩
  let seatShare : ℝ := partyShare * (seats : ℝ)
  have hsplit :
      partyShare * ((seats + 1 : ℕ) : ℝ) = seatShare + partyShare := by
    simp [seatShare, Nat.cast_add, Nat.cast_one, mul_add]
  rw [hsplit] at hlower hupper
  have hlower' : seatShare + partyShare - 1 ≤ (seatCount : ℝ) := by
    exact hlower
  have hupper' : (seatCount : ℝ) < seatShare + partyShare := by
    exact hupper
  have hseatShare_nonneg : 0 ≤ seatShare :=
    mul_nonneg hpos.le (Nat.cast_nonneg seats)
  have hseatShare_lt_count_add_one : seatShare < (seatCount : ℝ) + 1 := by
    linarith
  have hcount_lt_seatShare_add_one : (seatCount : ℝ) < seatShare + 1 := by
    linarith
  have hfloor_le_count : ⌊seatShare⌋₊ ≤ seatCount := by
    apply Nat.lt_succ_iff.mp
    rw [Nat.floor_lt hseatShare_nonneg]
    simpa [Nat.cast_add, Nat.cast_one] using hseatShare_lt_count_add_one
  by_cases hcount_le_seatShare : (seatCount : ℝ) ≤ seatShare
  · left
    have hcount_le_floor : seatCount ≤ ⌊seatShare⌋₊ :=
      Nat.le_floor hcount_le_seatShare
    exact le_antisymm hcount_le_floor hfloor_le_count
  · right
    have hseatShare_lt_count : seatShare < (seatCount : ℝ) :=
      lt_of_not_ge hcount_le_seatShare
    have hceil_le_count : ⌈seatShare⌉₊ ≤ seatCount :=
      (Nat.ceil_le).2 hseatShare_lt_count.le
    have hcount_le_ceil : seatCount ≤ ⌈seatShare⌉₊ := by
      cases seatCount with
      | zero =>
          exact Nat.zero_le _
      | succ n =>
          rw [Nat.add_one_le_ceil_iff]
          have : ((n : ℕ) : ℝ) + 1 < seatShare + 1 := by
            simpa [Nat.cast_add, Nat.cast_one] using hcount_lt_seatShare_add_one
          linarith
    exact le_antisymm hcount_le_ceil hceil_le_count

/--
A leftmost maximizer of the two-party PAV seat score has a floor/ceiling
rounded seat share.
-/
theorem roundedSeatShare_of_isMinArgmaxOn {seatCount seats : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hmin : IsMinArgmaxOn (twoPartyPAVSeatScore partyShare seats) seatCount seats) :
    roundedSeatShare seatCount partyShare seats :=
  pavSeatInterval_roundedSeatShare hpos hle <|
    pavSeatInterval_of_isMinArgmaxOn hpos hle hmin

end Voting
end SocialChoice
end AppliedModelingLib
