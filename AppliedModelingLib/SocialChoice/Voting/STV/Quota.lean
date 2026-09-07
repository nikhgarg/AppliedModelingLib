import AppliedModelingLib.SocialChoice.Voting.STV
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# STV Quota Arithmetic

Reusable arithmetic facts for Droop-style STV quota proofs.
-/

namespace AppliedModelingLib
namespace SocialChoice
namespace Voting

/--
If there are at least `seats * (seats + 1)` voters, then `seats` Droop quotas
fit inside the total electorate.
-/
theorem seats_mul_STVQuota_le_voters {seats voters : ℕ}
    (hvoters : seats * (seats + 1) ≤ voters) :
    seats * STVQuota seats voters ≤ voters := by
  unfold STVQuota
  have hdiv : seats ≤ voters / (seats + 1) := by
    exact (Nat.le_div_iff_mul_le (Nat.succ_pos seats)).2 (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hvoters)
  have hdecomp :
      (seats + 1) * (voters / (seats + 1)) + voters % (seats + 1) = voters :=
    Nat.div_add_mod voters (seats + 1)
  calc
    seats * (voters / (seats + 1) + 1)
        = seats * (voters / (seats + 1)) + seats := by
          rw [Nat.mul_add, Nat.mul_one]
    _ ≤ seats * (voters / (seats + 1)) + voters / (seats + 1) :=
          Nat.add_le_add_left hdiv _
    _ ≤ seats * (voters / (seats + 1)) + voters / (seats + 1) +
          voters % (seats + 1) :=
          Nat.le_add_right _ _
    _ = (seats + 1) * (voters / (seats + 1)) + voters % (seats + 1) := by
          rw [Nat.add_mul, Nat.one_mul]
    _ = voters := hdecomp

/--
Under the same voter-count condition, the total electorate divided by the
Droop quota is at least the number of seats.
-/
theorem seats_le_voters_div_STVQuota {seats voters : ℕ}
    (hvoters : seats * (seats + 1) ≤ voters) :
    (seats : ℝ) ≤ (voters : ℝ) / (STVQuota seats voters : ℝ) := by
  have hquota_pos : 0 < STVQuota seats voters := by
    unfold STVQuota
    exact Nat.succ_pos _
  have hquota_pos_real : (0 : ℝ) < (STVQuota seats voters : ℝ) :=
    Nat.cast_pos.mpr hquota_pos
  exact (le_div_iff₀ hquota_pos_real).2 (by
    exact_mod_cast seats_mul_STVQuota_le_voters hvoters)

/--
The total electorate divided by the Droop quota is strictly below `seats + 1`.
Equivalently, no more than `seats` disjoint full Droop quotas fit in the
electorate.
-/
theorem voters_div_STVQuota_lt_seats_succ (seats voters : ℕ) :
    (voters : ℝ) / (STVQuota seats voters : ℝ) < (seats : ℝ) + 1 := by
  have hmod_lt : voters % (seats + 1) < seats + 1 :=
    Nat.mod_lt voters (Nat.succ_pos seats)
  have hdecomp :
      (seats + 1) * (voters / (seats + 1)) + voters % (seats + 1) = voters :=
    Nat.div_add_mod voters (seats + 1)
  have hlt_nat :
      voters < (voters / (seats + 1) + 1) * (seats + 1) := by
    calc
      voters = (seats + 1) * (voters / (seats + 1)) +
          voters % (seats + 1) := hdecomp.symm
      _ < (seats + 1) * (voters / (seats + 1)) + (seats + 1) :=
            Nat.add_lt_add_left hmod_lt _
      _ = (voters / (seats + 1) + 1) * (seats + 1) := by
            ring
  have hlt_real :
      (voters : ℝ) <
        (STVQuota seats voters : ℝ) * ((seats : ℝ) + 1) := by
    have hcast :
        (voters : ℝ) <
          ((voters / (seats + 1) + 1) * (seats + 1) : ℕ) := by
      exact_mod_cast hlt_nat
    unfold STVQuota
    norm_num [Nat.cast_add, Nat.cast_one, Nat.cast_mul] at hcast ⊢
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcast
  have hquota_pos : 0 < (STVQuota seats voters : ℝ) := by
    exact_mod_cast (Nat.succ_pos (voters / (seats + 1)))
  rw [div_lt_iff₀ hquota_pos]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hlt_real

/--
The floor of a party's proportional seat share is no larger than the floor of
its vote count divided by the Droop quota.
-/
theorem floor_partyShare_mul_seats_le_floor_partyShare_mul_voters_div_quota
    {seats voters : ℕ} {partyShare : ℝ}
    (hshare_nonneg : 0 ≤ partyShare)
    (hvoters : seats * (seats + 1) ≤ voters) :
    ⌊partyShare * (seats : ℝ)⌋₊ ≤
      ⌊partyShare * ((voters : ℝ) / (STVQuota seats voters : ℝ))⌋₊ := by
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_left (seats_le_voters_div_STVQuota hvoters) hshare_nonneg

/--
For two complementary parties, the sum of their canonical Droop-quota floors is
at most the number of seats. This is the quota-capacity arithmetic used in the
solid-coalition STV proof after the two same-party quota processes separate.
-/
theorem twoParty_floor_votes_div_STVQuota_sum_le_seats
    {seats voters : ℕ} {partyShare : ℝ}
    (hshare_nonneg : 0 ≤ partyShare) (hshare_le : partyShare ≤ 1) :
    ⌊partyShare * ((voters : ℝ) / (STVQuota seats voters : ℝ))⌋₊ +
        ⌊(1 - partyShare) *
          ((voters : ℝ) / (STVQuota seats voters : ℝ))⌋₊ ≤ seats := by
  set totalQuotaMass : ℝ := (voters : ℝ) / (STVQuota seats voters : ℝ)
  let partyFloor : ℕ := ⌊partyShare * totalQuotaMass⌋₊
  let otherFloor : ℕ := ⌊(1 - partyShare) * totalQuotaMass⌋₊
  have htotal_nonneg : 0 ≤ totalQuotaMass := by
    unfold totalQuotaMass
    positivity
  have hparty_nonneg : 0 ≤ partyShare * totalQuotaMass :=
    mul_nonneg hshare_nonneg htotal_nonneg
  have hother_nonneg : 0 ≤ (1 - partyShare) * totalQuotaMass :=
    mul_nonneg (sub_nonneg.mpr hshare_le) htotal_nonneg
  have hparty_floor_le :
      (partyFloor : ℝ) ≤ partyShare * totalQuotaMass := by
    simpa [partyFloor] using
      (Nat.floor_le hparty_nonneg :
        (⌊partyShare * totalQuotaMass⌋₊ : ℝ) ≤
          partyShare * totalQuotaMass)
  have hother_floor_le :
      (otherFloor : ℝ) ≤ (1 - partyShare) * totalQuotaMass := by
    simpa [otherFloor] using
      (Nat.floor_le hother_nonneg :
        (⌊(1 - partyShare) * totalQuotaMass⌋₊ : ℝ) ≤
          (1 - partyShare) * totalQuotaMass)
  have hfloor_sum_le :
      ((partyFloor + otherFloor : ℕ) : ℝ) ≤ totalQuotaMass := by
    norm_num [Nat.cast_add]
    nlinarith
  have htotal_lt : totalQuotaMass < (seats : ℝ) + 1 := by
    simpa [totalQuotaMass] using voters_div_STVQuota_lt_seats_succ seats voters
  have hsum_lt :
      ((partyFloor + otherFloor : ℕ) : ℝ) < (seats : ℝ) + 1 := by
    exact lt_of_le_of_lt hfloor_sum_le htotal_lt
  have hnat_lt : partyFloor + otherFloor < seats + 1 := by
    exact_mod_cast hsum_lt
  simpa [partyFloor, otherFloor] using Nat.lt_succ_iff.mp hnat_lt

/--
A residual certificate for a party-level quota process: after electing
`seatsElected` candidates, the remaining party vote mass is nonnegative and
strictly below one quota.
-/
def QuotaResidualBound (seatsElected : ℕ) (initialVotes quota : ℝ) : Prop :=
  0 < quota ∧
    ∃ residual, 0 ≤ residual ∧ residual < quota ∧
      initialVotes = (seatsElected : ℝ) * quota + residual

/--
The canonical residual after taking `floor (initialVotes / quota)` full quotas
is nonnegative and strictly below one quota.
-/
theorem quotaResidualBound_floor_votes_div_quota {initialVotes quota : ℝ}
    (hquota_pos : 0 < quota) (hvotes_nonneg : 0 ≤ initialVotes) :
    QuotaResidualBound ⌊initialVotes / quota⌋₊ initialVotes quota := by
  let quotaSeats : ℕ := ⌊initialVotes / quota⌋₊
  refine ⟨hquota_pos, initialVotes - (quotaSeats : ℝ) * quota, ?_, ?_, ?_⟩
  · have hx_nonneg : 0 ≤ initialVotes / quota :=
      div_nonneg hvotes_nonneg hquota_pos.le
    have hfloor_le :
        (quotaSeats : ℝ) ≤ initialVotes / quota := by
      simpa [quotaSeats] using
        (Nat.floor_le hx_nonneg : (⌊initialVotes / quota⌋₊ : ℝ) ≤
          initialVotes / quota)
    have hdiv_mul : (initialVotes / quota) * quota = initialVotes := by
      field_simp [hquota_pos.ne']
    nlinarith
  · have hx_lt : initialVotes / quota < (quotaSeats : ℝ) + 1 := by
      simpa [quotaSeats, Nat.cast_add, Nat.cast_one] using
        (Nat.lt_floor_add_one (initialVotes / quota) : initialVotes / quota <
          (⌊initialVotes / quota⌋₊ : ℝ) + 1)
    have hdiv_mul : (initialVotes / quota) * quota = initialVotes := by
      field_simp [hquota_pos.ne']
    nlinarith
  · ring

/--
A lower-bound witness for a quota process: at least `quotaSeats` candidates
reach quota before the final seat count is read, and those quota seats leave
less than one quota of residual party vote mass.
-/
def QuotaLowerBoundWitness (finalSeats : ℕ) (initialVotes quota : ℝ) : Prop :=
  ∃ quotaSeats, quotaSeats ≤ finalSeats ∧
    QuotaResidualBound quotaSeats initialVotes quota

/--
If the final party seat count is at least the canonical quota floor, then it
has the quota lower-bound witness.
-/
theorem quotaLowerBoundWitness_of_floor_votes_div_quota_le_finalSeats
    {finalSeats : ℕ} {initialVotes quota : ℝ}
    (hquota_pos : 0 < quota) (hvotes_nonneg : 0 ≤ initialVotes)
    (hfinal : ⌊initialVotes / quota⌋₊ ≤ finalSeats) :
    QuotaLowerBoundWitness finalSeats initialVotes quota :=
  ⟨⌊initialVotes / quota⌋₊, hfinal,
    quotaResidualBound_floor_votes_div_quota hquota_pos hvotes_nonneg⟩

/--
If a party-level quota process leaves less than one quota of residual votes,
then the elected party seats are at least the floor of initial votes divided by
the quota.
-/
theorem floor_votes_div_quota_le_seatsElected_of_residualBound
    {seatsElected : ℕ} {initialVotes quota : ℝ}
    (hres : QuotaResidualBound seatsElected initialVotes quota) :
    ⌊initialVotes / quota⌋₊ ≤ seatsElected := by
  rcases hres with ⟨hquota_pos, residual, hres_nonneg, hres_lt, hinit⟩
  have hx_nonneg : 0 ≤ initialVotes / quota := by
    rw [hinit]
    positivity
  have hx_lt : initialVotes / quota < (seatsElected : ℝ) + 1 := by
    rw [hinit]
    have hquot_lt : residual / quota < 1 := by
      rw [div_lt_one hquota_pos]
      exact hres_lt
    have hquot_nonneg : 0 ≤ residual / quota := div_nonneg hres_nonneg hquota_pos.le
    field_simp [hquota_pos.ne']
    nlinarith
  have hfloor_lt : ⌊initialVotes / quota⌋₊ < seatsElected + 1 := by
    rw [Nat.floor_lt hx_nonneg]
    simpa [Nat.cast_add, Nat.cast_one] using hx_lt
  exact Nat.lt_succ_iff.mp hfloor_lt

/--
A quota lower-bound witness implies the final seat count is at least the floor
of the initial vote mass divided by the quota.
-/
theorem floor_votes_div_quota_le_finalSeats_of_quotaLowerBoundWitness
    {finalSeats : ℕ} {initialVotes quota : ℝ}
    (hwitness : QuotaLowerBoundWitness finalSeats initialVotes quota) :
    ⌊initialVotes / quota⌋₊ ≤ finalSeats := by
  rcases hwitness with ⟨quotaSeats, hquotaSeats_le, hres⟩
  exact le_trans (floor_votes_div_quota_le_seatsElected_of_residualBound hres)
    hquotaSeats_le

end Voting
end SocialChoice
end AppliedModelingLib
