import AppliedModelingLib.SocialChoice.Voting.Thiele
import Mathlib.Tactic.Linarith

/-!
# Voting Proportionality Lemmas

Reusable floor/ceiling arithmetic for proportional multi-member voting rules.

These lemmas are rule-agnostic: STV, Thiele/PAV, and other party-list style
proofs can first establish party lower bounds plus seat conservation, then use
this file to derive the rounded seat-share conclusion.
-/

namespace AppliedModelingLib
namespace SocialChoice
namespace Voting

/--
The complement lower bound controls the upper rounded seat count for a party.

If the other party has at least the floor of its proportional share, then the
remaining seats are at most the ceiling of this party's proportional share.
-/
theorem seats_sub_floor_complement_le_ceil {seats : ℕ} {partyShare : ℝ} :
    seats - ⌊(1 - partyShare) * (seats : ℝ)⌋₊ ≤
      ⌈partyShare * (seats : ℝ)⌉₊ := by
  let partyTarget : ℝ := partyShare * (seats : ℝ)
  let otherTarget : ℝ := (1 - partyShare) * (seats : ℝ)
  have hsum : otherTarget + partyTarget = (seats : ℝ) := by
    dsimp [otherTarget, partyTarget]
    ring
  have hother_lt :
      otherTarget < (⌊otherTarget⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one otherTarget
  have hparty_le : partyTarget ≤ (⌈partyTarget⌉₊ : ℝ) :=
    Nat.le_ceil partyTarget
  have hseats_lt :
      (seats : ℝ) <
        ((⌊otherTarget⌋₊ + ⌈partyTarget⌉₊ + 1 : ℕ) : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_one]
    linarith
  have hseats_le :
      seats ≤ ⌊otherTarget⌋₊ + ⌈partyTarget⌉₊ :=
    Nat.lt_succ_iff.mp (Nat.cast_lt.mp (by
      simpa [Nat.cast_add, Nat.cast_one] using hseats_lt))
  have hsub :
      seats - ⌊otherTarget⌋₊ ≤ ⌈partyTarget⌉₊ := by
    omega
  simpa [otherTarget, partyTarget] using hsub

/--
Two-party lower bounds plus total-seat conservation imply the rounded seat
share for the focal party.
-/
theorem roundedSeatShare_of_twoParty_lowerBounds {partySeats otherSeats seats : ℕ}
    {partyShare : ℝ}
    (htotal : partySeats + otherSeats = seats)
    (hlower : ⌊partyShare * (seats : ℝ)⌋₊ ≤ partySeats)
    (hotherLower : ⌊(1 - partyShare) * (seats : ℝ)⌋₊ ≤ otherSeats) :
    roundedSeatShare partySeats partyShare seats := by
  apply roundedSeatShare_of_floor_le_of_le_ceil hlower
  have hsubceil := seats_sub_floor_complement_le_ceil
    (seats := seats) (partyShare := partyShare)
  have hparty_le_sub :
      partySeats ≤ seats - ⌊(1 - partyShare) * (seats : ℝ)⌋₊ := by
    omega
  exact le_trans hparty_le_sub hsubceil

/--
Two-party lower bounds plus an upper bound on the visible two-party total
imply the rounded seat share for the focal party.
-/
theorem roundedSeatShare_of_twoParty_lowerBounds_le_total
    {partySeats otherSeats seats : ℕ} {partyShare : ℝ}
    (htotal_le : partySeats + otherSeats ≤ seats)
    (hlower : ⌊partyShare * (seats : ℝ)⌋₊ ≤ partySeats)
    (hotherLower : ⌊(1 - partyShare) * (seats : ℝ)⌋₊ ≤ otherSeats) :
    roundedSeatShare partySeats partyShare seats := by
  apply roundedSeatShare_of_floor_le_of_le_ceil hlower
  have hsubceil := seats_sub_floor_complement_le_ceil
    (seats := seats) (partyShare := partyShare)
  have hparty_le_sub :
      partySeats ≤ seats - ⌊(1 - partyShare) * (seats : ℝ)⌋₊ := by
    omega
  exact le_trans hparty_le_sub hsubceil

end Voting
end SocialChoice
end AppliedModelingLib
