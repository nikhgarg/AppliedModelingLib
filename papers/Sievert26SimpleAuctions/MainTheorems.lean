import Sievert26SimpleAuctions.Main
import Sievert26SimpleAuctions.UpperBound
import Sievert26SimpleAuctions.Bracket
import Sievert26SimpleAuctions.IID
import Sievert26SimpleAuctions.IID100

/-!
# Main Theorems: Machine-Verified Two-Sided Bounds for Simple Multi-Item Auctions

Implementation re-export module aggregating the five formally verified paper results:
- Theorem 1 (`lower_bound_with_det`): `REV(D) > 2.1946 * max(SREV(D), BREV(D))` via a deterministic mechanism.
- Theorem 2 (`upper_bound_two`, `upper_bound`): `REV(D) <= 1.1187 * SREV(D) + 1.367299 * BREV(D) <= 2.486 * max(SREV(D), BREV(D))`.
- Corollary 3 (`cStar_mem`): `2.1946 <= c* <= 2.486`.
- Theorem 4 (`iid_lower_bound_with_mech`): 40 i.i.d. items with deterministic two-part tariff `(entry fee 9, item price 4)` achieving `> 1.316`.
- Proposition 5 (`iid100_lower_bound_proof`): 100 i.i.d. items with deterministic two-part tariff `(entry fee 9, item price 4)` achieving `>= 1.324907`.
-/
