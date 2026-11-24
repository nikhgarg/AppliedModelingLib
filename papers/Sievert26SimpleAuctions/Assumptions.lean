/-!
# Paper Assumptions: Machine-Verified Two-Sided Bounds for Simple Multi-Item Auctions

No additional beyond-paper assumptions or axioms are required. Every model primitive
(finitely supported nonnegative item distributions `FinDist`, independent product
realizations, incentive-compatible and individually rational direct mechanisms
`Mechanism`, and `SREV`, `BREV`, `REV`, `cStar`) is defined directly in Lean, and
all five named results are proved natively from Lean's standard axioms
`[propext, Classical.choice, Quot.sound]`.
-/

namespace Sievert26SimpleAuctions
end Sievert26SimpleAuctions
