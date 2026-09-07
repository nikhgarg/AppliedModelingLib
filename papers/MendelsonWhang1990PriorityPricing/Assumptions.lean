import MendelsonWhang1990PriorityPricing.MainTheorems

/-!
# Paper Assumptions: Optimal Incentive-Compatible Priority Pricing for the M/M/1 Queue

This file is the only paper-local place for assumptions that are not derived in
Lean. Keep it small. Each declaration must be explicitly stated by the paper,
listed in `status.json` `review_surface.assumption_names`, and judged in
`audit/assumption_match_llm.json` as a true source/model assumption rather than a
proof convenience.

Use `-- audit-premise: <exact Lean binder>` comments to route hidden theorem
premises to an approved assumption declaration when the audit reports an exact
binder string.

Start empty. Add a proposition here only after locating it as a literal source
antecedent. Never move an unproved lemma or target conclusion here merely to
make a statement skeleton compile.
-/

namespace MendelsonWhang1990PriorityPricing

end MendelsonWhang1990PriorityPricing
