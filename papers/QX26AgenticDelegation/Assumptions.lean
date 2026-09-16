/-
Copyright (c) 2026 Alexander Quispe and Kevin Xu. All rights reserved.
Released under Apache 2.0 license.
Authors: Alexander Quispe, Kevin Xu
-/
import QX26AgenticDelegation.Model

/-!
# Paper Assumptions: Agentic Delegation and the Language Frontier of Software Developers

Source-backed Assumptions 1–3 from arXiv 2605.25438v2 §4 / Appendix A.
These are the standalone model definitions (not convenience axioms), declared
in `Model.lean` in this namespace:

- `Assumption1_foothold` — unfamiliar-language foothold \(\gamma s-r_C\le 0\)
- `Assumption2Hypotheses` / `Assumption2_verification` — verification technology
- `Assumption3_exchangeable` — exchangeable unfamiliar-language candidates

They are listed in `status.json` `review_surface.assumption_names`.
-/

namespace QX26AgenticDelegation

/-- Assumption 1 (augmentation requires a foothold), unfamiliar-language
clause: \(\gamma s-r_C\le 0\). Source: arXiv 2605.25438v2 §4. -/
-- audit-premise: hAss1 : Assumption1_foothold p
def assumption1_foothold (p : TaskParams) : Prop :=
  Assumption1_foothold p

/-- Assumption 2 (verification technology) as five signed finite-difference
inequalities. Source: arXiv 2605.25438v2 §4. -/
def assumption2_verification (H : Assumption2Hypotheses) : Prop :=
  Assumption2_verification H

/-- Assumption 3: unfamiliar languages are exchangeable given developer
characteristics, with a common per-language activation increment \(p\ge 0\).
Source: arXiv 2605.25438v2 Appendix A.5. -/
def assumption3_exchangeable {K : Type*} (U : Finset K) (pInc : K → ℝ) : Prop :=
  Assumption3_exchangeable U pInc

end QX26AgenticDelegation
