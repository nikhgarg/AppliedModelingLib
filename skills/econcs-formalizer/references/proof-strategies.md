# Proof Strategy Router

This file intentionally stays short. Load only the detailed reference for the
library layer touched by the current proof.

| Proof area | Reference |
|---|---|
| Finite sums, signs, rounding, asymptotics, graph/counting | `proof-foundations-math.md` |
| Finite PMFs, expectations, conditional probability, Markov chains/dynamic kernels, CTMCs, renewal-reward, reward-rate, concentration, measure inequalities, continuous densities/RUM | `proof-foundations-probability.md` |
| Finite argmax, objective comparison, maximizer existence, LP certificates/BFS | `proof-foundations-optimization.md` |
| Recommendation allocation, accuracy/diversity, producer fairness, symmetric recommendation LPs | `proof-recommender-systems.md` |
| Online algorithms, AdWords/MSVV, online matching, regret/Yao | `proof-algorithms-online.md` |
| Auctions and mechanisms | `proof-mechanism-design.md` |
| Matching, fair division, rankings/Mallows/social choice | `proof-markets-social-choice.md` |

General rule: classify the proof type first, then open the smallest relevant
reference. Move sideways to a smaller seam of the same type when proof search
starts looping; do not compensate by loading every reference file.

When updating the skill after a long session, write the lesson where the next
agent will look first: workflow/context/validation guidance belongs in
`SKILL.md`, while proof moves belong in the relevant domain reference. Prefer
one concrete reusable pattern, failed approach, or exact build/search command
over a broad reminder that duplicates existing guidance.

For stronger-model pauses, record the exact source/Lean mismatch, strongest
proved result, and remaining seam in the paper-local working memo or another
authorized internal record. Do not change public status, website visibility, or
release metadata without explicit authorization. At a later authorized status or
closeout boundary, summarize the mathematical result rather than a long helper
lemma changelog.
