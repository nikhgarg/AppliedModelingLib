# Formalization Notes

This file preserves the previous hand-written paper-folder README content.
The paper-folder `README.md` is now a generated status overview.

## Source Inventory

This hand-maintained inventory is outside the generated README block. It
records the paper's named source items and their current Lean status without
claiming human or independent release certification.

| Source item | Anchor | Current Lean status |
|---|---:|---|
| Model, stable matching preliminaries, cutoff characterization setup | `cited publication:1`, `cited publication:22` | Implemented by the concrete PG23 continuum model and stability/cutoff bridge; not a standalone reviewed theorem row. |
| Supply and Demand Lemma | `cited publication:37` | Proved for monoculture and polyculture as `review_lemma1_supplyDemand_monoculture` and `review_lemma1_supplyDemand_polyculture`. |
| Monoculture and polyculture type instantiations | `cited publication:48` | Implemented in concrete type-law definitions used by the reviewed rows. |
| Appendix connected-support CDF observation | `cited publication:1`, `cited publication:9` | Proved as `review_proposition_cdfIncreasing_connectedSupport` in support-interior form; invalid endpoint CDF equalities are not used. |
| Appendix positive interval-mass observation | `cited publication:26` | Proved as `review_proposition_nonzeroMeasure_openInterval` for open intervals meeting the support interior. |
| Equal Cutoffs Lemma | `cited publication:70` | Proved for monoculture and polyculture as `review_lemma2_equalCutoffs_monoculture` and `review_lemma2_equalCutoffs_polyculture`. |
| Probability formula proposition | `cited publication:80` | Proved as `review_proposition_probabilityFormula` with visible nonatomic-noise regularity for weak-to-strict event conversion. |
| Lower Cutoff Under Monoculture corollary | `cited publication:99` | Proved as `review_corollary4_monocultureCutoff_lt_polycultureCutoff` with visible corrected support-domain premises. |
| Maximum Order Statistic definition | `cited publication:111` | Formalized as supporting definitions in `MainTheorems.lean`; not a review row. |
| Maximum-Concentrating Distribution definition | `cited publication:124` | Formalized as supporting definitions in `MainTheorems.lean`; not a review row. |
| Theorem 1, Wisdom of the Crowds | `cited publication:10` | Proved as probability and welfare rows: `review_theorem1_probability` and `review_theorem1_welfare`. |
| Theorem 2, Likelihood of Matching to Top Choice or At All | `cited publication:80` | Proved as three rows: top-choice probability, top-ranked monoculture assignment, and eventual match advantage. |
| Differential application access setup | `cited publication:109`, `cited publication:116` | Implemented in the differential-access concrete model; not a standalone reviewed theorem row. |
| Differential-access Equal Cutoffs Lemma | `cited publication:152` | Proved as monoculture and polyculture rows with explicit regularity premises. |
| Nash Equilibrium proposition | `cited publication:160` | Proved as `review_proposition_nash_differentialApplicationAccess` for expected favorite-success payoff under iid equal-cutoff success indicators. |
| Theorem 3, Differential Application Access | `cited publication:176` | Proved as direct shared-cutoff probability clauses plus the scalar-bridge row. The bridge derives score-level nullity from `NoAtoms valueLaw` and derives the differential scalar equation from common raw clearing. |
| Computational experiments | `cited publication:1`, `cited publication:32`, `cited publication:36`, `cited publication:53` | Out of current Lean theorem scope. |
| Conclusion | `cited publication:1` | Narrative and future-work discussion; no Lean theorem row. |
