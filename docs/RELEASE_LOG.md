# Release log

This log highlights changes that affect what readers can rely on. Reports retain
the precise result-by-result statements and qualifications.

## September 8, 2026 — Reports and CI maintenance

- **Documentation:** removed obsolete generated audit summaries from the reports for
  [DGD26](https://gargnikhil.com/AppliedModelingLib/artifacts/papers/DGD26AdmissionsPredictability/FINAL_VALIDATION_REPORT.html),
  [GCG24](https://gargnikhil.com/AppliedModelingLib/artifacts/papers/GCG24UserItemFairness/FINAL_VALIDATION_REPORT.html),
  [GHKR22](https://gargnikhil.com/AppliedModelingLib/artifacts/papers/GHKR22BiasBounties/FINAL_VALIDATION_REPORT.html),
  [GHW01](https://gargnikhil.com/AppliedModelingLib/artifacts/papers/GHW01DigitalGoods/FINAL_VALIDATION_REPORT.html),
  [GKGMM19](https://gargnikhil.com/AppliedModelingLib/artifacts/papers/GKGMM19IterativeLocalVoting/FINAL_VALIDATION_REPORT.html),
  [GS62](https://gargnikhil.com/AppliedModelingLib/artifacts/papers/GS62CollegeAdmissions/FINAL_VALIDATION_REPORT.html),
  [Ge et al. (2024)](https://gargnikhil.com/AppliedModelingLib/artifacts/papers/GeEtAl2024AlignmentAxioms/FINAL_VALIDATION_REPORT.html),
  [KR21](https://gargnikhil.com/AppliedModelingLib/artifacts/papers/KR21Monoculture/FINAL_VALIDATION_REPORT.html),
  [LBG24](https://gargnikhil.com/AppliedModelingLib/artifacts/papers/LBG24SpatialUnderreporting/FINAL_VALIDATION_REPORT.html),
  [LG21](https://gargnikhil.com/AppliedModelingLib/artifacts/papers/LG21TestOptionalPolicies/FINAL_VALIDATION_REPORT.html),
  [PKG25](https://gargnikhil.com/AppliedModelingLib/artifacts/papers/PKG25NoFreeLunch/FINAL_VALIDATION_REPORT.html). Detailed result statements and qualifications are retained.
- **Proofs and coverage:** the maintenance updates retain the same 36 papers and mathematical claims. The LG21 Lean edits only guard existing diagnostic commands.
- **Validation tooling:** updated public evidence readers and review launchers, and registered already-published support modules used by Falahatgar et al. (2017), PG23 and PG24.

[Maintenance changes, PRs #46–54](https://github.com/nikhgarg/AppliedModelingLib/compare/12bf6330436b1e6e718f8beba0d7fdfb55d2c487...8c9bfda5db334096e92952c79681e020c3b06f2a) · [Report cleanup](https://github.com/nikhgarg/AppliedModelingLib/pull/53).

## September 7, 2026 — Accuracy–diversity and website follow-up

- **Proofs and coverage — PRPKG24, Reconciling the Accuracy–Diversity Trade-off
  in Recommendations:** added a checked counterexample to Proposition 2's
  sharper finite rounding constant; the proved bound remains `(2T+1)/N` and
  the square-root share limit is unchanged. Proposition 4 now has a concrete
  sphere-measure argument with clarified density and radial-kernel conditions.
- **Documentation — PRPKG24:** updated the validation report, clarification
  memo, and review packet to distinguish shared regularity conventions from
  result-specific corrections.
  [Read the report](https://gargnikhil.com/AppliedModelingLib/artifacts/papers/PRPKG24AccuracyDiversity/FINAL_VALIDATION_REPORT.html) · [Release PR](https://github.com/nikhgarg/AppliedModelingLib/pull/45).
- **Website:** AI and applications appears immediately after Foundations in
  the library table. Deployment checks verify the published documents, their
  links, and the old project URLs.

## September 7, 2026 — Public release and readable reports

- **Coverage:** published a 36-paper collection, including 34 entries marked
  Formalized and two existing partial formalizations. Individual reports state
  any formalization gaps and the exact scope of the checked results.
- **Documentation:** revised result tables and clarification memos to identify
  what differs from the source, why, and whether a counterexample establishes
  the distinction. Published readable HTML reports and memos with mathematics,
  DAGs, review packets, and source links.
- **Project:** renamed EconCSLib to AppliedModelingLib. Previous repository links
  continue to redirect; the former project website points to the current site.
- **Validation tooling:** documentation changes skip Lean builds; paper changes
  select affected papers and import dependents. Shared-library and audit-tooling
  changes retain broader checks. Existing source and semantic-review evidence
  is reused only when its checked inputs remain current.

[Public release](https://github.com/nikhgarg/AppliedModelingLib/pull/42) ·
[Readable reports](https://github.com/nikhgarg/AppliedModelingLib/pull/43) ·
[CI improvements](https://github.com/nikhgarg/AppliedModelingLib/pull/44)
