# Release log

This log highlights changes that affect what readers can rely on. Reports retain
the precise result-by-result statements and qualifications.

## September 7, 2026 — Accuracy–diversity and website follow-up

- **Proofs and coverage — PRPKG24, Reconciling the Accuracy–Diversity Trade-off
  in Recommendations:** added a checked counterexample to Proposition 2's
  sharper finite rounding constant; the proved bound remains `(2T+1)/N` and
  the square-root share limit is unchanged. Proposition 4 now has a concrete
  sphere-measure argument with clarified density and radial-kernel conditions.
- **Documentation — PRPKG24:** updated the validation report, clarification
  memo, and review packet to distinguish shared regularity conventions from
  result-specific corrections.
  [Read the report](https://gargnikhil.com/AppliedModelingLib/artifacts/papers/PRPKG24AccuracyDiversity/FINAL_VALIDATION_REPORT.html).
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
