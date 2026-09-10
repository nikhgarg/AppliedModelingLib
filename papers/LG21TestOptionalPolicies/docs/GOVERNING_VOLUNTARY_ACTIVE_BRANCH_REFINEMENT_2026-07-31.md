# Governing Voluntary Active-Branch Refinement: LG21 Section 4

Recorded: 2026-07-31

## Purpose and Authority

This memo records the governing formal rendering of the source's Section 4
operational unraveling for the two voluntary protocols: optional reporting and
reporting-required-after-taking. It is not a caveat, a replacement theorem, or
a restriction to the mandatory-given-access protocol. It makes explicit the
selection that the source uses operationally when it says that the school knows
the decision functions and that any nonreporting or nontaking fraction is
unstable.

The refinement is intentionally separate from bare static Definition 1. It
must never be presented as a theorem that every static-RCD completion of
Definition 1 selects all actions.

The pinned archive is `cited publication`, SHA-256
`11fb7a52959948847ce19d85adf97256a30c3f1575941ff6efec0e33bf908e1c`.

## Source Anchors

- The source defines the access, take, and report actions and their feasibility
  order at `cited publication:205-228`.
- It gives the two decision stages - taking after learning skill and reporting
  after learning the score - at `cited publication:229-244`.
- It says the school knows the decision functions and uses them in Bayesian
  estimation at `cited publication:239-244`; Definition 1 gives static feasibility,
  weak-response, and policy-consistency conditions at `cited publication:256-395`.
- Lemma 4.1 states the all-take/all-report conclusion and its operational
  unraveling explanation at `cited publication:492-516`. The Appendix optional proof
  explicitly begins after assuming all taking at `cited publication:1784-1803`; the
  report-required taking argument is at `cited publication:2224-2316`.
- Propositions 4.2--4.3 and Theorem 4.4 use Lemma 4.1 in their Section 4
  arguments at `cited publication:550-632` and `cited publication:2318-2553`.

## Governing Refinement

For each positive-measure public-base region, choose a source-timed,
self-enforcing positive-mass candidate and select a branch that is maximal
almost everywhere under extension by such candidates. In the optional protocol
the full branch is take-and-report; in the report-required protocol it is take
(and therefore report). The selected profile itself must be a candidate, not a
bare action record.

A candidate has the following semantic contents.

1. It supplies the literal action history and PBO identities only for public
   action branches with positive population mass.
2. It preserves the source timing. Optional testing first compares taking with
   the expected best score-stage continuation; then a taker compares reporting
   and withholding after observing the score. Optional no-report is the union
   of no-taking and take-and-withhold. Reporting-required-after-taking has only
   the pre-score take decision.
3. On every attained branch, it supplies the relevant weak member responses
   and closure against strict profitable entry by eligible outsiders. Those
   comparisons use the candidate's recalibrated, selected PBOs.
4. It assigns no PBO, payoff, or response comparison to an unattained branch.
   In particular, the refinement does not manufacture a finite off-path PBO,
   an `-infinity` payoff, or a null-branch RCD version.

The branch-maximal rule is the formal form of the paper's operational
maximal-disclosure/unraveling reading. It is needed because a static regular
conditional-distribution completion can leave a null action history
underdetermined. The rule is visible in the paper-facing interface and is not
hidden in an implementation theorem or inferred from a function name.

## Exact Scope and Nonclaims

Under this refinement, the Section 4 Lemma 4.1 endpoint establishes only that
the selected voluntary actions are all active almost everywhere in the source
access population. The downstream Proposition 4.2, Proposition 4.3, and
Theorem 4.4 routes use the resulting actual action/output law.

It does **not** claim any of the following:

- pointwise all-type action equality;
- uniqueness of an arbitrary static Definition 1/RCD equilibrium;
- uniqueness of an off-path PBO, policy, full equilibrium record, or regular
  conditional-distribution version; or
- a value or best-response comparison at a null action branch.

Thus the source's all-action conclusion is formalized transparently as an
almost-everywhere selected-action result under its operational unraveling
interpretation. The mandatory-given-access protocol remains separate: its
action is forced by feasibility and is not evidence for either voluntary
protocol.

## Review Surface

The review declarations are in `PaperInterface.lean`:

- `voluntary_optional_self_enforcing_candidate`;
- `voluntary_report_required_self_enforcing_candidate`;
- `voluntary_optional_active_branch_selection`; and
- `voluntary_report_required_active_branch_selection`.

Their underlying structures are
`ObservedAccessVoluntarySelfEnforcingCandidates.lean` and
`ObservedAccessVoluntaryActiveBranchSelection.lean`. A semantic audit must
expand these declarations and confirm the positive-branch guards, both action
stages, candidate-side response and outsider closure, and the a.e.-only
conclusion. It must reject a route that replaces this refinement with a bare
Definition 1 hypothesis or an arbitrary off-path conditional value.
