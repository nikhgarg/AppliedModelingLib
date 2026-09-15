# LG24 Active Source Map

## Target

- Paper: *Redesigning Service Level Agreements: Equity and Efficiency in City
  Government Operations*.
- Current public source: [arXiv:2410.14825v2](https://arxiv.org/abs/2410.14825v2),
  revised September 7, 2026.

The selected source statements correspond to the arXiv version cited above.
The tables below describe the formalized scope; transcript line ranges refer
to the source text used for the accepted review.

## Normal Named Scope

Normal coverage includes exactly five named Proposition environments:

| Source result | Transcript anchor | Lean evidence |
| --- | --- | --- |
| Equivalent reciprocal-capacity representation | :686-698 | paper_prop_opt_reformulation |
| Extreme efficiency | :823-832 | paper_prop_extreme_efficiency |
| Extreme equity | :842-858 | paper_prop_extreme_equity |
| Price of equity | :926-959 | paper_prop_price_of_equity |
| Centralization gain | :1136-1155 | paper_prop_centralization |

Algorithms, simulations, figures, captions, and ordinary prose are outside
normal named-theory coverage unless a separate deep all-prose review selects
them.

## Explicit Supplemental Formula Scope

| Source formula | Transcript anchor | Lean evidence |
| --- | --- | --- |
| Typical-admitted-request stationary GPS response tail | :555-565 | paper_stationary_gps_response_tail |
| All-request SLA Palm/intensity rate fraction | :586-602 | paper_sla_from_stationary_gps_tail |

The rate-fraction row does not assert a raw-arrival almost-sure
empirical-frequency result.

## Source Model Route

The active route proves the selected-Palm tail from source primitives through
literal finite GPS/FCFS replays, Borel measurability, physical global-past
reset, selected-Palm remote-past semantics, and the M/M/1 comparator. No
paper-facing theorem accepts a tail certificate or a stationarity/replay
witness as a premise.

The globally stationary queue condition exposes nonnegative capacity, positive
SLA weights with total weight at most one, and aggregate admitted SLA load
strictly below capacity. The separate target-local margin is
s_target < C phi_target. Always-backlogged no-guarantee work is outside the
SLA load sum and receives only residual capacity. This separation is explicit
in the active interface; it is not an unexplained extra assumption or an
unproved all-class per-weight slack condition.
