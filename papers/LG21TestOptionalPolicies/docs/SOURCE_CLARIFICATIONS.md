# Source Clarifications: LG21 Test-Optional Policies

Source anchors refer to `cited publication`.

## Theorem 3.1: nonreport mixture and fixed point

- The access weight using `C A(c)` → `C(1-A(c))/[(1-C)+C(1-A(c))]`, where `C` is the access fraction and `A(c)=Pr(S>=c)` the reported-score tail. Nonreporting uses the below-cutoff population (lines 1134–1172, 1233–1267).
- The current fixed-point proof explicitly assumes continuous lower-tail mass and first moment, positive denominator, and endpoint signs (lines 1268–1390). Whether the source conditions imply this package, or another proof avoids it, is unresolved here.

## Theorem 3.2: policy scope and operational blankness

- Randomized reported-score estimates → deterministic reported output in the checked theorem; the common no-report/no-take law may remain arbitrary with finite expectations (lines 199–218, 256–395, 455–461, 1614–1778). For each supplied equilibrium and fixed public-feature fibre, latent-skill or observable fairness implies either zero reporter mass or equality of the actual output kernel to the no-report law almost everywhere under the score law. In the report-required schedule, replace reporters by takers, the no-report law by the no-take law, and the score law by the Gaussian skill law. This asserts operational equality on attained inputs, not every off-path input.
- Equal expected estimates do not identify output laws: `delta_0` and `(delta_-1+delta_1)/2` have mean zero. The checked Gaussian example makes reported laws depend on score sign while keeping their means zero, and gives nonreporters and students without access the equilibrium reporter-mixture law. Deterministic reported output removes this ambiguity; the example does not establish that determinism is the only sufficient restriction.
- The summary's “demographic” reference → “observable,” matching its argument (lines 1770–1782).

## Equilibrium timing, population laws, and active branches

- **Theorem 3.1: source equilibrium → also exclude profitable group entry after recalibrating the school’s estimates.** The alternative changes behavior on positive mass in a measurable public-feature region, preserves score technology and behavior elsewhere, recalibrates attained posteriors, and satisfies the stated response and strict entry-gain comparisons. Optional entry is tested on any such region; required entry starts where current taking is zero. Deriving this restriction from Definition 1 remains a formalization gap. Necessity is unknown: the source may imply it, or another proof may avoid it.
- **Voluntary Section 4: source equilibrium → maximal self-enforcing participation.** No admissible candidate can strictly enlarge the selected active set, up to null sets, on any positive-mass measurable public-feature region. Candidates satisfy the same posterior, response, and entry/exit conditions. The active set consists of takers who report under optional reporting, and takers under required reporting. This is maximality under inclusion, not a greatest set. Selected profiles exist, but proving the paper’s conclusions for equilibria without this selection remains a formalization gap; necessity of the restriction is unknown.
- Source access “preset and uncorrelated with skill and features” (line 207) → independence from the entire skill/noise block in the one-student law. Zero correlation alone does not give the conditional-law identities used here.

## Lemma 4.1 and Proposition 4.3: calculations

- Lemma 4.1's cutoff calculation → `c=(qtilde-intercept)/slope` on the positive-slope domain, obtained by solving `intercept+slope*c=qtilde` (lines 2183–2220, 2262–2310).
- Proposition 4.3's conditional-to-marginal comparison → a direct calculation of unconditional posterior-mean variance (lines 2495–2505). For prior variance `v>0` and independent signal precision sum `J`, that variance is `v-(1/v+J)^(-1)`. An additional positive-precision score strictly increases it, proving that the two marginal estimate laws differ on the current equilibrium domain.
