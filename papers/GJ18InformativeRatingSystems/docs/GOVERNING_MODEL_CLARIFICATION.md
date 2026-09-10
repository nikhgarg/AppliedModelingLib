# Rating histories and ranking accuracy: model clarifications

## Model readings

- **Ratings keep accumulating:** use a positive rating-arrival rate
  $g(\theta)>0$ for every seller type $\theta$, so the number of ratings
  $n_k(\theta)=\lfloor k g(\theta)\rfloor$ grows with time. This is the
  large-sample regime of the paper's convergence and rate arguments.
  Source: `cited publication:669–670, 745`.
- **Independent rating histories:** conditional on a seller's quality, ratings
  are independent draws from that quality's rating distribution; different
  sellers' histories are also independent. This makes explicit the
  independence used in the Appendix's pairwise probability calculation.
  Source: `cited publication:1638–1642`.

## Theorem 1 reading

- **Adjacent pairs:** the printed minimum through $i=M-1$ → a minimum through
  $i=M-2$, where $M$ is the number of ordered seller types. There is no next
  type after the last one.
- **Strict quality comparisons:** require upper-tail probabilities to increase
  strictly with quality only above the lowest rating. At the lowest rating,
  the upper-tail probability is one for every seller type.
- **Impossible scores:** allow the large-deviation cost to be $+\infty$
  outside the rating support. Minimizing these costs gives the finite rate in
  Theorem 1. This avoids requiring every rating to have positive probability.

<a id="displayed-indices-and-finite-state-route"></a>

## Average scores and the probability calculation

- **Average of $n$ ratings:** summing from $0$ through $n$ → summing from $0$
  through $n-1$. The former has one extra term. This corrects the
  aggregate-score display.
- **Appendix probability calculation:** a continuum approximation → direct
  bounds for finite, independent rating histories. The upper and lower bounds
  differ by fixed multiplicative constants, which disappear when taking
  $-\log(\text{probability})/k$. The resulting exponential rate is unchanged.

<a id="population-state-boundary"></a>

## From individual ratings to the seller population

- **Population distribution:** draw a seller's type uniformly from the finite
  type set, draw that seller's independent rating history, and average the
  ratings. The joint distribution of type and average score is the population
  state $\mu_k$. The proofs connect this description to the paper's pairwise
  and overall ranking measures.
- **Population-update notation:** the printed recurrence mixes the time
  indices for adding a new rating and recomputing the seller's average
  (`cited publication:710–715`). The formalization defines $\mu_k$ directly
  from these independent rating histories and proves convergence and ranking
  rates for that process.
