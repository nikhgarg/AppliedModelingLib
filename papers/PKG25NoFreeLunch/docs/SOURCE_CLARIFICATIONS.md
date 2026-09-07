# Source Clarifications: A No Free Lunch Theorem for Human-AI Collaboration

## Loss, correctness, and calibration

- **Opening “accuracy” $\mathbb E[|\widehat Y(X)-Y|]$ → zero-one loss.**
  Expected correctness is its complement $1-\mathbb E[|\widehat Y(X)-Y|]$.

## Mixtures and finite partitions

- **Proposition 6 component-$m$ sampling weight $\lambda_\ell$ →
  $\lambda_m$.** The component's joint law and accuracy equations use the
  same simplex weight.
- **Undefined label-frequency quotient on a null partition cell → zero**
  in the finite predictor-realization construction used by Lemma 8 and
  Proposition 9. This fills an otherwise undefined branch.

## Proposition 9's two settings

- **First setting's “small positive” $\epsilon$ → $0<\epsilon<1/2$** to
  keep the constructed prediction profiles interior.
- **Second setting's free-index denominator →
  $2+\sum_j[p_j/(1-p_j)+(1-q_j)/q_j]$**, where $p,q$ are the compared
  interior prediction profiles. Both odds families must be summed to define
  the normalized finite probability law.

- **Proposition 9 mixture “sufficiently close to one” → weights $7/8$ and
  $1/8$**, which satisfy its strict comparison.
