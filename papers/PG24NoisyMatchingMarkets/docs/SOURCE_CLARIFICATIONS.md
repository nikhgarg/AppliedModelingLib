# Source clarifications: Wisdom and Foolishness of Noisy Matching Markets

Source: [*Wisdom and Foolishness of Noisy Matching Markets*](https://arxiv.org/abs/2402.16771). Proposition and lemma numbers below are the numbers rendered in the paper's attenuation and amplification appendices.

## Appendix Proposition 1: lower-tail orientation and polynomial rate

- **What changes:** the displayed integral from `vS` to infinity → the matched mass at values at or below `vS`, with the displayed `O(C^{-K(β,γ)})` rate. The sentence immediately after the display, the preceding reduction, and Theorem 1 all concern students below `vS`; by contrast, the displayed upper-tail integral converges to the positive supply when match probability converges to one above `vS`.
- **Additional condition:** beta-max concentration alone → beta-max concentration plus `MemLp (fun x : ℝ => x) 2 D` for one iid noise draw. The Case-2 lower-tail Chebyshev calculation is a statement about a single draw, whereas beta-max concentration controls maxima. Under this explicit finite-second-moment condition, the formalization proves the stated polynomial lower-tail rate uniformly over the literal stable-market instances.

## Appendix Propositions 7(ii) and 8: one-draw Chebyshev condition

- **What changes:** the Proposition 7(ii) near-one rate under beta-max concentration alone → the same rate with the finite iid one-draw second moment above. The proof applies Chebyshev to one draw. The formalization uses the lower-tail complement valid in the presence of atoms and the squared Chebyshev denominator; it retains the displayed exponent.
- **What changes:** the Proposition 8 lower-tail high-cutoff integral rate under beta-max concentration alone → the same `O(C^{-K(β,γ)})` rate with that inherited one-draw finite-second-moment condition. Proposition 8 invokes Proposition 7(ii), so it needs the same condition. The corrected result retains the paper's below-`vS` integral and exponent.

## Appendix Propositions 3 and 4: the high-cutoff block at the pivot

- **What changes:** the initially defined open block `C((P*, infinity))` → the closed block `C([P*, infinity))` used by the dense-cluster proof. At a cutoff tie, the two sets differ. The proof's dense cluster begins at `P*`, and its subsequent integral argument also uses the closed block. The formalization retains Proposition 3's two displayed rates, Proposition 4's lower-tail integral rate, and the strict low-side separation; this is a boundary convention, not a change to the market primitives.

## Appendix Propositions 10, 14, and 15: actual affordance probabilities and local inputs

- **What changes:** an informal use of `p_mu(v,F_i)` with immediately preceding calculations left implicit → the actual iid cutoff-affordance probability together with precisely the endpoint, capacity, and tail-ratio estimates used in the local derivation. Proposition 10 retains its positive `sigma` witness, positive `epsilon`, and strict open interval. Proposition 14 retains its strict large-firm probability-difference bound. Proposition 15 retains the `eta((v*,v_+)) = sqrt(epsilon)` selection and its small-firm bound below `v*`. These are explicit proof-context inputs rather than additional economic assumptions.

## Other appendix proof corrections

- **What changes:** the printed capacity algebra in Appendix Propositions 2 and 5 → the correctly signed capacity calculation. The displayed rates are unchanged.
- **What changes:** the intermediate event comparisons in Appendix Propositions 3 and 4 → the valid Chebyshev inclusions at the stated endpoints. The displayed rates are unchanged.
- **What changes:** the maximum-growth equality in Appendix Lemma 6 → a triangle-inequality and independent-sample argument, with atom-safe tail events. Its `o(log n)` conclusion is unchanged.
- **What changes:** the central-window and all-real bridge in the amplification appendix → the displayed central interval together with a finite long-tail shift argument from an interior anchor. Theorem 2's all-real conclusion is retained.

## Coalition conditional laws

- **What changes:** a conditional-noise description stated for every value vector → a conditional law on the student-law support, almost everywhere. This is the measure-theoretic reading needed for the affordability probabilities and integrals in Theorems 3 and 4.
