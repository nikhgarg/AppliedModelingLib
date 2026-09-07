# Source Clarifications

## Prune output size

- Main Lemma 5 and Supplemental Lemma 15: `|S'| < 2n'` → `|S'| <= 2n'`, where `S'` is Prune's output and `n'` its stopping parameter. Algorithm 2 already stops on an input of size `2n'`, so equality is possible.

## Algorithm 7: complementary estimates and threshold

- Supplemental Algorithm 7: `p-hat(j,i) = 1-p(i,j)` → `p-hat(j,i) = 1-p-hat(i,j)`, and selection threshold `1/2-epsilon` → `1/2-epsilon/2`. Each unordered pair is sampled once; the reverse estimate must be its complement, and the following Lemma 20 proof uses the corrected margin to establish an epsilon-ranking with probability at least `1-delta`.
