# Source Clarifications

Source: [*User-Item Fairness Tradeoffs in Recommendations*](https://openreview.net/pdf?id=ZOZjMs3JTs).

## Theorem 4: population masses and positive tolerance ([Section 5, p. 7](https://openreview.net/pdf?id=ZOZjMs3JTs#page=7); [Appendix E, p. 39](https://openreview.net/pdf?id=ZOZjMs3JTs#page=39))

- Cold-start mass `1-beta` → `1-2 beta`, alongside two known-type masses of `beta` each. The corrected masses sum to one and match Appendix E's item equation. Theorem 4 retains `1/n < beta < 1/2`, where `n` is the number of items.

## Appendix E Lemma 15: center display (Appendix E, p. 38)

- The center formula omitting one mirrored known type → `lambda=1/(1+L_t)`, where `lambda` is the common normalized item utility and `L_t` the center pivot's utility-ratio sum. The [center-equation note](APPENDIX_E_LEMMA15_SOURCE_NOTE.md) gives the equation and a numerical witness.
