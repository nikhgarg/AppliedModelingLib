# Appendix E Lemma 15 Source Clarification

- [Appendix E, Lemma 15 (p. 38)](https://openreview.net/pdf?id=ZOZjMs3JTs): center value `(2 beta q_t + 1-2 beta)/(1+q_t L_t)` → `lambda=1/(1+L_t)`. Here `beta` is each known type's population mass, `q_t` the center utility ratio, `L_t` the pivot's utility-ratio sum, `x_t` the known type's pivot allocation, and `z_t` the cold-start type's normalized center allocation. At the center, `q_t=1/2` and `z_t=1`; both mirrored known types contribute, giving `lambda=4 beta q_t x_t+(1-2 beta)z_t=1-lambda L_t`, using `x_t=1-lambda L_t/(2 beta)`.
- With `n=3` items, `beta=2/5`, `q_t=1/2`, and `L_t=4/3`, the corrected value is `3/7`, while the printed expression is `9/25`. The correction affects this center display.
