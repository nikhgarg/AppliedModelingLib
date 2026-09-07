# Source Clarifications

## Proposition 1: floor-Droop arithmetic

- Appendix C's temporary assumption that turnout `V` is divisible by `M+1` → exact floor-Droop arithmetic for every turnout in Proposition 1, where `M` is the seat count. With `Q=floor(V/(M+1))+1`, use `(M+1)(Q-1) <= V < (M+1)Q` and the source bound `V >= M(M+1)`. This supplies the nondivisible cases of the same rounded-seat conclusion without adding a turnout assumption.
