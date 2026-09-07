import SeshadriUgander2020IIATesting.Assumptions
import SeshadriUgander2020IIATesting.EulerianDecomposition
import SeshadriUgander2020IIATesting.AppendixEntropy
import SeshadriUgander2020IIATesting.AppendixProjection
import SeshadriUgander2020IIATesting.AppendixConvexHull
import SeshadriUgander2020IIATesting.AppendixCycleBounds
import SeshadriUgander2020IIATesting.CorollaryOne
import SeshadriUgander2020IIATesting.AllEvenSubsetsTesting
import SeshadriUgander2020IIATesting.Testing

/-!
# Paper interface: Seshadri--Ugander (2020)

This file presents each selected source result once as a transparent semantic
target. The main-text results come first. Appendix results follow in source and
dependency order. Source definitions are audited at their actual declarations
in the imported paper modules rather than through reflexive wrappers.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators
open AppliedModelingLib.Foundations.Graph

/-! ## Main-text results -/

/-- Source Lemma 2: under `ε ≥ 2 μ(σ) δ`, every oriented component is
`δ`-separated from IIA and the orientation-mixture experiment is not harder
than the original composite IIA test.  The second conjunct records the stated
source consequence `ε ≥ 4nδ ≥ 2μ(σ)δ` for simple-cycle decompositions. -/
def lemma2_testing_reductionSpec : Prop := by
  classical
  exact ∀ {F : ChoiceFrame} (D : ChoiceSystem.CycleDecomposition F)
    (W : D.AlternatingCycleWitness) (ε δ : ℝ)
    (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1) (hδ_nonneg : 0 ≤ δ)
    (N : ℕ),
      (2 * D.cycleMean * δ ≤ ε →
        ( (∀ a : D.Cycle → Bool,
            ChoiceSystem.SeparatedFromIIA
              (ChoiceSystem.perturb (D.orientedSign a)
                ε hε_nonneg hε_le_one) δ) ∧
          ∀ φ : FiniteDistribution.Test (Fin N → F.Observation),
            ∃ a : D.Cycle → Bool,
              FiniteDistribution.binaryError
                  (FiniteDistribution.product
                    (ChoiceSystem.asFiniteDistribution
                      (ChoiceSystem.uniform F)) N)
                  (FiniteDistribution.mixtureOfProducts
                    (Finset.univ : Finset (D.Cycle → Bool))
                    Finset.univ_nonempty
                    (fun orientation => ChoiceSystem.asFiniteDistribution
                      (ChoiceSystem.perturb (D.orientedSign orientation) ε
                        hε_nonneg hε_le_one)) N) φ ≤
                FiniteDistribution.binaryError
                  (FiniteDistribution.product
                    (ChoiceSystem.asFiniteDistribution
                      (ChoiceSystem.uniform F)) N)
                  (FiniteDistribution.product
                    (ChoiceSystem.asFiniteDistribution
                      (ChoiceSystem.perturb (D.orientedSign a) ε
                        hε_nonneg hε_le_one)) N) φ)) ∧
      (D.cycleMean ≤ 2 * (Fintype.card F.Item : ℝ) →
        4 * (Fintype.card F.Item : ℝ) * δ ≤ ε →
        2 * D.cycleMean * δ ≤ ε)

/-- Source Lemma 3: the chi-square distance of an arbitrary balanced
perturbation mixture is bounded by the displayed pairwise exponential sum. -/
def lemma3_chiSquare_mixtureSpec : Prop := by
  classical
  exact ∀ {F : ChoiceFrame} {β : Type} (B : Finset β) (hB : B.Nonempty)
    (b : β → ChoiceSystem.BalancedSign F) (ε : ℝ)
    (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1) (N : ℕ),
      FiniteDistribution.chiSquare
          (FiniteDistribution.mixtureOfProducts B hB
            (fun z => ChoiceSystem.asFiniteDistribution
              (ChoiceSystem.perturb (b z) ε hε_nonneg hε_le_one)) N)
          (FiniteDistribution.product
            (ChoiceSystem.asFiniteDistribution (ChoiceSystem.uniform F)) N) + 1 ≤
        (1 / (B.card : ℝ) ^ 2) *
          ∑ z ∈ B, ∑ z' ∈ B,
            Real.exp ((N : ℝ) *
              (ε ^ 2 / (F.incidenceCount : ℝ) *
                ChoiceSystem.signInner (b z) (b z')))

/-- Source Lemma 4: independently orienting the cycles gives the paper's
`N² ε⁴ α(σ)/(2d)` chi-square exponent. -/
def lemma4_cycle_chiSquareSpec : Prop := by
  classical
  exact ∀ {F : ChoiceFrame} (D : ChoiceSystem.CycleDecomposition F) (ε : ℝ),
    ∀ (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1) (N : ℕ),
      FiniteDistribution.chiSquare
          (FiniteDistribution.mixtureOfProducts
            (Finset.univ : Finset (D.Cycle → Bool)) Finset.univ_nonempty
            (fun a => ChoiceSystem.asFiniteDistribution
              (ChoiceSystem.perturb (D.orientedSign a) ε
                hε_nonneg hε_le_one)) N)
          (FiniteDistribution.product
            (ChoiceSystem.asFiniteDistribution (ChoiceSystem.uniform F)) N) + 1 ≤
        Real.exp (((N : ℝ) ^ 2 * ε ^ 4 / (2 * (F.incidenceCount : ℝ))) *
          CycleMixture.cycleDispersion F.incidenceCount D.length)

/-- Source Theorem 1: the finite minimax-risk lower bound and the two stated
fixed-error rate consequences.  The necessary source-domain condition
`2 μ(σ) δ ≤ 1` makes the constructed perturbation a probability. -/
def theorem1_testing_lower_boundSpec : Prop :=
  ∀ {F : ChoiceFrame} (D : ChoiceSystem.CycleDecomposition F)
    (_W : D.AlternatingCycleWitness) (δ : ℝ) (hδ_pos : 0 < δ)
    (hsmall : 2 * D.cycleMean * δ ≤ 1) (N : ℕ) (hN_pos : 0 < N),
        ChoiceSystem.ProductTestingLowerBound (F := F) N δ
          (1 / 2 - (1 / 4 : ℝ) *
            Real.sqrt (Real.exp
              ((8 * D.cycleMean ^ 4 *
                  CycleMixture.cycleDispersion F.incidenceCount
                    D.length * (N : ℝ) ^ 2 * δ ^ 4) /
                (F.incidenceCount : ℝ)) - 1)) ∧
        (ChoiceSystem.HasQuarterAccurateTest (F := F) N δ →
          Real.sqrt
            (((F.incidenceCount : ℝ) * Real.log 2) /
              (8 * D.cycleMean ^ 4 *
                CycleMixture.cycleDispersion F.incidenceCount D.length * δ ^ 4)) ≤
            (N : ℝ)) ∧
        (ChoiceSystem.HasQuarterAccurateTest (F := F) N δ →
          Real.sqrt (Real.sqrt
            (((F.incidenceCount : ℝ) * Real.log 2) /
              (8 * D.cycleMean ^ 4 *
                CycleMixture.cycleDispersion F.incidenceCount D.length *
                  (N : ℝ) ^ 2))) ≤ δ)

/-- Corrected source Corollary 1. The positive-denominator premise records
the necessary case condition for the printed rational mean branch; the
unconditional `2n` branch remains part of the minimum. -/
def corollary1_global_lower_bound_correctedSpec : Prop :=
  ∀ {F : ChoiceFrame} (hEulerian : F.Eulerian),
    4 ≤ Fintype.card F.Item →
      0 < (F.incidenceCount : ℝ) - 4 * (Fintype.card F.Item : ℝ) +
        2 * (4 * Real.logb 2 (Fintype.card F.Item)) →
      ∀ δ : ℝ, 0 ≤ δ →
        2 * F.sourceCorollaryMeanBound * δ ≤ 1 → ∀ N : ℕ,
          ChoiceSystem.ProductTestingLowerBound (F := F) N δ
            (1 / 2 - (1 / 4 : ℝ) *
              Real.sqrt (Real.exp
                ((8 * F.sourceCorollaryMeanBound ^ 4 *
                    F.sourceCorollaryDispersionBound * (N : ℝ) ^ 2 * δ ^ 4) /
                  (F.incidenceCount : ℝ)) - 1))

/-! ## Appendix results -/

/-- Appendix Fact `cvx_hull_dense`: finite mixtures of IIA choice systems are
dense in all finite choice systems in total variation. -/
def fact_convex_hull_denseSpec : Prop :=
  ∀ {F : ChoiceFrame} (q : ChoiceSystem F) (ε : ℝ),
    0 < ε → ∃ r, ChoiceSystem.InFiniteConvexHullIIA r ∧ q.totalVariation r < ε

/-- Appendix Lemma `iia_invariance`: equal choice-set and item marginals give
the same set of IIA KL projections. -/
def lemma_iia_projection_invarianceSpec : Prop :=
  ∀ {F : ChoiceFrame} (q₁ q₂ : ChoiceSystem F),
    (∀ C : F.SetId, q₁.setMass C = q₂.setMass C) →
      (∀ x : F.Item, q₁.itemMass x = q₂.itemMass x) →
        q₁.iiaProjection = q₂.iiaProjection

/-- Appendix Fact `max_entropy`, with the source's closed-simplex boundary
represented by extended-real cross entropy. -/
def fact_entropy_cross_entropySpec : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (q : PMF α),
    sInf (AppliedModelingLib.finiteCrossEntropyExtendedRange q) =
      AppliedModelingLib.finiteEntropy q

/-- Appendix bipartite cycle-decomposition lemma: the actual pruning/BFS trace
has the source logarithmic cycle cap and both displayed residual budgets. -/
def lemma_bipartite_cycle_decompositionSpec : Prop := by
  classical
  exact ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right : Set V),
    G.IsBipartiteWith left right →
      ∃ P : PartialSimpleCyclePacking G
          (2 * ⌊2 * Real.logb 2 left.ncard⌋₊),
        edgeCount G - P.usedEdges.card ≤
          min (2 * left.ncard + right.ncard)
            (4 * left.ncard + oddDegreeCount G right)

/-- Corrected Appendix comparison-incidence decomposition lemma. The source's
rational mean branch is asserted only when its denominator is positive; the
proved decomposition also satisfies the source dispersion minimum. -/
def lemma_comparison_incidence_decomposition_correctedSpec : Prop :=
  ∀ (F : ChoiceFrame), F.Eulerian → 4 ≤ Fintype.card F.Item →
    0 < (F.incidenceCount : ℝ) - 4 * (Fintype.card F.Item : ℝ) +
      2 * (4 * Real.logb 2 (Fintype.card F.Item)) →
      ∃ D : ChoiceSystem.CycleDecomposition F,
        D.cycleMean ≤ F.sourceCorollaryMeanBound ∧
          CycleMixture.cycleDispersion F.incidenceCount D.length ≤
            F.sourceCorollaryDispersionBound

/-- Corrected Appendix all-even-subsets corollary. The valid range begins at
`n = 3`; at the printed `n = 2` endpoint the comparison graph is not Eulerian. -/
def corollary_all_even_subsets_correctedSpec : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n),
    ∃ D : ChoiceSystem.CycleDecomposition
        (AllEvenChoiceSet.frame n (by omega)),
      D.cycleMean ≤ 5 * Real.logb 2 (n : ℝ) ∧
        CycleMixture.cycleDispersion
            (AllEvenChoiceSet.frame n (by omega)).incidenceCount D.length ≤
          5 * Real.logb 2 (n : ℝ)

end SeshadriUgander2020IIATesting
