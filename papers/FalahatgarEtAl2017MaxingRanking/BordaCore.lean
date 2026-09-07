import FalahatgarEtAl2017MaxingRanking.CoreDefinitions
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin

/-!
# Borda-score primitives

Section 5 of Falahatgar et al. studies Borda objectives without SST.  This
file fixes the exact finite-score definitions and proves the deterministic
reductions from uniform score estimates to approximate Borda maxing and
ranking.
-/

namespace FalahatgarEtAl2017MaxingRanking

open scoped BigOperators

/-- The Borda score: win probability against a uniformly selected arm. -/
noncomputable def bordaScore {Arm : Type*} [Fintype Arm]
    (winProbability : Arm → Arm → ℝ) (arm : Arm) : ℝ :=
  (∑ opponent : Arm, winProbability arm opponent) / (Fintype.card Arm : ℝ)

/-- An arm whose Borda score is within `epsilon` of every competitor's. -/
def EpsilonBordaMaximum {Arm : Type*} [Fintype Arm]
    (winProbability : Arm → Arm → ℝ) (epsilon : ℝ) (selected : Arm) : Prop :=
  ∀ competitor, bordaScore winProbability competitor - epsilon ≤
    bordaScore winProbability selected

/-- A finite Borda ranking, with earlier positions no more than `epsilon` below later ones. -/
def EpsilonBordaRanking {Arm : Type*} [Fintype Arm]
    (winProbability : Arm → Arm → ℝ) (epsilon : ℝ)
    (ranking : Fin (Fintype.card Arm) → Arm) : Prop :=
  Function.Bijective ranking ∧
    ∀ first second, first.val ≤ second.val →
      bordaScore winProbability (ranking second) - epsilon ≤
        bordaScore winProbability (ranking first)

/-- The output order is nonincreasing in its supplied estimated scores. -/
def EstimatedScoresSorted {Arm : Type*} [Fintype Arm]
    (estimate : Arm → ℝ) (ranking : Fin (Fintype.card Arm) → Arm) : Prop :=
  ∀ first second, first.val ≤ second.val → estimate (ranking second) ≤ estimate (ranking first)

/--
An Algorithm 9 ranking rule returns every arm exactly once and orders the
arms by nonincreasing supplied score.  The source leaves tie breaking open,
so it is intentionally not part of this semantic contract.
-/
def IsEmpiricalBordaRankingRule {Arm : Type*} [Fintype Arm]
    (rankingRule : (Arm → ℝ) → Fin (Fintype.card Arm) → Arm) : Prop :=
  ∀ estimate,
    Function.Bijective (rankingRule estimate) ∧
      EstimatedScoresSorted estimate (rankingRule estimate)

/-- A fixed finite enumeration supplies a deterministic tie-breaking order on arms. -/
@[reducible] noncomputable def finiteTieBreakOrder {Arm : Type*} [Fintype Arm] :
    LinearOrder Arm :=
  LinearOrder.lift' (Fintype.equivFin Arm) (Fintype.equivFin Arm).injective

/--
The total order used by the Borda sorter: larger estimated scores come first,
with the fixed finite order breaking ties.
-/
@[reducible] noncomputable def empiricalBordaOrder {Arm : Type*} [Fintype Arm]
    (estimate : Arm → ℝ) : LinearOrder Arm := by
  letI : LinearOrder Arm := finiteTieBreakOrder
  let coordinate : Arm → (OrderDual ℝ ×ₗ Arm) := fun arm =>
    toLex (OrderDual.toDual (estimate arm), arm)
  apply LinearOrder.lift' coordinate
  intro first second hequal
  exact congrArg (fun pair => (ofLex pair).2) hequal

/--
The deterministic ranking output of sorting all finite arms by nonincreasing
estimated Borda score, with a fixed tie break.
-/
noncomputable def empiricalBordaRanking {Arm : Type*} [Fintype Arm]
    (estimate : Arm → ℝ) : Fin (Fintype.card Arm) → Arm := by
  letI : LinearOrder Arm := empiricalBordaOrder estimate
  exact (Finset.orderEmbOfFin (Finset.univ : Finset Arm) (by simp)).toFun

/-- The empirical-score order reverses the numerical score order. -/
theorem empiricalBordaOrder_score_antitone {Arm : Type*} [Fintype Arm]
    (estimate : Arm → ℝ) {first second : Arm}
    (horder : @LE.le Arm (empiricalBordaOrder estimate).toLE first second) :
    estimate second ≤ estimate first := by
  letI : LinearOrder Arm := finiteTieBreakOrder
  change toLex (OrderDual.toDual (estimate first), first) ≤
    toLex (OrderDual.toDual (estimate second), second) at horder
  have hscore := Prod.Lex.monotone_fst _ _ horder
  exact hscore

/-- The empirical Borda sorter returns each finite arm exactly once. -/
theorem empiricalBordaRanking_bijective {Arm : Type*} [Fintype Arm]
    (estimate : Arm → ℝ) : Function.Bijective (empiricalBordaRanking estimate) := by
  letI : LinearOrder Arm := empiricalBordaOrder estimate
  let hcard : (Finset.univ : Finset Arm).card = Fintype.card Arm := by simp
  change Function.Bijective (Finset.orderEmbOfFin (Finset.univ : Finset Arm) hcard)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · exact (Finset.orderEmbOfFin (Finset.univ : Finset Arm) hcard).injective
  · simp

/-- The empirical Borda sorter is nonincreasing in the supplied score estimate. -/
theorem empiricalBordaRanking_sorted {Arm : Type*} [Fintype Arm]
    (estimate : Arm → ℝ) :
    EstimatedScoresSorted estimate (empiricalBordaRanking estimate) := by
  intro first second hindex
  letI : LinearOrder Arm := empiricalBordaOrder estimate
  let hcard : (Finset.univ : Finset Arm).card = Fintype.card Arm := by simp
  change estimate ((Finset.orderEmbOfFin (Finset.univ : Finset Arm) hcard) second) ≤
    estimate ((Finset.orderEmbOfFin (Finset.univ : Finset Arm) hcard) first)
  apply empiricalBordaOrder_score_antitone estimate
  exact (Finset.orderEmbOfFin (Finset.univ : Finset Arm) hcard).monotone hindex

/-- The concrete deterministic tie breaker realizes the source-facing ranking rule. -/
theorem empiricalBordaRanking_isRule {Arm : Type*} [Fintype Arm] :
    IsEmpiricalBordaRankingRule (@empiricalBordaRanking Arm inferInstance) := by
  intro estimate
  exact ⟨empiricalBordaRanking_bijective estimate, empiricalBordaRanking_sorted estimate⟩

/--
Uniform `ε/2` score accuracy and an estimated-score maximizer give an
`ε`-Borda maximum.  This is the deterministic core of Theorem 8's bandit
reduction.
-/
theorem epsilonBordaMaximum_of_uniformEstimate
    {Arm : Type*} [Fintype Arm]
    (winProbability : Arm → Arm → ℝ) (estimate : Arm → ℝ) (epsilon : ℝ) (selected : Arm)
    (huniform : ∀ arm,
      |estimate arm - bordaScore winProbability arm| < epsilon / 2)
    (hmaximalEstimate : ∀ competitor, estimate competitor ≤ estimate selected) :
    EpsilonBordaMaximum winProbability epsilon selected := by
  intro competitor
  have hcompetitor := (abs_lt.mp (huniform competitor)).1
  have hselected := (abs_lt.mp (huniform selected)).2
  have hbest := hmaximalEstimate competitor
  linarith

/--
Uniform `ε/2` score accuracy turns an order sorted by estimated scores into
an `ε`-Borda ranking.  This is the deterministic core of Theorem 9.
-/
theorem epsilonBordaRanking_of_uniformEstimate
    {Arm : Type*} [Fintype Arm]
    (winProbability : Arm → Arm → ℝ) (estimate : Arm → ℝ) (epsilon : ℝ)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hbijective : Function.Bijective ranking)
    (hsorted : EstimatedScoresSorted estimate ranking)
    (huniform : ∀ arm,
      |estimate arm - bordaScore winProbability arm| < epsilon / 2) :
    EpsilonBordaRanking winProbability epsilon ranking := by
  refine ⟨hbijective, ?_⟩
  intro first second horder
  have hsecond := (abs_lt.mp (huniform (ranking second))).1
  have hfirst := (abs_lt.mp (huniform (ranking first))).2
  have hsort := hsorted first second horder
  linarith

end FalahatgarEtAl2017MaxingRanking
