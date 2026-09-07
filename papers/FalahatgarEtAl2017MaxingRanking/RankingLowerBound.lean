import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import FalahatgarEtAl2017MaxingRanking.CoreDefinitions
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.Perm

/-!
# Random-hidden-comparison core for the ranking lower bound

Appendix B.1 of the source reduces ranking to locating one distinguished
comparison.  Its adaptive lower bound needs a random relabeling argument:
before the distinguished comparison is queried, the transcript must be
independent of its uniformly random location.  This module proves the exact
finite probability calculation once that independence is represented by a
product PMF.  The likelihood transfer from the source's small-`μ` model to
that idealized product experiment remains a separate theorem obligation.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib

/-- The unordered distinct arm pairs that form the comparison coordinates. -/
abbrev unorderedComparisonCoordinate (Arm : Type*) := { pair : Sym2 Arm // ¬ pair.IsDiag }

/-- There are exactly `n.choose 2` unordered distinct comparison coordinates. -/
theorem unorderedComparisonCoordinate_card
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] :
    Fintype.card (unorderedComparisonCoordinate Arm) = (Fintype.card Arm).choose 2 :=
  Sym2.card_subtype_not_diag

/-- At least two arms supply a nonempty population of unordered comparisons. -/
theorem unorderedComparisonCoordinate_nonempty_of_card_ge_two
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (hcard : 2 ≤ Fintype.card Arm) : Nonempty (unorderedComparisonCoordinate Arm) := by
  apply Fintype.card_pos_iff.mp
  rw [unorderedComparisonCoordinate_card]
  exact Nat.choose_pos hcard

/--
The positive forward centered gap in the Appendix B.1 hard instance.  Every
forward pair has gap `mu`, except for the endpoint pair `(0,n-1)`, whose gap is
`1 / 2`.  The reverse orientation is added by `theorem7PreferenceGap`.
-/
noncomputable def theorem7ForwardGap (n : ℕ) (mu : ℝ) (i j : Fin n) : ℝ :=
  if i.val = 0 ∧ j.val + 1 = n then 1 / 2 else mu

/--
The centered preference matrix in the source's Theorem 7 construction, on its
displayed linear order of arms.  It has the exceptional endpoint comparison
and otherwise uses the small positive gap `mu` in the forward direction.
-/
noncomputable def theorem7PreferenceGap (n : ℕ) (mu : ℝ) (i j : Fin n) : ℝ :=
  if i.val < j.val then theorem7ForwardGap n mu i j
  else if j.val < i.val then -theorem7ForwardGap n mu j i else 0

/--
Away from the exceptional endpoint pair, every distinct comparison in the
source hard matrix has centered gap either `mu` or `-mu`.
-/
lemma theorem7PreferenceGap_eq_mu_or_neg_mu_of_not_endpoints
    {n : ℕ} {mu : ℝ} (i j : Fin n) (hneq : i ≠ j)
    (hforward : ¬ (i.val = 0 ∧ j.val + 1 = n))
    (hreverse : ¬ (j.val = 0 ∧ i.val + 1 = n)) :
    theorem7PreferenceGap n mu i j = mu ∨ theorem7PreferenceGap n mu i j = -mu := by
  unfold theorem7PreferenceGap
  by_cases hij : i.val < j.val
  · left
    rw [if_pos hij, theorem7ForwardGap, if_neg hforward]
  · by_cases hji : j.val < i.val
    · right
      rw [if_neg hij, if_pos hji, theorem7ForwardGap, if_neg hreverse]
    · have heq : i = j := Fin.ext (Nat.le_antisymm (Nat.le_of_not_gt hji)
        (Nat.le_of_not_gt hij))
      exact False.elim (hneq heq)

/-- Positivity of every forward gap in the Theorem 7 construction. -/
private lemma theorem7ForwardGap_pos
    {n : ℕ} {mu : ℝ} (hmu : 0 < mu) (i j : Fin n) :
    0 < theorem7ForwardGap n mu i j := by
  rw [theorem7ForwardGap]
  split_ifs <;> linarith

/--
For a positive `mu`, the nonnegative comparisons in the Theorem 7 construction
are exactly the forward weak order comparisons.
-/
lemma theorem7PreferenceGap_nonneg_iff_index_le
    {n : ℕ} {mu : ℝ} (hmu : 0 < mu) (i j : Fin n) :
    0 ≤ theorem7PreferenceGap n mu i j ↔ i.val ≤ j.val := by
  unfold theorem7PreferenceGap
  by_cases hij : i.val < j.val
  · simp [hij, Nat.le_of_lt hij, (theorem7ForwardGap_pos hmu i j).le]
  · by_cases hji : j.val < i.val
    · rw [if_neg hij, if_pos hji]
      constructor
      · intro h
        have hpos := theorem7ForwardGap_pos hmu j i
        linarith
      · intro h
        exact False.elim ((Nat.not_le_of_lt hji) h)
    · have heq : i.val = j.val := Nat.le_antisymm (Nat.le_of_not_gt hji)
        (Nat.le_of_not_gt hij)
      simp [heq]

/-- Moving the right endpoint forward cannot lower a Theorem 7 forward gap. -/
lemma theorem7ForwardGap_left_le
    {n : ℕ} {mu : ℝ} (hmu : mu ≤ 1 / 2) (i j k : Fin n)
    (hjk : j.val ≤ k.val) :
    theorem7ForwardGap n mu i j ≤ theorem7ForwardGap n mu i k := by
  unfold theorem7ForwardGap
  by_cases hij : i.val = 0 ∧ j.val + 1 = n
  · have hjlast : j.val + 1 = n := hij.2
    have hjmax : j.val = n - 1 := by omega
    have hkle : k.val ≤ n - 1 := by omega
    have hkeq : k.val = j.val := by omega
    simp [hij, hkeq]
  · split_ifs with hik
    · exact hmu
    · rfl

/-- Moving the left endpoint backward cannot lower a Theorem 7 forward gap. -/
lemma theorem7ForwardGap_right_le
    {n : ℕ} {mu : ℝ} (hmu : mu ≤ 1 / 2) (i j k : Fin n)
    (hij : i.val ≤ j.val) :
    theorem7ForwardGap n mu j k ≤ theorem7ForwardGap n mu i k := by
  unfold theorem7ForwardGap
  by_cases hjk : j.val = 0 ∧ k.val + 1 = n
  · have hjzero : j.val = 0 := hjk.1
    have hizer : i.val = 0 := by omega
    simp [hjk, hizer]
  · split_ifs with hik
    · exact hmu
    · rfl

/--
The source's exceptional-pair small-`mu` preference construction satisfies
strong stochastic transitivity whenever `0 < mu ≤ 1 / 2`.
-/
theorem theorem7PreferenceGap_strongStochasticTransitivity
    (n : ℕ) (mu : ℝ) (hmu : 0 < mu) (hmuHalf : mu ≤ 1 / 2) :
    StrongStochasticTransitivity (theorem7PreferenceGap n mu) := by
  intro first middle last hfirstMiddle hmiddleLast
  have hfirstMiddleOrder :=
    (theorem7PreferenceGap_nonneg_iff_index_le hmu first middle).mp hfirstMiddle
  have hmiddleLastOrder :=
    (theorem7PreferenceGap_nonneg_iff_index_le hmu middle last).mp hmiddleLast
  have hfirstLastOrder := hfirstMiddleOrder.trans hmiddleLastOrder
  have hfirstLastNonnegative :=
    (theorem7PreferenceGap_nonneg_iff_index_le hmu first last).mpr hfirstLastOrder
  apply max_le
  · by_cases heq : first.val = middle.val
    · have hfin : first = middle := Fin.ext heq
      subst middle
      simpa [theorem7PreferenceGap] using hfirstLastNonnegative
    · have hlt : first.val < middle.val := lt_of_le_of_ne hfirstMiddleOrder heq
      have hfirstLastLt : first.val < last.val := lt_of_lt_of_le hlt hmiddleLastOrder
      rw [theorem7PreferenceGap, if_pos hlt, theorem7PreferenceGap, if_pos hfirstLastLt]
      exact theorem7ForwardGap_left_le hmuHalf first middle last hmiddleLastOrder
  · by_cases heq : middle.val = last.val
    · have hfin : middle = last := Fin.ext heq
      subst last
      simpa [theorem7PreferenceGap] using hfirstLastNonnegative
    · have hlt : middle.val < last.val := lt_of_le_of_ne hmiddleLastOrder heq
      have hfirstLastLt : first.val < last.val := lt_of_le_of_lt hfirstMiddleOrder hlt
      rw [theorem7PreferenceGap, if_pos hlt, theorem7PreferenceGap, if_pos hfirstLastLt]
      exact theorem7ForwardGap_right_le hmuHalf first middle last hfirstMiddleOrder

/--
With at least two arms, the reversed exceptional endpoint comparison has
centered value `-1 / 2`, independently of the small ordinary gap `mu`.
-/
lemma theorem7PreferenceGap_last_first
    {n : ℕ} {mu : ℝ} (hcard : 2 ≤ n) (first last : Fin n)
    (hfirst : first.val = 0) (hlast : last.val + 1 = n) :
    theorem7PreferenceGap n mu last first = -(1 / 2 : ℝ) := by
  have hlastPositive : 0 < last.val := by omega
  rw [theorem7PreferenceGap, if_neg (by omega), if_pos (by omega)]
  rw [theorem7ForwardGap, if_pos ⟨hfirst, hlast⟩]

/--
Every `1 / 4`-ranking of the source's Theorem 7 construction places its
exceptional first endpoint before its exceptional last endpoint.  This is the
source-to-ranking part of the reduction; the random-relabeling distribution is
separate.
-/
theorem theorem7_epsilonRanking_orders_endpoints
    {n : ℕ} {mu : ℝ} (hcard : 2 ≤ n)
    (ranking : Fin (Fintype.card (Fin n)) → Fin n)
    (hranking : EpsilonPreferenceRanking (theorem7PreferenceGap n mu) (1 / 4) ranking)
    (first last : Fin n) (hfirst : first.val = 0) (hlast : last.val + 1 = n) :
    ∃ firstSlot lastSlot, ranking firstSlot = first ∧ ranking lastSlot = last ∧
      firstSlot.val < lastSlot.val := by
  rcases hranking.1.2 first with ⟨firstSlot, hfirstSlot⟩
  rcases hranking.1.2 last with ⟨lastSlot, hlastSlot⟩
  refine ⟨firstSlot, lastSlot, hfirstSlot, hlastSlot, ?_⟩
  by_contra hnot
  have hlastFirst : lastSlot.val ≤ firstSlot.val := Nat.le_of_not_gt hnot
  have hgap : -(1 / 4 : ℝ) ≤ theorem7PreferenceGap n mu last first := by
    rw [← hlastSlot, ← hfirstSlot]
    exact hranking.2 lastSlot firstSlot hlastFirst
  rw [theorem7PreferenceGap_last_first hcard first last hfirst hlast] at hgap
  norm_num at hgap

/-- The first source position in the `n`-arm Theorem 7 hard instance. -/
noncomputable def theorem7FirstPosition (n : ℕ) (hcard : 2 ≤ n) : Fin n :=
  ⟨0, by omega⟩

/-- The last source position in the `n`-arm Theorem 7 hard instance. -/
noncomputable def theorem7LastPosition (n : ℕ) (hcard : 2 ≤ n) : Fin n :=
  ⟨n - 1, by omega⟩

@[simp] lemma theorem7FirstPosition_val (n : ℕ) (hcard : 2 ≤ n) :
    (theorem7FirstPosition n hcard).val = 0 := rfl

@[simp] lemma theorem7LastPosition_val (n : ℕ) (hcard : 2 ≤ n) :
    (theorem7LastPosition n hcard).val + 1 = n := by
  dsimp [theorem7LastPosition]
  omega

/-- The two source endpoints are distinct whenever there are at least two arms. -/
lemma theorem7SourceEndpoints_ne (n : ℕ) (hcard : 2 ≤ n) :
    theorem7FirstPosition n hcard ≠ theorem7LastPosition n hcard := by
  intro heq
  have hval := congrArg Fin.val heq
  dsimp [theorem7FirstPosition, theorem7LastPosition] at hval
  omega

/--
A canonical relabeling with prescribed, distinct images of the two exceptional
source endpoints.  This realizes a concrete hard instance for each possible
ordered pair of observed arm labels.
-/
noncomputable def theorem7RelabelingOfOrderedEndpoints
    (n : ℕ) (hcard : 2 ≤ n) (first last : Fin n) : Equiv.Perm (Fin n) :=
  let initial := Equiv.swap (theorem7FirstPosition n hcard) first
  Equiv.swap (initial (theorem7LastPosition n hcard)) last * initial

/-- The canonical relabeling sends the first source endpoint to its prescribed label. -/
lemma theorem7RelabelingOfOrderedEndpoints_first
    {n : ℕ} (hcard : 2 ≤ n) (first last : Fin n) (hneq : first ≠ last) :
    theorem7RelabelingOfOrderedEndpoints n hcard first last
      (theorem7FirstPosition n hcard) = first := by
  unfold theorem7RelabelingOfOrderedEndpoints
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro heq
    apply theorem7SourceEndpoints_ne n hcard
    apply (Equiv.swap (theorem7FirstPosition n hcard) first).injective
    simpa using heq
  · exact hneq

/-- The canonical relabeling sends the last source endpoint to its prescribed label. -/
lemma theorem7RelabelingOfOrderedEndpoints_last
    {n : ℕ} (hcard : 2 ≤ n) (first last : Fin n) :
    theorem7RelabelingOfOrderedEndpoints n hcard first last
      (theorem7LastPosition n hcard) = last := by
  unfold theorem7RelabelingOfOrderedEndpoints
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

/--
The Theorem 7 source model after relabeling its linearly ordered hard instance.
The relabeling sends the source endpoint positions to the two exceptional arm
labels and transports every other small-`mu` comparison accordingly.
-/
noncomputable def theorem7RelabeledPreferenceGap
    (n : ℕ) (mu : ℝ) (relabel : Equiv.Perm (Fin n)) (i j : Fin n) : ℝ :=
  theorem7PreferenceGap n mu (relabel.symm i) (relabel.symm j)

/-- Relabeling preserves strong stochastic transitivity of the Theorem 7 model. -/
theorem theorem7RelabeledPreferenceGap_strongStochasticTransitivity
    (n : ℕ) (mu : ℝ) (hmu : 0 < mu) (hmuHalf : mu ≤ 1 / 2)
    (relabel : Equiv.Perm (Fin n)) :
    StrongStochasticTransitivity (theorem7RelabeledPreferenceGap n mu relabel) := by
  intro first middle last hfirstMiddle hmiddleLast
  change 0 ≤ theorem7PreferenceGap n mu (relabel.symm first) (relabel.symm middle) at hfirstMiddle
  change 0 ≤ theorem7PreferenceGap n mu (relabel.symm middle) (relabel.symm last) at hmiddleLast
  change max (theorem7PreferenceGap n mu (relabel.symm first) (relabel.symm middle))
      (theorem7PreferenceGap n mu (relabel.symm middle) (relabel.symm last)) ≤
    theorem7PreferenceGap n mu (relabel.symm first) (relabel.symm last)
  exact theorem7PreferenceGap_strongStochasticTransitivity n mu hmu hmuHalf
    (relabel.symm first) (relabel.symm middle) (relabel.symm last)
    hfirstMiddle hmiddleLast

/--
In every relabeled hard instance, the images of the source endpoints retain
the exceptional forward centered gap `1 / 2`.
-/
lemma theorem7RelabeledPreferenceGap_special_forward
    {n : ℕ} {mu : ℝ} (hcard : 2 ≤ n) (relabel : Equiv.Perm (Fin n)) :
    theorem7RelabeledPreferenceGap n mu relabel
      (relabel ⟨0, by omega⟩) (relabel ⟨n - 1, by omega⟩) = 1 / 2 := by
  let first : Fin n := ⟨0, by omega⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hfirstLast : first.val < last.val := by
    dsimp [first, last]
    omega
  have hfirst : first.val = 0 := by rfl
  have hlast : last.val + 1 = n := by
    dsimp [last]
    omega
  have hbase : theorem7PreferenceGap n mu first last = 1 / 2 := by
    rw [theorem7PreferenceGap, if_pos hfirstLast]
    rw [theorem7ForwardGap, if_pos ⟨hfirst, hlast⟩]
  convert hbase using 1
  all_goals simp [theorem7RelabeledPreferenceGap, first, last]

/-- The reverse exceptional comparison in a relabeled hard instance has gap `-1 / 2`. -/
lemma theorem7RelabeledPreferenceGap_special_reverse
    {n : ℕ} {mu : ℝ} (hcard : 2 ≤ n) (relabel : Equiv.Perm (Fin n)) :
    theorem7RelabeledPreferenceGap n mu relabel
      (relabel ⟨n - 1, by omega⟩) (relabel ⟨0, by omega⟩) = -(1 / 2 : ℝ) := by
  let first : Fin n := ⟨0, by omega⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hfirst : first.val = 0 := by rfl
  have hlast : last.val + 1 = n := by
    dsimp [last]
    omega
  have hbase : theorem7PreferenceGap n mu last first = -(1 / 2 : ℝ) :=
    theorem7PreferenceGap_last_first hcard first last hfirst hlast
  convert hbase using 1
  all_goals simp [theorem7RelabeledPreferenceGap, first, last]

/--
Every `1 / 4`-ranking of a relabeled hard instance places the image of source
position `0` before the image of source position `n - 1`.
-/
theorem theorem7Relabeled_epsilonRanking_orders_special_endpoints
    {n : ℕ} {mu : ℝ} (hcard : 2 ≤ n)
    (relabel : Equiv.Perm (Fin n))
    (ranking : Fin (Fintype.card (Fin n)) → Fin n)
    (hranking : EpsilonPreferenceRanking
      (theorem7RelabeledPreferenceGap n mu relabel) (1 / 4) ranking) :
    ∃ firstSlot lastSlot,
      ranking firstSlot = relabel ⟨0, by omega⟩ ∧
      ranking lastSlot = relabel ⟨n - 1, by omega⟩ ∧ firstSlot.val < lastSlot.val := by
  let first : Fin n := ⟨0, by omega⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hreverse : theorem7RelabeledPreferenceGap n mu relabel
      (relabel last) (relabel first) = -(1 / 2 : ℝ) := by
    exact theorem7RelabeledPreferenceGap_special_reverse hcard relabel
  rcases hranking.1.2 (relabel first) with ⟨firstSlot, hfirstSlot⟩
  rcases hranking.1.2 (relabel last) with ⟨lastSlot, hlastSlot⟩
  refine ⟨firstSlot, lastSlot, hfirstSlot, hlastSlot, ?_⟩
  by_contra hnot
  have hlastFirst : lastSlot.val ≤ firstSlot.val := Nat.le_of_not_gt hnot
  have hgap : -(1 / 4 : ℝ) ≤
      theorem7RelabeledPreferenceGap n mu relabel (relabel last) (relabel first) := by
    rw [← hlastSlot, ← hfirstSlot]
    exact hranking.2 lastSlot firstSlot hlastFirst
  rw [hreverse] at hgap
  norm_num at hgap

/--
The concrete Theorem 7 hard model whose exceptional comparison has the
prescribed ordered labels `first` and `last`.
-/
noncomputable def theorem7OrderedEndpointPreferenceGap
    (n : ℕ) (mu : ℝ) (hcard : 2 ≤ n) (first last : Fin n) : Fin n → Fin n → ℝ :=
  theorem7RelabeledPreferenceGap n mu
    (theorem7RelabelingOfOrderedEndpoints n hcard first last)

/-- Every prescribed-endpoint Theorem 7 hard instance is SST. -/
theorem theorem7OrderedEndpointPreferenceGap_strongStochasticTransitivity
    (n : ℕ) (mu : ℝ) (hcard : 2 ≤ n) (hmu : 0 < mu) (hmuHalf : mu ≤ 1 / 2)
    (first last : Fin n) :
    StrongStochasticTransitivity
      (theorem7OrderedEndpointPreferenceGap n mu hcard first last) := by
  exact theorem7RelabeledPreferenceGap_strongStochasticTransitivity n mu hmu hmuHalf _

/-- The prescribed forward exceptional comparison has centered gap `1 / 2`. -/
lemma theorem7OrderedEndpointPreferenceGap_special_forward
    {n : ℕ} {mu : ℝ} (hcard : 2 ≤ n) (first last : Fin n) (hneq : first ≠ last) :
    theorem7OrderedEndpointPreferenceGap n mu hcard first last first last = 1 / 2 := by
  let relabel := theorem7RelabelingOfOrderedEndpoints n hcard first last
  have hspecial := theorem7RelabeledPreferenceGap_special_forward (mu := mu) hcard relabel
  dsimp only [relabel] at hspecial
  change theorem7RelabeledPreferenceGap n mu
    (theorem7RelabelingOfOrderedEndpoints n hcard first last)
    ((theorem7RelabelingOfOrderedEndpoints n hcard first last) (theorem7FirstPosition n hcard))
    ((theorem7RelabelingOfOrderedEndpoints n hcard first last) (theorem7LastPosition n hcard)) = 1 / 2 at hspecial
  rw [theorem7RelabelingOfOrderedEndpoints_first hcard first last hneq,
    theorem7RelabelingOfOrderedEndpoints_last hcard first last] at hspecial
  exact hspecial

/-- The prescribed reverse exceptional comparison has centered gap `-1 / 2`. -/
lemma theorem7OrderedEndpointPreferenceGap_special_reverse
    {n : ℕ} {mu : ℝ} (hcard : 2 ≤ n) (first last : Fin n) (hneq : first ≠ last) :
    theorem7OrderedEndpointPreferenceGap n mu hcard first last last first = -(1 / 2 : ℝ) := by
  let relabel := theorem7RelabelingOfOrderedEndpoints n hcard first last
  have hspecial := theorem7RelabeledPreferenceGap_special_reverse (mu := mu) hcard relabel
  dsimp only [relabel] at hspecial
  change theorem7RelabeledPreferenceGap n mu
    (theorem7RelabelingOfOrderedEndpoints n hcard first last)
    ((theorem7RelabelingOfOrderedEndpoints n hcard first last) (theorem7LastPosition n hcard))
    ((theorem7RelabelingOfOrderedEndpoints n hcard first last) (theorem7FirstPosition n hcard)) =
      -(1 / 2 : ℝ) at hspecial
  rw [theorem7RelabelingOfOrderedEndpoints_last hcard first last,
    theorem7RelabelingOfOrderedEndpoints_first hcard first last hneq] at hspecial
  exact hspecial

/--
After relabeling, every distinct nonexceptional pair still has centered gap
`mu` or `-mu`.  The unordered-pair premise is what excludes both orientations
of the special endpoint comparison.
-/
lemma theorem7OrderedEndpointPreferenceGap_eq_mu_or_neg_mu_of_not_special
    {n : ℕ} {mu : ℝ} (hcard : 2 ≤ n) (first last i j : Fin n)
    (hfirstLast : first ≠ last) (hij : i ≠ j)
    (hnotSpecial : Sym2.mk i j ≠ Sym2.mk first last) :
    theorem7OrderedEndpointPreferenceGap n mu hcard first last i j = mu ∨
      theorem7OrderedEndpointPreferenceGap n mu hcard first last i j = -mu := by
  let relabel := theorem7RelabelingOfOrderedEndpoints n hcard first last
  have hsourceNe : relabel.symm i ≠ relabel.symm j := by
    intro heq
    apply hij
    simpa using congrArg relabel heq
  have hforward : ¬ ((relabel.symm i).val = 0 ∧ (relabel.symm j).val + 1 = n) := by
    rintro ⟨hi, hj⟩
    have hsourceI : relabel.symm i = theorem7FirstPosition n hcard := Fin.ext hi
    have hsourceJ : relabel.symm j = theorem7LastPosition n hcard := by
      apply Fin.ext
      have hlast := theorem7LastPosition_val n hcard
      omega
    have hlabelI : i = first := by
      calc
        i = relabel (relabel.symm i) := (relabel.apply_symm_apply i).symm
        _ = relabel (theorem7FirstPosition n hcard) := by rw [hsourceI]
        _ = first := theorem7RelabelingOfOrderedEndpoints_first hcard first last hfirstLast
    have hlabelJ : j = last := by
      calc
        j = relabel (relabel.symm j) := (relabel.apply_symm_apply j).symm
        _ = relabel (theorem7LastPosition n hcard) := by rw [hsourceJ]
        _ = last := theorem7RelabelingOfOrderedEndpoints_last hcard first last
    apply hnotSpecial
    rw [hlabelI, hlabelJ]
  have hreverse : ¬ ((relabel.symm j).val = 0 ∧ (relabel.symm i).val + 1 = n) := by
    rintro ⟨hj, hi⟩
    have hsourceI : relabel.symm i = theorem7LastPosition n hcard := by
      apply Fin.ext
      have hlast := theorem7LastPosition_val n hcard
      omega
    have hsourceJ : relabel.symm j = theorem7FirstPosition n hcard := Fin.ext hj
    have hlabelI : i = last := by
      calc
        i = relabel (relabel.symm i) := (relabel.apply_symm_apply i).symm
        _ = relabel (theorem7LastPosition n hcard) := by rw [hsourceI]
        _ = last := theorem7RelabelingOfOrderedEndpoints_last hcard first last
    have hlabelJ : j = first := by
      calc
        j = relabel (relabel.symm j) := (relabel.apply_symm_apply j).symm
        _ = relabel (theorem7FirstPosition n hcard) := by rw [hsourceJ]
        _ = first := theorem7RelabelingOfOrderedEndpoints_first hcard first last hfirstLast
    apply hnotSpecial
    rw [hlabelI, hlabelJ]
    exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)
  change theorem7PreferenceGap n mu (relabel.symm i) (relabel.symm j) = mu ∨
    theorem7PreferenceGap n mu (relabel.symm i) (relabel.symm j) = -mu
  exact theorem7PreferenceGap_eq_mu_or_neg_mu_of_not_endpoints _ _ hsourceNe hforward hreverse

/--
For every prescribed pair of distinct arm labels, a `1 / 4`-ranking of the
corresponding Theorem 7 hard instance must place the first label before the
second.  Thus the randomized-relabeling family has the ranking implication
used by the source lower-bound argument on every atom of its support.
-/
theorem theorem7OrderedEndpoint_epsilonRanking_orders_endpoints
    {n : ℕ} {mu : ℝ} (hcard : 2 ≤ n) (first last : Fin n) (hneq : first ≠ last)
    (ranking : Fin (Fintype.card (Fin n)) → Fin n)
    (hranking : EpsilonPreferenceRanking
      (theorem7OrderedEndpointPreferenceGap n mu hcard first last) (1 / 4) ranking) :
    ∃ firstSlot lastSlot,
      ranking firstSlot = first ∧ ranking lastSlot = last ∧ firstSlot.val < lastSlot.val := by
  rcases hranking.1.2 first with ⟨firstSlot, hfirstSlot⟩
  rcases hranking.1.2 last with ⟨lastSlot, hlastSlot⟩
  refine ⟨firstSlot, lastSlot, hfirstSlot, hlastSlot, ?_⟩
  by_contra hnot
  have hlastFirst : lastSlot.val ≤ firstSlot.val := Nat.le_of_not_gt hnot
  have hrankingGap := hranking.2 lastSlot firstSlot hlastFirst
  have hgap : -(1 / 4 : ℝ) ≤
      theorem7OrderedEndpointPreferenceGap n mu hcard first last last first := by
    simpa only [hlastSlot, hfirstSlot] using hrankingGap
  rw [theorem7OrderedEndpointPreferenceGap_special_reverse hcard first last hneq] at hgap
  norm_num at hgap

/--
The canonical increasing ordered endpoints of an unordered comparison
coordinate.  A non-diagonal `Sym2` coordinate contains exactly two labels.
-/
noncomputable def theorem7CanonicalEndpoints
    {n : ℕ} (coordinate : unorderedComparisonCoordinate (Fin n)) : Fin n × Fin n := by
  let arms := coordinate.val.toFinset
  have hcard : arms.card = 2 := Sym2.card_toFinset_of_not_isDiag _ coordinate.property
  have hnonempty : arms.Nonempty := Finset.card_pos.mp (by omega)
  exact (arms.min' hnonempty, arms.max' hnonempty)

/-- The canonical endpoints of an unordered coordinate are distinct. -/
lemma theorem7CanonicalEndpoints_distinct
    {n : ℕ} (coordinate : unorderedComparisonCoordinate (Fin n)) :
    (theorem7CanonicalEndpoints coordinate).1 ≠ (theorem7CanonicalEndpoints coordinate).2 := by
  classical
  let arms := coordinate.val.toFinset
  have hcard : arms.card = 2 := Sym2.card_toFinset_of_not_isDiag _ coordinate.property
  have hnonempty : arms.Nonempty := Finset.card_pos.mp (by omega)
  have hminmem : arms.min' hnonempty ∈ arms := Finset.min'_mem _ _
  obtain ⟨other, hothermem, hotherne⟩ :=
    Finset.exists_mem_ne (by omega : 1 < arms.card) (arms.min' hnonempty)
  have hlt : arms.min' hnonempty < arms.max' hnonempty :=
    Finset.min'_lt_max' arms hminmem hothermem hotherne.symm
  change arms.min' hnonempty ≠ arms.max' hnonempty
  exact ne_of_lt hlt

/-- The unordered coordinate recovered from the canonical endpoints is the original coordinate. -/
lemma theorem7CanonicalEndpoints_coordinate_eq
    {n : ℕ} (coordinate : unorderedComparisonCoordinate (Fin n)) :
    Sym2.mk (theorem7CanonicalEndpoints coordinate).1 (theorem7CanonicalEndpoints coordinate).2 =
      coordinate.val := by
  classical
  let arms := coordinate.val.toFinset
  have hcard : arms.card = 2 := Sym2.card_toFinset_of_not_isDiag _ coordinate.property
  have hnonempty : arms.Nonempty := Finset.card_pos.mp (by omega)
  have hminmem : arms.min' hnonempty ∈ arms := Finset.min'_mem _ _
  have hmaxmem : arms.max' hnonempty ∈ arms := Finset.max'_mem _ _
  have hlt : arms.min' hnonempty < arms.max' hnonempty := by
    obtain ⟨other, hothermem, hotherne⟩ :=
      Finset.exists_mem_ne (by omega : 1 < arms.card) (arms.min' hnonempty)
    exact Finset.min'_lt_max' arms hminmem hothermem hotherne.symm
  have hpairs : ({arms.min' hnonempty, arms.max' hnonempty} : Finset (Fin n)) = arms := by
    apply Finset.eq_of_subset_of_card_le
    · intro arm harm
      simp only [Finset.mem_insert, Finset.mem_singleton] at harm
      rcases harm with harm | harm
      · simpa [harm] using hminmem
      · simpa [harm] using hmaxmem
    · rw [hcard]
      simp [ne_of_lt hlt]
  change Sym2.mk (arms.min' hnonempty) (arms.max' hnonempty) = coordinate.val
  apply Sym2.ext
  intro arm
  calc
    arm ∈ Sym2.mk (arms.min' hnonempty) (arms.max' hnonempty) ↔
        arm ∈ ({arms.min' hnonempty, arms.max' hnonempty} : Finset (Fin n)) := by
      rw [← Sym2.mem_toFinset, Sym2.toFinset_mk_eq]
    _ ↔ arm ∈ arms := by rw [hpairs]
    _ ↔ arm ∈ coordinate.val := by
      simp [arms]

/--
Orient an unordered hidden comparison coordinate with an independent bit.  The
orientation is the exact endpoint input for the uniformly relabeled hard-model
family.
-/
noncomputable def theorem7EndpointsOfCoordinate
    {n : ℕ} (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool) : Fin n × Fin n :=
  if orientation then theorem7CanonicalEndpoints coordinate
  else (theorem7CanonicalEndpoints coordinate).swap

/-- The oriented endpoint pair remains distinct for either orientation bit. -/
lemma theorem7EndpointsOfCoordinate_distinct
    {n : ℕ} (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool) :
    (theorem7EndpointsOfCoordinate coordinate orientation).1 ≠
      (theorem7EndpointsOfCoordinate coordinate orientation).2 := by
  rw [theorem7EndpointsOfCoordinate]
  split_ifs
  · exact theorem7CanonicalEndpoints_distinct coordinate
  · exact (theorem7CanonicalEndpoints_distinct coordinate).symm

/-- Forgetting the orientation bit recovers the hidden unordered coordinate. -/
lemma theorem7EndpointsOfCoordinate_coordinate_eq
    {n : ℕ} (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool) :
    Sym2.mk (theorem7EndpointsOfCoordinate coordinate orientation).1
      (theorem7EndpointsOfCoordinate coordinate orientation).2 = coordinate.val := by
  rw [theorem7EndpointsOfCoordinate]
  split_ifs
  · exact theorem7CanonicalEndpoints_coordinate_eq coordinate
  · rw [← theorem7CanonicalEndpoints_coordinate_eq coordinate]
    exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)

/--
The source's Theorem 7 SST hard model indexed by the same uniform hidden
unordered coordinate and orientation bit as `randomHiddenComparisonBitLaw`.
-/
noncomputable def theorem7HiddenCoordinatePreferenceGap
    (n : ℕ) (mu : ℝ) (hcard : 2 ≤ n)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool) : Fin n → Fin n → ℝ :=
  theorem7OrderedEndpointPreferenceGap n mu hcard
    (theorem7EndpointsOfCoordinate coordinate orientation).1
    (theorem7EndpointsOfCoordinate coordinate orientation).2

/-- Each coordinate-and-orientation hard instance satisfies SST. -/
theorem theorem7HiddenCoordinatePreferenceGap_strongStochasticTransitivity
    (n : ℕ) (mu : ℝ) (hcard : 2 ≤ n) (hmu : 0 < mu) (hmuHalf : mu ≤ 1 / 2)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool) :
    StrongStochasticTransitivity
      (theorem7HiddenCoordinatePreferenceGap n mu hcard coordinate orientation) := by
  exact theorem7OrderedEndpointPreferenceGap_strongStochasticTransitivity n mu hcard hmu hmuHalf _ _

/--
For a queried unordered pair different from the hidden exceptional pair, the
canonical-orientation centered gap in the hidden-coordinate hard model is
exactly `mu` or `-mu`.
-/
lemma theorem7HiddenCoordinatePreferenceGap_eq_mu_or_neg_mu_of_not_hidden
    {n : ℕ} {mu : ℝ} (hcard : 2 ≤ n)
    (coordinate query : unorderedComparisonCoordinate (Fin n)) (orientation : Bool)
    (hnotHidden : query ≠ coordinate) :
    theorem7HiddenCoordinatePreferenceGap n mu hcard coordinate orientation
        (theorem7CanonicalEndpoints query).1 (theorem7CanonicalEndpoints query).2 = mu ∨
      theorem7HiddenCoordinatePreferenceGap n mu hcard coordinate orientation
        (theorem7CanonicalEndpoints query).1 (theorem7CanonicalEndpoints query).2 = -mu := by
  have hqueryDistinct := theorem7CanonicalEndpoints_distinct query
  have hhiddenDistinct := theorem7EndpointsOfCoordinate_distinct coordinate orientation
  have hnotSpecial :
      Sym2.mk (theorem7CanonicalEndpoints query).1 (theorem7CanonicalEndpoints query).2 ≠
        Sym2.mk (theorem7EndpointsOfCoordinate coordinate orientation).1
          (theorem7EndpointsOfCoordinate coordinate orientation).2 := by
    intro heq
    apply hnotHidden
    apply Subtype.ext
    calc
      query.val = Sym2.mk (theorem7CanonicalEndpoints query).1
          (theorem7CanonicalEndpoints query).2 :=
        (theorem7CanonicalEndpoints_coordinate_eq query).symm
      _ = Sym2.mk (theorem7EndpointsOfCoordinate coordinate orientation).1
          (theorem7EndpointsOfCoordinate coordinate orientation).2 := heq
      _ = coordinate.val := theorem7EndpointsOfCoordinate_coordinate_eq coordinate orientation
  exact theorem7OrderedEndpointPreferenceGap_eq_mu_or_neg_mu_of_not_special hcard
    (theorem7EndpointsOfCoordinate coordinate orientation).1
    (theorem7EndpointsOfCoordinate coordinate orientation).2
    (theorem7CanonicalEndpoints query).1 (theorem7CanonicalEndpoints query).2
    hhiddenDistinct hqueryDistinct hnotSpecial

/--
The ordinary-query response direction in a hidden-coordinate hard model:
`true` means the canonical first endpoint has the positive `mu` gap.
-/
noncomputable def theorem7HiddenCoordinateOrdinaryDirection
    (n : ℕ) (mu : ℝ) (hcard : 2 ≤ n)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool)
    (query : unorderedComparisonCoordinate (Fin n)) : Bool :=
  decide (theorem7HiddenCoordinatePreferenceGap n mu hcard coordinate orientation
    (theorem7CanonicalEndpoints query).1 (theorem7CanonicalEndpoints query).2 = mu)

/--
Every `1 / 4`-ranking of a coordinate-and-orientation hard instance orders its
two hidden endpoints in the orientation selected by that bit.
-/
theorem theorem7HiddenCoordinate_epsilonRanking_orders_endpoints
    {n : ℕ} {mu : ℝ} (hcard : 2 ≤ n)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool)
    (ranking : Fin (Fintype.card (Fin n)) → Fin n)
    (hranking : EpsilonPreferenceRanking
      (theorem7HiddenCoordinatePreferenceGap n mu hcard coordinate orientation) (1 / 4) ranking) :
    ∃ firstSlot lastSlot,
      ranking firstSlot = (theorem7EndpointsOfCoordinate coordinate orientation).1 ∧
      ranking lastSlot = (theorem7EndpointsOfCoordinate coordinate orientation).2 ∧
      firstSlot.val < lastSlot.val := by
  exact theorem7OrderedEndpoint_epsilonRanking_orders_endpoints hcard _ _
    (theorem7EndpointsOfCoordinate_distinct coordinate orientation) ranking hranking

/-- A ranking places `first` before `last` when their output slots occur in that order. -/
noncomputable def theorem7RankingPutsBefore
    {n : ℕ} (ranking : Fin (Fintype.card (Fin n)) → Fin n) (first last : Fin n) : Prop :=
  ∃ firstSlot lastSlot, ranking firstSlot = first ∧ ranking lastSlot = last ∧ firstSlot.val < lastSlot.val

/-- A bijective ranking cannot place the same two labels in both strict orders. -/
lemma theorem7RankingPutsBefore_not_reverse_of_injective
    {n : ℕ} (ranking : Fin (Fintype.card (Fin n)) → Fin n)
    (hinjective : Function.Injective ranking) (first last : Fin n)
    (hbefore : theorem7RankingPutsBefore ranking first last) :
    ¬ theorem7RankingPutsBefore ranking last first := by
  rintro ⟨firstSlot, lastSlot, hfirst, hlast, hlt⟩
  rcases hbefore with ⟨forwardFirstSlot, forwardLastSlot, hforwardFirst, hforwardLast, hforwardLt⟩
  have hfirstEq : firstSlot = forwardLastSlot :=
    hinjective (hfirst.trans hforwardLast.symm)
  have hlastEq : lastSlot = forwardFirstSlot :=
    hinjective (hlast.trans hforwardFirst.symm)
  subst firstSlot
  subst lastSlot
  omega

/--
The orientation predicted by a ranking for one hidden unordered coordinate:
`true` means it places the canonical first endpoint before the second.
-/
noncomputable def theorem7RankingOrientationPrediction
    {n : ℕ} (ranking : Fin (Fintype.card (Fin n)) → Fin n)
    (coordinate : unorderedComparisonCoordinate (Fin n)) : Bool := by
  classical
  exact decide (theorem7RankingPutsBefore ranking
    (theorem7CanonicalEndpoints coordinate).1 (theorem7CanonicalEndpoints coordinate).2)

/--
Success on the source `1 / 4`-ranking task determines the hidden orientation
bit from the ranking output, even though this prediction may vary by hidden
comparison coordinate.
-/
theorem theorem7RankingOrientationPrediction_eq_orientation_of_epsilonRanking
    {n : ℕ} {mu : ℝ} (hcard : 2 ≤ n)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool)
    (ranking : Fin (Fintype.card (Fin n)) → Fin n)
    (hranking : EpsilonPreferenceRanking
      (theorem7HiddenCoordinatePreferenceGap n mu hcard coordinate orientation) (1 / 4) ranking) :
    theorem7RankingOrientationPrediction ranking coordinate = orientation := by
  classical
  cases orientation
  · have hreverse : theorem7RankingPutsBefore ranking
      (theorem7CanonicalEndpoints coordinate).2 (theorem7CanonicalEndpoints coordinate).1 := by
      simpa [theorem7RankingPutsBefore, theorem7EndpointsOfCoordinate] using
        theorem7HiddenCoordinate_epsilonRanking_orders_endpoints hcard coordinate false ranking hranking
    have hnot : ¬ theorem7RankingPutsBefore ranking
        (theorem7CanonicalEndpoints coordinate).1 (theorem7CanonicalEndpoints coordinate).2 :=
      theorem7RankingPutsBefore_not_reverse_of_injective ranking hranking.1.1 _ _ hreverse
    rw [theorem7RankingOrientationPrediction]
    exact decide_eq_false hnot
  · have hforward : theorem7RankingPutsBefore ranking
      (theorem7CanonicalEndpoints coordinate).1 (theorem7CanonicalEndpoints coordinate).2 := by
      simpa [theorem7RankingPutsBefore, theorem7EndpointsOfCoordinate] using
        theorem7HiddenCoordinate_epsilonRanking_orders_endpoints hcard coordinate true ranking hranking
    rw [theorem7RankingOrientationPrediction]
    exact decide_eq_true hforward

/--
A deterministic finite comparison procedure for the Theorem 7 ranking task.
At each round it chooses an unordered pair from the previously observed binary
outcomes, and returns a candidate full ranking after its comparison budget.
-/
structure Theorem7AdaptiveRankingProcedure (n comparisonBudget : ℕ) where
  query : (round : Fin comparisonBudget) → (Fin round.val → Bool) →
    unorderedComparisonCoordinate (Fin n)
  output : (Fin comparisonBudget → Bool) → Fin (Fintype.card (Fin n)) → Fin n

/-- The outcome history available strictly before one comparison round. -/
def theorem7OutcomePrefix {comparisonBudget : ℕ}
    (outcomes : Fin comparisonBudget → Bool) (round : Fin comparisonBudget) :
    Fin round.val → Bool := fun earlier =>
  outcomes (Fin.castLT earlier (Nat.lt_trans earlier.isLt round.isLt))

/-- The coordinate selected by a procedure at a concrete outcome trace and round. -/
def theorem7ProcedureQueryAt {n comparisonBudget : ℕ}
    (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (outcomes : Fin comparisonBudget → Bool) (round : Fin comparisonBudget) :
    unorderedComparisonCoordinate (Fin n) :=
  procedure.query round (theorem7OutcomePrefix outcomes round)

/-- All distinct comparison coordinates selected along a concrete outcome trace. -/
def theorem7ProcedureQueriedCoordinates {n comparisonBudget : ℕ}
    (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (outcomes : Fin comparisonBudget → Bool) : Finset (unorderedComparisonCoordinate (Fin n)) :=
  Finset.univ.image (theorem7ProcedureQueryAt procedure outcomes)

/-- A procedure that makes `comparisonBudget` rounds visits at most that many coordinates. -/
lemma theorem7ProcedureQueriedCoordinates_card_le {n comparisonBudget : ℕ}
    (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (outcomes : Fin comparisonBudget → Bool) :
    (theorem7ProcedureQueriedCoordinates procedure outcomes).card ≤ comparisonBudget := by
  unfold theorem7ProcedureQueriedCoordinates
  calc
    (Finset.univ.image (theorem7ProcedureQueryAt procedure outcomes)).card ≤
        (Finset.univ : Finset (Fin comparisonBudget)).card := Finset.card_image_le
    _ = comparisonBudget := Fintype.card_fin _

/--
The finite base-model response trace.  A query of the hidden coordinate returns
its orientation bit; every other query returns its corresponding independent
fair-noise bit.  The recursion makes the query at each round depend on the
actual preceding responses.
-/
noncomputable def theorem7ActualOutcomePrefix
    {n comparisonBudget : ℕ} (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool)
    (noise : Fin comparisonBudget → Bool) : (roundCount : ℕ) → Fin roundCount → Bool
  | 0 => fun round => Fin.elim0 round
  | roundCount + 1 =>
      Fin.snoc (theorem7ActualOutcomePrefix procedure coordinate orientation noise roundCount)
        (if hround : roundCount < comparisonBudget then
          if procedure.query ⟨roundCount, hround⟩
              (theorem7ActualOutcomePrefix procedure coordinate orientation noise roundCount) = coordinate then
            orientation
          else noise ⟨roundCount, hround⟩
        else false)

/-- The complete actual response trace obtained from the recursive base-model process. -/
noncomputable def theorem7ActualOutcomeTrace
    {n comparisonBudget : ℕ} (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool)
    (noise : Fin comparisonBudget → Bool) : Fin comparisonBudget → Bool :=
  theorem7ActualOutcomePrefix procedure coordinate orientation noise comparisonBudget

/--
The actual response prefix reconstructed from only the auxiliary-noise bits
already revealed.  This is extensionally the same recursion as
`theorem7ActualOutcomePrefix`, but its finite-history interface is needed to
make the small-`mu` auxiliary-noise PMF adaptive in the correct filtration.
-/
noncomputable def theorem7ActualOutcomeFromNoiseHistory
    {n comparisonBudget : ℕ} (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool) :
    (roundCount : ℕ) → (hroundCount : roundCount ≤ comparisonBudget) →
      (noiseHistory : Fin roundCount → Bool) → Fin roundCount → Bool
  | 0, _, _ => Fin.elim0
  | roundCount + 1, hroundCount, noiseHistory =>
      Fin.snoc
        (theorem7ActualOutcomeFromNoiseHistory procedure coordinate orientation roundCount
          (Nat.le_of_succ_le hroundCount) (Fin.init noiseHistory))
        (if procedure.query ⟨roundCount, Nat.lt_of_succ_le hroundCount⟩
            (theorem7ActualOutcomeFromNoiseHistory procedure coordinate orientation roundCount
              (Nat.le_of_succ_le hroundCount) (Fin.init noiseHistory)) = coordinate then
          orientation
        else noiseHistory (Fin.last roundCount))

/-- The prefix of an exogenous fair-noise trace at a smaller round count. -/
noncomputable def theorem7NoisePrefix {comparisonBudget : ℕ}
    (noise : Fin comparisonBudget → Bool) (roundCount : ℕ) (hroundCount : roundCount ≤ comparisonBudget) :
    Fin roundCount → Bool := fun round =>
  noise (Fin.castLT round (lt_of_lt_of_le round.isLt hroundCount))

/-- The fair-noise prefix is consistent when a new final round is appended. -/
lemma theorem7NoisePrefix_succ_castSucc {comparisonBudget roundCount : ℕ}
    (noise : Fin comparisonBudget → Bool) (hroundCount : roundCount + 1 ≤ comparisonBudget)
    (round : Fin roundCount) :
    theorem7NoisePrefix noise (roundCount + 1) hroundCount round.castSucc =
      theorem7NoisePrefix noise roundCount (Nat.le_of_succ_le hroundCount) round := by
  unfold theorem7NoisePrefix
  congr 1

/-- The new final entry of a fair-noise prefix is the matching full-trace bit. -/
lemma theorem7NoisePrefix_succ_last {comparisonBudget roundCount : ℕ}
    (noise : Fin comparisonBudget → Bool) (hroundCount : roundCount + 1 ≤ comparisonBudget) :
    theorem7NoisePrefix noise (roundCount + 1) hroundCount (Fin.last roundCount) =
      noise ⟨roundCount, Nat.lt_of_succ_le hroundCount⟩ := by
  unfold theorem7NoisePrefix
  congr 1

/--
Reconstructing from a revealed auxiliary-noise prefix gives the same actual
responses as the original full-noise recursion; future noise bits are never
consulted before their round.
-/
lemma theorem7ActualOutcomeFromNoiseHistory_eq_actualOutcomePrefix
    {n comparisonBudget : ℕ} (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool)
    (noise : Fin comparisonBudget → Bool) :
    ∀ (roundCount : ℕ) (hroundCount : roundCount ≤ comparisonBudget),
      theorem7ActualOutcomeFromNoiseHistory procedure coordinate orientation roundCount hroundCount
        (theorem7NoisePrefix noise roundCount hroundCount) =
        theorem7ActualOutcomePrefix procedure coordinate orientation noise roundCount := by
  intro roundCount
  induction roundCount with
  | zero =>
      intro hroundCount
      funext round
      exact Fin.elim0 round
  | succ roundCount ih =>
      intro hroundCount
      have hnoiseInit :
          Fin.init (theorem7NoisePrefix noise (roundCount + 1) hroundCount) =
            theorem7NoisePrefix noise roundCount (Nat.le_of_succ_le hroundCount) := by
        funext earlier
        exact theorem7NoisePrefix_succ_castSucc noise hroundCount earlier
      funext round
      refine Fin.lastCases ?_ ?_ round
      · simp only [theorem7ActualOutcomeFromNoiseHistory, Fin.snoc_last,
          theorem7ActualOutcomePrefix, dif_pos (Nat.lt_of_succ_le hroundCount)]
        rw [hnoiseInit, ih (Nat.le_of_succ_le hroundCount),
          theorem7NoisePrefix_succ_last noise hroundCount]
      · intro earlier
        simp only [theorem7ActualOutcomeFromNoiseHistory, Fin.snoc_castSucc,
          theorem7ActualOutcomePrefix]
        rw [hnoiseInit, ih (Nat.le_of_succ_le hroundCount)]

/--
Whether a procedure's next query is the hidden coordinate is measurable from
the auxiliary-noise history alone: the procedure first reconstructs its actual
response prefix and then chooses the next unordered pair.
-/
noncomputable def theorem7ProcedureNoiseHistorySpecial
    {n comparisonBudget : ℕ} (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool)
    (round : Fin comparisonBudget) (noiseHistory : Fin round.val → Bool) : Bool :=
  procedure.query round
    (theorem7ActualOutcomeFromNoiseHistory procedure coordinate orientation round.val round.isLt.le
      noiseHistory) = coordinate

/-- The finite-history exceptional-query indicator agrees with the full-trace query. -/
lemma theorem7ProcedureNoiseHistorySpecial_eq_fullTrace
    {n comparisonBudget : ℕ} (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool)
    (noise : Fin comparisonBudget → Bool) (round : Fin comparisonBudget) :
    theorem7ProcedureNoiseHistorySpecial procedure coordinate orientation round
      (theorem7NoisePrefix noise round.val round.isLt.le) =
      decide (procedure.query round
        (theorem7ActualOutcomePrefix procedure coordinate orientation noise round.val) = coordinate) := by
  unfold theorem7ProcedureNoiseHistorySpecial
  rw [theorem7ActualOutcomeFromNoiseHistory_eq_actualOutcomePrefix procedure coordinate orientation noise
    round.val round.isLt.le]

/--
Until the hidden coordinate is queried, the actual base-model trace agrees
exactly with the independent fair-noise trace.  This is the finite adaptive
pre-hit coupling omitted from the source proof sketch.
-/
lemma theorem7Prehit_actualPrefix_eq_noisePrefix
    {n comparisonBudget : ℕ} (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool)
    (noise : Fin comparisonBudget → Bool)
    (hmiss : coordinate ∉ theorem7ProcedureQueriedCoordinates procedure noise) :
    ∀ roundCount (hroundCount : roundCount ≤ comparisonBudget),
      theorem7ActualOutcomePrefix procedure coordinate orientation noise roundCount =
        theorem7NoisePrefix noise roundCount hroundCount := by
  intro roundCount
  induction roundCount with
  | zero =>
      intro hroundCount
      funext round
      exact Fin.elim0 round
  | succ roundCount ih =>
      intro hroundCount
      funext round
      refine Fin.lastCases ?_ ?_ round
      · simp only [theorem7ActualOutcomePrefix, Fin.snoc_last]
        have hqueryPrefix :
            theorem7ActualOutcomePrefix procedure coordinate orientation noise roundCount =
              theorem7OutcomePrefix noise ⟨roundCount, Nat.lt_of_succ_le hroundCount⟩ := by
          rw [ih (Nat.le_of_succ_le hroundCount)]
          funext earlier
          simp [theorem7NoisePrefix, theorem7OutcomePrefix]
        have hqueryMiss : procedure.query ⟨roundCount, Nat.lt_of_succ_le hroundCount⟩
            (theorem7ActualOutcomePrefix procedure coordinate orientation noise roundCount) ≠ coordinate := by
          rw [hqueryPrefix]
          intro heq
          apply hmiss
          exact Finset.mem_image.mpr ⟨⟨roundCount, Nat.lt_of_succ_le hroundCount⟩, Finset.mem_univ _, heq⟩
        simp only [dif_pos (Nat.lt_of_succ_le hroundCount), if_neg hqueryMiss]
        exact theorem7NoisePrefix_succ_last noise hroundCount
      · intro earlier
        simp only [theorem7ActualOutcomePrefix, Fin.snoc_castSucc]
        rw [ih (Nat.le_of_succ_le hroundCount)]
        exact theorem7NoisePrefix_succ_castSucc noise hroundCount earlier

/-- The full actual trace is fair noise whenever the noise-query path misses the hidden coordinate. -/
theorem theorem7Prehit_actualTrace_eq_noise
    {n comparisonBudget : ℕ} (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool)
    (noise : Fin comparisonBudget → Bool)
    (hmiss : coordinate ∉ theorem7ProcedureQueriedCoordinates procedure noise) :
    theorem7ActualOutcomeTrace procedure coordinate orientation noise = noise := by
  rw [theorem7ActualOutcomeTrace,
    theorem7Prehit_actualPrefix_eq_noisePrefix procedure coordinate orientation noise hmiss
      comparisonBudget (le_refl _)]
  funext round
  unfold theorem7NoisePrefix
  congr 1

/--
The one-step probability in the `mu = 0` comparison model, after a fixed
adaptive transcript has determined whether the current query is exceptional.
An exceptional outcome is deterministic; every other outcome is a fair bit.
-/
noncomputable def theorem7BaseOutcomeProbability (special outcome : Bool) : ℝ :=
  if special then if outcome then 1 else 0 else 1 / 2

/--
The corresponding one-step probability in the source's small-`mu` model.
The exceptional query remains deterministic and ordinary queries have bias
`mu` in their ordered direction.
-/
noncomputable def theorem7SmallMuOutcomeProbability
    (mu : ℝ) (special outcome : Bool) : ℝ :=
  if special then if outcome then 1 else 0
  else if outcome then 1 / 2 + mu else 1 / 2 - mu

/--
The likelihood of a fixed finite outcome transcript.  Its `special` indicator
may have been selected adaptively by earlier outcomes; after conditioning on a
realized transcript it is simply a finite sequence of one-step factors.
-/
noncomputable def theorem7TranscriptLikelihood
    {roundCount : ℕ} (oneStep : Bool → Bool → ℝ)
    (special outcome : Fin roundCount → Bool) : ℝ :=
  ∏ round, oneStep (special round) (outcome round)

/-- Nonnegativity of a base-model transcript factor. -/
private lemma theorem7BaseOutcomeProbability_nonneg
    (special outcome : Bool) : 0 ≤ theorem7BaseOutcomeProbability special outcome := by
  cases special <;> cases outcome <;> norm_num [theorem7BaseOutcomeProbability]

/-- Nonnegativity of a small-`mu` transcript factor in the probability range. -/
private lemma theorem7SmallMuOutcomeProbability_nonneg
    {mu : ℝ} (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2) (special outcome : Bool) :
    0 ≤ theorem7SmallMuOutcomeProbability mu special outcome := by
  cases special <;> cases outcome <;>
    simp [theorem7SmallMuOutcomeProbability] <;> linarith

/--
Each small-`mu` transcript factor is at most `1 + 2 * mu` times the
corresponding base-model factor.
-/
private lemma theorem7SmallMuOutcomeProbability_le_scaled_base
    {mu : ℝ} (hmu : 0 ≤ mu) (special outcome : Bool) :
    theorem7SmallMuOutcomeProbability mu special outcome ≤
      (1 + 2 * mu) * theorem7BaseOutcomeProbability special outcome := by
  cases special <;> cases outcome <;>
    simp [theorem7SmallMuOutcomeProbability, theorem7BaseOutcomeProbability] <;> linarith

/--
The exact finite likelihood transfer underlying Appendix B.1: for every
fixed transcript of at most `roundCount` comparisons, the small-`mu` likelihood
is at most `(1 + 2 * mu)^roundCount` times its `mu = 0` likelihood.  Connecting
this pointwise inequality to a randomized adaptive algorithm remains the
separate relabeling/trace-law bridge.
-/
theorem theorem7TranscriptLikelihood_smallMu_le_base_scaled
    {roundCount : ℕ} {mu : ℝ} (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2)
    (special outcome : Fin roundCount → Bool) :
    theorem7TranscriptLikelihood (theorem7SmallMuOutcomeProbability mu) special outcome ≤
      (1 + 2 * mu) ^ roundCount *
        theorem7TranscriptLikelihood theorem7BaseOutcomeProbability special outcome := by
  have hpoint : ∀ round : Fin roundCount,
      theorem7SmallMuOutcomeProbability mu (special round) (outcome round) ≤
        (1 + 2 * mu) * theorem7BaseOutcomeProbability (special round) (outcome round) := by
    intro round
    exact theorem7SmallMuOutcomeProbability_le_scaled_base hmu _ _
  calc
    theorem7TranscriptLikelihood (theorem7SmallMuOutcomeProbability mu) special outcome ≤
        ∏ round, (1 + 2 * mu) * theorem7BaseOutcomeProbability (special round) (outcome round) := by
      unfold theorem7TranscriptLikelihood
      apply Finset.prod_le_prod
      · intro round _
        exact theorem7SmallMuOutcomeProbability_nonneg hmu hmuHalf _ _
      · intro round _
        exact hpoint round
    _ = (1 + 2 * mu) ^ roundCount *
        theorem7TranscriptLikelihood theorem7BaseOutcomeProbability special outcome := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      simp [theorem7TranscriptLikelihood]

/--
The one-step small-`mu` response probability with its ordinary comparison
direction made explicit.  A relabeled hard instance can orient an ordinary
unordered pair either way, so its `mu` bias need not agree with a fixed global
Boolean outcome convention.  Exceptional comparisons remain deterministic.
-/
noncomputable def theorem7OrientedSmallMuOutcomeProbability
    (mu : ℝ) (special ordinaryDirection outcome : Bool) : ℝ :=
  if special then if outcome then 1 else 0
  else if outcome = ordinaryDirection then 1 / 2 + mu else 1 / 2 - mu

/--
On a nonhidden query, the oriented Bernoulli probability exactly equals the
source hard model's probability for the canonical first endpoint to win.
-/
lemma theorem7HiddenCoordinateOrdinaryResponseProbability_eq_model
    {n : ℕ} {mu : ℝ} (hcard : 2 ≤ n) (hmu : 0 < mu)
    (coordinate query : unorderedComparisonCoordinate (Fin n)) (orientation outcome : Bool)
    (hnotHidden : query ≠ coordinate) :
    theorem7OrientedSmallMuOutcomeProbability mu false
      (theorem7HiddenCoordinateOrdinaryDirection n mu hcard coordinate orientation query) outcome =
      if outcome then
        1 / 2 + theorem7HiddenCoordinatePreferenceGap n mu hcard coordinate orientation
          (theorem7CanonicalEndpoints query).1 (theorem7CanonicalEndpoints query).2
      else
        1 / 2 - theorem7HiddenCoordinatePreferenceGap n mu hcard coordinate orientation
          (theorem7CanonicalEndpoints query).1 (theorem7CanonicalEndpoints query).2 := by
  rcases theorem7HiddenCoordinatePreferenceGap_eq_mu_or_neg_mu_of_not_hidden
      hcard coordinate query orientation hnotHidden with hgap | hgap
  · have hdirection :
        theorem7HiddenCoordinateOrdinaryDirection n mu hcard coordinate orientation query = true := by
      rw [theorem7HiddenCoordinateOrdinaryDirection]
      exact decide_eq_true hgap
    rw [hdirection, hgap]
    cases outcome <;> simp [theorem7OrientedSmallMuOutcomeProbability]
  · have hgapNe : theorem7HiddenCoordinatePreferenceGap n mu hcard coordinate orientation
        (theorem7CanonicalEndpoints query).1 (theorem7CanonicalEndpoints query).2 ≠ mu := by
      rw [hgap]
      linarith
    have hdirection :
        theorem7HiddenCoordinateOrdinaryDirection n mu hcard coordinate orientation query = false := by
      rw [theorem7HiddenCoordinateOrdinaryDirection]
      exact decide_eq_false hgapNe
    rw [hdirection, hgap]
    cases outcome
    · simp [theorem7OrientedSmallMuOutcomeProbability]
    · simp [theorem7OrientedSmallMuOutcomeProbability]
      ring

/-- The oriented small-`mu` factor is nonnegative in the probability range. -/
private lemma theorem7OrientedSmallMuOutcomeProbability_nonneg
    {mu : ℝ} (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2)
    (special ordinaryDirection outcome : Bool) :
    0 ≤ theorem7OrientedSmallMuOutcomeProbability mu special ordinaryDirection outcome := by
  cases special <;> cases ordinaryDirection <;> cases outcome <;>
    simp [theorem7OrientedSmallMuOutcomeProbability] <;> linarith

/--
An oriented ordinary comparison has the same pointwise likelihood upper bound
as the fixed-direction version: its favored outcome can only gain a factor
`1 + 2 * mu` over a fair response, while the exceptional deterministic factor
is unchanged.
-/
private lemma theorem7OrientedSmallMuOutcomeProbability_le_scaled_base
    {mu : ℝ} (hmu : 0 ≤ mu) (special ordinaryDirection outcome : Bool) :
    theorem7OrientedSmallMuOutcomeProbability mu special ordinaryDirection outcome ≤
      (1 + 2 * mu) * theorem7BaseOutcomeProbability special outcome := by
  cases special <;> cases ordinaryDirection <;> cases outcome <;>
    simp [theorem7OrientedSmallMuOutcomeProbability, theorem7BaseOutcomeProbability] <;> linarith

/-- The `true` probability of an oriented response is at most one. -/
private lemma theorem7OrientedSmallMuOutcomeProbability_true_le_one
    {mu : ℝ} (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2)
    (special ordinaryDirection : Bool) :
    theorem7OrientedSmallMuOutcomeProbability mu special ordinaryDirection true ≤ 1 := by
  cases special <;> cases ordinaryDirection <;>
    simp [theorem7OrientedSmallMuOutcomeProbability] <;> linarith

/--
The Bernoulli response kernel associated with a specified exceptional-query
indicator and ordinary direction.  It is the finite one-step law used to
construct the adaptive trace experiment below.
-/
noncomputable def theorem7OrientedSmallMuResponseLaw
    (mu : ℝ) (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2)
    (special ordinaryDirection : Bool) : PMF Bool :=
  PMF.bernoulli
    ⟨theorem7OrientedSmallMuOutcomeProbability mu special ordinaryDirection true,
      theorem7OrientedSmallMuOutcomeProbability_nonneg hmu hmuHalf special ordinaryDirection true⟩
    (by
      simpa using
        theorem7OrientedSmallMuOutcomeProbability_true_le_one hmu hmuHalf special ordinaryDirection)

/-- The response kernel has exactly the declared oriented one-step masses. -/
lemma theorem7OrientedSmallMuResponseLaw_apply_toReal
    {mu : ℝ} (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2)
    (special ordinaryDirection outcome : Bool) :
    (theorem7OrientedSmallMuResponseLaw mu hmu hmuHalf special ordinaryDirection outcome).toReal =
      theorem7OrientedSmallMuOutcomeProbability mu special ordinaryDirection outcome := by
  unfold theorem7OrientedSmallMuResponseLaw
  rw [PMF.bernoulli_apply]
  cases outcome
  · change ((1 - ⟨theorem7OrientedSmallMuOutcomeProbability mu special ordinaryDirection true,
      theorem7OrientedSmallMuOutcomeProbability_nonneg hmu hmuHalf special ordinaryDirection true⟩ :
        NNReal) : ℝ) =
      theorem7OrientedSmallMuOutcomeProbability mu special ordinaryDirection false
    rw [NNReal.coe_sub]
    · change 1 - theorem7OrientedSmallMuOutcomeProbability mu special ordinaryDirection true =
        theorem7OrientedSmallMuOutcomeProbability mu special ordinaryDirection false
      cases special <;> cases ordinaryDirection <;>
        simp [theorem7OrientedSmallMuOutcomeProbability] <;> linarith
    · exact theorem7OrientedSmallMuOutcomeProbability_true_le_one hmu hmuHalf special ordinaryDirection
  · change ((⟨theorem7OrientedSmallMuOutcomeProbability mu special ordinaryDirection true,
      theorem7OrientedSmallMuOutcomeProbability_nonneg hmu hmuHalf special ordinaryDirection true⟩ :
        NNReal) : ℝ) =
      theorem7OrientedSmallMuOutcomeProbability mu special ordinaryDirection true
    rfl

/--
The finite trace PMF generated by history-dependent binary response kernels.
At round `r`, the kernel receives precisely the outcomes from earlier rounds;
the recursive `bind` therefore represents an adaptive experiment without any
independence assumption between its final trace coordinates.
-/
noncomputable def theorem7AdaptiveBinaryTraceLaw
    {comparisonBudget : ℕ}
    (response : (round : Fin comparisonBudget) → (Fin round.val → Bool) → PMF Bool) :
    (roundCount : ℕ) → (hroundCount : roundCount ≤ comparisonBudget) →
      PMF (Fin roundCount → Bool)
  | 0, _ => PMF.pure Fin.elim0
  | roundCount + 1, hroundCount =>
      PMF.bind
        (theorem7AdaptiveBinaryTraceLaw response roundCount
          (Nat.le_of_succ_le hroundCount))
        (fun history =>
          PMF.map (fun outcome => Fin.snoc history outcome)
            (response ⟨roundCount, Nat.lt_of_succ_le hroundCount⟩ history))

/-- Mapping one binary response onto the final entry of a trace has one preimage. -/
private lemma pmfMapSnoc_apply
    {roundCount : ℕ} (response : PMF Bool)
    (history target : Fin roundCount → Bool) (outcome : Bool) :
    PMF.map (fun responseOutcome => Fin.snoc history responseOutcome) response
      (@Fin.snoc roundCount (fun _ => Bool) target outcome) =
        if target = history then response outcome else 0 := by
  classical
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_bool]
  simp only [Fin.snoc_inj]
  by_cases htarget : target = history
  · subst target
    cases outcome <;> simp
  · simp [htarget]

/--
The product of the realized history-dependent response masses along a finite
trace, defined recursively by peeling off its final response.
-/
noncomputable def theorem7AdaptiveBinaryTraceMass
    {comparisonBudget : ℕ}
    (response : (round : Fin comparisonBudget) → (Fin round.val → Bool) → PMF Bool) :
    (roundCount : ℕ) → (hroundCount : roundCount ≤ comparisonBudget) →
      (outcomes : Fin roundCount → Bool) → ENNReal
  | 0, _, _ => 1
  | roundCount + 1, hroundCount, outcomes =>
      theorem7AdaptiveBinaryTraceMass response roundCount
        (Nat.le_of_succ_le hroundCount) (Fin.init outcomes) *
        response ⟨roundCount, Nat.lt_of_succ_le hroundCount⟩ (Fin.init outcomes)
          (outcomes (Fin.last roundCount))

/--
The atom mass of the adaptive trace PMF is the product of its conditional
one-step masses.  This is the finite chain rule for a history-dependent
binary response process.
-/
theorem theorem7AdaptiveBinaryTraceLaw_apply
    {comparisonBudget : ℕ}
    (response : (round : Fin comparisonBudget) → (Fin round.val → Bool) → PMF Bool) :
    ∀ (roundCount : ℕ) (hroundCount : roundCount ≤ comparisonBudget)
      (outcomes : Fin roundCount → Bool),
      theorem7AdaptiveBinaryTraceLaw response roundCount hroundCount outcomes =
        theorem7AdaptiveBinaryTraceMass response roundCount hroundCount outcomes := by
  intro roundCount
  induction roundCount with
  | zero =>
      intro hroundCount outcomes
      have houtcomes : outcomes = Fin.elim0 := Subsingleton.elim _ _
      subst outcomes
      simp [theorem7AdaptiveBinaryTraceLaw, theorem7AdaptiveBinaryTraceMass]
  | succ roundCount ih =>
      intro hroundCount outcomes
      cases outcomes using Fin.snocCases with
      | snoc history outcome =>
          rw [theorem7AdaptiveBinaryTraceLaw, PMF.bind_apply, tsum_fintype]
          simp_rw [pmfMapSnoc_apply]
          rw [Finset.sum_eq_single history]
          · rw [ih (Nat.le_of_succ_le hroundCount) history]
            simp [theorem7AdaptiveBinaryTraceMass]
          · intro other _ hother
            simp [hother.symm]
          · simp

/--
Pointwise domination of each conditional response kernel transfers to the
whole adaptive trace, with one factor per comparison round.  This is the PMF
chain-rule bridge needed to turn a one-step likelihood calculation into an
event-probability comparison.
-/
theorem theorem7AdaptiveBinaryTraceMass_toReal_le_scaled
    {comparisonBudget : ℕ}
    (small base : (round : Fin comparisonBudget) → (Fin round.val → Bool) → PMF Bool)
    (factor : ℝ) (hfactor : 0 ≤ factor)
    (hpoint : ∀ (round : Fin comparisonBudget) (history : Fin round.val → Bool)
      (outcome : Bool),
      (small round history outcome).toReal ≤ factor * (base round history outcome).toReal) :
    ∀ (roundCount : ℕ) (hroundCount : roundCount ≤ comparisonBudget)
      (outcomes : Fin roundCount → Bool),
      (theorem7AdaptiveBinaryTraceMass small roundCount hroundCount outcomes).toReal ≤
        factor ^ roundCount *
          (theorem7AdaptiveBinaryTraceMass base roundCount hroundCount outcomes).toReal := by
  intro roundCount
  induction roundCount with
  | zero =>
      intro hroundCount outcomes
      simp [theorem7AdaptiveBinaryTraceMass]
  | succ roundCount ih =>
      intro hroundCount outcomes
      cases outcomes using Fin.snocCases with
      | snoc history outcome =>
          simp only [theorem7AdaptiveBinaryTraceMass, ENNReal.toReal_mul,
            Fin.init_snoc, Fin.snoc_last]
          have hprefix := ih (Nat.le_of_succ_le hroundCount) history
          have hresponse := hpoint ⟨roundCount, Nat.lt_of_succ_le hroundCount⟩ history outcome
          have hsmallNonneg : 0 ≤
              (small ⟨roundCount, Nat.lt_of_succ_le hroundCount⟩ history outcome).toReal :=
            ENNReal.toReal_nonneg
          have hbasePrefixNonneg : 0 ≤
              (theorem7AdaptiveBinaryTraceMass base roundCount
                (Nat.le_of_succ_le hroundCount) history).toReal := ENNReal.toReal_nonneg
          have hfactorPowNonneg : 0 ≤ factor ^ roundCount := pow_nonneg hfactor _
          calc
            (theorem7AdaptiveBinaryTraceMass small roundCount
                (Nat.le_of_succ_le hroundCount) history).toReal *
                (small ⟨roundCount, Nat.lt_of_succ_le hroundCount⟩ history outcome).toReal ≤
              (factor ^ roundCount *
                (theorem7AdaptiveBinaryTraceMass base roundCount
                  (Nat.le_of_succ_le hroundCount) history).toReal) *
                (small ⟨roundCount, Nat.lt_of_succ_le hroundCount⟩ history outcome).toReal :=
              mul_le_mul_of_nonneg_right hprefix hsmallNonneg
            _ ≤ (factor ^ roundCount *
                (theorem7AdaptiveBinaryTraceMass base roundCount
                  (Nat.le_of_succ_le hroundCount) history).toReal) *
                (factor *
                  (base ⟨roundCount, Nat.lt_of_succ_le hroundCount⟩ history outcome).toReal) :=
              mul_le_mul_of_nonneg_left hresponse
                (mul_nonneg hfactorPowNonneg hbasePrefixNonneg)
            _ = factor ^ (roundCount + 1) *
                ((theorem7AdaptiveBinaryTraceMass base roundCount
                  (Nat.le_of_succ_le hroundCount) history).toReal *
                  (base ⟨roundCount, Nat.lt_of_succ_le hroundCount⟩ history outcome).toReal) := by
              rw [pow_succ]
              ring

/--
When every history-dependent response kernel is a fair bit, the adaptive trace
PMF is exactly the uniform law on complete Boolean traces.
-/
theorem theorem7AdaptiveBinaryTraceLaw_allFair_eq_uniform
    {comparisonBudget : ℕ} :
    theorem7AdaptiveBinaryTraceLaw
      (fun (round : Fin comparisonBudget) (_ : Fin round.val → Bool) => uniformPMF Bool)
      comparisonBudget (le_refl _) = uniformPMF (Fin comparisonBudget → Bool) := by
  have hmass : ∀ (roundCount : ℕ) (hroundCount : roundCount ≤ comparisonBudget)
      (outcomes : Fin roundCount → Bool),
      theorem7AdaptiveBinaryTraceMass
        (fun (round : Fin comparisonBudget) (_ : Fin round.val → Bool) => uniformPMF Bool)
        roundCount hroundCount outcomes =
        ∏ round : Fin roundCount, uniformPMF Bool (outcomes round) := by
    intro roundCount
    induction roundCount with
    | zero =>
        intro hroundCount outcomes
        simp [theorem7AdaptiveBinaryTraceMass]
    | succ roundCount ih =>
        intro hroundCount outcomes
        cases outcomes using Fin.snocCases with
        | snoc history outcome =>
            rw [theorem7AdaptiveBinaryTraceMass]
            simp only [Fin.init_snoc, Fin.snoc_last]
            rw [ih (Nat.le_of_succ_le hroundCount) history]
            simp [pow_succ]
  calc
    theorem7AdaptiveBinaryTraceLaw
        (fun (round : Fin comparisonBudget) (_ : Fin round.val → Bool) => uniformPMF Bool)
        comparisonBudget (le_refl _) =
      pmfProduct (Fin comparisonBudget) Bool (uniformPMF Bool) := by
        ext outcomes
        rw [theorem7AdaptiveBinaryTraceLaw_apply, hmass, pmfProduct_apply]
    _ = uniformPMF (Fin comparisonBudget → Bool) :=
      pmfProduct_uniformPMF_eq_uniformPMF_fun (Fin comparisonBudget) Bool

/--
The auxiliary-noise trace law for the small-`mu` experiment.  A noise bit is
still fair when the current query is exceptional (because the actual response
will ignore that auxiliary bit); otherwise it receives the ordinary
comparison's oriented small-`mu` Bernoulli law.
-/
noncomputable def theorem7AdaptiveOrientedNoiseLaw
    {comparisonBudget : ℕ} (mu : ℝ) (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2)
    (special ordinaryDirection : (round : Fin comparisonBudget) →
      (Fin round.val → Bool) → Bool) : PMF (Fin comparisonBudget → Bool) :=
  theorem7AdaptiveBinaryTraceLaw
    (fun round history =>
      if special round history then uniformPMF Bool
      else theorem7OrientedSmallMuResponseLaw mu hmu hmuHalf false
        (ordinaryDirection round history))
    comparisonBudget (le_refl _)

/--
The small-`mu` auxiliary-noise law has the source's pointwise likelihood
upper bound relative to independent fair noise, even when exceptional-query
locations and ordinary directions are selected adaptively from prior noise.
-/
theorem theorem7AdaptiveOrientedNoiseLaw_apply_toReal_le_uniform_scaled
    {comparisonBudget : ℕ} {mu : ℝ} (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2)
    (special ordinaryDirection : (round : Fin comparisonBudget) →
      (Fin round.val → Bool) → Bool)
    (noise : Fin comparisonBudget → Bool) :
    (theorem7AdaptiveOrientedNoiseLaw mu hmu hmuHalf special ordinaryDirection noise).toReal ≤
      (1 + 2 * mu) ^ comparisonBudget * (uniformPMF (Fin comparisonBudget → Bool) noise).toReal := by
  have hfactor : 0 ≤ 1 + 2 * mu := by linarith
  have hpoint : ∀ (round : Fin comparisonBudget) (history : Fin round.val → Bool)
      (outcome : Bool),
      ((if special round history then uniformPMF Bool
        else theorem7OrientedSmallMuResponseLaw mu hmu hmuHalf false
          (ordinaryDirection round history)) outcome).toReal ≤
        (1 + 2 * mu) * (uniformPMF Bool outcome).toReal := by
    intro round history outcome
    by_cases hspecial : special round history
    · rw [if_pos hspecial, uniformPMF_apply_toReal]
      norm_num
      linarith
    · rw [if_neg hspecial, theorem7OrientedSmallMuResponseLaw_apply_toReal]
      simpa [theorem7BaseOutcomeProbability, uniformPMF_apply_toReal] using
        theorem7OrientedSmallMuOutcomeProbability_le_scaled_base hmu false
          (ordinaryDirection round history) outcome
  rw [theorem7AdaptiveOrientedNoiseLaw, theorem7AdaptiveBinaryTraceLaw_apply]
  calc
    (theorem7AdaptiveBinaryTraceMass
        (fun round history =>
          if special round history then uniformPMF Bool
          else theorem7OrientedSmallMuResponseLaw mu hmu hmuHalf false
            (ordinaryDirection round history))
        comparisonBudget (le_refl _) noise).toReal ≤
      (1 + 2 * mu) ^ comparisonBudget *
        (theorem7AdaptiveBinaryTraceMass
          (fun (round : Fin comparisonBudget) (_ : Fin round.val → Bool) => uniformPMF Bool)
          comparisonBudget (le_refl _) noise).toReal :=
      theorem7AdaptiveBinaryTraceMass_toReal_le_scaled _ _ (1 + 2 * mu) hfactor hpoint
        comparisonBudget (le_refl _) noise
    _ = (1 + 2 * mu) ^ comparisonBudget *
        (uniformPMF (Fin comparisonBudget → Bool) noise).toReal := by
      rw [← theorem7AdaptiveBinaryTraceLaw_apply]
      rw [theorem7AdaptiveBinaryTraceLaw_allFair_eq_uniform]

/--
The concrete small-`mu` auxiliary-noise law for one finite adaptive ranking
procedure and one hidden-coordinate hard instance.  A round is exceptional
exactly when the procedure's query of its reconstructed actual history equals
the hidden coordinate; otherwise its canonical pair direction is read from
the source preference matrix.
-/
noncomputable def theorem7ProcedureSmallMuNoiseLaw
    {n comparisonBudget : ℕ} (mu : ℝ) (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2)
    (hcard : 2 ≤ n) (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool) :
    PMF (Fin comparisonBudget → Bool) :=
  theorem7AdaptiveOrientedNoiseLaw mu hmu hmuHalf
    (theorem7ProcedureNoiseHistorySpecial procedure coordinate orientation)
    (fun round noiseHistory =>
      theorem7HiddenCoordinateOrdinaryDirection n mu hcard coordinate orientation
        (procedure.query round
          (theorem7ActualOutcomeFromNoiseHistory procedure coordinate orientation round.val
            round.isLt.le noiseHistory)))

/--
The concrete procedure-level small-`mu` noise experiment satisfies the same
adaptive likelihood bound against the uniform auxiliary-noise law.
-/
theorem theorem7ProcedureSmallMuNoiseLaw_apply_toReal_le_uniform_scaled
    {n comparisonBudget : ℕ} {mu : ℝ} (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2)
    (hcard : 2 ≤ n) (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool)
    (noise : Fin comparisonBudget → Bool) :
    (theorem7ProcedureSmallMuNoiseLaw mu hmu hmuHalf hcard procedure coordinate orientation noise).toReal ≤
      (1 + 2 * mu) ^ comparisonBudget * (uniformPMF (Fin comparisonBudget → Bool) noise).toReal := by
  exact theorem7AdaptiveOrientedNoiseLaw_apply_toReal_le_uniform_scaled hmu hmuHalf
    (theorem7ProcedureNoiseHistorySpecial procedure coordinate orientation)
    (fun round noiseHistory =>
      theorem7HiddenCoordinateOrdinaryDirection n mu hcard coordinate orientation
        (procedure.query round
          (theorem7ActualOutcomeFromNoiseHistory procedure coordinate orientation round.val
            round.isLt.le noiseHistory))) noise

/--
The likelihood of a transcript when the preferred ordinary outcome can vary
from round to round.  The direction is fixed after conditioning on the
realized adaptive transcript, just as the exceptional-query indicator is.
-/
noncomputable def theorem7OrientedTranscriptLikelihood
    {roundCount : ℕ} (mu : ℝ)
    (special ordinaryDirection outcome : Fin roundCount → Bool) : ℝ :=
  ∏ round, theorem7OrientedSmallMuOutcomeProbability mu
    (special round) (ordinaryDirection round) (outcome round)

/--
The likelihood comparison remains valid for an adaptively chosen orientation
of every ordinary query.  This is the pointwise source bridge needed for the
concrete relabeled Theorem 7 family; only the induced adaptive trace PMFs
remain to be connected to this product expression.
-/
theorem theorem7OrientedTranscriptLikelihood_smallMu_le_base_scaled
    {roundCount : ℕ} {mu : ℝ} (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2)
    (special ordinaryDirection outcome : Fin roundCount → Bool) :
    theorem7OrientedTranscriptLikelihood mu special ordinaryDirection outcome ≤
      (1 + 2 * mu) ^ roundCount *
        theorem7TranscriptLikelihood theorem7BaseOutcomeProbability special outcome := by
  have hpoint : ∀ round : Fin roundCount,
      theorem7OrientedSmallMuOutcomeProbability mu (special round)
          (ordinaryDirection round) (outcome round) ≤
        (1 + 2 * mu) * theorem7BaseOutcomeProbability (special round) (outcome round) := by
    intro round
    exact theorem7OrientedSmallMuOutcomeProbability_le_scaled_base hmu _ _ _
  calc
    theorem7OrientedTranscriptLikelihood mu special ordinaryDirection outcome ≤
        ∏ round, (1 + 2 * mu) * theorem7BaseOutcomeProbability
          (special round) (outcome round) := by
      unfold theorem7OrientedTranscriptLikelihood
      apply Finset.prod_le_prod
      · intro round _
        exact theorem7OrientedSmallMuOutcomeProbability_nonneg hmu hmuHalf _ _ _
      · intro round _
        exact hpoint round
    _ = (1 + 2 * mu) ^ roundCount *
        theorem7TranscriptLikelihood theorem7BaseOutcomeProbability special outcome := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      simp [theorem7TranscriptLikelihood]

/--
A finite pointwise likelihood ratio bound transfers directly to every event
probability.  This is the PMF step used after a concrete adaptive transcript
law has been identified with the products above.
-/
theorem pmfProb_le_mul_of_pointwise_mass_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (small base : PMF Ω) (event : Ω → Prop) [DecidablePred event]
    (factor : ℝ)
    (hmass : ∀ outcome, (small outcome).toReal ≤ factor * (base outcome).toReal) :
    pmfProb small event ≤ factor * pmfProb base event := by
  unfold pmfProb pmfExp
  calc
    ∑ outcome : Ω, (small outcome).toReal * (if event outcome then (1 : ℝ) else 0) ≤
        ∑ outcome : Ω, (factor * (base outcome).toReal) *
          (if event outcome then (1 : ℝ) else 0) := by
      refine Finset.sum_le_sum ?_
      intro outcome _
      by_cases hevent : event outcome
      · simp [hevent]
        exact hmass outcome
      · simp [hevent]
    _ = factor * ∑ outcome : Ω, (base outcome).toReal *
          (if event outcome then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro outcome _
      ring

/--
The finite source likelihood comparison turns a `7/8` success probability in
the small-`mu` model into a `3/4` success probability in the base model once
the product factor is at most `7/6`.
-/
theorem theorem7_base_success_probability_of_smallMu_success
    {Trace : Type*} [Fintype Trace] [DecidableEq Trace]
    (small base : PMF Trace) (success : Trace → Prop) [DecidablePred success]
    (factor : ℝ)
    (htransfer : pmfProb small success ≤ factor * pmfProb base success)
    (hfactor : factor ≤ (7 : ℝ) / 6)
    (hsmall : (7 : ℝ) / 8 ≤ pmfProb small success) :
    (3 : ℝ) / 4 ≤ pmfProb base success := by
  have hbaseNonneg : 0 ≤ pmfProb base success := pmfProb_nonneg base success
  have hfactorPos : 0 < factor := by
    by_contra hnot
    have hfactorNonpos : factor ≤ 0 := le_of_not_gt hnot
    have hproductNonpos : factor * pmfProb base success ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hfactorNonpos hbaseNonneg
    nlinarith
  by_contra hnot
  have hbaseLt : pmfProb base success < (3 : ℝ) / 4 := lt_of_not_ge hnot
  have hfirst : factor * pmfProb base success < factor * ((3 : ℝ) / 4) :=
    mul_lt_mul_of_pos_left hbaseLt hfactorPos
  have hsecond : factor * ((3 : ℝ) / 4) ≤ ((7 : ℝ) / 6) * ((3 : ℝ) / 4) :=
    mul_le_mul_of_nonneg_right hfactor (by norm_num)
  nlinarith

/--
Sample an arbitrary transcript and then an independent uniformly hidden
comparison coordinate.  This is the ideal pre-hit experiment used by the
random-relabeling route for Theorem 7.
-/
noncomputable def randomHiddenComparisonLaw
    {Trace Comparison : Type*} [Fintype Trace] [DecidableEq Trace]
    [Fintype Comparison] [DecidableEq Comparison] [Nonempty Comparison]
    (traceLaw : PMF Trace) : PMF (Trace × Comparison) :=
  traceLaw.bind fun trace => (uniformPMF Comparison).map fun comparison =>
    (trace, comparison)

/--
In an independent random-relabeling experiment, a transcript that queries at
most `budget` comparison coordinates hits the uniformly hidden coordinate
with probability at most `budget / |Comparison|`.
-/
theorem randomHiddenComparisonLaw_hit_probability_le
    {Trace Comparison : Type*} [Fintype Trace] [DecidableEq Trace]
    [Fintype Comparison] [DecidableEq Comparison] [Nonempty Comparison]
    (traceLaw : PMF Trace) (queried : Trace → Finset Comparison) (budget : ℕ)
    (hbudget : ∀ trace, (queried trace).card ≤ budget) :
    pmfProb (randomHiddenComparisonLaw traceLaw)
      (fun traceComparison => traceComparison.2 ∈ queried traceComparison.1) ≤
      (budget : ℝ) / (Fintype.card Comparison : ℝ) := by
  classical
  unfold randomHiddenComparisonLaw
  rw [pmfProb_bind]
  have hpoint : ∀ trace : Trace,
      pmfProb ((uniformPMF Comparison).map fun comparison => (trace, comparison))
        (fun traceComparison => traceComparison.2 ∈ queried traceComparison.1) ≤
        (budget : ℝ) / (Fintype.card Comparison : ℝ) := by
    intro trace
    rw [pmfProb_map]
    change pmfProb (uniformPMF Comparison) (fun comparison => comparison ∈ queried trace) ≤ _
    rw [pmfProb_uniformPMF_finset]
    apply div_le_div_of_nonneg_right
    · exact_mod_cast hbudget trace
    · positivity
  calc
    pmfExp traceLaw (fun trace =>
        pmfProb ((uniformPMF Comparison).map fun comparison => (trace, comparison))
          (fun traceComparison => traceComparison.2 ∈ queried traceComparison.1)) ≤
        pmfExp traceLaw (fun _ => (budget : ℝ) / (Fintype.card Comparison : ℝ)) :=
      pmfExp_le_pmfExp_of_forall_le traceLaw _ _ hpoint
    _ = (budget : ℝ) / (Fintype.card Comparison : ℝ) := pmfExp_const traceLaw _

/--
The ideal experiment also gives the hidden comparison an independent uniformly
random orientation.  This is the symmetric no-information branch of the
ranking lower-bound game.
-/
noncomputable def randomHiddenComparisonBitLaw
    {Trace Comparison : Type*} [Fintype Trace] [DecidableEq Trace]
    [Fintype Comparison] [DecidableEq Comparison] [Nonempty Comparison]
    (traceLaw : PMF Trace) : PMF ((Trace × Comparison) × Bool) :=
  traceLaw.bind fun trace =>
    (uniformPMF Comparison).bind fun comparison =>
      (uniformPMF Bool).map fun bit => ((trace, comparison), bit)

/--
Sample a uniformly hidden coordinate and orientation, then draw an auxiliary
trace from a law that may depend on both hidden values.  This is the finite
mixture form of the source's small-`mu` experiment.
-/
noncomputable def hiddenComparisonConditionalTraceLaw
    {Trace Comparison : Type*} [Fintype Trace] [DecidableEq Trace]
    [Fintype Comparison] [DecidableEq Comparison] [Nonempty Comparison]
    (conditionalTraceLaw : Comparison → Bool → PMF Trace) : PMF ((Trace × Comparison) × Bool) :=
  (uniformPMF Comparison).bind fun comparison =>
    (uniformPMF Bool).bind fun orientation =>
      (conditionalTraceLaw comparison orientation).map fun trace => ((trace, comparison), orientation)

/-- A trace tagged with fixed hidden values has one preimage under the tagging map. -/
private lemma pmfMapTagHiddenComparison_apply
    {Trace Comparison : Type*} [Fintype Trace] [DecidableEq Trace]
    [DecidableEq Comparison]
    (traceLaw : PMF Trace) (comparison : Comparison) (orientation : Bool)
    (targetTrace : Trace) (targetComparison : Comparison) (targetOrientation : Bool) :
    (traceLaw.map fun currentTrace => ((currentTrace, comparison), orientation))
      ((targetTrace, targetComparison), targetOrientation) =
      if targetComparison = comparison ∧ targetOrientation = orientation then traceLaw targetTrace else 0 := by
  classical
  rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single targetTrace]
  · simp
  · intro other _ hother
    simp [hother.symm]
  · simp

/-- Atom formula for the hidden-coordinate conditional trace mixture. -/
theorem hiddenComparisonConditionalTraceLaw_apply
    {Trace Comparison : Type*} [Fintype Trace] [DecidableEq Trace]
    [Fintype Comparison] [DecidableEq Comparison] [Nonempty Comparison]
    (conditionalTraceLaw : Comparison → Bool → PMF Trace)
    (trace : Trace) (comparison : Comparison) (orientation : Bool) :
    hiddenComparisonConditionalTraceLaw conditionalTraceLaw ((trace, comparison), orientation) =
      uniformPMF Comparison comparison * uniformPMF Bool orientation *
        conditionalTraceLaw comparison orientation trace := by
  classical
  unfold hiddenComparisonConditionalTraceLaw
  rw [PMF.bind_apply, tsum_fintype, Finset.sum_eq_single comparison]
  · rw [PMF.bind_apply, tsum_fintype, Finset.sum_eq_single orientation]
    · rw [pmfMapTagHiddenComparison_apply]
      simp [mul_assoc]
    · intro other _ hother
      rw [pmfMapTagHiddenComparison_apply]
      simp [hother.symm]
    · simp
  · intro other _ hother
    rw [PMF.bind_apply, tsum_fintype]
    simp_rw [pmfMapTagHiddenComparison_apply]
    simp [hother.symm]
  · simp

/-- Atom formula for the independent hidden-coordinate-and-bit experiment. -/
theorem randomHiddenComparisonBitLaw_apply
    {Trace Comparison : Type*} [Fintype Trace] [DecidableEq Trace]
    [Fintype Comparison] [DecidableEq Comparison] [Nonempty Comparison]
    (traceLaw : PMF Trace) (trace : Trace) (comparison : Comparison) (orientation : Bool) :
    randomHiddenComparisonBitLaw traceLaw ((trace, comparison), orientation) =
      traceLaw trace * uniformPMF Comparison comparison * uniformPMF Bool orientation := by
  classical
  unfold randomHiddenComparisonBitLaw
  rw [PMF.bind_apply, tsum_fintype, Finset.sum_eq_single trace]
  · rw [PMF.bind_apply, tsum_fintype, Finset.sum_eq_single comparison]
    · rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single orientation]
      · simp [mul_assoc]
      · intro other _ hother
        simp [hother.symm]
      · simp
    · intro other _ hother
      rw [PMF.map_apply, tsum_fintype]
      simp [hother.symm]
    · simp
  · intro other _ hother
    rw [PMF.bind_apply, tsum_fintype]
    simp_rw [PMF.map_apply, tsum_fintype]
    simp [hother.symm]
  · simp

/--
Conditional pointwise trace domination remains valid after independently
mixing over a uniformly hidden comparison coordinate and orientation bit.
-/
theorem hiddenComparisonConditionalTraceLaw_apply_toReal_le_randomHidden
    {Trace Comparison : Type*} [Fintype Trace] [DecidableEq Trace]
    [Fintype Comparison] [DecidableEq Comparison] [Nonempty Comparison]
    (conditionalTraceLaw : Comparison → Bool → PMF Trace) (baseTraceLaw : PMF Trace)
    (factor : ℝ)
    (hpoint : ∀ (comparison : Comparison) (orientation : Bool) (trace : Trace),
      (conditionalTraceLaw comparison orientation trace).toReal ≤
        factor * (baseTraceLaw trace).toReal)
    (trace : Trace) (comparison : Comparison) (orientation : Bool) :
    (hiddenComparisonConditionalTraceLaw conditionalTraceLaw
      ((trace, comparison), orientation)).toReal ≤
      factor * (randomHiddenComparisonBitLaw baseTraceLaw
        ((trace, comparison), orientation)).toReal := by
  rw [hiddenComparisonConditionalTraceLaw_apply, randomHiddenComparisonBitLaw_apply]
  simp only [ENNReal.toReal_mul]
  have hweightNonneg : 0 ≤
      (uniformPMF Comparison comparison).toReal * (uniformPMF Bool orientation).toReal :=
    mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  calc
    ((uniformPMF Comparison comparison).toReal * (uniformPMF Bool orientation).toReal) *
        (conditionalTraceLaw comparison orientation trace).toReal ≤
      ((uniformPMF Comparison comparison).toReal * (uniformPMF Bool orientation).toReal) *
        (factor * (baseTraceLaw trace).toReal) :=
      mul_le_mul_of_nonneg_left (hpoint comparison orientation trace) hweightNonneg
    _ = factor *
        ((baseTraceLaw trace).toReal * (uniformPMF Comparison comparison).toReal *
          (uniformPMF Bool orientation).toReal) := by ring

/--
The complete small-`mu` auxiliary-noise experiment for a procedure, with the
hidden unordered pair and orientation drawn uniformly before its conditional
adaptive trace is generated.
-/
noncomputable def theorem7SmallMuHiddenNoiseLaw
    {n comparisonBudget : ℕ} (mu : ℝ) (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2)
    (hcard : 2 ≤ n) (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget) :
    PMF (((Fin comparisonBudget → Bool) × unorderedComparisonCoordinate (Fin n)) × Bool) := by
  classical
  letI : Nonempty (unorderedComparisonCoordinate (Fin n)) :=
    unorderedComparisonCoordinate_nonempty_of_card_ge_two (by simpa using hcard)
  exact hiddenComparisonConditionalTraceLaw (fun coordinate orientation =>
    theorem7ProcedureSmallMuNoiseLaw mu hmu hmuHalf hcard procedure coordinate orientation)

/-- The existing uniform-noise hidden-pair experiment, packaged without a typeclass binder. -/
noncomputable def theorem7BaseHiddenNoiseLaw
    {n comparisonBudget : ℕ} (hcard : 2 ≤ n) :
    PMF (((Fin comparisonBudget → Bool) × unorderedComparisonCoordinate (Fin n)) × Bool) := by
  classical
  letI : Nonempty (unorderedComparisonCoordinate (Fin n)) :=
    unorderedComparisonCoordinate_nonempty_of_card_ge_two (by simpa using hcard)
  exact randomHiddenComparisonBitLaw
    (Comparison := unorderedComparisonCoordinate (Fin n))
    (uniformPMF (Fin comparisonBudget → Bool))

/--
Every atom of the complete small-`mu` experiment is at most the adaptive
likelihood factor times the matching atom of the uniform-noise hidden-pair
experiment used by the base lower bound.
-/
theorem theorem7SmallMuHiddenNoiseLaw_apply_toReal_le_base_scaled
    {n comparisonBudget : ℕ} {mu : ℝ} (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2)
    (hcard : 2 ≤ n) (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (noise : Fin comparisonBudget → Bool)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool) :
    (theorem7SmallMuHiddenNoiseLaw mu hmu hmuHalf hcard procedure
      ((noise, coordinate), orientation)).toReal ≤
      (1 + 2 * mu) ^ comparisonBudget *
        (theorem7BaseHiddenNoiseLaw (comparisonBudget := comparisonBudget) hcard
          ((noise, coordinate), orientation)).toReal := by
  classical
  letI : Nonempty (unorderedComparisonCoordinate (Fin n)) :=
    unorderedComparisonCoordinate_nonempty_of_card_ge_two (by simpa using hcard)
  simpa [theorem7SmallMuHiddenNoiseLaw, theorem7BaseHiddenNoiseLaw] using
    (hiddenComparisonConditionalTraceLaw_apply_toReal_le_randomHidden
      (fun hiddenCoordinate hiddenOrientation =>
        theorem7ProcedureSmallMuNoiseLaw mu hmu hmuHalf hcard procedure
          hiddenCoordinate hiddenOrientation)
      (uniformPMF (Fin comparisonBudget → Bool))
      ((1 + 2 * mu) ^ comparisonBudget)
      (fun hiddenCoordinate hiddenOrientation hiddenNoise =>
        theorem7ProcedureSmallMuNoiseLaw_apply_toReal_le_uniform_scaled
          hmu hmuHalf hcard procedure hiddenCoordinate hiddenOrientation hiddenNoise)
      noise coordinate orientation)

/-- A constant finite predicate has probability zero or one according to its truth value. -/
private theorem pmfProb_constPredicate
    {α : Type*} [Fintype α] [DecidableEq α]
    (law : PMF α) (p : Prop) [Decidable p] :
    pmfProb law (fun _ => p) = if p then 1 else 0 := by
  unfold pmfProb
  by_cases hp : p <;> simp [hp, pmfExp_const]

/-- An independent uniform bit agrees with any transcript-based prediction with probability one half. -/
private theorem uniformBit_prediction_probability
    {Trace : Type*} [Fintype Trace] [DecidableEq Trace]
    (prediction : Trace → Bool) (trace : Trace) :
    pmfProb (uniformPMF Bool) (fun bit => prediction trace = bit) = (1 : ℝ) / 2 := by
  calc
    pmfProb (uniformPMF Bool) (fun bit => prediction trace = bit) =
        pmfProb (uniformPMF Bool) (fun bit => bit = prediction trace) :=
      pmfProb_congr (uniformPMF Bool) (by intro bit; simp [eq_comm])
    _ = (Fintype.card Bool : ℝ)⁻¹ := pmfProb_uniformPMF_singleton (prediction trace)
    _ = (1 : ℝ) / 2 := by norm_num

/--
Adding the independent orientation bit does not help find the hidden
comparison: a transcript with at most `budget` queries still hits it with
probability at most `budget / |Comparison|`.
-/
theorem randomHiddenComparisonBitLaw_hit_probability_le
    {Trace Comparison : Type*} [Fintype Trace] [DecidableEq Trace]
    [Fintype Comparison] [DecidableEq Comparison] [Nonempty Comparison]
    (traceLaw : PMF Trace) (queried : Trace → Finset Comparison) (budget : ℕ)
    (hbudget : ∀ trace, (queried trace).card ≤ budget) :
    pmfProb (randomHiddenComparisonBitLaw (Comparison := Comparison) traceLaw)
      (fun traceComparisonBit => traceComparisonBit.1.2 ∈ queried traceComparisonBit.1.1) ≤
      (budget : ℝ) / (Fintype.card Comparison : ℝ) := by
  classical
  unfold randomHiddenComparisonBitLaw
  rw [pmfProb_bind]
  apply pmfExp_le_of_forall_le
  intro trace
  rw [pmfProb_bind]
  calc
    pmfExp (uniformPMF Comparison) (fun comparison =>
      pmfProb ((uniformPMF Bool).map fun bit => ((trace, comparison), bit))
        (fun traceComparisonBit => traceComparisonBit.1.2 ∈ queried traceComparisonBit.1.1)) =
      pmfExp (uniformPMF Comparison) (fun comparison =>
        pmfProb (uniformPMF Bool) (fun _ => comparison ∈ queried trace)) := by
          apply pmfExp_congr
          intro comparison
          rw [pmfProb_map]
    _ = pmfExp (uniformPMF Comparison) (fun comparison =>
        if comparison ∈ queried trace then (1 : ℝ) else 0) := by
          apply pmfExp_congr
          intro comparison
          exact pmfProb_constPredicate (uniformPMF Bool) (comparison ∈ queried trace)
    _ = pmfProb (uniformPMF Comparison) (fun comparison => comparison ∈ queried trace) := by
          rfl
    _ = ((queried trace).card : ℝ) / (Fintype.card Comparison : ℝ) :=
      pmfProb_uniformPMF_finset (queried trace)
    _ ≤ (budget : ℝ) / (Fintype.card Comparison : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hbudget trace
      · positivity

/--
Before the hidden orientation is observed, every transcript-based prediction
is correct with probability exactly one half in the ideal experiment.
-/
theorem randomHiddenComparisonBitLaw_prediction_probability
    {Trace Comparison : Type*} [Fintype Trace] [DecidableEq Trace]
    [Fintype Comparison] [DecidableEq Comparison] [Nonempty Comparison]
    (traceLaw : PMF Trace) (prediction : Trace → Bool) :
    pmfProb (randomHiddenComparisonBitLaw (Comparison := Comparison) traceLaw)
      (fun traceComparisonBit => prediction traceComparisonBit.1.1 = traceComparisonBit.2) =
      (1 : ℝ) / 2 := by
  classical
  unfold randomHiddenComparisonBitLaw
  rw [pmfProb_bind]
  calc
    pmfExp traceLaw (fun trace =>
      pmfProb ((uniformPMF Comparison).bind fun comparison =>
        (uniformPMF Bool).map fun bit => ((trace, comparison), bit))
        (fun traceComparisonBit => prediction traceComparisonBit.1.1 = traceComparisonBit.2)) =
      pmfExp traceLaw (fun _ => (1 : ℝ) / 2) := by
        apply pmfExp_congr
        intro trace
        rw [pmfProb_bind]
        calc
          pmfExp (uniformPMF Comparison) (fun comparison =>
            pmfProb ((uniformPMF Bool).map fun bit => ((trace, comparison), bit))
              (fun traceComparisonBit => prediction traceComparisonBit.1.1 = traceComparisonBit.2)) =
            pmfExp (uniformPMF Comparison) (fun _ => (1 : ℝ) / 2) := by
              apply pmfExp_congr
              intro comparison
              rw [pmfProb_map]
              change pmfProb (uniformPMF Bool) (fun bit => prediction trace = bit) = _
              exact uniformBit_prediction_probability prediction trace
          _ = (1 : ℝ) / 2 := pmfExp_const (uniformPMF Comparison) _
    _ = (1 : ℝ) / 2 := pmfExp_const traceLaw _

/--
An idealized ranking procedure can be correct only by either finding the
hidden coordinate or guessing its independent orientation.  Its success
probability is therefore at most the hit probability plus one half.
-/
theorem randomHiddenComparisonBitLaw_hit_or_predict_probability_le
    {Trace Comparison : Type*} [Fintype Trace] [DecidableEq Trace]
    [Fintype Comparison] [DecidableEq Comparison] [Nonempty Comparison]
    (traceLaw : PMF Trace) (queried : Trace → Finset Comparison)
    (prediction : Trace → Bool) (budget : ℕ)
    (hbudget : ∀ trace, (queried trace).card ≤ budget) :
    pmfProb (randomHiddenComparisonBitLaw (Comparison := Comparison) traceLaw)
      (fun traceComparisonBit =>
        traceComparisonBit.1.2 ∈ queried traceComparisonBit.1.1 ∨
          prediction traceComparisonBit.1.1 = traceComparisonBit.2) ≤
      (budget : ℝ) / (Fintype.card Comparison : ℝ) + 1 / 2 := by
  classical
  let law := randomHiddenComparisonBitLaw (Comparison := Comparison) traceLaw
  let hit : (Trace × Comparison) × Bool → Prop := fun traceComparisonBit =>
    traceComparisonBit.1.2 ∈ queried traceComparisonBit.1.1
  let correct : (Trace × Comparison) × Bool → Prop := fun traceComparisonBit =>
    prediction traceComparisonBit.1.1 = traceComparisonBit.2
  have hhit : pmfProb law hit ≤ (budget : ℝ) / (Fintype.card Comparison : ℝ) := by
    exact randomHiddenComparisonBitLaw_hit_probability_le traceLaw queried budget hbudget
  have hcorrect : pmfProb law correct = (1 : ℝ) / 2 := by
    exact randomHiddenComparisonBitLaw_prediction_probability traceLaw prediction
  calc
    pmfProb law (fun traceComparisonBit => hit traceComparisonBit ∨ correct traceComparisonBit) =
        pmfProb law hit + pmfProb law correct -
          pmfProb law (fun traceComparisonBit => hit traceComparisonBit ∧ correct traceComparisonBit) :=
      pmfProb_or_eq_add_sub_inter law hit correct
    _ ≤ pmfProb law hit + pmfProb law correct := by
      exact sub_le_self _
        (pmfProb_nonneg law (fun traceComparisonBit => hit traceComparisonBit ∧ correct traceComparisonBit))
    _ ≤ (budget : ℝ) / (Fintype.card Comparison : ℝ) + 1 / 2 := by
      linarith

/--
The source's `7/8` target has a finite ideal-game consequence: if every
successful ranking must either query the hidden comparison or correctly guess
its independent orientation, then the query budget is at least three eighths
of the hidden-comparison population.
-/
theorem randomHiddenComparisonBitLaw_query_lower_bound_of_success
    {Trace Comparison : Type*} [Fintype Trace] [DecidableEq Trace]
    [Fintype Comparison] [DecidableEq Comparison] [Nonempty Comparison]
    (traceLaw : PMF Trace) (queried : Trace → Finset Comparison)
    (prediction : Trace → Bool) (success : (Trace × Comparison) × Bool → Prop)
    [DecidablePred success] (budget : ℕ)
    (hbudget : ∀ trace, (queried trace).card ≤ budget)
    (hcover : ∀ traceComparisonBit, success traceComparisonBit →
      traceComparisonBit.1.2 ∈ queried traceComparisonBit.1.1 ∨
        prediction traceComparisonBit.1.1 = traceComparisonBit.2)
    (hsuccess : (7 : ℝ) / 8 ≤
      pmfProb (randomHiddenComparisonBitLaw (Comparison := Comparison) traceLaw) success) :
    (3 : ℝ) / 8 * (Fintype.card Comparison : ℝ) ≤ budget := by
  classical
  let law := randomHiddenComparisonBitLaw (Comparison := Comparison) traceLaw
  have hupper := randomHiddenComparisonBitLaw_hit_or_predict_probability_le
    traceLaw queried prediction budget hbudget
  have hsuccessLe : pmfProb law success ≤
      pmfProb law (fun traceComparisonBit =>
        traceComparisonBit.1.2 ∈ queried traceComparisonBit.1.1 ∨
          prediction traceComparisonBit.1.1 = traceComparisonBit.2) := by
    apply pmfProb_le_of_imp
    exact hcover
  have hratio : (3 : ℝ) / 8 ≤ (budget : ℝ) / (Fintype.card Comparison : ℝ) := by
    dsimp only [law] at hsuccess hsuccessLe hupper
    linarith
  have hcard : 0 < (Fintype.card Comparison : ℝ) := by positivity
  calc
    (3 : ℝ) / 8 * (Fintype.card Comparison : ℝ) ≤
        ((budget : ℝ) / (Fintype.card Comparison : ℝ)) * (Fintype.card Comparison : ℝ) :=
      mul_le_mul_of_nonneg_right hratio hcard.le
    _ = budget := by field_simp [ne_of_gt hcard]

/--
The independent uniform orientation bit is still correct only half the time
when a prediction may depend on both the transcript and the hidden comparison
coordinate.  This is the form needed to read an orientation prediction from a
candidate ranking of a particular pair of arms.
-/
private theorem uniformBit_coordinate_prediction_probability
    {Trace Comparison : Type*} [Fintype Trace] [DecidableEq Trace]
    [Fintype Comparison] [DecidableEq Comparison]
    (prediction : Trace → Comparison → Bool) (trace : Trace) (comparison : Comparison) :
    pmfProb (uniformPMF Bool) (fun bit => prediction trace comparison = bit) = (1 : ℝ) / 2 := by
  calc
    pmfProb (uniformPMF Bool) (fun bit => prediction trace comparison = bit) =
        pmfProb (uniformPMF Bool) (fun bit => bit = prediction trace comparison) :=
      pmfProb_congr (uniformPMF Bool) (by intro bit; simp [eq_comm])
    _ = (Fintype.card Bool : ℝ)⁻¹ := pmfProb_uniformPMF_singleton (prediction trace comparison)
    _ = (1 : ℝ) / 2 := by norm_num

/--
For a uniformly hidden coordinate and independent bit, a coordinate-specific
orientation prediction based on the pre-hit transcript is correct with
probability exactly one half.
-/
theorem randomHiddenComparisonBitLaw_coordinate_prediction_probability
    {Trace Comparison : Type*} [Fintype Trace] [DecidableEq Trace]
    [Fintype Comparison] [DecidableEq Comparison] [Nonempty Comparison]
    (traceLaw : PMF Trace) (prediction : Trace → Comparison → Bool) :
    pmfProb (randomHiddenComparisonBitLaw (Comparison := Comparison) traceLaw)
      (fun traceComparisonBit => prediction traceComparisonBit.1.1 traceComparisonBit.1.2 =
        traceComparisonBit.2) = (1 : ℝ) / 2 := by
  classical
  unfold randomHiddenComparisonBitLaw
  rw [pmfProb_bind]
  calc
    pmfExp traceLaw (fun trace =>
      pmfProb ((uniformPMF Comparison).bind fun comparison =>
        (uniformPMF Bool).map fun bit => ((trace, comparison), bit))
        (fun traceComparisonBit => prediction traceComparisonBit.1.1 traceComparisonBit.1.2 =
          traceComparisonBit.2)) =
        pmfExp traceLaw (fun _ => (1 : ℝ) / 2) := by
      apply pmfExp_congr
      intro trace
      rw [pmfProb_bind]
      calc
        pmfExp (uniformPMF Comparison) (fun comparison =>
          pmfProb ((uniformPMF Bool).map fun bit => ((trace, comparison), bit))
            (fun traceComparisonBit => prediction traceComparisonBit.1.1 traceComparisonBit.1.2 =
              traceComparisonBit.2)) =
            pmfExp (uniformPMF Comparison) (fun _ => (1 : ℝ) / 2) := by
              apply pmfExp_congr
              intro comparison
              rw [pmfProb_map]
              change pmfProb (uniformPMF Bool)
                (fun bit => prediction trace comparison = bit) = _
              exact uniformBit_coordinate_prediction_probability prediction trace comparison
        _ = (1 : ℝ) / 2 := pmfExp_const (uniformPMF Comparison) _
    _ = (1 : ℝ) / 2 := pmfExp_const traceLaw _

/--
With a coordinate-specific orientation prediction, ideal success remains
bounded by the hidden-coordinate hit probability plus one half.
-/
theorem randomHiddenComparisonBitLaw_hit_or_coordinate_predict_probability_le
    {Trace Comparison : Type*} [Fintype Trace] [DecidableEq Trace]
    [Fintype Comparison] [DecidableEq Comparison] [Nonempty Comparison]
    (traceLaw : PMF Trace) (queried : Trace → Finset Comparison)
    (prediction : Trace → Comparison → Bool) (budget : ℕ)
    (hbudget : ∀ trace, (queried trace).card ≤ budget) :
    pmfProb (randomHiddenComparisonBitLaw (Comparison := Comparison) traceLaw)
      (fun traceComparisonBit =>
        traceComparisonBit.1.2 ∈ queried traceComparisonBit.1.1 ∨
          prediction traceComparisonBit.1.1 traceComparisonBit.1.2 = traceComparisonBit.2) ≤
      (budget : ℝ) / (Fintype.card Comparison : ℝ) + 1 / 2 := by
  classical
  let law := randomHiddenComparisonBitLaw (Comparison := Comparison) traceLaw
  let hit : (Trace × Comparison) × Bool → Prop := fun traceComparisonBit =>
    traceComparisonBit.1.2 ∈ queried traceComparisonBit.1.1
  let correct : (Trace × Comparison) × Bool → Prop := fun traceComparisonBit =>
    prediction traceComparisonBit.1.1 traceComparisonBit.1.2 = traceComparisonBit.2
  have hhit : pmfProb law hit ≤ (budget : ℝ) / (Fintype.card Comparison : ℝ) := by
    exact randomHiddenComparisonBitLaw_hit_probability_le traceLaw queried budget hbudget
  have hcorrect : pmfProb law correct = (1 : ℝ) / 2 := by
    exact randomHiddenComparisonBitLaw_coordinate_prediction_probability traceLaw prediction
  calc
    pmfProb law (fun traceComparisonBit => hit traceComparisonBit ∨ correct traceComparisonBit) =
        pmfProb law hit + pmfProb law correct -
          pmfProb law (fun traceComparisonBit => hit traceComparisonBit ∧ correct traceComparisonBit) :=
      pmfProb_or_eq_add_sub_inter law hit correct
    _ ≤ pmfProb law hit + pmfProb law correct := by
      exact sub_le_self _
        (pmfProb_nonneg law (fun traceComparisonBit => hit traceComparisonBit ∧ correct traceComparisonBit))
    _ ≤ (budget : ℝ) / (Fintype.card Comparison : ℝ) + 1 / 2 := by linarith

/--
The ideal lower bound with a coordinate-specific orientation prediction.  It
directly matches a ranking algorithm, whose output can order different hidden
pairs in different directions while still having no information about the
unqueried pair's independent orientation.
-/
theorem randomHiddenComparisonBitLaw_coordinate_query_lower_bound_of_success
    {Trace Comparison : Type*} [Fintype Trace] [DecidableEq Trace]
    [Fintype Comparison] [DecidableEq Comparison] [Nonempty Comparison]
    (traceLaw : PMF Trace) (queried : Trace → Finset Comparison)
    (prediction : Trace → Comparison → Bool) (success : (Trace × Comparison) × Bool → Prop)
    [DecidablePred success] (budget : ℕ)
    (hbudget : ∀ trace, (queried trace).card ≤ budget)
    (hcover : ∀ traceComparisonBit, success traceComparisonBit →
      traceComparisonBit.1.2 ∈ queried traceComparisonBit.1.1 ∨
        prediction traceComparisonBit.1.1 traceComparisonBit.1.2 = traceComparisonBit.2)
    (hsuccess : (7 : ℝ) / 8 ≤
      pmfProb (randomHiddenComparisonBitLaw (Comparison := Comparison) traceLaw) success) :
    (3 : ℝ) / 8 * (Fintype.card Comparison : ℝ) ≤ budget := by
  classical
  let law := randomHiddenComparisonBitLaw (Comparison := Comparison) traceLaw
  have hupper := randomHiddenComparisonBitLaw_hit_or_coordinate_predict_probability_le
    traceLaw queried prediction budget hbudget
  have hsuccessLe : pmfProb law success ≤
      pmfProb law (fun traceComparisonBit =>
        traceComparisonBit.1.2 ∈ queried traceComparisonBit.1.1 ∨
          prediction traceComparisonBit.1.1 traceComparisonBit.1.2 = traceComparisonBit.2) := by
    apply pmfProb_le_of_imp
    exact hcover
  have hratio : (3 : ℝ) / 8 ≤ (budget : ℝ) / (Fintype.card Comparison : ℝ) := by
    dsimp only [law] at hsuccess hsuccessLe hupper
    linarith
  have hcard : 0 < (Fintype.card Comparison : ℝ) := by positivity
  calc
    (3 : ℝ) / 8 * (Fintype.card Comparison : ℝ) ≤
        ((budget : ℝ) / (Fintype.card Comparison : ℝ)) * (Fintype.card Comparison : ℝ) :=
      mul_le_mul_of_nonneg_right hratio hcard.le
    _ = budget := by field_simp [ne_of_gt hcard]

/--
The ideal-game lower bound specialized to the unordered pairwise comparison
coordinates of a finite arm set.
-/
theorem unorderedComparisonCoordinate_query_lower_bound_of_success
    {Arm Trace : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Trace] [DecidableEq Trace]
    [Nonempty (unorderedComparisonCoordinate Arm)]
    (traceLaw : PMF Trace) (queried : Trace → Finset (unorderedComparisonCoordinate Arm))
    (prediction : Trace → Bool)
    (success : ((Trace × unorderedComparisonCoordinate Arm) × Bool) → Prop)
    [DecidablePred success] (budget : ℕ)
    (hbudget : ∀ trace, (queried trace).card ≤ budget)
    (hcover : ∀ traceComparisonBit, success traceComparisonBit →
      traceComparisonBit.1.2 ∈ queried traceComparisonBit.1.1 ∨
        prediction traceComparisonBit.1.1 = traceComparisonBit.2)
    (hsuccess : (7 : ℝ) / 8 ≤
      pmfProb (randomHiddenComparisonBitLaw
        (Comparison := unorderedComparisonCoordinate Arm) traceLaw) success) :
    (3 : ℝ) / 8 * ((Fintype.card Arm).choose 2 : ℝ) ≤ budget := by
  have hcore := randomHiddenComparisonBitLaw_query_lower_bound_of_success
    traceLaw queried prediction success budget hbudget hcover hsuccess
  rw [unorderedComparisonCoordinate_card] at hcore
  exact hcore

/--
The unordered-pair specialization of the ideal lower bound when the candidate
ranking's predicted orientation is allowed to depend on the candidate pair.
-/
theorem unorderedComparisonCoordinate_coordinate_query_lower_bound_of_success
    {Arm Trace : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Trace] [DecidableEq Trace]
    [Nonempty (unorderedComparisonCoordinate Arm)]
    (traceLaw : PMF Trace) (queried : Trace → Finset (unorderedComparisonCoordinate Arm))
    (prediction : Trace → unorderedComparisonCoordinate Arm → Bool)
    (success : ((Trace × unorderedComparisonCoordinate Arm) × Bool) → Prop)
    [DecidablePred success] (budget : ℕ)
    (hbudget : ∀ trace, (queried trace).card ≤ budget)
    (hcover : ∀ traceComparisonBit, success traceComparisonBit →
      traceComparisonBit.1.2 ∈ queried traceComparisonBit.1.1 ∨
        prediction traceComparisonBit.1.1 traceComparisonBit.1.2 = traceComparisonBit.2)
    (hsuccess : (7 : ℝ) / 8 ≤
      pmfProb (randomHiddenComparisonBitLaw
        (Comparison := unorderedComparisonCoordinate Arm) traceLaw) success) :
    (3 : ℝ) / 8 * ((Fintype.card Arm).choose 2 : ℝ) ≤ budget := by
  have hcore := randomHiddenComparisonBitLaw_coordinate_query_lower_bound_of_success
    traceLaw queried prediction success budget hbudget hcover hsuccess
  rw [unorderedComparisonCoordinate_card] at hcore
  exact hcore

/--
For at least two arms, the ideal-game coordinate lower bound is explicitly
quadratic: it is at least `3 n² / 32` pairwise comparisons.
-/
theorem unorderedComparisonCoordinate_quadratic_query_lower_bound_of_success
    {Arm Trace : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Trace] [DecidableEq Trace]
    [Nonempty (unorderedComparisonCoordinate Arm)]
    (hcard : 2 ≤ Fintype.card Arm)
    (traceLaw : PMF Trace) (queried : Trace → Finset (unorderedComparisonCoordinate Arm))
    (prediction : Trace → Bool)
    (success : ((Trace × unorderedComparisonCoordinate Arm) × Bool) → Prop)
    [DecidablePred success] (budget : ℕ)
    (hbudget : ∀ trace, (queried trace).card ≤ budget)
    (hcover : ∀ traceComparisonBit, success traceComparisonBit →
      traceComparisonBit.1.2 ∈ queried traceComparisonBit.1.1 ∨
        prediction traceComparisonBit.1.1 = traceComparisonBit.2)
    (hsuccess : (7 : ℝ) / 8 ≤
      pmfProb (randomHiddenComparisonBitLaw
        (Comparison := unorderedComparisonCoordinate Arm) traceLaw) success) :
    (3 : ℝ) / 32 * (Fintype.card Arm : ℝ) ^ 2 ≤ budget := by
  have hchoose :
      (3 : ℝ) / 32 * (Fintype.card Arm : ℝ) ^ 2 ≤
        (3 : ℝ) / 8 * ((Fintype.card Arm).choose 2 : ℝ) := by
    rw [Nat.cast_choose_two]
    have hcardReal : (2 : ℝ) ≤ Fintype.card Arm := by exact_mod_cast hcard
    nlinarith
  exact hchoose.trans
    (unorderedComparisonCoordinate_query_lower_bound_of_success traceLaw queried prediction
      success budget hbudget hcover hsuccess)

/--
For at least two arms, a coordinate-specific orientation prediction still
forces the same explicit quadratic ideal-game lower bound.
-/
theorem unorderedComparisonCoordinate_coordinate_quadratic_query_lower_bound_of_success
    {Arm Trace : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Trace] [DecidableEq Trace]
    [Nonempty (unorderedComparisonCoordinate Arm)]
    (hcard : 2 ≤ Fintype.card Arm)
    (traceLaw : PMF Trace) (queried : Trace → Finset (unorderedComparisonCoordinate Arm))
    (prediction : Trace → unorderedComparisonCoordinate Arm → Bool)
    (success : ((Trace × unorderedComparisonCoordinate Arm) × Bool) → Prop)
    [DecidablePred success] (budget : ℕ)
    (hbudget : ∀ trace, (queried trace).card ≤ budget)
    (hcover : ∀ traceComparisonBit, success traceComparisonBit →
      traceComparisonBit.1.2 ∈ queried traceComparisonBit.1.1 ∨
        prediction traceComparisonBit.1.1 traceComparisonBit.1.2 = traceComparisonBit.2)
    (hsuccess : (7 : ℝ) / 8 ≤
      pmfProb (randomHiddenComparisonBitLaw
        (Comparison := unorderedComparisonCoordinate Arm) traceLaw) success) :
    (3 : ℝ) / 32 * (Fintype.card Arm : ℝ) ^ 2 ≤ budget := by
  have hchoose :
      (3 : ℝ) / 32 * (Fintype.card Arm : ℝ) ^ 2 ≤
        (3 : ℝ) / 8 * ((Fintype.card Arm).choose 2 : ℝ) := by
    rw [Nat.cast_choose_two]
    have hcardReal : (2 : ℝ) ≤ Fintype.card Arm := by exact_mod_cast hcard
    nlinarith
  exact hchoose.trans
    (unorderedComparisonCoordinate_coordinate_query_lower_bound_of_success
      traceLaw queried prediction success budget hbudget hcover hsuccess)

/--
The actual base-model success event of a finite adaptive ranking procedure.
Its coordinates are independent fair-noise traces, hidden unordered pairs, and
hidden orientation bits; the actual procedure trace changes only when it
queries that pair.
-/
noncomputable def theorem7BaseRankingSuccess
    {n comparisonBudget : ℕ} (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (hcard : 2 ≤ n) : ((Fin comparisonBudget → Bool) ×
      unorderedComparisonCoordinate (Fin n)) × Bool → Prop := fun traceComparisonBit =>
  EpsilonPreferenceRanking
    (theorem7HiddenCoordinatePreferenceGap n 0 hcard traceComparisonBit.1.2 traceComparisonBit.2)
    (1 / 4) (procedure.output
      (theorem7ActualOutcomeTrace procedure traceComparisonBit.1.2 traceComparisonBit.2 traceComparisonBit.1.1))

/-- The coordinate-specific orientation prediction read from a procedure's ghost-trace output. -/
noncomputable def theorem7ProcedureOrientationPrediction
    {n comparisonBudget : ℕ} (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (noise : Fin comparisonBudget → Bool)
    (coordinate : unorderedComparisonCoordinate (Fin n)) : Bool :=
  theorem7RankingOrientationPrediction (procedure.output noise) coordinate

/--
Base-model ranking success either hits the hidden coordinate on its independent
fair-noise query path or correctly predicts its unseen orientation bit.
-/
lemma theorem7BaseRankingSuccess_cover
    {n comparisonBudget : ℕ} (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (hcard : 2 ≤ n) (noise : Fin comparisonBudget → Bool)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool)
    (hsuccess : theorem7BaseRankingSuccess procedure hcard ((noise, coordinate), orientation)) :
    coordinate ∈ theorem7ProcedureQueriedCoordinates procedure noise ∨
      theorem7ProcedureOrientationPrediction procedure noise coordinate = orientation := by
  by_cases hhit : coordinate ∈ theorem7ProcedureQueriedCoordinates procedure noise
  · exact Or.inl hhit
  · right
    unfold theorem7BaseRankingSuccess at hsuccess
    rw [theorem7Prehit_actualTrace_eq_noise procedure coordinate orientation noise hhit] at hsuccess
    exact theorem7RankingOrientationPrediction_eq_orientation_of_epsilonRanking
      hcard coordinate orientation (procedure.output noise) hsuccess

/--
The ideal-game lower bound applied to a finite adaptive procedure's actual
base-model success event.  The typeclass-rich auxiliary surface is internal;
the source-facing probability wrapper below has only the paper parameters.
-/
private theorem theorem7BaseRankingProcedure_quadratic_query_lower_bound_aux
    {n comparisonBudget : ℕ} [Nonempty (unorderedComparisonCoordinate (Fin n))]
    (hcard : 2 ≤ n)
    (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    [DecidablePred (theorem7BaseRankingSuccess procedure hcard)]
    (hsuccess : (7 : ℝ) / 8 ≤
      pmfProb (randomHiddenComparisonBitLaw
        (Comparison := unorderedComparisonCoordinate (Fin n))
        (uniformPMF (Fin comparisonBudget → Bool)))
        (theorem7BaseRankingSuccess procedure hcard)) :
    (3 : ℝ) / 32 * (n : ℝ) ^ 2 ≤ comparisonBudget := by
  classical
  simpa [theorem7ProcedureOrientationPrediction] using
    (unorderedComparisonCoordinate_coordinate_quadratic_query_lower_bound_of_success
      (Arm := Fin n) (by simpa using hcard)
      (uniformPMF (Fin comparisonBudget → Bool))
      (theorem7ProcedureQueriedCoordinates procedure)
      (fun noise coordinate => theorem7ProcedureOrientationPrediction procedure noise coordinate)
      (theorem7BaseRankingSuccess procedure hcard) comparisonBudget
      (fun noise => theorem7ProcedureQueriedCoordinates_card_le procedure noise)
      (fun traceComparisonBit hsuccess =>
        theorem7BaseRankingSuccess_cover procedure hcard traceComparisonBit.1.1 traceComparisonBit.1.2
          traceComparisonBit.2 hsuccess)
      hsuccess)

/--
The base-model success probability of a finite adaptive ranking procedure,
under independent uniform fair-noise bits, a hidden pair, and its orientation.
-/
noncomputable def theorem7BaseRankingSuccessProbability
    {n comparisonBudget : ℕ} (hcard : 2 ≤ n)
    (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget) : ℝ := by
  classical
  letI : Nonempty (unorderedComparisonCoordinate (Fin n)) :=
    unorderedComparisonCoordinate_nonempty_of_card_ge_two (by simpa using hcard)
  letI : DecidablePred (theorem7BaseRankingSuccess procedure hcard) := Classical.decPred _
  exact pmfProb (randomHiddenComparisonBitLaw
    (Comparison := unorderedComparisonCoordinate (Fin n))
    (uniformPMF (Fin comparisonBudget → Bool)))
    (theorem7BaseRankingSuccess procedure hcard)

/--
In the `mu = 0` base experiment, any finite adaptive procedure that outputs a
`1 / 4`-ranking with probability at least `7/8` uses at least `3 n² / 32`
comparison rounds.  This is the rigorous randomized-relabeling core of the
source's Theorem 7 proof sketch.
-/
theorem theorem7BaseRankingProcedure_quadratic_query_lower_bound
    {n comparisonBudget : ℕ} (hcard : 2 ≤ n)
    (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (hsuccess : (7 : ℝ) / 8 ≤ theorem7BaseRankingSuccessProbability hcard procedure) :
    (3 : ℝ) / 32 * (n : ℝ) ^ 2 ≤ comparisonBudget := by
  classical
  letI : Nonempty (unorderedComparisonCoordinate (Fin n)) :=
    unorderedComparisonCoordinate_nonempty_of_card_ge_two (by simpa using hcard)
  letI : DecidablePred (theorem7BaseRankingSuccess procedure hcard) := Classical.decPred _
  apply theorem7BaseRankingProcedure_quadratic_query_lower_bound_aux hcard procedure
  simpa [theorem7BaseRankingSuccessProbability] using hsuccess

/--
The ranking-success event for an arbitrary member of the Theorem 7
hidden-coordinate hard family.  The same event is evaluated under the small-
`mu` conditional trace law and under the uniform auxiliary-noise law.
-/
noncomputable def theorem7RankingSuccessAtMu
    {n comparisonBudget : ℕ} (mu : ℝ)
    (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (hcard : 2 ≤ n) : ((Fin comparisonBudget → Bool) ×
      unorderedComparisonCoordinate (Fin n)) × Bool → Prop := fun traceComparisonBit =>
  EpsilonPreferenceRanking
    (theorem7HiddenCoordinatePreferenceGap n mu hcard traceComparisonBit.1.2 traceComparisonBit.2)
    (1 / 4) (procedure.output
      (theorem7ActualOutcomeTrace procedure traceComparisonBit.1.2 traceComparisonBit.2 traceComparisonBit.1.1))

/--
Uniform-noise success on any hard-family member still either queries the hidden
coordinate on the ghost path or recovers its orientation from the output
ranking.  This deterministic implication does not require `mu = 0`.
-/
lemma theorem7RankingSuccessAtMu_cover
    {n comparisonBudget : ℕ} (mu : ℝ)
    (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (hcard : 2 ≤ n) (noise : Fin comparisonBudget → Bool)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool)
    (hsuccess : theorem7RankingSuccessAtMu mu procedure hcard ((noise, coordinate), orientation)) :
    coordinate ∈ theorem7ProcedureQueriedCoordinates procedure noise ∨
      theorem7ProcedureOrientationPrediction procedure noise coordinate = orientation := by
  by_cases hhit : coordinate ∈ theorem7ProcedureQueriedCoordinates procedure noise
  · exact Or.inl hhit
  · right
    unfold theorem7RankingSuccessAtMu at hsuccess
    rw [theorem7Prehit_actualTrace_eq_noise procedure coordinate orientation noise hhit] at hsuccess
    exact theorem7RankingOrientationPrediction_eq_orientation_of_epsilonRanking
      hcard coordinate orientation (procedure.output noise) hsuccess

/-- The uniform auxiliary-noise success probability for the `mu` hard family. -/
noncomputable def theorem7RankingSuccessAtMuBaseProbability
    {n comparisonBudget : ℕ} (mu : ℝ) (hcard : 2 ≤ n)
    (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget) : ℝ := by
  classical
  letI : DecidablePred (theorem7RankingSuccessAtMu mu procedure hcard) := Classical.decPred _
  exact pmfProb (theorem7BaseHiddenNoiseLaw (comparisonBudget := comparisonBudget) hcard)
    (theorem7RankingSuccessAtMu mu procedure hcard)

/-- The complete small-`mu` success probability of a finite adaptive procedure. -/
noncomputable def theorem7SmallMuRankingSuccessProbability
    {n comparisonBudget : ℕ} (mu : ℝ) (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2)
    (hcard : 2 ≤ n) (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget) : ℝ := by
  classical
  letI : DecidablePred (theorem7RankingSuccessAtMu mu procedure hcard) := Classical.decPred _
  exact pmfProb (theorem7SmallMuHiddenNoiseLaw mu hmu hmuHalf hcard procedure)
    (theorem7RankingSuccessAtMu mu procedure hcard)

/--
An elementary finite numerical bound for the likelihood factor.  It is stated
through the transparent scaled budget `2 * mu * T`; the source choice
`mu < 1 / n^10` and `T ≤ n² / 20` is a sufficient instance when `n ≥ 2`.
-/
theorem theorem7LikelihoodFactor_le_sevenSixths_of_scaledBudget
    {comparisonBudget : ℕ} {mu : ℝ} (hmu : 0 ≤ mu)
    (hscaled : 2 * mu * (comparisonBudget : ℝ) ≤ (1 : ℝ) / 7) :
    (1 + 2 * mu) ^ comparisonBudget ≤ (7 : ℝ) / 6 := by
  have hproduct : (1 + 2 * mu) ^ comparisonBudget ≤
      Real.exp ((comparisonBudget : ℝ) * (2 * mu)) := by
    calc
      (1 + 2 * mu) ^ comparisonBudget = ∏ _ : Fin comparisonBudget, (1 + 2 * mu) := by
        simp
      _ = ∏ _ : Fin comparisonBudget, (1 + (2 * mu)) := by ring
      _ ≤ Real.exp (∑ _ : Fin comparisonBudget, (2 * mu)) :=
        Real.prod_one_add_le_exp_sum Finset.univ (fun _ => mul_nonneg (by norm_num) hmu)
      _ = Real.exp ((comparisonBudget : ℝ) * (2 * mu)) := by simp
  have hargumentNonneg : 0 ≤ (comparisonBudget : ℝ) * (2 * mu) := by positivity
  have hargumentLe : (comparisonBudget : ℝ) * (2 * mu) ≤ (1 : ℝ) / 7 := by
    nlinarith [hscaled]
  have hargumentLtOne : (comparisonBudget : ℝ) * (2 * mu) < 1 := by
    exact hargumentLe.trans_lt (by norm_num)
  have hexp : Real.exp ((comparisonBudget : ℝ) * (2 * mu)) ≤
      1 / (1 - (comparisonBudget : ℝ) * (2 * mu)) :=
    Real.exp_bound_div_one_sub_of_interval hargumentNonneg hargumentLtOne
  have hdenomPos : 0 < 1 - (comparisonBudget : ℝ) * (2 * mu) := by linarith
  have hfraction : 1 / (1 - (comparisonBudget : ℝ) * (2 * mu)) ≤ (7 : ℝ) / 6 := by
    rw [div_le_iff₀ hdenomPos]
    nlinarith [hargumentLe]
  exact hproduct.trans (hexp.trans hfraction)

/--
The source-scale hypotheses `mu ≤ 1 / n^10` and `T ≤ n² / 20` imply the
scaled-budget condition used by the finite likelihood calculation.
-/
theorem theorem7SourceMu_scaledBudget_le_oneSeventh
    {n comparisonBudget : ℕ} {mu : ℝ} (hcard : 2 ≤ n)
    (hmuSource : mu ≤ 1 / (n : ℝ) ^ 10)
    (hbudget : (comparisonBudget : ℝ) ≤ (n : ℝ) ^ 2 / 20) :
    2 * mu * (comparisonBudget : ℝ) ≤ (1 : ℝ) / 7 := by
  have hnReal : (2 : ℝ) ≤ n := by exact_mod_cast hcard
  have hnPositive : 0 < (n : ℝ) := by linarith
  have hnPowPositive : 0 < (n : ℝ) ^ 10 := pow_pos hnPositive _
  have hmuBound : 2 * mu ≤ 2 * (1 / (n : ℝ) ^ 10) :=
    mul_le_mul_of_nonneg_left hmuSource (by norm_num)
  calc
    2 * mu * (comparisonBudget : ℝ) = (2 * mu) * (comparisonBudget : ℝ) := by ring
    _ ≤ (2 * (1 / (n : ℝ) ^ 10)) * (comparisonBudget : ℝ) :=
      mul_le_mul_of_nonneg_right hmuBound (Nat.cast_nonneg _)
    _ ≤ (2 * (1 / (n : ℝ) ^ 10)) * ((n : ℝ) ^ 2 / 20) :=
      mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = 1 / (10 * (n : ℝ) ^ 8) := by
      field_simp [ne_of_gt hnPowPositive]
      ring
    _ ≤ (1 : ℝ) / 7 := by
      have hnEight : (2 : ℝ) ^ 8 ≤ (n : ℝ) ^ 8 :=
        pow_le_pow_left₀ (by norm_num) hnReal _
      have hdenomPositive : 0 < 10 * (n : ℝ) ^ 8 := by positivity
      rw [div_le_iff₀ hdenomPositive]
      norm_num at hnEight ⊢
      nlinarith

/-- The literal source-scale `mu` and comparison-budget bounds give the `7/6` factor. -/
theorem theorem7SourceMuLikelihoodFactor_le_sevenSixths
    {n comparisonBudget : ℕ} {mu : ℝ} (hcard : 2 ≤ n) (hmu : 0 ≤ mu)
    (hmuSource : mu ≤ 1 / (n : ℝ) ^ 10)
    (hbudget : (comparisonBudget : ℝ) ≤ (n : ℝ) ^ 2 / 20) :
    (1 + 2 * mu) ^ comparisonBudget ≤ (7 : ℝ) / 6 :=
  theorem7LikelihoodFactor_le_sevenSixths_of_scaledBudget hmu
    (theorem7SourceMu_scaledBudget_le_oneSeventh hcard hmuSource hbudget)

/--
The base lower-bound argument applies unchanged to uniform auxiliary noise
when success is judged against a fixed positive-`mu` hard model.
-/
private theorem theorem7RankingSuccessAtMu_base_quadratic_query_lower_bound_aux
    {n comparisonBudget : ℕ} [Nonempty (unorderedComparisonCoordinate (Fin n))]
    (mu : ℝ) (hcard : 2 ≤ n)
    (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    [DecidablePred (theorem7RankingSuccessAtMu mu procedure hcard)]
    (hsuccess : (3 : ℝ) / 4 ≤
      pmfProb (theorem7BaseHiddenNoiseLaw (comparisonBudget := comparisonBudget) hcard)
        (theorem7RankingSuccessAtMu mu procedure hcard)) :
    (1 : ℝ) / 16 * (n : ℝ) ^ 2 ≤ comparisonBudget := by
  classical
  let traceLaw := uniformPMF (Fin comparisonBudget → Bool)
  let success := theorem7RankingSuccessAtMu mu procedure hcard
  let queried := theorem7ProcedureQueriedCoordinates procedure
  let prediction := fun noise coordinate => theorem7ProcedureOrientationPrediction procedure noise coordinate
  let law := randomHiddenComparisonBitLaw
    (Comparison := unorderedComparisonCoordinate (Fin n)) traceLaw
  have hupper := randomHiddenComparisonBitLaw_hit_or_coordinate_predict_probability_le
    traceLaw queried prediction comparisonBudget
    (fun noise => theorem7ProcedureQueriedCoordinates_card_le procedure noise)
  have hsuccessLe : pmfProb law success ≤
      pmfProb law (fun traceComparisonBit =>
        traceComparisonBit.1.2 ∈ queried traceComparisonBit.1.1 ∨
          prediction traceComparisonBit.1.1 traceComparisonBit.1.2 = traceComparisonBit.2) := by
    apply pmfProb_le_of_imp
    intro traceComparisonBit hsuccessTrace
    exact theorem7RankingSuccessAtMu_cover mu procedure hcard traceComparisonBit.1.1
      traceComparisonBit.1.2 traceComparisonBit.2 hsuccessTrace
  have hsuccessLaw : (3 : ℝ) / 4 ≤ pmfProb law success := by
    simpa [law, traceLaw, success, theorem7BaseHiddenNoiseLaw] using hsuccess
  have hratio : (1 : ℝ) / 4 ≤
      (comparisonBudget : ℝ) / (Fintype.card (unorderedComparisonCoordinate (Fin n)) : ℝ) := by
    dsimp only [law] at hupper hsuccessLe hsuccessLaw
    linarith
  have hcomparisonCard : 0 < (Fintype.card (unorderedComparisonCoordinate (Fin n)) : ℝ) := by
    positivity
  have hcoordinateLower : (1 : ℝ) / 4 *
      (Fintype.card (unorderedComparisonCoordinate (Fin n)) : ℝ) ≤ comparisonBudget := by
    calc
      (1 : ℝ) / 4 * (Fintype.card (unorderedComparisonCoordinate (Fin n)) : ℝ) ≤
          ((comparisonBudget : ℝ) /
            (Fintype.card (unorderedComparisonCoordinate (Fin n)) : ℝ)) *
            (Fintype.card (unorderedComparisonCoordinate (Fin n)) : ℝ) :=
        mul_le_mul_of_nonneg_right hratio hcomparisonCard.le
      _ = comparisonBudget := by field_simp [ne_of_gt hcomparisonCard]
  have hquadratic : (1 : ℝ) / 16 * (n : ℝ) ^ 2 ≤
      (1 : ℝ) / 4 * (Fintype.card (unorderedComparisonCoordinate (Fin n)) : ℝ) := by
    rw [unorderedComparisonCoordinate_card]
    rw [Nat.cast_choose_two]
    simp only [Fintype.card_fin]
    have hcardReal : (2 : ℝ) ≤ n := by exact_mod_cast hcard
    nlinarith
  exact hquadratic.trans hcoordinateLower

/--
Conditional small-`mu` ranking success at the source `7/8` target forces the
same quadratic query lower bound whenever its finite likelihood factor is at
most `7/6`.  This closes the adaptive likelihood and randomized-relabeling
bridge, leaving only the source's numerical choice of `mu` to instantiate the
factor premise.
-/
theorem theorem7SmallMuRankingProcedure_quadratic_query_lower_bound_of_likelihoodFactor
    {n comparisonBudget : ℕ} {mu : ℝ} (hmu : 0 < mu) (hmuHalf : mu ≤ 1 / 2)
    (hcard : 2 ≤ n) (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (hfactor : (1 + 2 * mu) ^ comparisonBudget ≤ (7 : ℝ) / 6)
    (hsuccess : (7 : ℝ) / 8 ≤
      theorem7SmallMuRankingSuccessProbability mu hmu.le hmuHalf hcard procedure) :
    (1 : ℝ) / 16 * (n : ℝ) ^ 2 ≤ comparisonBudget := by
  classical
  letI : Nonempty (unorderedComparisonCoordinate (Fin n)) :=
    unorderedComparisonCoordinate_nonempty_of_card_ge_two (by simpa using hcard)
  letI : DecidablePred (theorem7RankingSuccessAtMu mu procedure hcard) := Classical.decPred _
  have htransfer :
      pmfProb (theorem7SmallMuHiddenNoiseLaw mu hmu.le hmuHalf hcard procedure)
        (theorem7RankingSuccessAtMu mu procedure hcard) ≤
      (1 + 2 * mu) ^ comparisonBudget *
        pmfProb (theorem7BaseHiddenNoiseLaw (comparisonBudget := comparisonBudget) hcard)
          (theorem7RankingSuccessAtMu mu procedure hcard) :=
    pmfProb_le_mul_of_pointwise_mass_le
      (theorem7SmallMuHiddenNoiseLaw mu hmu.le hmuHalf hcard procedure)
      (theorem7BaseHiddenNoiseLaw (comparisonBudget := comparisonBudget) hcard)
      (theorem7RankingSuccessAtMu mu procedure hcard)
      ((1 + 2 * mu) ^ comparisonBudget)
      (fun traceComparisonBit =>
        theorem7SmallMuHiddenNoiseLaw_apply_toReal_le_base_scaled hmu.le hmuHalf hcard procedure
          traceComparisonBit.1.1 traceComparisonBit.1.2 traceComparisonBit.2)
  have hsmall : (7 : ℝ) / 8 ≤
      pmfProb (theorem7SmallMuHiddenNoiseLaw mu hmu.le hmuHalf hcard procedure)
        (theorem7RankingSuccessAtMu mu procedure hcard) := by
    simpa [theorem7SmallMuRankingSuccessProbability] using hsuccess
  have hbase : (3 : ℝ) / 4 ≤
      pmfProb (theorem7BaseHiddenNoiseLaw (comparisonBudget := comparisonBudget) hcard)
        (theorem7RankingSuccessAtMu mu procedure hcard) :=
    theorem7_base_success_probability_of_smallMu_success _ _ _ _ htransfer hfactor hsmall
  exact theorem7RankingSuccessAtMu_base_quadratic_query_lower_bound_aux mu hcard procedure hbase

/--
The source-scale small-`mu` regime directly instantiates the complete
adaptive randomized-relabeling lower bound.
-/
theorem theorem7SmallMuRankingProcedure_quadratic_query_lower_bound_of_sourceScale
    {n comparisonBudget : ℕ} {mu : ℝ} (hmu : 0 < mu) (hmuHalf : mu ≤ 1 / 2)
    (hcard : 2 ≤ n) (hmuSource : mu ≤ 1 / (n : ℝ) ^ 10)
    (hbudget : (comparisonBudget : ℝ) ≤ (n : ℝ) ^ 2 / 20)
    (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (hsuccess : (7 : ℝ) / 8 ≤
      theorem7SmallMuRankingSuccessProbability mu hmu.le hmuHalf hcard procedure) :
    (1 : ℝ) / 16 * (n : ℝ) ^ 2 ≤ comparisonBudget := by
  apply theorem7SmallMuRankingProcedure_quadratic_query_lower_bound_of_likelihoodFactor
    hmu hmuHalf hcard procedure
  · exact theorem7SourceMuLikelihoodFactor_le_sevenSixths hcard hmu.le hmuSource hbudget
  · exact hsuccess

/--
No finite adaptive procedure using at most `n² / 20` comparisons can meet the
source's `7/8` ranking-success target on every source-scale Theorem 7 hard
instance.  This is the source proof's lower-bound contradiction in an explicit
finite form.
-/
theorem theorem7SmallMuRankingProcedure_not_sourceBudget_success
    {n comparisonBudget : ℕ} {mu : ℝ} (hmu : 0 < mu) (hmuHalf : mu ≤ 1 / 2)
    (hcard : 2 ≤ n) (hmuSource : mu ≤ 1 / (n : ℝ) ^ 10)
    (hbudget : (comparisonBudget : ℝ) ≤ (n : ℝ) ^ 2 / 20)
    (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget) :
    ¬ ((7 : ℝ) / 8 ≤
      theorem7SmallMuRankingSuccessProbability mu hmu.le hmuHalf hcard procedure) := by
  intro hsuccess
  have hlower := theorem7SmallMuRankingProcedure_quadratic_query_lower_bound_of_sourceScale
    hmu hmuHalf hcard hmuSource hbudget procedure hsuccess
  have hnNat : 0 < n := by omega
  have hnPositive : 0 < (n : ℝ) := by exact_mod_cast hnNat
  have hsq : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnPositive
  nlinarith

/-- The uniform law on relabeled exceptional comparison coordinates. -/
noncomputable def theorem7UniformHiddenCoordinateLaw
    {n : ℕ} (hcard : 2 ≤ n) : PMF (unorderedComparisonCoordinate (Fin n)) := by
  classical
  letI : Nonempty (unorderedComparisonCoordinate (Fin n)) :=
    unorderedComparisonCoordinate_nonempty_of_card_ge_two (by simpa using hcard)
  exact uniformPMF (unorderedComparisonCoordinate (Fin n))

/--
The ranking-success probability for one fixed source hard instance, indexed by
its relabeled exceptional coordinate and orientation.  Only the comparison
noise remains random in this conditional experiment.
-/
noncomputable def theorem7SmallMuInstanceSuccessProbability
    {n comparisonBudget : ℕ} (mu : ℝ) (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2)
    (hcard : 2 ≤ n) (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool) : ℝ := by
  classical
  letI : DecidablePred (theorem7RankingSuccessAtMu mu procedure hcard) := Classical.decPred _
  exact pmfProb (theorem7ProcedureSmallMuNoiseLaw mu hmu hmuHalf hcard procedure
    coordinate orientation)
    (fun noise => theorem7RankingSuccessAtMu mu procedure hcard ((noise, coordinate), orientation))

/--
The small-`mu` hard-distribution success probability is the uniform mixture of
the conditional fixed-instance success probabilities.
-/
theorem theorem7SmallMuRankingSuccessProbability_eq_uniform_instance_average
    {n comparisonBudget : ℕ} (mu : ℝ) (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2)
    (hcard : 2 ≤ n) (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget) :
    theorem7SmallMuRankingSuccessProbability mu hmu hmuHalf hcard procedure =
      pmfExp (theorem7UniformHiddenCoordinateLaw hcard) (fun coordinate =>
        pmfExp (uniformPMF Bool) (fun orientation =>
          theorem7SmallMuInstanceSuccessProbability mu hmu hmuHalf hcard procedure
            coordinate orientation)) := by
  classical
  letI : Nonempty (unorderedComparisonCoordinate (Fin n)) :=
    unorderedComparisonCoordinate_nonempty_of_card_ge_two (by simpa using hcard)
  letI : DecidablePred (theorem7RankingSuccessAtMu mu procedure hcard) := Classical.decPred _
  change theorem7SmallMuRankingSuccessProbability mu hmu hmuHalf hcard procedure =
    pmfExp (uniformPMF (unorderedComparisonCoordinate (Fin n))) (fun coordinate =>
      pmfExp (uniformPMF Bool) (fun orientation =>
        theorem7SmallMuInstanceSuccessProbability mu hmu hmuHalf hcard procedure
          coordinate orientation))
  unfold theorem7SmallMuRankingSuccessProbability theorem7SmallMuHiddenNoiseLaw
  unfold hiddenComparisonConditionalTraceLaw
  rw [pmfProb_bind]
  apply pmfExp_congr
  intro coordinate
  rw [pmfProb_bind]
  apply pmfExp_congr
  intro orientation
  rw [pmfProb_map]
  rfl

/--
For every deterministic finite adaptive procedure below the source budget,
some relabeled source hard instance has ranking-success probability below the
source target.  This is the finite existential-model form of Theorem 7.
-/
theorem theorem7_exists_source_hard_instance_of_deterministic_procedure
    {n comparisonBudget : ℕ} {mu : ℝ} (hmu : 0 < mu) (hmuHalf : mu ≤ 1 / 2)
    (hcard : 2 ≤ n) (hmuSource : mu ≤ 1 / (n : ℝ) ^ 10)
    (hbudget : (comparisonBudget : ℝ) ≤ (n : ℝ) ^ 2 / 20)
    (procedure : Theorem7AdaptiveRankingProcedure n comparisonBudget) :
    ∃ coordinate : unorderedComparisonCoordinate (Fin n), ∃ orientation : Bool,
      ¬ ((7 : ℝ) / 8 ≤ theorem7SmallMuInstanceSuccessProbability
        mu hmu.le hmuHalf hcard procedure coordinate orientation) := by
  classical
  letI : Nonempty (unorderedComparisonCoordinate (Fin n)) :=
    unorderedComparisonCoordinate_nonempty_of_card_ge_two (by simpa using hcard)
  by_contra hinstance
  push Not at hinstance
  have hcoordinate : ∀ coordinate : unorderedComparisonCoordinate (Fin n),
      (7 : ℝ) / 8 ≤ pmfExp (uniformPMF Bool) (fun orientation =>
        theorem7SmallMuInstanceSuccessProbability mu hmu.le hmuHalf hcard procedure
          coordinate orientation) := by
    intro coordinate
    calc
      (7 : ℝ) / 8 = pmfExp (uniformPMF Bool) (fun _ => (7 : ℝ) / 8) :=
        (pmfExp_const (uniformPMF Bool) _).symm
      _ ≤ pmfExp (uniformPMF Bool) (fun orientation =>
        theorem7SmallMuInstanceSuccessProbability mu hmu.le hmuHalf hcard procedure
          coordinate orientation) :=
        pmfExp_le_pmfExp_of_forall_le (uniformPMF Bool) _ _ (hinstance coordinate)
  have hglobal : (7 : ℝ) / 8 ≤
      theorem7SmallMuRankingSuccessProbability mu hmu.le hmuHalf hcard procedure := by
    rw [theorem7SmallMuRankingSuccessProbability_eq_uniform_instance_average]
    calc
      (7 : ℝ) / 8 = pmfExp (uniformPMF (unorderedComparisonCoordinate (Fin n)))
          (fun _ => (7 : ℝ) / 8) :=
        (pmfExp_const (uniformPMF (unorderedComparisonCoordinate (Fin n))) _).symm
      _ ≤ pmfExp (uniformPMF (unorderedComparisonCoordinate (Fin n))) (fun coordinate =>
          pmfExp (uniformPMF Bool) (fun orientation =>
            theorem7SmallMuInstanceSuccessProbability mu hmu.le hmuHalf hcard procedure
              coordinate orientation)) :=
        pmfExp_le_pmfExp_of_forall_le
          (uniformPMF (unorderedComparisonCoordinate (Fin n))) _ _ hcoordinate
  exact theorem7SmallMuRankingProcedure_not_sourceBudget_success hmu hmuHalf hcard
    hmuSource hbudget procedure hglobal

/-- Independent finite expectations may be evaluated in either order. -/
private theorem pmfExp_swap
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (f : α → β → ℝ) :
    pmfExp μ (fun a => pmfExp ν (fun b => f a b)) =
      pmfExp ν (fun b => pmfExp μ (fun a => f a b)) := by
  unfold pmfExp
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro b _
  refine Finset.sum_congr rfl ?_
  intro a _
  ring

/--
The hard-distribution ranking-success probability of a procedure with a finite
independent internal random tape.  Sampling the tape before comparisons turns
each seed into a deterministic adaptive procedure, while `seedLaw` retains the
algorithm's arbitrary finite randomization.
-/
noncomputable def theorem7SeededSmallMuRankingSuccessProbability
    {Seed : Type*} [Fintype Seed] [DecidableEq Seed] {n comparisonBudget : ℕ}
    (seedLaw : PMF Seed) (mu : ℝ) (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2)
    (hcard : 2 ≤ n) (procedure : Seed → Theorem7AdaptiveRankingProcedure n comparisonBudget) : ℝ :=
  pmfExp seedLaw (fun seed =>
    theorem7SmallMuRankingSuccessProbability mu hmu hmuHalf hcard (procedure seed))

/--
The success probability of a seeded procedure on one fixed relabeled source
hard instance, after averaging only its independent internal random tape.
-/
noncomputable def theorem7SeededSmallMuInstanceSuccessProbability
    {Seed : Type*} [Fintype Seed] [DecidableEq Seed] {n comparisonBudget : ℕ}
    (seedLaw : PMF Seed) (mu : ℝ) (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2)
    (hcard : 2 ≤ n) (procedure : Seed → Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (coordinate : unorderedComparisonCoordinate (Fin n)) (orientation : Bool) : ℝ :=
  pmfExp seedLaw (fun seed => theorem7SmallMuInstanceSuccessProbability mu hmu hmuHalf hcard
    (procedure seed) coordinate orientation)

/--
The seeded hard-distribution success probability is the uniform mixture of its
seed-averaged fixed-instance success probabilities.  The proof only swaps
three independent finite expectations.
-/
theorem theorem7SeededSmallMuRankingSuccessProbability_eq_uniform_instance_average
    {Seed : Type*} [Fintype Seed] [DecidableEq Seed] {n comparisonBudget : ℕ}
    (seedLaw : PMF Seed) (mu : ℝ) (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2)
    (hcard : 2 ≤ n) (procedure : Seed → Theorem7AdaptiveRankingProcedure n comparisonBudget) :
    theorem7SeededSmallMuRankingSuccessProbability seedLaw mu hmu hmuHalf hcard procedure =
      pmfExp (theorem7UniformHiddenCoordinateLaw hcard) (fun coordinate =>
        pmfExp (uniformPMF Bool) (fun orientation =>
          theorem7SeededSmallMuInstanceSuccessProbability seedLaw mu hmu hmuHalf hcard
            procedure coordinate orientation)) := by
  classical
  letI : Nonempty (unorderedComparisonCoordinate (Fin n)) :=
    unorderedComparisonCoordinate_nonempty_of_card_ge_two (by simpa using hcard)
  unfold theorem7SeededSmallMuRankingSuccessProbability
  simp_rw [theorem7SmallMuRankingSuccessProbability_eq_uniform_instance_average
    mu hmu hmuHalf hcard]
  change pmfExp seedLaw (fun seed =>
      pmfExp (uniformPMF (unorderedComparisonCoordinate (Fin n))) (fun coordinate =>
        pmfExp (uniformPMF Bool) (fun orientation =>
          theorem7SmallMuInstanceSuccessProbability mu hmu hmuHalf hcard
            (procedure seed) coordinate orientation))) = _
  calc
    pmfExp seedLaw (fun seed =>
        pmfExp (uniformPMF (unorderedComparisonCoordinate (Fin n))) (fun coordinate =>
          pmfExp (uniformPMF Bool) (fun orientation =>
            theorem7SmallMuInstanceSuccessProbability mu hmu hmuHalf hcard
              (procedure seed) coordinate orientation))) =
        pmfExp (uniformPMF (unorderedComparisonCoordinate (Fin n))) (fun coordinate =>
          pmfExp seedLaw (fun seed =>
            pmfExp (uniformPMF Bool) (fun orientation =>
              theorem7SmallMuInstanceSuccessProbability mu hmu hmuHalf hcard
                (procedure seed) coordinate orientation))) :=
      pmfExp_swap seedLaw (uniformPMF (unorderedComparisonCoordinate (Fin n))) _
    _ = pmfExp (uniformPMF (unorderedComparisonCoordinate (Fin n))) (fun coordinate =>
        pmfExp (uniformPMF Bool) (fun orientation =>
          pmfExp seedLaw (fun seed =>
            theorem7SmallMuInstanceSuccessProbability mu hmu hmuHalf hcard
              (procedure seed) coordinate orientation))) := by
      apply pmfExp_congr
      intro coordinate
      exact pmfExp_swap seedLaw (uniformPMF Bool) _
    _ = _ := rfl

/--
If a finite randomized procedure reaches the source success target on the
uniform hard distribution, then one positive-probability tape seed already
reaches that target.  This is the finite random-tape reduction needed before
applying the deterministic trace lower bound.
-/
theorem theorem7_exists_seed_of_seeded_smallMu_success
    {Seed : Type*} [Fintype Seed] [DecidableEq Seed] [Nonempty Seed]
    {n comparisonBudget : ℕ} {mu : ℝ} (seedLaw : PMF Seed)
    (hmu : 0 ≤ mu) (hmuHalf : mu ≤ 1 / 2) (hcard : 2 ≤ n)
    (procedure : Seed → Theorem7AdaptiveRankingProcedure n comparisonBudget)
    (hsuccess : (7 : ℝ) / 8 ≤ theorem7SeededSmallMuRankingSuccessProbability
      seedLaw mu hmu hmuHalf hcard procedure) :
    ∃ seed, 0 < (seedLaw seed).toReal ∧ (7 : ℝ) / 8 ≤
      theorem7SmallMuRankingSuccessProbability mu hmu hmuHalf hcard (procedure seed) := by
  by_contra hseed
  have hstrict : ∀ seed, 0 < (seedLaw seed).toReal →
      theorem7SmallMuRankingSuccessProbability mu hmu hmuHalf hcard (procedure seed) <
        (7 : ℝ) / 8 := by
    intro seed hmass
    by_contra hnot
    apply hseed
    exact ⟨seed, hmass, le_of_not_gt hnot⟩
  have havg : pmfExp seedLaw (fun seed =>
      theorem7SmallMuRankingSuccessProbability mu hmu hmuHalf hcard (procedure seed)) <
      (7 : ℝ) / 8 :=
    pmfExp_lt_of_support_forall_lt seedLaw _ _ hstrict
  exact (not_lt_of_ge hsuccess) (by
    simpa [theorem7SeededSmallMuRankingSuccessProbability] using havg)

/--
The source-scale Theorem 7 contradiction also holds for any finite internal
random tape with an arbitrary PMF.  Hence randomization independent of the
comparison outcomes cannot evade the quadratic hard-distribution lower bound.
-/
theorem theorem7SeededSmallMuRankingProcedure_not_sourceBudget_success
    {Seed : Type*} [Fintype Seed] [DecidableEq Seed] [Nonempty Seed]
    {n comparisonBudget : ℕ} {mu : ℝ} (seedLaw : PMF Seed) (hmu : 0 < mu)
    (hmuHalf : mu ≤ 1 / 2) (hcard : 2 ≤ n)
    (hmuSource : mu ≤ 1 / (n : ℝ) ^ 10)
    (hbudget : (comparisonBudget : ℝ) ≤ (n : ℝ) ^ 2 / 20)
    (procedure : Seed → Theorem7AdaptiveRankingProcedure n comparisonBudget) :
    ¬ ((7 : ℝ) / 8 ≤ theorem7SeededSmallMuRankingSuccessProbability
      seedLaw mu hmu.le hmuHalf hcard procedure) := by
  intro hsuccess
  rcases theorem7_exists_seed_of_seeded_smallMu_success seedLaw hmu.le hmuHalf hcard procedure
      hsuccess with ⟨seed, _hmass, hseedSuccess⟩
  exact theorem7SmallMuRankingProcedure_not_sourceBudget_success hmu hmuHalf hcard
    hmuSource hbudget (procedure seed) hseedSuccess

/--
For a finite randomized adaptive procedure below the source budget, there is a
relabeled SST hard instance on which its seed-averaged ranking-success
probability is below `7/8`.  This packages the hard distribution into the
existential-model form stated by Theorem 7.
-/
theorem theorem7_exists_source_hard_instance_of_seeded_procedure
    {Seed : Type*} [Fintype Seed] [DecidableEq Seed] [Nonempty Seed]
    {n comparisonBudget : ℕ} {mu : ℝ} (seedLaw : PMF Seed) (hmu : 0 < mu)
    (hmuHalf : mu ≤ 1 / 2) (hcard : 2 ≤ n)
    (hmuSource : mu ≤ 1 / (n : ℝ) ^ 10)
    (hbudget : (comparisonBudget : ℝ) ≤ (n : ℝ) ^ 2 / 20)
    (procedure : Seed → Theorem7AdaptiveRankingProcedure n comparisonBudget) :
    ∃ coordinate : unorderedComparisonCoordinate (Fin n), ∃ orientation : Bool,
      ¬ ((7 : ℝ) / 8 ≤ theorem7SeededSmallMuInstanceSuccessProbability
        seedLaw mu hmu.le hmuHalf hcard procedure coordinate orientation) := by
  classical
  letI : Nonempty (unorderedComparisonCoordinate (Fin n)) :=
    unorderedComparisonCoordinate_nonempty_of_card_ge_two (by simpa using hcard)
  by_contra hinstance
  push Not at hinstance
  have hcoordinate : ∀ coordinate : unorderedComparisonCoordinate (Fin n),
      (7 : ℝ) / 8 ≤ pmfExp (uniformPMF Bool) (fun orientation =>
        theorem7SeededSmallMuInstanceSuccessProbability seedLaw mu hmu.le hmuHalf hcard procedure
          coordinate orientation) := by
    intro coordinate
    calc
      (7 : ℝ) / 8 = pmfExp (uniformPMF Bool) (fun _ => (7 : ℝ) / 8) :=
        (pmfExp_const (uniformPMF Bool) _).symm
      _ ≤ pmfExp (uniformPMF Bool) (fun orientation =>
        theorem7SeededSmallMuInstanceSuccessProbability seedLaw mu hmu.le hmuHalf hcard procedure
          coordinate orientation) :=
        pmfExp_le_pmfExp_of_forall_le (uniformPMF Bool) _ _ (hinstance coordinate)
  have hglobal : (7 : ℝ) / 8 ≤
      theorem7SeededSmallMuRankingSuccessProbability seedLaw mu hmu.le hmuHalf hcard procedure := by
    rw [theorem7SeededSmallMuRankingSuccessProbability_eq_uniform_instance_average]
    calc
      (7 : ℝ) / 8 = pmfExp (uniformPMF (unorderedComparisonCoordinate (Fin n)))
          (fun _ => (7 : ℝ) / 8) :=
        (pmfExp_const (uniformPMF (unorderedComparisonCoordinate (Fin n))) _).symm
      _ ≤ pmfExp (uniformPMF (unorderedComparisonCoordinate (Fin n))) (fun coordinate =>
          pmfExp (uniformPMF Bool) (fun orientation =>
            theorem7SeededSmallMuInstanceSuccessProbability seedLaw mu hmu.le hmuHalf hcard procedure
              coordinate orientation)) :=
        pmfExp_le_pmfExp_of_forall_le
          (uniformPMF (unorderedComparisonCoordinate (Fin n))) _ _ hcoordinate
  exact theorem7SeededSmallMuRankingProcedure_not_sourceBudget_success seedLaw hmu hmuHalf hcard
    hmuSource hbudget procedure hglobal

end FalahatgarEtAl2017MaxingRanking
