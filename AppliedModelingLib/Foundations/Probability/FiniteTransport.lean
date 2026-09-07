import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Finite Transport Couplings

Finite couplings of probability mass functions and their expectation
comparison inequality.  The latter is the primal transport estimate underlying
Wasserstein sensitivity arguments: a test function changes in expectation by
at most its pointwise change averaged under any coupling.

The point-mass coupling below directly reuses Mathlib's `PMF.pure` from
[`ProbabilityMassFunction/Monad.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/ProbabilityMassFunction/Monad.lean)
and `PMF.pure_map` from
[`ProbabilityMassFunction/Constructions.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean)
at the repository's pinned Mathlib commit, under Apache-2.0. No upstream code
is copied or ported here.
-/

namespace AppliedModelingLib

/-- A joint finite PMF whose first and second marginals are the prescribed laws. -/
structure FiniteCoupling {α β : Type*} (μ : PMF α) (ν : PMF β) where
  law : PMF (α × β)
  fst_marginal : law.map Prod.fst = μ
  snd_marginal : law.map Prod.snd = ν

namespace FiniteCoupling

variable {α β : Type*}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable {μ : PMF α} {ν : PMF β}

/-- The expected cost of a finite coupling. -/
noncomputable def expectedCost (coupling : FiniteCoupling μ ν) (cost : α → β → ℝ) : ℝ :=
  pmfExp coupling.law (fun pair => cost pair.1 pair.2)

/-- The first-coordinate expectation of a coupling is its first marginal expectation. -/
theorem pmfExp_fst (coupling : FiniteCoupling μ ν) (f : α → ℝ) :
    pmfExp coupling.law (fun pair => f pair.1) = pmfExp μ f := by
  calc
    pmfExp coupling.law (fun pair => f pair.1) =
        pmfExp (coupling.law.map Prod.fst) f :=
      (pmfExp_map coupling.law Prod.fst f).symm
    _ = pmfExp μ f := by rw [coupling.fst_marginal]

/-- The second-coordinate expectation of a coupling is its second marginal expectation. -/
theorem pmfExp_snd (coupling : FiniteCoupling μ ν) (g : β → ℝ) :
    pmfExp coupling.law (fun pair => g pair.2) = pmfExp ν g := by
  calc
    pmfExp coupling.law (fun pair => g pair.2) =
        pmfExp (coupling.law.map Prod.snd) g :=
      (pmfExp_map coupling.law Prod.snd g).symm
    _ = pmfExp ν g := by rw [coupling.snd_marginal]

/-- The first-coordinate vector expectation of a coupling is its first marginal expectation. -/
theorem pmfVectorExp_fst {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (coupling : FiniteCoupling μ ν) (f : α → V) :
    pmfVectorExp coupling.law (fun pair => f pair.1) = pmfVectorExp μ f := by
  calc
    pmfVectorExp coupling.law (fun pair => f pair.1) =
        pmfVectorExp (coupling.law.map Prod.fst) f :=
          (pmfVectorExp_map coupling.law Prod.fst f).symm
    _ = pmfVectorExp μ f := by rw [coupling.fst_marginal]

/-- The second-coordinate vector expectation of a coupling is its second marginal expectation. -/
theorem pmfVectorExp_snd {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (coupling : FiniteCoupling μ ν) (g : β → V) :
    pmfVectorExp coupling.law (fun pair => g pair.2) = pmfVectorExp ν g := by
  calc
    pmfVectorExp coupling.law (fun pair => g pair.2) =
        pmfVectorExp (coupling.law.map Prod.snd) g :=
          (pmfVectorExp_map coupling.law Prod.snd g).symm
    _ = pmfVectorExp ν g := by rw [coupling.snd_marginal]

/-- Express a difference of marginal expectations as a joint expectation. -/
theorem pmfExp_sub_eq (coupling : FiniteCoupling μ ν) (f : α → ℝ) (g : β → ℝ) :
    pmfExp μ f - pmfExp ν g =
      pmfExp coupling.law (fun pair => f pair.1 - g pair.2) := by
  rw [← coupling.pmfExp_fst f, ← coupling.pmfExp_snd g, ← pmfExp_sub]

/-- Express a difference of marginal vector expectations as a joint vector expectation. -/
theorem pmfVectorExp_sub_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (coupling : FiniteCoupling μ ν) (f : α → V) (g : β → V) :
    pmfVectorExp μ f - pmfVectorExp ν g =
      pmfVectorExp coupling.law (fun pair => f pair.1 - g pair.2) := by
  rw [← coupling.pmfVectorExp_fst f, ← coupling.pmfVectorExp_snd g]
  unfold pmfVectorExp
  symm
  calc
    ∑ pair, (coupling.law pair).toReal • (f pair.1 - g pair.2) =
        ∑ pair, ((coupling.law pair).toReal • f pair.1 -
          (coupling.law pair).toReal • g pair.2) := by
            apply Finset.sum_congr rfl
            intro pair _
            rw [smul_sub]
    _ = ∑ pair, (coupling.law pair).toReal • f pair.1 -
        ∑ pair, (coupling.law pair).toReal • g pair.2 :=
          by rw [Finset.sum_sub_distrib]

/-- The absolute value of a finite expectation is at most the expectation of the absolute value. -/
theorem abs_pmfExp_le_pmfExp_abs (law : PMF α) (f : α → ℝ) :
    |pmfExp law f| ≤ pmfExp law (fun value => |f value|) := by
  unfold pmfExp
  calc
    |∑ value : α, (law value).toReal * f value|
        ≤ ∑ value : α, |(law value).toReal * f value| :=
      Finset.abs_sum_le_sum_abs (fun value : α => (law value).toReal * f value) Finset.univ
    _ = ∑ value : α, (law value).toReal * |f value| := by
      refine Finset.sum_congr rfl ?_
      intro value _
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]

/-- A uniform pointwise difference bound transfers to finite expectations. -/
theorem abs_pmfExp_sub_le_of_forall_abs_sub_le (law : PMF α) (f g : α → ℝ) (bound : ℝ)
    (hbound : ∀ value, |f value - g value| ≤ bound) :
    |pmfExp law f - pmfExp law g| ≤ bound := by
  rw [← pmfExp_sub]
  calc
    |pmfExp law (fun value => f value - g value)|
        ≤ pmfExp law (fun value => |f value - g value|) :=
      abs_pmfExp_le_pmfExp_abs law _
    _ ≤ pmfExp law (fun _ => bound) :=
      pmfExp_le_pmfExp_of_forall_le law _ _ hbound
    _ = bound := pmfExp_const law bound

/-- A coupling bounds the difference of two expectations by its expected pointwise cost. -/
theorem abs_pmfExp_sub_le_expectedCost (coupling : FiniteCoupling μ ν)
    (f : α → ℝ) (g : β → ℝ) (cost : α → β → ℝ)
    (hcost : ∀ left right, |f left - g right| ≤ cost left right) :
    |pmfExp μ f - pmfExp ν g| ≤ coupling.expectedCost cost := by
  rw [coupling.pmfExp_sub_eq f g]
  calc
    |pmfExp coupling.law (fun pair => f pair.1 - g pair.2)|
        ≤ pmfExp coupling.law (fun pair => |f pair.1 - g pair.2|) :=
      abs_pmfExp_le_pmfExp_abs coupling.law _
    _ ≤ pmfExp coupling.law (fun pair => cost pair.1 pair.2) :=
      pmfExp_le_pmfExp_of_forall_le coupling.law _ _ (fun pair => hcost pair.1 pair.2)
    _ = coupling.expectedCost cost := rfl

/-- A real bound certified by the existence of a finite coupling of at most that cost. -/
def HasExpectedCostLE (μ : PMF α) (ν : PMF β) (cost : α → β → ℝ) (bound : ℝ) : Prop :=
  ∃ coupling : FiniteCoupling μ ν, coupling.expectedCost cost ≤ bound

/-- The point-mass coupling between two deterministic outcomes. -/
noncomputable def pure (left : α) (right : β) :
    FiniteCoupling (PMF.pure left) (PMF.pure right) where
  law := PMF.pure (left, right)
  fst_marginal := PMF.pure_map Prod.fst (left, right)
  snd_marginal := PMF.pure_map Prod.snd (left, right)

/-- A point-mass coupling incurs exactly the cost of its two atoms. -/
@[simp] theorem expectedCost_pure (left : α) (right : β) (cost : α → β → ℝ) :
    (pure left right).expectedCost cost = cost left right := by
  classical
  unfold expectedCost pmfExp pure
  rw [Finset.sum_eq_single (left, right)]
  · simp [PMF.pure_apply]
  · intro pair _ hpair
    simp [PMF.pure_apply, hpair]
  · simp

/--
The deterministic graph coupling of a finite base law and a map.  Its first
marginal is the pushforward and its second marginal is the base law.  This is
the finite counterpart of a Monge transport plan and is useful whenever a
pointwise optimizer is selected for each nominal state.
-/
noncomputable def graph (base : PMF β) (transport : β → α) :
    FiniteCoupling (base.map transport) base where
  law := base.map (fun right => (transport right, right))
  fst_marginal := by
    calc
      (base.map (fun right => (transport right, right))).map Prod.fst =
          base.map (fun right => transport right) := by
        rw [PMF.map_comp]
        congr 1
      _ = base.map transport := rfl
  snd_marginal := by
    calc
      (base.map (fun right => (transport right, right))).map Prod.snd =
          base.map id := by
        rw [PMF.map_comp]
        congr 1
      _ = base := PMF.map_id base

/-- The graph coupling's cost is the base expectation of pointwise transport cost. -/
theorem expectedCost_graph (base : PMF β) (transport : β → α)
    (cost : α → β → ℝ) :
    (graph base transport).expectedCost cost =
      pmfExp base (fun right => cost (transport right) right) := by
  unfold expectedCost graph
  simpa [Function.comp_def] using
    (pmfExp_map base (fun right => (transport right, right))
      (fun pair => cost pair.1 pair.2))

/-- The diagonal finite coupling of a law with itself. -/
noncomputable def diagonal (base : PMF α) : FiniteCoupling base base where
  law := base.map (fun state => (state, state))
  fst_marginal := by
    calc
      (base.map (fun state => (state, state))).map Prod.fst = base.map id := by
        rw [PMF.map_comp]
        congr 1
      _ = base := PMF.map_id base
  snd_marginal := by
    calc
      (base.map (fun state => (state, state))).map Prod.snd = base.map id := by
        rw [PMF.map_comp]
        congr 1
      _ = base := PMF.map_id base

/-- The diagonal coupling averages a cost along its diagonal. -/
theorem expectedCost_diagonal (base : PMF α) (cost : α → α → ℝ) :
    (diagonal base).expectedCost cost = pmfExp base (fun state => cost state state) := by
  unfold expectedCost diagonal
  simpa [Function.comp_def] using
    (pmfExp_map base (fun state => (state, state)) (fun pair => cost pair.1 pair.2))

/-- The independent-product coupling of two finite PMFs. -/
noncomputable def independentCoupling (μ : PMF α) (ν : PMF β) : FiniteCoupling μ ν where
  law := μ.bind fun left => ν.map fun right => (left, right)
  fst_marginal := by
    rw [PMF.map_bind]
    calc
      μ.bind (fun left => PMF.map Prod.fst (PMF.map (fun right => (left, right)) ν)) =
          μ.bind PMF.pure := by
        congr 1
        funext left
        rw [PMF.map_comp]
        change PMF.map (fun _ : β => left) ν = PMF.pure left
        exact PMF.map_const ν left
      _ = μ := PMF.bind_pure μ
  snd_marginal := by
    rw [PMF.map_bind]
    calc
      μ.bind (fun left => PMF.map Prod.snd (PMF.map (fun right => (left, right)) ν)) =
          μ.bind fun _ => ν := by
        congr 1
        funext left
        rw [PMF.map_comp]
        change PMF.map (fun right : β => right) ν = ν
        exact PMF.map_id ν
      _ = ν := PMF.bind_const μ ν

/-- The set of costs achieved by finite couplings of two prescribed PMFs. -/
def transportCostSet (μ : PMF α) (ν : PMF β) (cost : α → β → ℝ) : Set ℝ :=
  {bound | ∃ coupling : FiniteCoupling μ ν, coupling.expectedCost cost = bound}

/-- The finite transport-cost set is nonempty, witnessed by independent sampling. -/
theorem transportCostSet_nonempty (μ : PMF α) (ν : PMF β) (cost : α → β → ℝ) :
    (transportCostSet μ ν cost).Nonempty :=
  ⟨(independentCoupling μ ν).expectedCost cost, ⟨independentCoupling μ ν, rfl⟩⟩

/-- A finite coupling with a pointwise nonnegative cost has nonnegative expected cost. -/
theorem expectedCost_nonneg_of_forall_nonneg
    (coupling : FiniteCoupling μ ν) (cost : α → β → ℝ)
    (hcost : ∀ left right, 0 ≤ cost left right) :
    0 ≤ coupling.expectedCost cost :=
  pmfExp_nonneg_of_forall_nonneg coupling.law _ (fun pair => hcost pair.1 pair.2)

/-- Nonnegative pointwise costs make the corresponding finite transport-cost set bounded below. -/
theorem bddBelow_transportCostSet_of_forall_nonneg
    (cost : α → β → ℝ) (hcost : ∀ left right, 0 ≤ cost left right) :
    BddBelow (transportCostSet μ ν cost) := by
  refine ⟨0, ?_⟩
  intro bound hbound
  rcases hbound with ⟨coupling, rfl⟩
  exact expectedCost_nonneg_of_forall_nonneg coupling cost hcost

/--
The infimum expected cost over finite couplings of two finite PMFs.  Unlike
`finiteWassersteinOne`, this definition permits distinct source and target
types and an arbitrary real-valued cost; nonnegativity is supplied explicitly
to the theorems that need the transport interpretation.
-/
noncomputable def finiteTransportCost
    (μ : PMF α) (ν : PMF β) (cost : α → β → ℝ) : ℝ :=
  sInf (transportCostSet μ ν cost)

/-- Every explicit finite coupling upper-bounds the finite transport infimum. -/
theorem finiteTransportCost_le_expectedCost
    (cost : α → β → ℝ) (hcost : ∀ left right, 0 ≤ cost left right)
    (coupling : FiniteCoupling μ ν) :
    finiteTransportCost μ ν cost ≤ coupling.expectedCost cost := by
  unfold finiteTransportCost
  apply csInf_le
  · exact bddBelow_transportCostSet_of_forall_nonneg cost hcost
  · exact ⟨coupling, rfl⟩

/-- A nonnegative pointwise cost has nonnegative finite transport infimum. -/
theorem finiteTransportCost_nonneg
    (cost : α → β → ℝ) (hcost : ∀ left right, 0 ≤ cost left right) :
    0 ≤ finiteTransportCost μ ν cost := by
  unfold finiteTransportCost
  refine le_csInf (transportCostSet_nonempty μ ν cost) ?_
  intro bound hbound
  rcases hbound with ⟨coupling, rfl⟩
  exact expectedCost_nonneg_of_forall_nonneg coupling cost hcost

/--
A nonnegative cost with zero diagonal gives zero finite transport cost from a
law to itself.  The deterministic identity graph supplies the upper bound;
pointwise nonnegativity supplies the lower bound.
-/
theorem finiteTransportCost_self_eq_zero
    (μ : PMF α) (cost : α → α → ℝ)
    (hcost : ∀ left right, 0 ≤ cost left right)
    (hdiagonal : ∀ state, cost state state = 0) :
    finiteTransportCost μ μ cost = 0 := by
  apply le_antisymm
  · have hgraph := finiteTransportCost_le_expectedCost cost hcost (diagonal μ)
    calc
      finiteTransportCost μ μ cost ≤ (diagonal μ).expectedCost cost := hgraph
      _ = pmfExp μ (fun state => cost state state) := expectedCost_diagonal μ cost
      _ = 0 := by simp [hdiagonal]
  · exact finiteTransportCost_nonneg cost hcost

/--
For every positive tolerance, some finite coupling is within that tolerance of
the transport infimum.  This is the approximation form needed when an
infimum need not yet be represented by a selected optimal coupling.
-/
theorem exists_expectedCost_lt_finiteTransportCost_add
    (cost : α → β → ℝ) (hcost : ∀ left right, 0 ≤ cost left right)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ coupling : FiniteCoupling μ ν,
      coupling.expectedCost cost < finiteTransportCost μ ν cost + epsilon := by
  obtain ⟨bound, hbound_mem, hbound_lt⟩ := exists_lt_of_csInf_lt
    (transportCostSet_nonempty μ ν cost) (by
      change sInf (transportCostSet μ ν cost) < sInf (transportCostSet μ ν cost) + epsilon
      linarith)
  rcases hbound_mem with ⟨coupling, hcoupling⟩
  refine ⟨coupling, ?_⟩
  rw [hcoupling]
  exact hbound_lt

/--
Finite Wasserstein-1: the infimum of expected data distances over finite
couplings of two PMFs.  The results below only use its sound primal direction;
they do not require an attainment or Kantorovich--Rubinstein duality theorem.
-/
noncomputable def finiteWassersteinOne
    {Data : Type*} [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (μ ν : PMF Data) : ℝ :=
  sInf (transportCostSet μ ν (fun left right => dist left right))

/--
The finite-alphabet `ℓ¹` discrepancy between two PMFs, expressed through
their real atom masses.  This deliberately uses the unhalved convention so
that a coordinatewise empirical-mass event converts directly to a bound by
`card Data * ε`.
-/
noncomputable def finiteL1MassDistance
    {Data : Type*} [Fintype Data] [DecidableEq Data]
    (μ ν : PMF Data) : ℝ :=
  ∑ datum : Data, |(μ datum).toReal - (ν datum).toReal|

/-- Coordinatewise control bounds the finite-alphabet `ℓ¹` PMF discrepancy. -/
theorem finiteL1MassDistance_le_card_mul_of_forall_abs_sub_le
    {Data : Type*} [Fintype Data] [DecidableEq Data]
    (μ ν : PMF Data) {epsilon : ℝ}
    (hmass : ∀ datum, |(μ datum).toReal - (ν datum).toReal| ≤ epsilon) :
    finiteL1MassDistance μ ν ≤ (Fintype.card Data : ℝ) * epsilon := by
  unfold finiteL1MassDistance
  calc
    ∑ datum : Data, |(μ datum).toReal - (ν datum).toReal| ≤
        ∑ _datum : Data, epsilon := by
      apply Finset.sum_le_sum
      intro datum _
      exact hmass datum
    _ = (Fintype.card Data : ℝ) * epsilon := by
      simp [Finset.sum_const, nsmul_eq_mul]

private theorem sum_pmf_apply_eq_one
    {Data : Type*} [Fintype Data] [DecidableEq Data] (μ : PMF Data) :
    ∑ datum : Data, μ datum = 1 := by
  simpa only [tsum_fintype] using μ.tsum_coe

private theorem sum_diagonal_indicator
    {Data : Type*} [Fintype Data] [DecidableEq Data]
    (mass : Data → ENNReal) :
    ∑ pair : Data × Data, (if pair.1 = pair.2 then mass pair.1 else 0) =
      ∑ datum : Data, mass datum := by
  rw [Fintype.sum_prod_type]
  simp

private theorem sum_residual_product
    {Data : Type*} [Fintype Data] [DecidableEq Data]
    (left right : Data → ENNReal) (normalizer : ENNReal) :
    ∑ pair : Data × Data, (left pair.1 / normalizer) * right pair.2 =
      (∑ datum : Data, left datum / normalizer) * ∑ datum : Data, right datum := by
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro leftDatum _
  rw [Finset.mul_sum]

private noncomputable def commonMass
    {Data : Type*} (μ ν : PMF Data) (datum : Data) : ENNReal :=
  min (μ datum) (ν datum)

private noncomputable def leftResidualMass
    {Data : Type*} (μ ν : PMF Data) (datum : Data) : ENNReal :=
  μ datum - commonMass μ ν datum

private noncomputable def rightResidualMass
    {Data : Type*} (μ ν : PMF Data) (datum : Data) : ENNReal :=
  ν datum - commonMass μ ν datum

private theorem sum_leftResidualMass
    {Data : Type*} [Fintype Data] [DecidableEq Data] (μ ν : PMF Data) :
    ∑ datum : Data, leftResidualMass μ ν datum =
      1 - ∑ datum : Data, commonMass μ ν datum := by
  apply ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top
  calc
    ∑ datum : Data, leftResidualMass μ ν datum +
        ∑ datum : Data, commonMass μ ν datum =
        ∑ datum : Data, (leftResidualMass μ ν datum + commonMass μ ν datum) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ datum : Data, μ datum := by
      apply Finset.sum_congr rfl
      intro datum _
      unfold leftResidualMass commonMass
      exact tsub_add_cancel_of_le (min_le_left _ _)
    _ = 1 := sum_pmf_apply_eq_one μ

private theorem sum_rightResidualMass
    {Data : Type*} [Fintype Data] [DecidableEq Data] (μ ν : PMF Data) :
    ∑ datum : Data, rightResidualMass μ ν datum =
      1 - ∑ datum : Data, commonMass μ ν datum := by
  apply ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top
  calc
    ∑ datum : Data, rightResidualMass μ ν datum +
        ∑ datum : Data, commonMass μ ν datum =
        ∑ datum : Data, (rightResidualMass μ ν datum + commonMass μ ν datum) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ datum : Data, ν datum := by
      apply Finset.sum_congr rfl
      intro datum _
      unfold rightResidualMass commonMass
      exact tsub_add_cancel_of_le (min_le_right _ _)
    _ = 1 := sum_pmf_apply_eq_one ν

private theorem leftResidualMass_sum_ne_zero_of_ne
    {Data : Type*} [Fintype Data] [DecidableEq Data] {μ ν : PMF Data}
    (hneq : μ ≠ ν) : ∑ datum : Data, leftResidualMass μ ν datum ≠ 0 := by
  intro hsum_zero
  have hright_sum_zero : ∑ datum : Data, rightResidualMass μ ν datum = 0 := by
    rw [sum_rightResidualMass, ← sum_leftResidualMass μ ν]
    exact hsum_zero
  have hleft_zero : ∀ datum : Data, leftResidualMass μ ν datum = 0 := by
    intro datum
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => bot_le)).mp hsum_zero datum
      (Finset.mem_univ _)
  have hright_zero : ∀ datum : Data, rightResidualMass μ ν datum = 0 := by
    intro datum
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => bot_le)).mp hright_sum_zero datum
      (Finset.mem_univ _)
  apply hneq
  apply PMF.ext
  intro datum
  apply le_antisymm
  · have h := (tsub_eq_zero_iff_le.mp (hleft_zero datum))
    exact h.trans (min_le_right _ _)
  · have h := (tsub_eq_zero_iff_le.mp (hright_zero datum))
    exact h.trans (min_le_left _ _)

private theorem leftResidualMass_sum_ne_top
    {Data : Type*} [Fintype Data] [DecidableEq Data] (μ ν : PMF Data) :
    (∑ datum : Data, leftResidualMass μ ν datum) ≠ ⊤ := by
  rw [sum_leftResidualMass]
  exact ENNReal.sub_ne_top ENNReal.one_ne_top

private theorem sum_leftResidualMass_div_self
    {Data : Type*} [Fintype Data] [DecidableEq Data] {μ ν : PMF Data}
    (hneq : μ ≠ ν) :
    ∑ datum : Data,
      leftResidualMass μ ν datum /
        (∑ other : Data, leftResidualMass μ ν other) = 1 := by
  let residualTotal : ENNReal := ∑ datum : Data, leftResidualMass μ ν datum
  have htotal_nonzero : residualTotal ≠ 0 := by
    exact leftResidualMass_sum_ne_zero_of_ne hneq
  have htotal_finite : residualTotal ≠ ⊤ := by
    exact leftResidualMass_sum_ne_top μ ν
  change ∑ datum : Data, leftResidualMass μ ν datum / residualTotal = 1
  calc
    ∑ datum : Data, leftResidualMass μ ν datum / residualTotal =
        (∑ datum : Data, leftResidualMass μ ν datum) * residualTotal⁻¹ := by
          simp only [div_eq_mul_inv, ← Finset.sum_mul]
    _ = residualTotal * residualTotal⁻¹ := by rfl
    _ = 1 := ENNReal.mul_inv_cancel htotal_nonzero htotal_finite

private theorem commonMass_sum_le_one
    {Data : Type*} [Fintype Data] [DecidableEq Data] (μ ν : PMF Data) :
    ∑ datum : Data, commonMass μ ν datum ≤ 1 := by
  calc
    ∑ datum : Data, commonMass μ ν datum ≤ ∑ datum : Data, μ datum := by
      apply Finset.sum_le_sum
      intro datum _
      exact min_le_left _ _
    _ = 1 := sum_pmf_apply_eq_one μ

private noncomputable def residualCouplingLaw
    {Data : Type*} [Fintype Data] [DecidableEq Data]
    (μ ν : PMF Data) (hneq : μ ≠ ν) : PMF (Data × Data) :=
  PMF.ofFintype
    (fun pair =>
      (if pair.1 = pair.2 then commonMass μ ν pair.1 else 0) +
        (leftResidualMass μ ν pair.1 /
          (∑ datum : Data, leftResidualMass μ ν datum)) *
            rightResidualMass μ ν pair.2)
    (by
      calc
        ∑ pair : Data × Data,
            ((if pair.1 = pair.2 then commonMass μ ν pair.1 else 0) +
              (leftResidualMass μ ν pair.1 /
                (∑ datum : Data, leftResidualMass μ ν datum)) *
                  rightResidualMass μ ν pair.2) =
            (∑ pair : Data × Data,
              if pair.1 = pair.2 then commonMass μ ν pair.1 else 0) +
              ∑ pair : Data × Data,
                (leftResidualMass μ ν pair.1 /
                  (∑ datum : Data, leftResidualMass μ ν datum)) *
                    rightResidualMass μ ν pair.2 := by
              rw [Finset.sum_add_distrib]
        _ = (∑ datum : Data, commonMass μ ν datum) +
              (∑ datum : Data,
                leftResidualMass μ ν datum /
                  (∑ other : Data, leftResidualMass μ ν other)) *
                ∑ datum : Data, rightResidualMass μ ν datum := by
              rw [sum_diagonal_indicator, sum_residual_product]
        _ = (∑ datum : Data, commonMass μ ν datum) +
              (1 - ∑ datum : Data, commonMass μ ν datum) := by
              rw [sum_leftResidualMass_div_self hneq, sum_rightResidualMass]
              simp
        _ = 1 := add_tsub_cancel_of_le (commonMass_sum_le_one μ ν))

private theorem residualCouplingLaw_fst_marginal
    {Data : Type*} [Fintype Data] [DecidableEq Data] (μ ν : PMF Data)
    (hneq : μ ≠ ν) :
    (residualCouplingLaw μ ν hneq).map Prod.fst = μ := by
  apply PMF.ext
  intro datum
  simp only [PMF.map_apply, tsum_fintype]
  rw [Fintype.sum_prod_type]
  simp only [residualCouplingLaw, PMF.ofFintype_apply]
  let density : Data → Data → ENNReal := fun left right =>
    (if left = right then commonMass μ ν left else 0) +
      (leftResidualMass μ ν left /
        (∑ other : Data, leftResidualMass μ ν other)) * rightResidualMass μ ν right
  change (∑ left : Data, ∑ right : Data,
    if datum = left then density left right else 0) = μ datum
  have htotal_nonzero : (∑ other : Data, leftResidualMass μ ν other) ≠ 0 :=
    leftResidualMass_sum_ne_zero_of_ne hneq
  have htotal_finite : (∑ other : Data, leftResidualMass μ ν other) ≠ ⊤ :=
    leftResidualMass_sum_ne_top μ ν
  have hright_total : (∑ other : Data, rightResidualMass μ ν other) =
      ∑ other : Data, leftResidualMass μ ν other := by
    calc
      (∑ other : Data, rightResidualMass μ ν other) =
          1 - ∑ other : Data, commonMass μ ν other := sum_rightResidualMass μ ν
      _ = ∑ other : Data, leftResidualMass μ ν other := (sum_leftResidualMass μ ν).symm
  calc
    (∑ left : Data, ∑ right : Data,
        if datum = left then density left right else 0) =
        ∑ left : Data, if datum = left then ∑ right : Data, density left right else 0 := by
          apply Finset.sum_congr rfl
          intro left _
          by_cases hleft : datum = left <;> simp [hleft]
    _ = ∑ right : Data, density datum right := Fintype.sum_ite_eq _ _
    _ = μ datum := by
      dsimp [density]
      rw [Finset.sum_add_distrib, Fintype.sum_ite_eq, ← Finset.mul_sum,
        hright_total, ENNReal.div_mul_cancel htotal_nonzero htotal_finite]
      unfold leftResidualMass commonMass
      rw [add_comm]
      exact tsub_add_cancel_of_le (min_le_left (μ datum) (ν datum))

private theorem residualCouplingLaw_snd_marginal
    {Data : Type*} [Fintype Data] [DecidableEq Data] (μ ν : PMF Data)
    (hneq : μ ≠ ν) :
    (residualCouplingLaw μ ν hneq).map Prod.snd = ν := by
  apply PMF.ext
  intro datum
  simp only [PMF.map_apply, tsum_fintype]
  rw [Fintype.sum_prod_type]
  simp only [residualCouplingLaw, PMF.ofFintype_apply]
  let density : Data → Data → ENNReal := fun left right =>
    (if left = right then commonMass μ ν left else 0) +
      (leftResidualMass μ ν left /
        (∑ other : Data, leftResidualMass μ ν other)) * rightResidualMass μ ν right
  change (∑ left : Data, ∑ right : Data,
    if datum = right then density left right else 0) = ν datum
  calc
    (∑ left : Data, ∑ right : Data,
        if datum = right then density left right else 0) =
        ∑ left : Data, density left datum := by
          apply Finset.sum_congr rfl
          intro left _
          exact Fintype.sum_ite_eq _ _
    _ = ν datum := by
      dsimp [density]
      rw [Finset.sum_add_distrib, Fintype.sum_ite_eq', ← Finset.sum_mul,
        sum_leftResidualMass_div_self hneq]
      simp only [one_mul]
      unfold rightResidualMass commonMass
      rw [add_comm]
      exact tsub_add_cancel_of_le (min_le_right (μ datum) (ν datum))

private noncomputable def residualCoupling
    {Data : Type*} [Fintype Data] [DecidableEq Data]
    (μ ν : PMF Data) (hneq : μ ≠ ν) : FiniteCoupling μ ν where
  law := residualCouplingLaw μ ν hneq
  fst_marginal := residualCouplingLaw_fst_marginal μ ν hneq
  snd_marginal := residualCouplingLaw_snd_marginal μ ν hneq

private theorem sum_residualJointMass
    {Data : Type*} [Fintype Data] [DecidableEq Data] {μ ν : PMF Data}
    (hneq : μ ≠ ν) :
    ∑ pair : Data × Data,
      (leftResidualMass μ ν pair.1 /
        (∑ datum : Data, leftResidualMass μ ν datum)) * rightResidualMass μ ν pair.2 =
      ∑ datum : Data, leftResidualMass μ ν datum := by
  rw [sum_residual_product, sum_leftResidualMass_div_self hneq]
  calc
    (1 : ENNReal) * ∑ datum : Data, rightResidualMass μ ν datum =
        ∑ datum : Data, rightResidualMass μ ν datum := one_mul _
    _ = 1 - ∑ datum : Data, commonMass μ ν datum := sum_rightResidualMass μ ν
    _ = ∑ datum : Data, leftResidualMass μ ν datum := (sum_leftResidualMass μ ν).symm

private theorem residualJointMass_ne_top
    {Data : Type*} [Fintype Data] [DecidableEq Data]
    (μ ν : PMF Data) {pair : Data × Data}
    (hneq : μ ≠ ν) :
    (leftResidualMass μ ν pair.1 /
      (∑ datum : Data, leftResidualMass μ ν datum)) * rightResidualMass μ ν pair.2 ≠ ⊤ := by
  apply ENNReal.mul_ne_top
  · apply ENNReal.div_ne_top
    · unfold leftResidualMass
      exact ENNReal.sub_ne_top (μ.apply_ne_top _)
    · exact leftResidualMass_sum_ne_zero_of_ne hneq
  · unfold rightResidualMass
    exact ENNReal.sub_ne_top (ν.apply_ne_top _)

private theorem residualCoupling_expectedCost_le_diameter_mul_residualMass
    {Data : Type*} [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (μ ν : PMF Data) (hneq : μ ≠ ν) (diameter : ℝ)
    (hdiameter : ∀ left right : Data, dist left right ≤ diameter) :
    (residualCoupling μ ν hneq).expectedCost (fun left right => dist left right) ≤
      diameter * (∑ datum : Data, leftResidualMass μ ν datum).toReal := by
  have hdiameter_nonneg : 0 ≤ diameter := by
    obtain ⟨datum, _⟩ := μ.support_nonempty
    simpa using hdiameter datum datum
  have hpointwise : ∀ pair : Data × Data,
      ((residualCouplingLaw μ ν hneq pair).toReal) * dist pair.1 pair.2 ≤
        diameter * ((leftResidualMass μ ν pair.1 /
          (∑ datum : Data, leftResidualMass μ ν datum)) *
            rightResidualMass μ ν pair.2).toReal := by
    rintro ⟨left, right⟩
    by_cases hsame : left = right
    · subst right
      rw [dist_self, mul_zero]
      exact mul_nonneg hdiameter_nonneg ENNReal.toReal_nonneg
    · simp only [residualCouplingLaw, PMF.ofFintype_apply, if_neg hsame, zero_add]
      calc
        ((leftResidualMass μ ν left /
          (∑ datum : Data, leftResidualMass μ ν datum)) *
            rightResidualMass μ ν right).toReal * dist left right ≤
            ((leftResidualMass μ ν left /
              (∑ datum : Data, leftResidualMass μ ν datum)) *
                rightResidualMass μ ν right).toReal * diameter :=
              mul_le_mul_of_nonneg_left (hdiameter left right) ENNReal.toReal_nonneg
        _ = diameter * ((leftResidualMass μ ν left /
          (∑ datum : Data, leftResidualMass μ ν datum)) *
            rightResidualMass μ ν right).toReal := by ring
  unfold expectedCost residualCoupling
  calc
    ∑ pair : Data × Data, (residualCouplingLaw μ ν hneq pair).toReal *
        dist pair.1 pair.2 ≤
        ∑ pair : Data × Data, diameter *
          ((leftResidualMass μ ν pair.1 /
            (∑ datum : Data, leftResidualMass μ ν datum)) *
              rightResidualMass μ ν pair.2).toReal := by
            apply Finset.sum_le_sum
            intro pair _
            exact hpointwise pair
    _ = diameter * ∑ pair : Data × Data,
        ((leftResidualMass μ ν pair.1 /
          (∑ datum : Data, leftResidualMass μ ν datum)) *
            rightResidualMass μ ν pair.2).toReal := by
          rw [Finset.mul_sum]
    _ = diameter * (∑ datum : Data, leftResidualMass μ ν datum).toReal := by
      congr 1
      rw [← ENNReal.toReal_sum]
      · exact congrArg ENNReal.toReal (sum_residualJointMass hneq)
      · intro pair _
        exact residualJointMass_ne_top μ ν hneq

private theorem leftResidualMass_ne_top
    {Data : Type*} (μ ν : PMF Data) (datum : Data) :
    leftResidualMass μ ν datum ≠ ⊤ := by
  unfold leftResidualMass
  exact ENNReal.sub_ne_top (μ.apply_ne_top _)

private theorem leftResidualMass_toReal_le_abs_massDifference
    {Data : Type*} (μ ν : PMF Data) (datum : Data) :
    (leftResidualMass μ ν datum).toReal ≤
      |(μ datum).toReal - (ν datum).toReal| := by
  by_cases hle : μ datum ≤ ν datum
  · have hcommon : commonMass μ ν datum = μ datum := by
      unfold commonMass
      exact min_eq_left hle
    rw [show leftResidualMass μ ν datum = 0 by
      unfold leftResidualMass
      rw [hcommon, tsub_self], ENNReal.toReal_zero]
    exact abs_nonneg _
  · have hle' : ν datum ≤ μ datum := le_of_lt (lt_of_not_ge hle)
    have hcommon : commonMass μ ν datum = ν datum := by
      unfold commonMass
      exact min_eq_right hle'
    rw [show leftResidualMass μ ν datum = μ datum - ν datum by
      unfold leftResidualMass
      rw [hcommon], ENNReal.toReal_sub_of_le hle' (μ.apply_ne_top _),
      abs_of_nonneg]
    exact sub_nonneg.mpr (ENNReal.toReal_mono (μ.apply_ne_top datum) hle')

private theorem leftResidualMass_total_toReal_le_finiteL1MassDistance
    {Data : Type*} [Fintype Data] [DecidableEq Data] (μ ν : PMF Data) :
    (∑ datum : Data, leftResidualMass μ ν datum).toReal ≤ finiteL1MassDistance μ ν := by
  have hsum : (∑ datum : Data, leftResidualMass μ ν datum).toReal =
      ∑ datum : Data, (leftResidualMass μ ν datum).toReal := by
    simpa using ENNReal.toReal_sum (s := (Finset.univ : Finset Data))
      (f := fun datum => leftResidualMass μ ν datum)
      (fun datum _ => leftResidualMass_ne_top μ ν datum)
  rw [hsum]
  unfold finiteL1MassDistance
  apply Finset.sum_le_sum
  intro datum _
  exact leftResidualMass_toReal_le_abs_massDifference μ ν datum

private noncomputable def diagonalCoupling
    {Data : Type*} [Fintype Data] [DecidableEq Data] (μ : PMF Data) :
    FiniteCoupling μ μ where
  law := μ.map fun datum => (datum, datum)
  fst_marginal := by
    rw [PMF.map_comp]
    simpa [Function.comp_def] using (PMF.map_id μ)
  snd_marginal := by
    rw [PMF.map_comp]
    simpa [Function.comp_def] using (PMF.map_id μ)

private theorem diagonalCoupling_expectedCost_zero
    {Data : Type*} [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (μ : PMF Data) :
    (diagonalCoupling μ).expectedCost (fun left right => dist left right) = 0 := by
  unfold expectedCost diagonalCoupling
  rw [pmfExp_map]
  simp

/-- Every explicit finite coupling upper-bounds the finite Wasserstein-1 infimum. -/
theorem finiteWassersteinOne_le_expectedCost
    {Data : Type*} [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    {μ ν : PMF Data} (coupling : FiniteCoupling μ ν) :
    finiteWassersteinOne μ ν ≤ coupling.expectedCost (fun left right => dist left right) := by
  unfold finiteWassersteinOne
  apply csInf_le
  · exact bddBelow_transportCostSet_of_forall_nonneg _ (fun _ _ => dist_nonneg)
  · exact ⟨coupling, rfl⟩

/--
On a finite metric alphabet, primal Wasserstein-1 is bounded by the diameter
times the unhalved `ℓ¹` discrepancy of the atom masses.  The proof constructs
the maximal common-mass coupling explicitly, so it does not rely on an
unavailable transport-duality theorem.
-/
theorem finiteWassersteinOne_le_diameter_mul_finiteL1MassDistance
    {Data : Type*} [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (μ ν : PMF Data) (diameter : ℝ)
    (hdiameter : ∀ left right : Data, dist left right ≤ diameter) :
    finiteWassersteinOne μ ν ≤ diameter * finiteL1MassDistance μ ν := by
  have hdiameter_nonneg : 0 ≤ diameter := by
    obtain ⟨datum, _⟩ := μ.support_nonempty
    simpa using hdiameter datum datum
  by_cases heq : μ = ν
  · subst ν
    have hzero : finiteL1MassDistance μ μ = 0 := by
      unfold finiteL1MassDistance
      simp
    rw [hzero, mul_zero]
    calc
      finiteWassersteinOne μ μ ≤
          (diagonalCoupling μ).expectedCost (fun left right => dist left right) :=
        finiteWassersteinOne_le_expectedCost (diagonalCoupling μ)
      _ = 0 := diagonalCoupling_expectedCost_zero μ
  · calc
      finiteWassersteinOne μ ν ≤
          (residualCoupling μ ν heq).expectedCost (fun left right => dist left right) :=
        finiteWassersteinOne_le_expectedCost (residualCoupling μ ν heq)
      _ ≤ diameter * (∑ datum : Data, leftResidualMass μ ν datum).toReal :=
        residualCoupling_expectedCost_le_diameter_mul_residualMass μ ν heq diameter hdiameter
      _ ≤ diameter * finiteL1MassDistance μ ν :=
        mul_le_mul_of_nonneg_left
          (leftResidualMass_total_toReal_le_finiteL1MassDistance μ ν) hdiameter_nonneg

/-- A coordinatewise finite-PMF mass bound yields an explicit finite W₁ bound. -/
theorem finiteWassersteinOne_le_diameter_card_mul_of_forall_abs_sub_le
    {Data : Type*} [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (μ ν : PMF Data) (diameter : ℝ)
    (hdiameter : ∀ left right : Data, dist left right ≤ diameter)
    {epsilon : ℝ}
    (hmass : ∀ datum, |(μ datum).toReal - (ν datum).toReal| ≤ epsilon) :
    finiteWassersteinOne μ ν ≤ diameter * ((Fintype.card Data : ℝ) * epsilon) := by
  have hdiameter_nonneg : 0 ≤ diameter := by
    obtain ⟨datum, _⟩ := μ.support_nonempty
    simpa using hdiameter datum datum
  calc
    finiteWassersteinOne μ ν ≤ diameter * finiteL1MassDistance μ ν :=
      finiteWassersteinOne_le_diameter_mul_finiteL1MassDistance μ ν diameter hdiameter
    _ ≤ diameter * ((Fintype.card Data : ℝ) * epsilon) :=
      mul_le_mul_of_nonneg_left
        (finiteL1MassDistance_le_card_mul_of_forall_abs_sub_le μ ν hmass)
        hdiameter_nonneg

/-- An explicit transport-cost certificate yields the associated finite W₁ bound. -/
theorem finiteWassersteinOne_le_of_expectedCostLE
    {Data : Type*} [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    {μ ν : PMF Data} {bound : ℝ}
    (htransport : HasExpectedCostLE μ ν (fun left right => dist left right) bound) :
    finiteWassersteinOne μ ν ≤ bound := by
  obtain ⟨coupling, hbound⟩ := htransport
  exact (finiteWassersteinOne_le_expectedCost coupling).trans hbound

/--
Finite Wasserstein-1 controls the change of expectation of a Lipschitz test
function.  The proof uses only the defining infimum over finite couplings: if
the asserted bound failed, a coupling whose cost lies strictly below the
resulting quotient would contradict the coupling-wise estimate.
-/
theorem abs_pmfExp_sub_le_lipschitz_finiteWassersteinOne
    {Data : Type*} [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    {μ ν : PMF Data} {L : NNReal} {f : Data → ℝ} (hf : LipschitzWith L f) :
    |pmfExp μ f - pmfExp ν f| ≤
      (L : ℝ) * finiteWassersteinOne μ ν := by
  have hcoupling_bound : ∀ coupling : FiniteCoupling μ ν,
      |pmfExp μ f - pmfExp ν f| ≤
        (L : ℝ) * coupling.expectedCost (fun left right => dist left right) := by
    intro coupling
    calc
      |pmfExp μ f - pmfExp ν f|
          ≤ coupling.expectedCost (fun left right => (L : ℝ) * dist left right) :=
        coupling.abs_pmfExp_sub_le_expectedCost f f _ (fun left right => by
          simpa [Real.dist_eq] using hf.dist_le_mul left right)
      _ = (L : ℝ) * coupling.expectedCost (fun left right => dist left right) := by
        change pmfExp coupling.law (fun pair => (L : ℝ) * dist pair.1 pair.2) =
          (L : ℝ) * pmfExp coupling.law (fun pair => dist pair.1 pair.2)
        exact pmfExp_const_mul coupling.law (L : ℝ) _
  by_cases hLzero : (L : ℝ) = 0
  · have hzero :
        |pmfExp μ f - pmfExp ν f| ≤
          (L : ℝ) * (independentCoupling μ ν).expectedCost
            (fun left right => dist left right) :=
      hcoupling_bound (independentCoupling μ ν)
    simpa [hLzero] using hzero
  · have hLpos : 0 < (L : ℝ) := lt_of_le_of_ne (by positivity) (Ne.symm hLzero)
    by_contra hbound
    have hstrict : (L : ℝ) * finiteWassersteinOne μ ν < |pmfExp μ f - pmfExp ν f| :=
      lt_of_not_ge hbound
    have hinf_lt : finiteWassersteinOne μ ν <
        |pmfExp μ f - pmfExp ν f| / (L : ℝ) := by
      apply (lt_div_iff₀ hLpos).mpr
      simpa [mul_comm] using hstrict
    obtain ⟨cost, hcost_mem, hcost_lt⟩ := exists_lt_of_csInf_lt
      (transportCostSet_nonempty μ ν (fun left right => dist left right)) (by
        simpa [finiteWassersteinOne] using hinf_lt)
    rcases hcost_mem with ⟨coupling, hcost_eq⟩
    have hcoupling : |pmfExp μ f - pmfExp ν f| ≤
        (L : ℝ) * coupling.expectedCost (fun left right => dist left right) :=
      hcoupling_bound coupling
    have hcost_strict : (L : ℝ) * coupling.expectedCost
        (fun left right => dist left right) < |pmfExp μ f - pmfExp ν f| := by
      rw [hcost_eq]
      calc
        (L : ℝ) * cost < (L : ℝ) *
            (|pmfExp μ f - pmfExp ν f| / (L : ℝ)) :=
          mul_lt_mul_of_pos_left hcost_lt hLpos
        _ = |pmfExp μ f - pmfExp ν f| := by
          field_simp [hLzero]
    exact (not_lt_of_ge hcoupling) hcost_strict

/--
Finite Wasserstein-1 controls the norm of the change of a Lipschitz vector
expectation.  As for the scalar result, no optimal coupling or transport-dual
theorem is needed: the conclusion follows directly from the infimum defining
`finiteWassersteinOne` and the coupling-wise vector estimate.
-/
theorem norm_pmfVectorExp_sub_le_lipschitz_finiteWassersteinOne
    {Data V : Type*} [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {μ ν : PMF Data} {L : NNReal} {f : Data → V} (hf : LipschitzWith L f) :
    ‖pmfVectorExp μ f - pmfVectorExp ν f‖ ≤
      (L : ℝ) * finiteWassersteinOne μ ν := by
  have hcoupling_bound : ∀ coupling : FiniteCoupling μ ν,
      ‖pmfVectorExp μ f - pmfVectorExp ν f‖ ≤
        (L : ℝ) * coupling.expectedCost (fun left right => dist left right) := by
    intro coupling
    rw [coupling.pmfVectorExp_sub_eq f f]
    calc
      ‖pmfVectorExp coupling.law (fun pair => f pair.1 - f pair.2)‖ ≤
          pmfExp coupling.law (fun pair => ‖f pair.1 - f pair.2‖) :=
        norm_pmfVectorExp_le_pmfExp_norm coupling.law _
      _ ≤ pmfExp coupling.law (fun pair => (L : ℝ) * dist pair.1 pair.2) :=
        pmfExp_le_pmfExp_of_forall_le coupling.law _ _ (fun pair => by
          simpa only [dist_eq_norm] using hf.dist_le_mul pair.1 pair.2)
      _ = (L : ℝ) * coupling.expectedCost (fun left right => dist left right) := by
        change pmfExp coupling.law (fun pair => (L : ℝ) * dist pair.1 pair.2) =
          (L : ℝ) * pmfExp coupling.law (fun pair => dist pair.1 pair.2)
        exact pmfExp_const_mul coupling.law (L : ℝ) _
  by_cases hLzero : (L : ℝ) = 0
  · have hzero :
        ‖pmfVectorExp μ f - pmfVectorExp ν f‖ ≤
          (L : ℝ) * (independentCoupling μ ν).expectedCost
            (fun left right => dist left right) :=
      hcoupling_bound (independentCoupling μ ν)
    simpa [hLzero] using hzero
  · have hLpos : 0 < (L : ℝ) := lt_of_le_of_ne (by positivity) (Ne.symm hLzero)
    by_contra hbound
    have hstrict : (L : ℝ) * finiteWassersteinOne μ ν <
        ‖pmfVectorExp μ f - pmfVectorExp ν f‖ :=
      lt_of_not_ge hbound
    have hinf_lt : finiteWassersteinOne μ ν <
        ‖pmfVectorExp μ f - pmfVectorExp ν f‖ / (L : ℝ) := by
      apply (lt_div_iff₀ hLpos).mpr
      simpa [mul_comm] using hstrict
    obtain ⟨cost, hcost_mem, hcost_lt⟩ := exists_lt_of_csInf_lt
      (transportCostSet_nonempty μ ν (fun left right => dist left right)) (by
        simpa [finiteWassersteinOne] using hinf_lt)
    rcases hcost_mem with ⟨coupling, hcost_eq⟩
    have hcoupling : ‖pmfVectorExp μ f - pmfVectorExp ν f‖ ≤
        (L : ℝ) * coupling.expectedCost (fun left right => dist left right) :=
      hcoupling_bound coupling
    have hcost_strict : (L : ℝ) * coupling.expectedCost
        (fun left right => dist left right) < ‖pmfVectorExp μ f - pmfVectorExp ν f‖ := by
      rw [hcost_eq]
      calc
        (L : ℝ) * cost < (L : ℝ) *
            (‖pmfVectorExp μ f - pmfVectorExp ν f‖ / (L : ℝ)) :=
          mul_lt_mul_of_pos_left hcost_lt hLpos
        _ = ‖pmfVectorExp μ f - pmfVectorExp ν f‖ := by
          field_simp [hLzero]
    exact (not_lt_of_ge hcoupling) hcost_strict

/--
The joint law coupling Bernoulli probabilities `p ≤ q` by sharing their `true`
mass and assigning the excess `q - p` only to `(false, true)`.
-/
noncomputable def monotoneBernoulliLaw (p q : NNReal) (hpq : p ≤ q) (hq : q ≤ 1) :
    PMF (Bool × Bool) :=
  PMF.ofFintype (fun pair =>
    if pair = (true, true) then p
    else if pair = (false, true) then q - p
    else if pair = (false, false) then 1 - q
    else 0) (by
      rw [Fintype.sum_prod_type]
      simp
      have hsum : p + (q - p) + (1 - q) = 1 := by
        rw [add_tsub_cancel_of_le hpq, add_tsub_cancel_of_le hq]
      exact_mod_cast (by simpa [add_assoc] using hsum))

/--
The monotone Bernoulli joint law has the two intended Bernoulli marginals.
-/
noncomputable def monotoneBernoulliCoupling
    (p q : NNReal) (hpq : p ≤ q) (hp : p ≤ 1) (hq : q ≤ 1) :
    FiniteCoupling (PMF.bernoulli p hp) (PMF.bernoulli q hq) where
  law := monotoneBernoulliLaw p q hpq hq
  fst_marginal := by
    apply PMF.ext
    intro outcome
    fin_cases outcome <;>
      simp only [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool]
    · simp [monotoneBernoulliLaw]
    · simp [monotoneBernoulliLaw]
      have hsum : (q - p) + (1 - q) = 1 - p := by
        rw [add_comm]
        exact tsub_add_tsub_cancel hq hpq
      exact_mod_cast hsum
  snd_marginal := by
    apply PMF.ext
    intro outcome
    fin_cases outcome <;>
      simp only [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool]
    · simp [monotoneBernoulliLaw]
      have hsum : p + (q - p) = q := add_tsub_cancel_of_le hpq
      exact_mod_cast hsum
    · simp [monotoneBernoulliLaw]

/--
Lift pointwise couplings of conditional laws through a shared finite base law.
The result couples the two resulting mixture laws while preserving the common
latent base coordinate.
-/
noncomputable def bindSharedBase
    {A B C : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (base : PMF A) (left : A → PMF B) (right : A → PMF C)
    (fiber : ∀ index, FiniteCoupling (left index) (right index)) :
    FiniteCoupling (base.bind left) (base.bind right) where
  law := base.bind fun index => (fiber index).law.map
    (fun pair => (pair.1, pair.2))
  fst_marginal := by
    rw [PMF.map_bind]
    congr 1
    funext index
    rw [PMF.map_comp]
    simpa [Function.comp_def] using (fiber index).fst_marginal
  snd_marginal := by
    rw [PMF.map_bind]
    congr 1
    funext index
    rw [PMF.map_comp]
    simpa [Function.comp_def] using (fiber index).snd_marginal

/--
Push a finite coupling forward along independent maps of its two coordinates.
This is the finite analogue of mapping a transport plan.
-/
noncomputable def map
    {γ δ : Type*} [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (coupling : FiniteCoupling μ ν) (leftMap : α → γ) (rightMap : β → δ) :
    FiniteCoupling (μ.map leftMap) (ν.map rightMap) where
  law := coupling.law.map (fun pair => (leftMap pair.1, rightMap pair.2))
  fst_marginal := by
    calc
      (coupling.law.map (fun pair => (leftMap pair.1, rightMap pair.2))).map Prod.fst =
          coupling.law.map (fun pair => leftMap pair.1) := by
            rw [PMF.map_comp]
            congr 1
      _ = (coupling.law.map Prod.fst).map leftMap := by
            rw [PMF.map_comp]
            congr 1
      _ = μ.map leftMap := by rw [coupling.fst_marginal]
  snd_marginal := by
    calc
      (coupling.law.map (fun pair => (leftMap pair.1, rightMap pair.2))).map Prod.snd =
          coupling.law.map (fun pair => rightMap pair.2) := by
            rw [PMF.map_comp]
            congr 1
      _ = (coupling.law.map Prod.snd).map rightMap := by
            rw [PMF.map_comp]
            congr 1
      _ = ν.map rightMap := by rw [coupling.snd_marginal]

/-- Reverse the two coordinates of a finite coupling. -/
noncomputable def swap (coupling : FiniteCoupling μ ν) : FiniteCoupling ν μ where
  law := coupling.law.map (fun pair => (pair.2, pair.1))
  fst_marginal := by
    rw [PMF.map_comp]
    simpa [Function.comp_def] using coupling.snd_marginal
  snd_marginal := by
    rw [PMF.map_comp]
    simpa [Function.comp_def] using coupling.fst_marginal

/-- The cost of a mapped coupling is the original cost pulled back to its coordinates. -/
theorem expectedCost_map
    {γ δ : Type*} [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (coupling : FiniteCoupling μ ν) (leftMap : α → γ) (rightMap : β → δ)
    (cost : γ → δ → ℝ) :
    (coupling.map leftMap rightMap).expectedCost cost =
      coupling.expectedCost (fun left right => cost (leftMap left) (rightMap right)) := by
  unfold expectedCost map
  simpa [Function.comp_def] using
    (pmfExp_map coupling.law (fun pair => (leftMap pair.1, rightMap pair.2))
      (fun pair => cost pair.1 pair.2))

/-- Reversing a coupling reverses the arguments of its cost function. -/
theorem expectedCost_swap (coupling : FiniteCoupling μ ν) (cost : β → α → ℝ) :
    coupling.swap.expectedCost cost =
      coupling.expectedCost (fun left right => cost right left) := by
  unfold expectedCost swap
  simpa [Function.comp_def] using
    (pmfExp_map coupling.law (fun pair => (pair.2, pair.1))
      (fun pair => cost pair.1 pair.2))

/-- The cost of a shared-base mixture coupling is the base expectation of its fiber costs. -/
theorem expectedCost_bindSharedBase
    {A B C : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (base : PMF A) (left : A → PMF B) (right : A → PMF C)
    (fiber : ∀ index, FiniteCoupling (left index) (right index))
    (cost : B → C → ℝ) :
    (bindSharedBase base left right fiber).expectedCost cost =
      pmfExp base (fun index => (fiber index).expectedCost cost) := by
  unfold expectedCost bindSharedBase
  rw [pmfExp_bind]
  apply pmfExp_congr
  intro index
  simpa [Function.comp_def] using
    (pmfExp_map (fiber index).law (fun pair => (pair.1, pair.2))
      (fun pair => cost pair.1 pair.2))

/--
The ordered Bernoulli coupling's expected zero-one mismatch cost is exactly
the difference of its true probabilities.
-/
theorem expectedCost_monotoneBernoulliCoupling
    (p q : NNReal) (hpq : p ≤ q) (hp : p ≤ 1) (hq : q ≤ 1) :
    (monotoneBernoulliCoupling p q hpq hp hq).expectedCost
      (fun first second : Bool => if first = second then (0 : ℝ) else 1) =
      (q : ℝ) - p := by
  unfold expectedCost monotoneBernoulliCoupling monotoneBernoulliLaw
  simp only [pmfExp, PMF.ofFintype_apply]
  rw [Fintype.sum_prod_type]
  simp
  rw [ENNReal.toReal_sub_of_le]
  · simp only [ENNReal.coe_toReal]
  · exact_mod_cast hpq
  · exact ENNReal.coe_ne_top

/-- A transport-cost certificate transfers a pointwise cost bound to expectations. -/
theorem abs_pmfExp_sub_le_of_expectedCostLE
    (f : α → ℝ) (g : β → ℝ) (cost : α → β → ℝ) (bound : ℝ)
    (htransport : HasExpectedCostLE μ ν cost bound)
    (hcost : ∀ left right, |f left - g right| ≤ cost left right) :
    |pmfExp μ f - pmfExp ν g| ≤ bound := by
  obtain ⟨coupling, hbound⟩ := htransport
  exact (coupling.abs_pmfExp_sub_le_expectedCost f g cost hcost).trans hbound

/-- A Lipschitz test function is stable in expectation along any finite coupling. -/
theorem abs_pmfExp_sub_le_lipschitz_expectedCost
    {Data : Type*} [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    {μ ν : PMF Data} (coupling : FiniteCoupling μ ν)
    {L : NNReal} {f : Data → ℝ} (hf : LipschitzWith L f) :
    |pmfExp μ f - pmfExp ν f| ≤
      (L : ℝ) * coupling.expectedCost (fun left right => dist left right) := by
  calc
    |pmfExp μ f - pmfExp ν f|
        ≤ coupling.expectedCost (fun left right => (L : ℝ) * dist left right) :=
      coupling.abs_pmfExp_sub_le_expectedCost f f _ (fun left right => by
        simpa [Real.dist_eq] using hf.dist_le_mul left right)
    _ = (L : ℝ) * coupling.expectedCost (fun left right => dist left right) := by
      change pmfExp coupling.law (fun pair => (L : ℝ) * dist pair.1 pair.2) =
        (L : ℝ) * pmfExp coupling.law (fun pair => dist pair.1 pair.2)
      exact pmfExp_const_mul coupling.law (L : ℝ) _

/-- A transport-cost certificate bounds expectation changes of a Lipschitz test function. -/
theorem abs_pmfExp_sub_le_lipschitz_of_expectedCostLE
    {Data : Type*} [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    {μ ν : PMF Data} {L : NNReal} {f : Data → ℝ} (hf : LipschitzWith L f)
    {bound : ℝ}
    (htransport : HasExpectedCostLE μ ν (fun left right => dist left right) bound) :
    |pmfExp μ f - pmfExp ν f| ≤ (L : ℝ) * bound := by
  obtain ⟨coupling, hbound⟩ := htransport
  exact (coupling.abs_pmfExp_sub_le_lipschitz_expectedCost hf).trans
    (mul_le_mul_of_nonneg_left hbound (by positivity))

/-- A Lipschitz vector statistic is stable in norm along any finite coupling. -/
theorem norm_pmfVectorExp_sub_le_lipschitz_expectedCost
    {Data V : Type*} [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {μ ν : PMF Data} (coupling : FiniteCoupling μ ν)
    {L : NNReal} {f : Data → V} (hf : LipschitzWith L f) :
    ‖pmfVectorExp μ f - pmfVectorExp ν f‖ ≤
      (L : ℝ) * coupling.expectedCost (fun left right => dist left right) := by
  rw [coupling.pmfVectorExp_sub_eq f f]
  calc
    ‖pmfVectorExp coupling.law (fun pair => f pair.1 - f pair.2)‖ ≤
        pmfExp coupling.law (fun pair => ‖f pair.1 - f pair.2‖) :=
      norm_pmfVectorExp_le_pmfExp_norm coupling.law _
    _ ≤ pmfExp coupling.law (fun pair => (L : ℝ) * dist pair.1 pair.2) :=
      pmfExp_le_pmfExp_of_forall_le coupling.law _ _ (fun pair => by
        simpa only [dist_eq_norm] using hf.dist_le_mul pair.1 pair.2)
    _ = (L : ℝ) * coupling.expectedCost (fun left right => dist left right) := by
      change pmfExp coupling.law (fun pair => (L : ℝ) * dist pair.1 pair.2) =
        (L : ℝ) * pmfExp coupling.law (fun pair => dist pair.1 pair.2)
      exact pmfExp_const_mul coupling.law (L : ℝ) _

/-- A finite transport certificate bounds the change of a Lipschitz vector expectation. -/
theorem norm_pmfVectorExp_sub_le_lipschitz_of_expectedCostLE
    {Data V : Type*} [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {μ ν : PMF Data} {L : NNReal} {f : Data → V} (hf : LipschitzWith L f)
    {bound : ℝ}
    (htransport : HasExpectedCostLE μ ν (fun left right => dist left right) bound) :
    ‖pmfVectorExp μ f - pmfVectorExp ν f‖ ≤ (L : ℝ) * bound := by
  obtain ⟨coupling, hbound⟩ := htransport
  exact (coupling.norm_pmfVectorExp_sub_le_lipschitz_expectedCost hf).trans
    (mul_le_mul_of_nonneg_left hbound (by positivity))

end FiniteCoupling

end AppliedModelingLib
