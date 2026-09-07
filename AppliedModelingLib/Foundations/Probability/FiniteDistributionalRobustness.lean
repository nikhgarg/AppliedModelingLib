import AppliedModelingLib.Foundations.Probability.FiniteTransport

/-!
# Finite distributionally robust optimization kernels

This module isolates the finite, pointwise-selection part of a
distributionally robust objective.  For a nominal finite PMF `Q`, a payoff
`r(action, nominal)`, and an arbitrary coupling whose second marginal is `Q`,
its expected payoff is at most the `Q` expectation of the pointwise maximum.
The deterministic pointwise-maximizing graph coupling attains that bound.

This is the kernel identity used in the penalized half of Wasserstein DRO:
set `r(x,z) = loss x - gamma * cost x z`.  It intentionally does *not* claim
the additional equality with a transport-infimum penalty.  That bridge needs
an independently proved transport-attainment/duality result and must expose
its own cost and measure hypotheses.

The module uses the finite PMF/coupling API from `FiniteTransport.lean`.
That API already records its Mathlib provenance and Apache-2.0 license.
-/

namespace AppliedModelingLib
namespace FiniteDRO

open scoped BigOperators

variable {Action Nominal : Type*}
variable [Fintype Action] [DecidableEq Action] [Nonempty Action]
variable [Fintype Nominal] [DecidableEq Nominal]

/-- A finite joint law whose nominal (second) marginal is fixed. -/
structure Kernel (Action : Type*) (nominal : PMF Nominal) where
  law : PMF (Action × Nominal)
  snd_marginal : law.map Prod.snd = nominal

namespace Kernel

variable {nominal : PMF Nominal}

/-- Expected payoff under a finite kernel. -/
noncomputable def expectedPayoff (kernel : Kernel Action nominal)
    (payoff : Action → Nominal → ℝ) : ℝ :=
  pmfExp kernel.law (fun pair => payoff pair.1 pair.2)

/-- A kernel has the prescribed nominal-marginal expectation for every statistic. -/
theorem pmfExp_snd (kernel : Kernel Action nominal) (statistic : Nominal → ℝ) :
    pmfExp kernel.law (fun pair => statistic pair.2) = pmfExp nominal statistic := by
  calc
    pmfExp kernel.law (fun pair => statistic pair.2) =
        pmfExp (kernel.law.map Prod.snd) statistic :=
      (pmfExp_map kernel.law Prod.snd statistic).symm
    _ = pmfExp nominal statistic := by rw [kernel.snd_marginal]

/-- Forgetting the first marginal of a finite coupling yields a fixed-second-marginal kernel. -/
noncomputable def ofFiniteCoupling
    {source : PMF Action} (coupling : FiniteCoupling source nominal) : Kernel Action nominal where
  law := coupling.law
  snd_marginal := coupling.snd_marginal

/-- Every finite kernel is a coupling of its induced first marginal and its fixed nominal law. -/
noncomputable def toFiniteCoupling (kernel : Kernel Action nominal) :
    FiniteCoupling (kernel.law.map Prod.fst) nominal where
  law := kernel.law
  fst_marginal := rfl
  snd_marginal := kernel.snd_marginal

/-- The deterministic graph of an action selector is a kernel over its base PMF. -/
noncomputable def graph (nominal : PMF Nominal) (choose : Nominal → Action) :
    Kernel Action nominal where
  law := (FiniteCoupling.graph nominal choose).law
  snd_marginal := (FiniteCoupling.graph nominal choose).snd_marginal

/-- The graph kernel's payoff is the nominal expectation of selected payoff. -/
theorem expectedPayoff_graph (nominal : PMF Nominal) (choose : Nominal → Action)
    (payoff : Action → Nominal → ℝ) :
    (graph nominal choose).expectedPayoff payoff =
      pmfExp nominal (fun state => payoff (choose state) state) := by
  exact FiniteCoupling.expectedCost_graph nominal choose payoff

end Kernel

/-- The finite set of payoffs attainable at one nominal state. -/
noncomputable def payoffValues (payoff : Action → Nominal → ℝ) (state : Nominal) :
    Finset ℝ :=
  Finset.univ.image (fun action => payoff action state)

theorem payoffValues_nonempty (payoff : Action → Nominal → ℝ) (state : Nominal) :
    (payoffValues payoff state).Nonempty := by
  unfold payoffValues
  exact Finset.image_nonempty.mpr Finset.univ_nonempty

/-- The attained pointwise finite supremum of a payoff. -/
noncomputable def envelope (payoff : Action → Nominal → ℝ) (state : Nominal) : ℝ :=
  (payoffValues payoff state).max' (payoffValues_nonempty payoff state)

/-- Every action payoff is at most the finite pointwise envelope. -/
theorem payoff_le_envelope (payoff : Action → Nominal → ℝ)
    (action : Action) (state : Nominal) :
    payoff action state ≤ envelope payoff state := by
  unfold envelope
  apply Finset.le_max'
  simp only [payoffValues, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨action, rfl⟩

/-- A deterministic action selector attaining the finite pointwise envelope. -/
noncomputable def argmax (payoff : Action → Nominal → ℝ) (state : Nominal) : Action :=
  Classical.choose (Finset.mem_image.mp
    (Finset.max'_mem (payoffValues payoff state)
      (payoffValues_nonempty payoff state)))

/-- The selected action realizes the finite pointwise envelope. -/
theorem argmax_attains (payoff : Action → Nominal → ℝ) (state : Nominal) :
    payoff (argmax payoff state) state = envelope payoff state := by
  unfold argmax envelope
  exact (Classical.choose_spec (Finset.mem_image.mp
    (Finset.max'_mem (payoffValues payoff state)
      (payoffValues_nonempty payoff state)))).2

/--
Pointwise perturbations of a finite payoff family perturb its attained
envelope by no more than the same amount.  This is the stability step behind
parameter-cover arguments for finite distributionally robust surrogates.
-/
theorem abs_envelope_sub_le_of_forall_abs_sub_le
    (first second : Action → Nominal → ℝ) (bound : ℝ)
    (hbound : ∀ action state, |first action state - second action state| ≤ bound)
    (state : Nominal) :
    |envelope first state - envelope second state| ≤ bound := by
  have hfirstUpper : envelope first state ≤ envelope second state + bound := by
    calc
      envelope first state = first (argmax first state) state :=
        (argmax_attains first state).symm
      _ ≤ second (argmax first state) state + bound := by
        linarith [(abs_le.mp (hbound (argmax first state) state)).2]
      _ ≤ envelope second state + bound :=
        add_le_add (payoff_le_envelope second (argmax first state) state) (le_refl bound)
  have hsecondUpper : envelope second state ≤ envelope first state + bound := by
    calc
      envelope second state = second (argmax second state) state :=
        (argmax_attains second state).symm
      _ ≤ first (argmax second state) state + bound := by
        linarith [(abs_le.mp (hbound (argmax second state) state)).1]
      _ ≤ envelope first state + bound :=
        add_le_add (payoff_le_envelope first (argmax second state) state) (le_refl bound)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/--
A certificate that a kernel attains the largest expected payoff among all
kernels with the same nominal second marginal.
-/
structure KernelOptimalityCertificate (nominal : PMF Nominal)
    (payoff : Action → Nominal → ℝ) where
  witness : Kernel Action nominal
  witness_value : witness.expectedPayoff payoff = pmfExp nominal (envelope payoff)
  upper_bound : ∀ kernel : Kernel Action nominal,
    kernel.expectedPayoff payoff ≤ pmfExp nominal (envelope payoff)

/--
Finite kernel duality: pointwise maximization followed by expectation is
exactly attained by the graph of a pointwise maximizing selector.
-/
noncomputable def kernelOptimalityCertificate (nominal : PMF Nominal)
    (payoff : Action → Nominal → ℝ) : KernelOptimalityCertificate nominal payoff where
  witness := Kernel.graph nominal (argmax payoff)
  witness_value := by
    rw [Kernel.expectedPayoff_graph]
    apply pmfExp_congr
    intro state
    exact argmax_attains payoff state
  upper_bound := by
    intro kernel
    calc
      kernel.expectedPayoff payoff ≤
          pmfExp kernel.law (fun pair => envelope payoff pair.2) :=
        pmfExp_le_pmfExp_of_forall_le kernel.law _ _
          (fun pair => payoff_le_envelope payoff pair.1 pair.2)
      _ = pmfExp nominal (envelope payoff) := kernel.pmfExp_snd _

/-- The graph witness attains the pointwise-envelope expected payoff. -/
theorem kernelOptimalityCertificate_witness_value (nominal : PMF Nominal)
    (payoff : Action → Nominal → ℝ) :
    (kernelOptimalityCertificate nominal payoff).witness.expectedPayoff payoff =
      pmfExp nominal (envelope payoff) :=
  (kernelOptimalityCertificate nominal payoff).witness_value

/-- Every finite kernel is bounded by the pointwise-envelope expected payoff. -/
theorem kernel_expectedPayoff_le_envelope (nominal : PMF Nominal)
    (payoff : Action → Nominal → ℝ) (kernel : Kernel Action nominal) :
    kernel.expectedPayoff payoff ≤ pmfExp nominal (envelope payoff) :=
  (kernelOptimalityCertificate nominal payoff).upper_bound kernel

/-- The pointwise penalized payoff used in finite distributionally robust optimization. -/
def penalizedPayoff (loss : Action → ℝ) (cost : Action → Nominal → ℝ)
    (penalty : ℝ) : Action → Nominal → ℝ :=
  fun action nominal => loss action - penalty * cost action nominal

/--
A uniform loss perturbation changes the finite penalized robust envelope by
at most that perturbation.  The cost and penalty are shared, so their terms
cancel before applying finite-envelope stability.
-/
theorem abs_envelope_penalizedPayoff_sub_le_of_forall_abs_sub_le
    (first second : Action → ℝ) (cost : Action → Nominal → ℝ) (penalty bound : ℝ)
    (hbound : ∀ action, |first action - second action| ≤ bound) (state : Nominal) :
    |envelope (penalizedPayoff first cost penalty) state -
      envelope (penalizedPayoff second cost penalty) state| ≤ bound := by
  apply abs_envelope_sub_le_of_forall_abs_sub_le
  intro action nominal
  have hrewrite :
      penalizedPayoff first cost penalty action nominal -
        penalizedPayoff second cost penalty action nominal = first action - second action := by
    simp only [penalizedPayoff]
    ring
  rw [hrewrite]
  exact hbound action

/--
A bounded loss gives the same absolute bound for its finite penalized envelope
when the cost is nonnegative with zero diagonal and the penalty is
nonnegative.  The lower bound uses the diagonal action; the upper bound uses
the selected finite maximizer.
-/
theorem abs_envelope_penalizedPayoff_le_of_loss_abs_le_selfCost_zero
    {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]
    (loss : State → ℝ) (cost : State → State → ℝ) (penalty bound : ℝ)
    (hloss : ∀ state, |loss state| ≤ bound)
    (hcost : ∀ first second, 0 ≤ cost first second)
    (hselfCost : ∀ state, cost state state = 0)
    (hpenalty : 0 ≤ penalty) (state : State) :
    |envelope (penalizedPayoff loss cost penalty) state| ≤ bound := by
  apply abs_le.mpr
  constructor
  · calc
      -bound ≤ loss state := (abs_le.mp (hloss state)).1
      _ = penalizedPayoff loss cost penalty state state := by
        unfold penalizedPayoff
        rw [hselfCost state]
        ring
      _ ≤ envelope (penalizedPayoff loss cost penalty) state :=
        payoff_le_envelope _ state state
  · rw [← argmax_attains (penalizedPayoff loss cost penalty) state]
    calc
      penalizedPayoff loss cost penalty
          (argmax (penalizedPayoff loss cost penalty) state) state ≤
          loss (argmax (penalizedPayoff loss cost penalty) state) := by
        unfold penalizedPayoff
        exact sub_le_self _ (mul_nonneg hpenalty
          (hcost (argmax (penalizedPayoff loss cost penalty) state) state))
      _ ≤ bound := (abs_le.mp (hloss _)).2

/--
The finite penalized transport objective, written as a supremum over source
PMFs.  Its equality with the nominal expectation of `envelope` is proved
below without selecting an optimal transport coupling.
-/
noncomputable def penalizedTransportValue (nominal : PMF Nominal)
    (loss : Action → ℝ) (cost : Action → Nominal → ℝ) (penalty : ℝ) : ℝ :=
  sSup (Set.range fun source : PMF Action =>
    pmfExp source loss - penalty *
      FiniteCoupling.finiteTransportCost source nominal cost)

/--
The penalized payoff of an explicit coupling is the expected pointwise
penalized payoff under its fixed-second-marginal kernel.
-/
theorem coupling_penalizedPayoff_eq_expectedPayoff
    {source : PMF Action} (nominal : PMF Nominal) (loss : Action → ℝ)
    (cost : Action → Nominal → ℝ) (penalty : ℝ)
    (coupling : FiniteCoupling source nominal) :
    pmfExp source loss - penalty * coupling.expectedCost cost =
      (Kernel.ofFiniteCoupling coupling).expectedPayoff
        (penalizedPayoff loss cost penalty) := by
  let kernel : Kernel Action nominal := Kernel.ofFiniteCoupling coupling
  change pmfExp source loss - penalty * coupling.expectedCost cost =
    kernel.expectedPayoff (penalizedPayoff loss cost penalty)
  dsimp [kernel, Kernel.ofFiniteCoupling, Kernel.expectedPayoff,
    FiniteCoupling.expectedCost, penalizedPayoff]
  rw [← coupling.pmfExp_fst loss, ← pmfExp_const_mul, ← pmfExp_sub]

/--
Any explicit coupling has penalized payoff bounded by the nominal expectation
of the pointwise penalized envelope.
-/
theorem coupling_penalizedPayoff_le_envelope
    {source : PMF Action} (nominal : PMF Nominal) (loss : Action → ℝ)
    (cost : Action → Nominal → ℝ) (penalty : ℝ)
    (coupling : FiniteCoupling source nominal) :
    pmfExp source loss - penalty * coupling.expectedCost cost ≤
      pmfExp nominal (envelope (penalizedPayoff loss cost penalty)) := by
  rw [coupling_penalizedPayoff_eq_expectedPayoff nominal loss cost penalty coupling]
  exact kernel_expectedPayoff_le_envelope nominal _ (Kernel.ofFiniteCoupling coupling)

/--
Every source PMF has penalized transport value at most the nominal expected
pointwise envelope.  The proof uses an arbitrarily near-optimal finite
coupling, so it does not assume that the transport infimum is attained.
-/
theorem penalized_sourceValue_le_envelope
    {source : PMF Action} (nominal : PMF Nominal) (loss : Action → ℝ)
    (cost : Action → Nominal → ℝ) (hcost : ∀ action state, 0 ≤ cost action state)
    (penalty : ℝ) (hpenalty : 0 ≤ penalty) :
    pmfExp source loss - penalty *
        FiniteCoupling.finiteTransportCost source nominal cost ≤
      pmfExp nominal (envelope (penalizedPayoff loss cost penalty)) := by
  by_cases hpenalty_zero : penalty = 0
  · simpa [hpenalty_zero] using
      (coupling_penalizedPayoff_le_envelope nominal loss cost penalty
        (FiniteCoupling.independentCoupling source nominal))
  · have hpenalty_pos : 0 < penalty := lt_of_le_of_ne hpenalty (Ne.symm hpenalty_zero)
    by_contra hbound
    let transport : ℝ := FiniteCoupling.finiteTransportCost source nominal cost
    let value : ℝ := pmfExp source loss - penalty * transport
    let envelopeValue : ℝ := pmfExp nominal (envelope (penalizedPayoff loss cost penalty))
    have hstrict : envelopeValue < value := by
      dsimp [value, envelopeValue, transport]
      exact lt_of_not_ge hbound
    let epsilon : ℝ := (value - envelopeValue) / (2 * penalty)
    have hepsilon_pos : 0 < epsilon := by
      dsimp [epsilon]
      exact div_pos (sub_pos.mpr hstrict) (by positivity)
    obtain ⟨coupling, hcoupling⟩ :=
      FiniteCoupling.exists_expectedCost_lt_finiteTransportCost_add
        (μ := source) (ν := nominal) cost hcost hepsilon_pos
    have hcost_mul : penalty * coupling.expectedCost cost < penalty * (transport + epsilon) := by
      simpa [transport] using mul_lt_mul_of_pos_left hcoupling hpenalty_pos
    have hepsilon_product : penalty * epsilon = (value - envelopeValue) / 2 := by
      dsimp [epsilon]
      field_simp [ne_of_gt hpenalty_pos]
    have hbetter : envelopeValue <
        pmfExp source loss - penalty * coupling.expectedCost cost := by
      dsimp [value] at hstrict hepsilon_product
      nlinarith [hcost_mul, hepsilon_product]
    have hupper := coupling_penalizedPayoff_le_envelope nominal loss cost penalty coupling
    exact (not_lt_of_ge hupper) (by simpa [envelopeValue] using hbetter)

/-- The finite penalized source values have the pointwise-envelope upper bound. -/
theorem bddAbove_penalizedSourceValues
    (nominal : PMF Nominal) (loss : Action → ℝ)
    (cost : Action → Nominal → ℝ) (hcost : ∀ action state, 0 ≤ cost action state)
    (penalty : ℝ) (hpenalty : 0 ≤ penalty) :
    BddAbove (Set.range fun source : PMF Action =>
      pmfExp source loss - penalty *
        FiniteCoupling.finiteTransportCost source nominal cost) := by
  refine ⟨pmfExp nominal (envelope (penalizedPayoff loss cost penalty)), ?_⟩
  intro value hvalue
  rcases hvalue with ⟨source, rfl⟩
  exact penalized_sourceValue_le_envelope nominal loss cost hcost penalty hpenalty

/--
Finite penalized transport duality: penalizing the finite transport infimum
equals the nominal expectation of the pointwise penalized envelope.  This is
the finite counterpart of the penalized equality in SNVD17 Proposition 1.
-/
theorem penalizedTransportValue_eq_envelope
    (nominal : PMF Nominal) (loss : Action → ℝ)
    (cost : Action → Nominal → ℝ) (hcost : ∀ action state, 0 ≤ cost action state)
    (penalty : ℝ) (hpenalty : 0 ≤ penalty) :
    penalizedTransportValue nominal loss cost penalty =
      pmfExp nominal (envelope (penalizedPayoff loss cost penalty)) := by
  let payoff := penalizedPayoff loss cost penalty
  let kernel : Kernel Action nominal := Kernel.graph nominal (argmax payoff)
  let source : PMF Action := kernel.law.map Prod.fst
  let coupling : FiniteCoupling source nominal := kernel.toFiniteCoupling
  have hupper := bddAbove_penalizedSourceValues nominal loss cost hcost penalty hpenalty
  have hkernel_value : kernel.expectedPayoff payoff = pmfExp nominal (envelope payoff) := by
    calc
      kernel.expectedPayoff payoff =
          pmfExp nominal (fun state => payoff (argmax payoff state) state) := by
            exact Kernel.expectedPayoff_graph nominal (argmax payoff) payoff
      _ = pmfExp nominal (envelope payoff) := by
            apply pmfExp_congr
            intro state
            exact argmax_attains payoff state
  have htransport : FiniteCoupling.finiteTransportCost source nominal cost ≤
      coupling.expectedCost cost :=
    FiniteCoupling.finiteTransportCost_le_expectedCost cost hcost coupling
  have hsource_value :
      pmfExp nominal (envelope payoff) ≤
        pmfExp source loss - penalty *
          FiniteCoupling.finiteTransportCost source nominal cost := by
    calc
      pmfExp nominal (envelope payoff) = kernel.expectedPayoff payoff := hkernel_value.symm
      _ = pmfExp source loss - penalty * coupling.expectedCost cost := by
        symm
        exact coupling_penalizedPayoff_eq_expectedPayoff nominal loss cost penalty coupling
      _ ≤ pmfExp source loss - penalty *
          FiniteCoupling.finiteTransportCost source nominal cost := by
        exact sub_le_sub_left (mul_le_mul_of_nonneg_left htransport hpenalty) _
  apply le_antisymm
  · unfold penalizedTransportValue
    refine csSup_le (Set.range_nonempty _) ?_
    intro value hvalue
    rcases hvalue with ⟨source, rfl⟩
    exact penalized_sourceValue_le_envelope nominal loss cost hcost penalty hpenalty
  · unfold penalizedTransportValue
    calc
      pmfExp nominal (envelope payoff) ≤
          pmfExp source loss - penalty *
            FiniteCoupling.finiteTransportCost source nominal cost := hsource_value
      _ ≤ sSup (Set.range fun source : PMF Action =>
          pmfExp source loss - penalty *
            FiniteCoupling.finiteTransportCost source nominal cost) :=
          le_csSup hupper ⟨source, rfl⟩

end FiniteDRO
end AppliedModelingLib
