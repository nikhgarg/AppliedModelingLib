import AppliedModelingLib.GameTheory.Choice.Equilibrium
import AppliedModelingLib.Foundations.Optimization.FiniteSearch
import AppliedModelingLib.Foundations.Probability.Conditional
import AppliedModelingLib.Foundations.Probability.FiniteTransport
import AppliedModelingLib.Foundations.Probability.PMFKernel
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Strategic Responses and Social Burden

This strategic-learning finite-population interface is shared by the strategic-classification
models of Hardt--Megiddo--Papadimitriou--Wootters (2015) and
Milli--Miller--Dragan--Hardt (2019).  It separates an agent's identity, type,
initial feature, manipulation cost, and best-response certificate from the
distributional objects used to score a classifier.  The homogeneous
feature-indexed interface remains available as the special case whose agents
are their own initial features and whose type space is `Unit`.

The social-burden definitions use `0` on a null conditioning event, following
the repository's `pmfConditionalExp` convention.  Paper-facing theorems must
therefore state positive-label mass when the ordinary conditional-expectation
reading is required.

The stochastic-response definitions directly reuse Mathlib's `PMF.pure`,
`PMF.map`, `PMF.bind`, and their support laws from
[`ProbabilityMassFunction/Monad.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/ProbabilityMassFunction/Monad.lean)
and
[`ProbabilityMassFunction/Constructions.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean),
and the finite-set uniform distribution from
[`Probability/Distributions/Uniform.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/Distributions/Uniform.lean),
at the repository's pinned Mathlib commit, under Apache-2.0.  No upstream code
is copied or ported here.
-/

namespace AppliedModelingLib

/-- A deterministic binary classifier. -/
abbrev BinaryClassifier (Feature : Type*) := Feature → Bool

/-- A randomized binary classifier, represented by its output PMF at each feature. -/
abbrev RandomizedBinaryClassifier (Feature : Type*) := PMFKernel Feature Bool

/-- Acceptance probability of a randomized binary classifier. -/
noncomputable def acceptanceProbability {Feature : Type*}
    (classifier : RandomizedBinaryClassifier Feature) (x : Feature) : ℝ :=
  (classifier x true).toReal

/-- Embed a deterministic classifier as a point-mass randomized classifier. -/
noncomputable def deterministicAsRandomized {Feature : Type*}
    (classifier : BinaryClassifier Feature) : RandomizedBinaryClassifier Feature :=
  PMFKernel.pure classifier

@[simp] theorem acceptanceProbability_deterministicAsRandomized
    {Feature : Type*} (classifier : BinaryClassifier Feature) (x : Feature) :
    acceptanceProbability (deterministicAsRandomized classifier) x =
      if classifier x then 1 else 0 := by
  by_cases h : classifier x = true <;>
    simp [acceptanceProbability, deterministicAsRandomized, h]

/--
Expected binary score when rejection pays `negativeScore` and acceptance pays
`positiveScore`.  This affine form supports both the usual `0/1` benefit and
the `-1/1` score used by strategic classification.
-/
noncomputable def randomizedBinaryScore {Feature : Type*}
    (negativeScore positiveScore : ℝ) (classifier : RandomizedBinaryClassifier Feature)
    (x : Feature) : ℝ :=
  negativeScore + (positiveScore - negativeScore) * acceptanceProbability classifier x

/-- A deterministic classifier's expected score is its corresponding endpoint score. -/
@[simp] theorem randomizedBinaryScore_deterministicAsRandomized
    {Feature : Type*} (negativeScore positiveScore : ℝ)
    (classifier : BinaryClassifier Feature) (x : Feature) :
    randomizedBinaryScore negativeScore positiveScore
        (deterministicAsRandomized classifier) x =
      if classifier x then positiveScore else negativeScore := by
  by_cases h : classifier x = true
  · simp [randomizedBinaryScore, h]
  · have hfalse : classifier x = false := Bool.eq_false_of_not_eq_true h
    simp [randomizedBinaryScore, hfalse]

/-- Expected `-1/1` classifier score, matching the strategic-classification convention. -/
noncomputable def signedRandomizedBinaryScore {Feature : Type*}
    (classifier : RandomizedBinaryClassifier Feature) (x : Feature) : ℝ :=
  randomizedBinaryScore (-1) 1 classifier x

@[simp] theorem signedRandomizedBinaryScore_deterministicAsRandomized
    {Feature : Type*} (classifier : BinaryClassifier Feature) (x : Feature) :
    signedRandomizedBinaryScore (deterministicAsRandomized classifier) x =
      if classifier x then 1 else -1 := by
  simp [signedRandomizedBinaryScore]

/--
A heterogeneous strategic environment separates agents from their economic
types and observable features.  Manipulation cost may depend on the type, the
agent's initial feature, and the chosen reported/post-manipulation feature.
-/
structure StrategicAgentEnvironment (Agent AgentType Feature : Type*) where
  agentType : Agent → AgentType
  initialFeature : Agent → Feature
  manipulationCost : AgentType → Feature → Feature → ℝ

/-- The manipulation cost faced by a particular agent for a chosen feature. -/
def StrategicAgentEnvironment.cost
    {Agent AgentType Feature : Type*}
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (agent : Agent) (chosen : Feature) : ℝ :=
  environment.manipulationCost
    (environment.agentType agent) (environment.initialFeature agent) chosen

/-- Utility of a heterogeneous agent from choosing a post-manipulation feature. -/
def agentStrategicUtility
    {Agent AgentType Feature : Type*}
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (agent : Agent) (chosen : Feature) : ℝ :=
  score chosen - environment.cost agent chosen

/-- A chosen feature maximizes a heterogeneous agent's strategic utility. -/
def IsAgentStrategicBestResponse
    {Agent AgentType Feature : Type*}
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (agent : Agent) (chosen : Feature) : Prop :=
  ∀ action, agentStrategicUtility score environment agent action ≤
    agentStrategicUtility score environment agent chosen

/-- The best-response correspondence of a heterogeneous strategic agent. -/
def agentStrategicBestResponses
    {Agent AgentType Feature : Type*}
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (agent : Agent) : Set Feature :=
  {chosen | IsAgentStrategicBestResponse score environment agent chosen}

/-- The finite best-response correspondence of a heterogeneous strategic agent. -/
noncomputable def agentStrategicBestResponseFinset
    {Agent AgentType Feature : Type*} [Fintype Feature]
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (agent : Agent) : Finset Feature := by
  classical
  exact Finset.univ.filter
    (IsAgentStrategicBestResponse score environment agent)

@[simp] theorem mem_agentStrategicBestResponseFinset_iff
    {Agent AgentType Feature : Type*} [Fintype Feature]
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (agent : Agent) (chosen : Feature) :
    chosen ∈ agentStrategicBestResponseFinset score environment agent ↔
      IsAgentStrategicBestResponse score environment agent chosen := by
  classical
  simp [agentStrategicBestResponseFinset]

theorem mem_agentStrategicBestResponses_iff
    {Agent AgentType Feature : Type*}
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (agent : Agent) (chosen : Feature) :
    chosen ∈ agentStrategicBestResponses score environment agent ↔
      IsAgentStrategicBestResponse score environment agent chosen :=
  Iff.rfl

/-- A finite feature/action space supplies every heterogeneous agent a best response. -/
theorem agentStrategicBestResponses_nonempty
    {Agent AgentType Feature : Type*} [Fintype Feature]
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (agent : Agent) :
    (agentStrategicBestResponses score environment agent).Nonempty := by
  classical
  obtain ⟨chosen, hchosen⟩ :=
    Optimization.exists_isMaximizerOn_of_finite (fun _ : Feature => True)
      (agentStrategicUtility score environment agent)
      ⟨environment.initialFeature agent, trivial⟩
  refine ⟨chosen, ?_⟩
  intro action
  exact hchosen.le trivial

/-- The finite best-response correspondence is nonempty for every agent. -/
theorem agentStrategicBestResponseFinset_nonempty
    {Agent AgentType Feature : Type*} [Fintype Feature]
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (agent : Agent) :
    (agentStrategicBestResponseFinset score environment agent).Nonempty := by
  obtain ⟨chosen, hchosen⟩ :=
    agentStrategicBestResponses_nonempty score environment agent
  exact ⟨chosen,
    (mem_agentStrategicBestResponseFinset_iff score environment agent chosen).2 hchosen⟩

/-- A noncomputably selected best response for each heterogeneous agent. -/
noncomputable def selectedAgentStrategicBestResponse
    {Agent AgentType Feature : Type*} [Fintype Feature]
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (agent : Agent) : Feature :=
  Classical.choose (agentStrategicBestResponses_nonempty score environment agent)

theorem selectedAgentStrategicBestResponse_spec
    {Agent AgentType Feature : Type*} [Fintype Feature]
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (agent : Agent) :
    IsAgentStrategicBestResponse score environment agent
      (selectedAgentStrategicBestResponse score environment agent) :=
  Classical.choose_spec (agentStrategicBestResponses_nonempty score environment agent)

/--
The homogeneous feature-indexed environment underlying the original strategic
response API: an agent is identified with its initial feature and all agents
share one manipulation-cost function.
-/
def homogeneousStrategicAgentEnvironment
    {Feature : Type*} (cost : Feature → Feature → ℝ) :
    StrategicAgentEnvironment Feature Unit Feature where
  agentType := fun _ => ()
  initialFeature := id
  manipulationCost := fun _ => cost

@[simp] theorem homogeneousStrategicAgentEnvironment_cost
    {Feature : Type*} (cost : Feature → Feature → ℝ)
    (initial chosen : Feature) :
    (homogeneousStrategicAgentEnvironment cost).cost initial chosen =
      cost initial chosen :=
  rfl

/-- Utility from changing `x` to `x'`: classification benefit minus manipulation cost. -/
def strategicUtility {Feature : Type*} (score : Feature → ℝ)
    (cost : Feature → Feature → ℝ) (x x' : Feature) : ℝ :=
  score x' - cost x x'

/-- A chosen action is a best response to the published score. -/
def IsStrategicBestResponse {Feature : Type*} (score : Feature → ℝ)
    (cost : Feature → Feature → ℝ) (x chosen : Feature) : Prop :=
  ∀ action, strategicUtility score cost x action ≤ strategicUtility score cost x chosen

@[simp] theorem agentStrategicUtility_homogeneous
    {Feature : Type*} (score : Feature → ℝ) (cost : Feature → Feature → ℝ)
    (initial chosen : Feature) :
    agentStrategicUtility score (homogeneousStrategicAgentEnvironment cost) initial chosen =
      strategicUtility score cost initial chosen :=
  rfl

@[simp] theorem isAgentStrategicBestResponse_homogeneous_iff
    {Feature : Type*} (score : Feature → ℝ) (cost : Feature → Feature → ℝ)
    (initial chosen : Feature) :
    IsAgentStrategicBestResponse score (homogeneousStrategicAgentEnvironment cost)
        initial chosen ↔
      IsStrategicBestResponse score cost initial chosen :=
  Iff.rfl

/-- The best-response correspondence of an agent at feature `x`. -/
def strategicBestResponses {Feature : Type*} (score : Feature → ℝ)
    (cost : Feature → Feature → ℝ) (x : Feature) : Set Feature :=
  {chosen | IsStrategicBestResponse score cost x chosen}

theorem mem_strategicBestResponses_iff {Feature : Type*} (score : Feature → ℝ)
    (cost : Feature → Feature → ℝ) (x chosen : Feature) :
    chosen ∈ strategicBestResponses score cost x ↔
      IsStrategicBestResponse score cost x chosen :=
  Iff.rfl

/-- A finite action space always has a strategic best response. -/
theorem strategicBestResponses_nonempty {Feature : Type*} [Fintype Feature]
    (score : Feature → ℝ) (cost : Feature → Feature → ℝ) (x : Feature) :
    (strategicBestResponses score cost x).Nonempty := by
  classical
  obtain ⟨chosen, hchosen⟩ :=
    Optimization.exists_isMaximizerOn_of_finite (fun _ : Feature => True)
      (strategicUtility score cost x) ⟨x, trivial⟩
  refine ⟨chosen, ?_⟩
  intro action
  exact hchosen.le trivial

/-- A noncomputably selected best response on a finite action space. -/
noncomputable def selectedStrategicBestResponse {Feature : Type*} [Fintype Feature]
    (score : Feature → ℝ) (cost : Feature → Feature → ℝ) (x : Feature) : Feature :=
  Classical.choose (strategicBestResponses_nonempty score cost x)

theorem selectedStrategicBestResponse_spec {Feature : Type*} [Fintype Feature]
    (score : Feature → ℝ) (cost : Feature → Feature → ℝ) (x : Feature) :
    IsStrategicBestResponse score cost x (selectedStrategicBestResponse score cost x) :=
  Classical.choose_spec (strategicBestResponses_nonempty score cost x)

/-- Best-response correspondence induced by the expected score of a randomized classifier. -/
noncomputable def randomizedClassifierBestResponses {Feature : Type*}
    (negativeScore positiveScore : ℝ) (classifier : RandomizedBinaryClassifier Feature)
    (cost : Feature → Feature → ℝ) (x : Feature) : Set Feature :=
  strategicBestResponses (randomizedBinaryScore negativeScore positiveScore classifier) cost x

theorem mem_randomizedClassifierBestResponses_iff {Feature : Type*}
    (negativeScore positiveScore : ℝ) (classifier : RandomizedBinaryClassifier Feature)
    (cost : Feature → Feature → ℝ) (x chosen : Feature) :
    chosen ∈ randomizedClassifierBestResponses negativeScore positiveScore classifier cost x ↔
      IsStrategicBestResponse (randomizedBinaryScore negativeScore positiveScore classifier)
        cost x chosen :=
  Iff.rfl

/-- A selected response map for a randomized classifier on a finite feature space. -/
noncomputable def selectedRandomizedClassifierResponse {Feature : Type*} [Fintype Feature]
    (negativeScore positiveScore : ℝ) (classifier : RandomizedBinaryClassifier Feature)
    (cost : Feature → Feature → ℝ) : Feature → Feature :=
  fun x => selectedStrategicBestResponse
    (randomizedBinaryScore negativeScore positiveScore classifier) cost x

theorem selectedRandomizedClassifierResponse_spec {Feature : Type*} [Fintype Feature]
    (negativeScore positiveScore : ℝ) (classifier : RandomizedBinaryClassifier Feature)
    (cost : Feature → Feature → ℝ) (x : Feature) :
    IsStrategicBestResponse (randomizedBinaryScore negativeScore positiveScore classifier)
      cost x (selectedRandomizedClassifierResponse negativeScore positiveScore classifier cost x) :=
  selectedStrategicBestResponse_spec
    (randomizedBinaryScore negativeScore positiveScore classifier) cost x

/-- A manipulation cost is separable when it is the positive part of a difference. -/
def IsSeparableManipulationCost {Feature : Type*}
    (cost : Feature → Feature → ℝ) : Prop :=
  ∃ initialCost finalCost : Feature → ℝ,
    (∀ initial final, cost initial final = max 0 (finalCost final - initialCost initial)) ∧
      Set.range initialCost ⊆ Set.range finalCost

/--
The range-inclusion clause in a separable manipulation cost supplies a
zero-cost action from every initial feature.
-/
theorem IsSeparableManipulationCost.exists_zero_cost {Feature : Type*}
    {cost : Feature → Feature → ℝ} (hseparable : IsSeparableManipulationCost cost)
    (initial : Feature) :
    ∃ final, cost initial final = 0 := by
  rcases hseparable with ⟨initialCost, finalCost, hformula, hrange⟩
  have hinitial : initialCost initial ∈ Set.range initialCost := ⟨initial, rfl⟩
  rcases hrange hinitial with ⟨final, hfinal⟩
  refine ⟨final, ?_⟩
  rw [hformula, hfinal]
  norm_num

/-- Package a strategic response as the existing generic one-agent choice problem. -/
def strategicResponseChoiceProblem {Feature : Type*} (score : Feature → ℝ)
    (cost : Feature → Feature → ℝ) (response : Feature → Feature) :
    ChoiceEquilibriumData Feature Feature where
  actionFeasible := fun _ _ => True
  chosenAction := response
  payoff := strategicUtility score cost
  consistency := True

theorem isChoiceEquilibrium_strategicResponseChoiceProblem_iff
    {Feature : Type*} (score : Feature → ℝ) (cost : Feature → Feature → ℝ)
    (response : Feature → Feature) :
    IsChoiceEquilibrium (strategicResponseChoiceProblem score cost response) ↔
      ∀ x, IsStrategicBestResponse score cost x (response x) := by
  constructor
  · intro h x action
    exact h.2.1 x action trivial
  · intro h
    refine ⟨?_, ?_, trivial⟩
    · intro x
      trivial
    · intro x action _
      exact h x action

/-- A deterministic response map viewed as a stochastic response kernel. -/
noncomputable def deterministicResponseKernel {Feature : Type*}
    (response : Feature → Feature) : PMFKernel Feature Feature :=
  PMFKernel.pure response

/-- A response kernel randomizes only over utility-maximizing actions. -/
def IsStrategicBestResponseKernel {Feature : Type*} (score : Feature → ℝ)
    (cost : Feature → Feature → ℝ) (response : Feature → PMF Feature) : Prop :=
  ∀ x chosen, chosen ∈ (response x).support → IsStrategicBestResponse score cost x chosen

/-- A deterministic heterogeneous-agent response viewed as a stochastic kernel. -/
noncomputable def deterministicAgentResponseKernel
    {Agent Feature : Type*} (response : Agent → Feature) : PMFKernel Agent Feature :=
  PMFKernel.pure response

/-- A heterogeneous-agent response kernel randomizes only over utility maximizers. -/
def IsAgentStrategicBestResponseKernel
    {Agent AgentType Feature : Type*}
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → PMF Feature) : Prop :=
  ∀ agent chosen, chosen ∈ (response agent).support →
    IsAgentStrategicBestResponse score environment agent chosen

/-- A deterministic heterogeneous kernel is optimal exactly when its map is pointwise optimal. -/
theorem deterministicAgentResponseKernel_isAgentStrategicBestResponseKernel_iff
    {Agent AgentType Feature : Type*}
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → Feature) :
    IsAgentStrategicBestResponseKernel score environment
        (deterministicAgentResponseKernel response) ↔
      ∀ agent, IsAgentStrategicBestResponse score environment agent (response agent) := by
  constructor
  · intro h agent
    exact h agent (response agent) (by simp [deterministicAgentResponseKernel])
  · intro h agent chosen hchosen
    have heq : chosen = response agent := by
      simpa [deterministicAgentResponseKernel] using hchosen
    rw [heq]
    exact h agent

/-- The selected finite heterogeneous-agent best responses as a stochastic kernel. -/
noncomputable def selectedAgentStrategicResponseKernel
    {Agent AgentType Feature : Type*} [Fintype Feature]
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature) :
    Agent → PMF Feature :=
  deterministicAgentResponseKernel
    (selectedAgentStrategicBestResponse score environment)

theorem selectedAgentStrategicResponseKernel_spec
    {Agent AgentType Feature : Type*} [Fintype Feature]
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature) :
    IsAgentStrategicBestResponseKernel score environment
      (selectedAgentStrategicResponseKernel score environment) := by
  rw [selectedAgentStrategicResponseKernel,
    deterministicAgentResponseKernel_isAgentStrategicBestResponseKernel_iff]
  exact selectedAgentStrategicBestResponse_spec score environment

/--
Uniform tie-breaking over every best response of each heterogeneous agent.
Unlike `selectedAgentStrategicResponseKernel`, this kernel has the entire
finite best-response correspondence as its support.
-/
noncomputable def uniformAgentStrategicResponseKernel
    {Agent AgentType Feature : Type*} [Fintype Feature]
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature) :
    Agent → PMF Feature :=
  fun agent => PMF.uniformOfFinset
    (agentStrategicBestResponseFinset score environment agent)
    (agentStrategicBestResponseFinset_nonempty score environment agent)

@[simp] theorem uniformAgentStrategicResponseKernel_support
    {Agent AgentType Feature : Type*} [Fintype Feature]
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (agent : Agent) (chosen : Feature) :
    chosen ∈ (uniformAgentStrategicResponseKernel score environment agent).support ↔
      IsAgentStrategicBestResponse score environment agent chosen := by
  rw [uniformAgentStrategicResponseKernel,
    PMF.mem_support_uniformOfFinset_iff]
  exact mem_agentStrategicBestResponseFinset_iff score environment agent chosen

theorem uniformAgentStrategicResponseKernel_spec
    {Agent AgentType Feature : Type*} [Fintype Feature]
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature) :
    IsAgentStrategicBestResponseKernel score environment
      (uniformAgentStrategicResponseKernel score environment) := by
  intro agent chosen hchosen
  exact (uniformAgentStrategicResponseKernel_support
    score environment agent chosen).1 hchosen

/-- Uniform tie-breaking over the best responses in a homogeneous environment. -/
noncomputable def uniformStrategicResponseKernel
    {Feature : Type*} [Fintype Feature]
    (score : Feature → ℝ) (cost : Feature → Feature → ℝ) :
    Feature → PMF Feature :=
  uniformAgentStrategicResponseKernel score
    (homogeneousStrategicAgentEnvironment cost)

@[simp] theorem uniformStrategicResponseKernel_support
    {Feature : Type*} [Fintype Feature]
    (score : Feature → ℝ) (cost : Feature → Feature → ℝ)
    (initial chosen : Feature) :
    chosen ∈ (uniformStrategicResponseKernel score cost initial).support ↔
      IsStrategicBestResponse score cost initial chosen := by
  rw [uniformStrategicResponseKernel,
    uniformAgentStrategicResponseKernel_support,
    isAgentStrategicBestResponse_homogeneous_iff]

theorem uniformStrategicResponseKernel_spec
    {Feature : Type*} [Fintype Feature]
    (score : Feature → ℝ) (cost : Feature → Feature → ℝ) :
    IsStrategicBestResponseKernel score cost
      (uniformStrategicResponseKernel score cost) := by
  intro initial chosen hchosen
  exact (uniformStrategicResponseKernel_support
    score cost initial chosen).1 hchosen

/-- A deterministic kernel is best responding exactly when its response map is pointwise optimal. -/
theorem deterministicResponseKernel_isStrategicBestResponseKernel_iff
    {Feature : Type*} (score : Feature → ℝ) (cost : Feature → Feature → ℝ)
    (response : Feature → Feature) :
    IsStrategicBestResponseKernel score cost (deterministicResponseKernel response) ↔
      ∀ x, IsStrategicBestResponse score cost x (response x) := by
  constructor
  · intro h x
    exact h x (response x) (by simp [deterministicResponseKernel])
  · intro h x chosen hchosen
    have heq : chosen = response x := by
      simpa [deterministicResponseKernel] using hchosen
    rw [heq]
    exact h x

/-- The selected randomized-classifier response, viewed as a stochastic kernel. -/
noncomputable def selectedRandomizedClassifierResponseKernel
    {Feature : Type*} [Fintype Feature]
    (negativeScore positiveScore : ℝ) (classifier : RandomizedBinaryClassifier Feature)
    (cost : Feature → Feature → ℝ) : Feature → PMF Feature :=
  deterministicResponseKernel
    (selectedRandomizedClassifierResponse negativeScore positiveScore classifier cost)

theorem selectedRandomizedClassifierResponseKernel_spec
    {Feature : Type*} [Fintype Feature]
    (negativeScore positiveScore : ℝ) (classifier : RandomizedBinaryClassifier Feature)
    (cost : Feature → Feature → ℝ) :
    IsStrategicBestResponseKernel
      (randomizedBinaryScore negativeScore positiveScore classifier) cost
      (selectedRandomizedClassifierResponseKernel negativeScore positiveScore classifier cost) := by
  rw [selectedRandomizedClassifierResponseKernel,
    deterministicResponseKernel_isStrategicBestResponseKernel_iff]
  exact selectedRandomizedClassifierResponse_spec negativeScore positiveScore classifier cost

/--
Primitive transport stability of an agent-indexed response family.  For every
agent and pair of deployed parameters, the two response laws have a coupling
whose expected feature distance is controlled by the parameter distance.
-/
def IsAgentResponseTransportSensitive
    {Parameter Agent Feature : Type*}
    [MetricSpace Parameter] [MetricSpace Feature]
    [Fintype Feature] [DecidableEq Feature]
    (response : Parameter → Agent → PMF Feature) (sensitivity : ℝ) : Prop :=
  ∀ first second agent,
    FiniteCoupling.HasExpectedCostLE
      (response first agent) (response second agent)
      (fun left right => dist left right)
      (sensitivity * dist first second)

/--
A pointwise Lipschitz deterministic response map induces a transport-sensitive
point-mass response family with the same coefficient.
-/
theorem isAgentResponseTransportSensitive_deterministicAgentResponseKernel
    {Parameter Agent Feature : Type*}
    [MetricSpace Parameter] [MetricSpace Feature]
    [Fintype Feature] [DecidableEq Feature]
    (response : Parameter → Agent → Feature) (sensitivity : NNReal)
    (hresponse : ∀ agent,
      LipschitzWith sensitivity (fun parameter => response parameter agent)) :
    IsAgentResponseTransportSensitive
      (fun parameter => deterministicAgentResponseKernel (response parameter))
      (sensitivity : ℝ) := by
  intro first second agent
  refine ⟨FiniteCoupling.pure (response first agent) (response second agent), ?_⟩
  simpa [deterministicAgentResponseKernel] using
    (hresponse agent).dist_le_mul first second

/--
The observable data law generated by a population of named agents.  The base
law may carry labels over agents rather than over their initial features; the
response kernel emits the post-manipulation feature while preserving the
agent's label.
-/
noncomputable def inducedAgentStrategicDataLaw
    {Agent Feature Label : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Label] [DecidableEq Label]
    (baseLaw : PMF (Agent × Label)) (response : Agent → PMF Feature) :
    PMF (Feature × Label) :=
  baseLaw.bind fun datum => (response datum.1).map fun changed => (changed, datum.2)

/--
Couple two induced strategic data laws by sampling the same named agent and
label, then applying a supplied coupling of that agent's two response laws.
-/
noncomputable def inducedAgentStrategicDataCoupling
    {Agent Feature Label : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Label] [DecidableEq Label]
    (baseLaw : PMF (Agent × Label)) (left right : Agent → PMF Feature)
    (fiber : ∀ agent, FiniteCoupling (left agent) (right agent)) :
    FiniteCoupling
      (inducedAgentStrategicDataLaw baseLaw left)
      (inducedAgentStrategicDataLaw baseLaw right) := by
  unfold inducedAgentStrategicDataLaw
  exact FiniteCoupling.bindSharedBase baseLaw
    (fun datum => (left datum.1).map fun changed => (changed, datum.2))
    (fun datum => (right datum.1).map fun changed => (changed, datum.2))
    (fun datum => (fiber datum.1).map
      (fun changed => (changed, datum.2))
      (fun changed => (changed, datum.2)))

/--
The shared-agent coupling pays exactly the base-population expectation of its
agent-level feature transport costs; preserving the label adds no distance.
-/
theorem expectedCost_inducedAgentStrategicDataCoupling
    {Agent Feature Label : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Feature] [DecidableEq Feature] [MetricSpace Feature]
    [Fintype Label] [DecidableEq Label] [MetricSpace Label]
    (baseLaw : PMF (Agent × Label)) (left right : Agent → PMF Feature)
    (fiber : ∀ agent, FiniteCoupling (left agent) (right agent)) :
    (inducedAgentStrategicDataCoupling baseLaw left right fiber).expectedCost
        (fun first second => dist first second) =
      pmfExp baseLaw fun datum =>
        (fiber datum.1).expectedCost (fun first second => dist first second) := by
  unfold inducedAgentStrategicDataCoupling
  simp only [id_eq]
  calc
    (FiniteCoupling.bindSharedBase baseLaw
          (fun datum => (left datum.1).map fun changed => (changed, datum.2))
          (fun datum => (right datum.1).map fun changed => (changed, datum.2))
          (fun datum => (fiber datum.1).map
            (fun changed => (changed, datum.2))
            (fun changed => (changed, datum.2)))).expectedCost
        (fun first second => dist first second) =
      pmfExp baseLaw fun datum =>
        ((fiber datum.1).map
          (fun changed => (changed, datum.2))
          (fun changed => (changed, datum.2))).expectedCost
            (fun first second => dist first second) :=
      FiniteCoupling.expectedCost_bindSharedBase _ _ _ _ _
    _ = pmfExp baseLaw fun datum =>
        (fiber datum.1).expectedCost (fun first second => dist first second) := by
      apply pmfExp_congr
      intro datum
      rw [FiniteCoupling.expectedCost_map]
      apply pmfExp_congr
      intro pair
      simp [Prod.dist_eq]

/--
Uniform agent-level transport bounds lift through the fixed population law to
the induced observable data laws with no loss in the coefficient.
-/
theorem inducedAgentStrategicDataLaw_hasExpectedCostLE
    {Agent Feature Label : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Feature] [DecidableEq Feature] [MetricSpace Feature]
    [Fintype Label] [DecidableEq Label] [MetricSpace Label]
    (baseLaw : PMF (Agent × Label)) (left right : Agent → PMF Feature)
    (bound : ℝ)
    (hfiber : ∀ agent,
      FiniteCoupling.HasExpectedCostLE (left agent) (right agent)
        (fun first second => dist first second) bound) :
    FiniteCoupling.HasExpectedCostLE
      (inducedAgentStrategicDataLaw baseLaw left)
      (inducedAgentStrategicDataLaw baseLaw right)
      (fun first second => dist first second) bound := by
  classical
  let fiber : ∀ agent, FiniteCoupling (left agent) (right agent) :=
    fun agent => (hfiber agent).choose
  refine ⟨inducedAgentStrategicDataCoupling baseLaw left right fiber, ?_⟩
  rw [expectedCost_inducedAgentStrategicDataCoupling]
  calc
    pmfExp baseLaw (fun datum =>
        (fiber datum.1).expectedCost (fun first second => dist first second)) ≤
        pmfExp baseLaw (fun _ => bound) := by
      apply pmfExp_le_pmfExp_of_forall_le
      intro datum
      exact (hfiber datum.1).choose_spec
    _ = bound := pmfExp_const baseLaw bound

/-- Tower property for statistics under a heterogeneous-agent response law. -/
theorem pmfExp_inducedAgentStrategicDataLaw
    {Agent Feature Label : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Label] [DecidableEq Label]
    (baseLaw : PMF (Agent × Label)) (response : Agent → PMF Feature)
    (statistic : Feature × Label → ℝ) :
    pmfExp (inducedAgentStrategicDataLaw baseLaw response) statistic =
      pmfExp baseLaw fun datum =>
        pmfExp (response datum.1) fun changed => statistic (changed, datum.2) := by
  rw [inducedAgentStrategicDataLaw, pmfExp_bind]
  congr 1
  funext datum
  rw [pmfExp_map]

/-- A deterministic heterogeneous response pushes the agent law through its feature map. -/
theorem pmfExp_inducedAgentStrategicDataLaw_deterministicAgentResponseKernel
    {Agent Feature Label : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Label] [DecidableEq Label]
    (baseLaw : PMF (Agent × Label)) (response : Agent → Feature)
    (statistic : Feature × Label → ℝ) :
    pmfExp
        (inducedAgentStrategicDataLaw baseLaw
          (deterministicAgentResponseKernel response)) statistic =
      pmfExp baseLaw fun datum => statistic (response datum.1, datum.2) := by
  rw [pmfExp_inducedAgentStrategicDataLaw]
  congr 1
  funext datum
  simp [deterministicAgentResponseKernel]

/-- The data law after a response kernel changes features but preserves labels. -/
noncomputable def inducedStrategicDataLaw {Feature Label : Type*}
    [Fintype Feature] [DecidableEq Feature] [Fintype Label] [DecidableEq Label]
    (baseLaw : PMF (Feature × Label)) (response : Feature → PMF Feature) :
    PMF (Feature × Label) :=
  baseLaw.bind fun datum => (response datum.1).map fun changed => (changed, datum.2)

@[simp] theorem inducedAgentStrategicDataLaw_featureAgents
    {Feature Label : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Label] [DecidableEq Label]
    (baseLaw : PMF (Feature × Label)) (response : Feature → PMF Feature) :
    inducedAgentStrategicDataLaw baseLaw response =
      inducedStrategicDataLaw baseLaw response :=
  rfl

/-- Tower property for a statistic under a strategically induced finite data law. -/
theorem pmfExp_inducedStrategicDataLaw {Feature Label : Type*}
    [Fintype Feature] [DecidableEq Feature] [Fintype Label] [DecidableEq Label]
    (baseLaw : PMF (Feature × Label)) (response : Feature → PMF Feature)
    (statistic : Feature × Label → ℝ) :
    pmfExp (inducedStrategicDataLaw baseLaw response) statistic =
      pmfExp baseLaw fun datum =>
        pmfExp (response datum.1) fun changed => statistic (changed, datum.2) := by
  rw [inducedStrategicDataLaw, pmfExp_bind]
  congr 1
  funext datum
  rw [pmfExp_map]

/-- A deterministic response kernel pushes the base law through its feature map. -/
theorem pmfExp_inducedStrategicDataLaw_deterministicResponseKernel
    {Feature Label : Type*}
    [Fintype Feature] [DecidableEq Feature] [Fintype Label] [DecidableEq Label]
    (baseLaw : PMF (Feature × Label)) (response : Feature → Feature)
    (statistic : Feature × Label → ℝ) :
    pmfExp (inducedStrategicDataLaw baseLaw (deterministicResponseKernel response)) statistic =
      pmfExp baseLaw fun datum => statistic (response datum.1, datum.2) := by
  rw [pmfExp_inducedStrategicDataLaw]
  congr 1
  funext datum
  simp [deterministicResponseKernel]

/-- Accuracy of a deterministic classifier after named heterogeneous agents respond. -/
noncomputable def agentStrategicAccuracy
    {Agent Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Agent × Bool)) (classifier : BinaryClassifier Feature)
    (response : Agent → Feature) : ℝ :=
  pmfExp baseLaw fun datum =>
    if classifier (response datum.1) = datum.2 then 1 else 0

/-- Heterogeneous-agent strategic accuracy is ordinary accuracy under the induced law. -/
theorem agentStrategicAccuracy_eq_pmfExp_inducedAgentStrategicDataLaw
    {Agent Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Agent × Bool)) (classifier : BinaryClassifier Feature)
    (response : Agent → Feature) :
    agentStrategicAccuracy baseLaw classifier response =
      pmfExp
        (inducedAgentStrategicDataLaw baseLaw
          (deterministicAgentResponseKernel response))
        (fun datum => if classifier datum.1 = datum.2 then 1 else 0) := by
  rw [pmfExp_inducedAgentStrategicDataLaw_deterministicAgentResponseKernel]
  rfl

/--
Expected accuracy when the population is indexed by heterogeneous agents and
both the deployed classifier and response kernel may randomize.
-/
noncomputable def randomizedAgentStrategicAccuracy
    {Agent Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Agent × Bool))
    (classifier : RandomizedBinaryClassifier Feature)
    (response : Agent → PMF Feature) : ℝ :=
  pmfExp (inducedAgentStrategicDataLaw baseLaw response) fun datum =>
    if datum.2 then acceptanceProbability classifier datum.1
    else 1 - acceptanceProbability classifier datum.1

/-- The heterogeneous randomized accuracy conservatively extends its deterministic form. -/
@[simp] theorem randomizedAgentStrategicAccuracy_deterministicAsRandomized
    {Agent Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Agent × Bool)) (classifier : BinaryClassifier Feature)
    (response : Agent → Feature) :
    randomizedAgentStrategicAccuracy baseLaw (deterministicAsRandomized classifier)
        (deterministicAgentResponseKernel response) =
      agentStrategicAccuracy baseLaw classifier response := by
  rw [randomizedAgentStrategicAccuracy,
    pmfExp_inducedAgentStrategicDataLaw_deterministicAgentResponseKernel]
  unfold agentStrategicAccuracy
  congr 1
  funext datum
  cases hlabel : datum.2 <;> cases hclassifier : classifier (response datum.1) <;>
    simp [hclassifier]

/-- Accuracy after strategic responses under a finite binary-labelled population. -/
noncomputable def strategicAccuracy {Feature : Type*}
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Feature × Bool)) (classifier : BinaryClassifier Feature)
    (response : Feature → Feature) : ℝ :=
  pmfExp baseLaw fun datum => if classifier (response datum.1) = datum.2 then 1 else 0

/-- Strategic accuracy is ordinary accuracy under the induced post-response law. -/
theorem strategicAccuracy_eq_pmfExp_inducedStrategicDataLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Feature × Bool)) (classifier : BinaryClassifier Feature)
    (response : Feature → Feature) :
    strategicAccuracy baseLaw classifier response =
      pmfExp (inducedStrategicDataLaw baseLaw (deterministicResponseKernel response))
        (fun datum => if classifier datum.1 = datum.2 then 1 else 0) := by
  rw [pmfExp_inducedStrategicDataLaw_deterministicResponseKernel]
  rfl

/--
Expected accuracy when both the deployed classifier and the strategic response
may randomize.  Classifier and response randomization are conditionally
independent given the post-response feature.
-/
noncomputable def randomizedStrategicAccuracy {Feature : Type*}
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Feature × Bool)) (classifier : RandomizedBinaryClassifier Feature)
    (response : Feature → PMF Feature) : ℝ :=
  pmfExp (inducedStrategicDataLaw baseLaw response) fun datum =>
    if datum.2 then acceptanceProbability classifier datum.1
    else 1 - acceptanceProbability classifier datum.1

/-- The randomized accuracy definition conservatively extends deterministic strategic accuracy. -/
@[simp] theorem randomizedStrategicAccuracy_deterministicAsRandomized
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Feature × Bool)) (classifier : BinaryClassifier Feature)
    (response : Feature → Feature) :
    randomizedStrategicAccuracy baseLaw (deterministicAsRandomized classifier)
        (deterministicResponseKernel response) =
      strategicAccuracy baseLaw classifier response := by
  rw [randomizedStrategicAccuracy,
    pmfExp_inducedStrategicDataLaw_deterministicResponseKernel]
  unfold strategicAccuracy
  congr 1
  funext datum
  cases hlabel : datum.2 <;> cases hclassifier : classifier (response datum.1) <;>
    simp [hclassifier]

/-- Finite set of features accepted by a binary classifier. -/
def acceptedFeatures {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (classifier : BinaryClassifier Feature) : Finset Feature :=
  Finset.univ.filter fun x => classifier x = true

/--
Minimum cost needed for `x` to reach an accepted feature.

The supplied nonemptiness witness makes the source paper's minimum explicit;
it avoids silently totalizing an empty acceptance set.
-/
noncomputable def individualBurden {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (cost : Feature → Feature → ℝ) (classifier : BinaryClassifier Feature) (x : Feature)
    (haccepted : (acceptedFeatures classifier).Nonempty) : ℝ :=
  ((acceptedFeatures classifier).image (cost x)).min' (haccepted.image (cost x))

/-- The finite individual burden is no larger than the cost of any accepted action. -/
theorem individualBurden_le_cost_of_accepted
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (cost : Feature → Feature → ℝ) (classifier : BinaryClassifier Feature)
    (initial final : Feature) (haccepted : (acceptedFeatures classifier).Nonempty)
    (hfinal : classifier final = true) :
    individualBurden cost classifier initial haccepted ≤ cost initial final := by
  unfold individualBurden
  apply Finset.min'_le
  apply Finset.mem_image_of_mem
  simpa [acceptedFeatures] using hfinal

/-- The finite individual burden is attained at an accepted action. -/
theorem exists_accepted_individualBurden_eq_cost
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (cost : Feature → Feature → ℝ) (classifier : BinaryClassifier Feature)
    (initial : Feature) (haccepted : (acceptedFeatures classifier).Nonempty) :
    ∃ final, classifier final = true ∧
      individualBurden cost classifier initial haccepted = cost initial final := by
  classical
  have hminimumMem :
      ((acceptedFeatures classifier).image (cost initial)).min'
          (haccepted.image (cost initial)) ∈
        (acceptedFeatures classifier).image (cost initial) :=
    Finset.min'_mem _ _
  obtain ⟨final, hfinal, hminimum⟩ := Finset.mem_image.mp hminimumMem
  refine ⟨final, ?_, ?_⟩
  · simpa [acceptedFeatures] using hfinal
  · exact hminimum.symm

/--
Individual burden is nonnegative whenever every manipulation cost is nonnegative.

This proof uses Mathlib's finite-minimum API from
[`Mathlib/Data/Finset/Max.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/Finset/Max.lean)
at pinned Apache-2.0 Mathlib revision
[`5450b53e5ddc75d46418fabb605edbf36bd0beb6`](https://github.com/leanprover-community/mathlib4/commit/5450b53e5ddc75d46418fabb605edbf36bd0beb6).
No external proof or code is copied or ported.
-/
theorem individualBurden_nonneg {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (cost : Feature → Feature → ℝ) (classifier : BinaryClassifier Feature) (x : Feature)
    (haccepted : (acceptedFeatures classifier).Nonempty)
    (hcostNonneg : ∀ initial final, 0 ≤ cost initial final) :
    0 ≤ individualBurden cost classifier x haccepted := by
  unfold individualBurden
  have hmember :
      ((acceptedFeatures classifier).image (cost x)).min'
          (haccepted.image (cost x)) ∈
        (acceptedFeatures classifier).image (cost x) :=
    Finset.min'_mem _ _
  obtain ⟨accepted, hacceptedMember, hminimum⟩ := Finset.mem_image.mp hmember
  rw [← hminimum]
  exact hcostNonneg x accepted

/--
Scaling all manipulation costs by a positive constant scales every individual burden.

The proof composes Mathlib's `Monotone.map_finset_min'` from
[`Mathlib/Data/Finset/Max.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/Finset/Max.lean)
at the pinned Apache-2.0 revision.  No external proof or code is copied or
ported.
-/
theorem individualBurden_const_mul {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (cost : Feature → Feature → ℝ) (classifier : BinaryClassifier Feature) (x : Feature)
    (haccepted : (acceptedFeatures classifier).Nonempty) (κ : ℝ) (hκ : 0 < κ) :
    individualBurden (fun initial final => κ * cost initial final) classifier x haccepted =
      κ * individualBurden cost classifier x haccepted := by
  classical
  have hscaleMonotone : Monotone (fun value : ℝ => κ * value) :=
    (strictMono_mul_left_of_pos hκ).monotone
  simpa only [individualBurden, Finset.image_image, Function.comp_apply] using
    (hscaleMonotone.map_finset_min' (haccepted.image (cost x))).symm

/-- Minimum cost for a heterogeneous agent to reach any accepted feature. -/
noncomputable def agentIndividualBurden
    {Agent AgentType Feature : Type*}
    [Fintype Feature] [DecidableEq Feature]
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (classifier : BinaryClassifier Feature) (agent : Agent)
    (haccepted : (acceptedFeatures classifier).Nonempty) : ℝ :=
  ((acceptedFeatures classifier).image (environment.cost agent)).min'
    (haccepted.image (environment.cost agent))

@[simp] theorem agentIndividualBurden_homogeneous
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (cost : Feature → Feature → ℝ) (classifier : BinaryClassifier Feature)
    (initial : Feature) (haccepted : (acceptedFeatures classifier).Nonempty) :
    agentIndividualBurden (homogeneousStrategicAgentEnvironment cost)
        classifier initial haccepted =
      individualBurden cost classifier initial haccepted :=
  rfl

/--
Restricting the accepted-feature set can only increase an individual's minimum
cost of reaching acceptance.
-/
theorem individualBurden_le_of_acceptedFeatures_subset
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (cost : Feature → Feature → ℝ)
    (lowerClassifier upperClassifier : BinaryClassifier Feature)
    (hlower : (acceptedFeatures lowerClassifier).Nonempty)
    (hupper : (acceptedFeatures upperClassifier).Nonempty)
    (hsubset : acceptedFeatures upperClassifier ⊆ acceptedFeatures lowerClassifier)
    (x : Feature) :
    individualBurden cost lowerClassifier x hlower ≤
      individualBurden cost upperClassifier x hupper := by
  unfold individualBurden
  apply Finset.le_min'
  intro value hvalue
  rcases Finset.mem_image.mp hvalue with ⟨final, hfinal, rfl⟩
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨final, hsubset hfinal, rfl⟩

/-- Social burden: expected individual burden conditional on a positive label. -/
noncomputable def socialBurden {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Feature × Bool)) (cost : Feature → Feature → ℝ)
    (classifier : BinaryClassifier Feature) (haccepted : (acceptedFeatures classifier).Nonempty) : ℝ :=
  pmfConditionalExp population (fun datum => datum.2 = true)
    (fun datum => individualBurden cost classifier datum.1 haccepted)

/-- Expected heterogeneous-agent burden conditional on a positive label. -/
noncomputable def agentSocialBurden
    {Agent AgentType Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Agent × Bool))
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (classifier : BinaryClassifier Feature)
    (haccepted : (acceptedFeatures classifier).Nonempty) : ℝ :=
  pmfConditionalExp population (fun datum => datum.2 = true)
    (fun datum => agentIndividualBurden environment classifier datum.1 haccepted)

@[simp] theorem agentSocialBurden_homogeneous
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Feature × Bool)) (cost : Feature → Feature → ℝ)
    (classifier : BinaryClassifier Feature)
    (haccepted : (acceptedFeatures classifier).Nonempty) :
    agentSocialBurden population (homogeneousStrategicAgentEnvironment cost)
        classifier haccepted =
      socialBurden population cost classifier haccepted :=
  rfl

/-- Burden conditional on a positive label and one economic agent type. -/
noncomputable def agentTypeSocialBurden
    {Agent AgentType Feature : Type*}
    [Fintype Agent] [DecidableEq Agent] [DecidableEq AgentType]
    [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Agent × Bool))
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (classifier : BinaryClassifier Feature)
    (haccepted : (acceptedFeatures classifier).Nonempty)
    (agentType : AgentType) : ℝ :=
  pmfConditionalExp population
    (fun datum => datum.2 = true ∧ environment.agentType datum.1 = agentType)
    (fun datum => agentIndividualBurden environment classifier datum.1 haccepted)

/-- Difference between the social burdens of two economic agent types. -/
noncomputable def agentTypeSocialGap
    {Agent AgentType Feature : Type*}
    [Fintype Agent] [DecidableEq Agent] [DecidableEq AgentType]
    [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Agent × Bool))
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (classifier : BinaryClassifier Feature)
    (haccepted : (acceptedFeatures classifier).Nonempty)
    (first second : AgentType) : ℝ :=
  agentTypeSocialBurden population environment classifier haccepted second -
    agentTypeSocialBurden population environment classifier haccepted first

/-- Heterogeneous-agent social burden inherits pointwise burden comparisons. -/
theorem agentSocialBurden_mono_of_forall_agentIndividualBurden_le
    {Agent AgentType Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Agent × Bool))
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (lowerClassifier upperClassifier : BinaryClassifier Feature)
    (hlower : (acceptedFeatures lowerClassifier).Nonempty)
    (hupper : (acceptedFeatures upperClassifier).Nonempty)
    (hburden : ∀ agent,
      agentIndividualBurden environment lowerClassifier agent hlower ≤
        agentIndividualBurden environment upperClassifier agent hupper) :
    agentSocialBurden population environment lowerClassifier hlower ≤
      agentSocialBurden population environment upperClassifier hupper := by
  unfold agentSocialBurden
  apply pmfConditionalExp_mono_of_forall_le
  intro datum _
  exact hburden datum.1

/-- Social burden conditional on both a positive label and group membership. -/
noncomputable def groupSocialBurden {Feature Group : Type*}
    [Fintype Feature] [DecidableEq Feature] [Fintype Group] [DecidableEq Group]
    (population : PMF (Feature × (Bool × Group))) (cost : Feature → Feature → ℝ)
    (classifier : BinaryClassifier Feature) (haccepted : (acceptedFeatures classifier).Nonempty)
    (group : Group) : ℝ :=
  pmfConditionalExp population (fun datum => datum.2.1 = true ∧ datum.2.2 = group)
    (fun datum => individualBurden cost classifier datum.1 haccepted)

/-- Difference between the social burdens of groups `b` and `a`. -/
noncomputable def socialGap {Feature Group : Type*}
    [Fintype Feature] [DecidableEq Feature] [Fintype Group] [DecidableEq Group]
    (population : PMF (Feature × (Bool × Group))) (cost : Feature → Feature → ℝ)
    (classifier : BinaryClassifier Feature) (haccepted : (acceptedFeatures classifier).Nonempty)
    (a b : Group) : ℝ :=
  groupSocialBurden population cost classifier haccepted b -
    groupSocialBurden population cost classifier haccepted a

/-- Group social burden is monotone whenever individual burden is pointwise monotone. -/
theorem groupSocialBurden_mono_of_forall_individualBurden_le
    {Feature Group : Type*} [Fintype Feature] [DecidableEq Feature]
    [Fintype Group] [DecidableEq Group]
    (population : PMF (Feature × (Bool × Group))) (cost : Feature → Feature → ℝ)
    (lowerClassifier upperClassifier : BinaryClassifier Feature)
    (hlower : (acceptedFeatures lowerClassifier).Nonempty)
    (hupper : (acceptedFeatures upperClassifier).Nonempty) (group : Group)
    (hburden : ∀ x,
      individualBurden cost lowerClassifier x hlower ≤
        individualBurden cost upperClassifier x hupper) :
    groupSocialBurden population cost lowerClassifier hlower group ≤
      groupSocialBurden population cost upperClassifier hupper group := by
  unfold groupSocialBurden
  apply pmfConditionalExp_mono_of_forall_le
  intro datum _
  exact hburden datum.1

/-- Social burden is monotone whenever individual burden is pointwise monotone. -/
theorem socialBurden_mono_of_forall_individualBurden_le
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Feature × Bool)) (cost : Feature → Feature → ℝ)
    (lowerClassifier upperClassifier : BinaryClassifier Feature)
    (hlower : (acceptedFeatures lowerClassifier).Nonempty)
    (hupper : (acceptedFeatures upperClassifier).Nonempty)
    (hburden : ∀ x,
      individualBurden cost lowerClassifier x hlower ≤
        individualBurden cost upperClassifier x hupper) :
    socialBurden population cost lowerClassifier hlower ≤
      socialBurden population cost upperClassifier hupper := by
  unfold socialBurden
  apply pmfConditionalExp_mono_of_forall_le
  intro datum _
  exact hburden datum.1

end AppliedModelingLib
