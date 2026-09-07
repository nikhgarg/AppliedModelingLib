import AppliedModelingLib.Learning.StrategicResponse

/-!
# Welfare under strategic response kernels

This module retains the named agent, label, and realized post-manipulation
feature in one response trace.  The trace is the joint law needed to express
actual manipulation cost and utility under randomized response maps; its
observable projection is the learner-facing strategic data law.

The main results provide:

- trace-to-observable and tower-expectation identities;
- expected score, manipulation cost, and strategic utility;
- positive-label and agent-type conditional realized burden;
- deterministic-kernel reductions; and
- invariance of expected utility across arbitrary best-response tie breaking.

Upstream credit: the trace identities directly use Mathlib's `PMF.map_bind`,
`PMF.map_comp`, and point-mass PMFs from
[`ProbabilityMassFunction/Constructions.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean)
and
[`ProbabilityMassFunction/Monad.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/ProbabilityMassFunction/Monad.lean),
at the repository's pinned Mathlib revision under Apache-2.0.  No external code
is copied or ported.
-/

namespace AppliedModelingLib

/--
One realized strategic response, retaining the named agent and its fixed label
alongside the post-manipulation feature observed by the learner.
-/
structure StrategicResponseTrace (Agent Label Feature : Type*) where
  agent : Agent
  label : Label
  changedFeature : Feature
deriving Fintype, DecidableEq

namespace StrategicResponseTrace

/-- The learner-facing feature-label datum obtained by forgetting agent identity. -/
def observableData {Agent Label Feature : Type*}
    (trace : StrategicResponseTrace Agent Label Feature) : Feature × Label :=
  (trace.changedFeature, trace.label)

end StrategicResponseTrace

/--
Joint response law: sample a named agent and label from the base population,
then sample that agent's realized post-manipulation feature.
-/
noncomputable def inducedAgentStrategicTraceLaw
    {Agent Label Feature : Type*}
    (baseLaw : PMF (Agent × Label)) (response : Agent → PMF Feature) :
    PMF (StrategicResponseTrace Agent Label Feature) :=
  baseLaw.bind fun datum =>
    (response datum.1).map fun changed =>
      { agent := datum.1, label := datum.2, changedFeature := changed }

/-- Forgetting agent identity in the joint trace gives the observable data law. -/
theorem map_inducedAgentStrategicTraceLaw_observableData
    {Agent Label Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Label] [DecidableEq Label]
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Agent × Label)) (response : Agent → PMF Feature) :
    (inducedAgentStrategicTraceLaw baseLaw response).map
        StrategicResponseTrace.observableData =
      inducedAgentStrategicDataLaw baseLaw response := by
  rw [inducedAgentStrategicTraceLaw, inducedAgentStrategicDataLaw,
    PMF.map_bind]
  congr 1
  funext datum
  rw [PMF.map_comp]
  rfl

/-- Tower property for a statistic on the full strategic response trace. -/
theorem pmfExp_inducedAgentStrategicTraceLaw
    {Agent Label Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Label] [DecidableEq Label]
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Agent × Label)) (response : Agent → PMF Feature)
    (statistic : StrategicResponseTrace Agent Label Feature → ℝ) :
    pmfExp (inducedAgentStrategicTraceLaw baseLaw response) statistic =
      pmfExp baseLaw fun datum =>
        pmfExp (response datum.1) fun changed =>
          statistic
            { agent := datum.1, label := datum.2, changedFeature := changed } := by
  rw [inducedAgentStrategicTraceLaw, pmfExp_bind]
  congr 1
  funext datum
  rw [pmfExp_map]

/-- Deterministic responses reduce the trace expectation to a base-law expectation. -/
theorem pmfExp_inducedAgentStrategicTraceLaw_deterministicAgentResponseKernel
    {Agent Label Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Label] [DecidableEq Label]
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Agent × Label)) (response : Agent → Feature)
    (statistic : StrategicResponseTrace Agent Label Feature → ℝ) :
    pmfExp
        (inducedAgentStrategicTraceLaw baseLaw
          (deterministicAgentResponseKernel response)) statistic =
      pmfExp baseLaw fun datum =>
        statistic
          { agent := datum.1, label := datum.2,
            changedFeature := response datum.1 } := by
  rw [pmfExp_inducedAgentStrategicTraceLaw]
  congr 1
  funext datum
  simp [deterministicAgentResponseKernel]

/-- A base-population event has the same probability when lifted to the trace. -/
theorem pmfProb_inducedAgentStrategicTraceLaw_baseEvent
    {Agent Label Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Label] [DecidableEq Label]
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Agent × Label)) (response : Agent → PMF Feature)
    (event : Agent × Label → Prop) [DecidablePred event] :
    pmfProb (inducedAgentStrategicTraceLaw baseLaw response)
        (fun trace => event (trace.agent, trace.label)) =
      pmfProb baseLaw event := by
  unfold pmfProb
  rw [pmfExp_inducedAgentStrategicTraceLaw]
  apply pmfExp_congr
  intro datum
  by_cases hevent : event datum
  · simp [hevent, pmfExp_const]
  · simp [hevent, pmfExp_const]

/-- Indicator expectations over base events satisfy the response-trace tower law. -/
theorem pmfIndicatorExp_inducedAgentStrategicTraceLaw_baseEvent
    {Agent Label Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Label] [DecidableEq Label]
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Agent × Label)) (response : Agent → PMF Feature)
    (event : Agent × Label → Prop) [DecidablePred event]
    (statistic : StrategicResponseTrace Agent Label Feature → ℝ) :
    pmfIndicatorExp (inducedAgentStrategicTraceLaw baseLaw response)
        (fun trace => event (trace.agent, trace.label)) statistic =
      pmfIndicatorExp baseLaw event (fun datum =>
        pmfExp (response datum.1) fun changed =>
          statistic
            { agent := datum.1, label := datum.2,
              changedFeature := changed }) := by
  unfold pmfIndicatorExp
  rw [pmfExp_inducedAgentStrategicTraceLaw]
  apply pmfExp_congr
  intro datum
  by_cases hevent : event datum
  · simp [hevent]
  · simp [hevent]

/-- Conditional tower property for events determined before strategic response. -/
theorem pmfConditionalExp_inducedAgentStrategicTraceLaw_baseEvent
    {Agent Label Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Label] [DecidableEq Label]
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Agent × Label)) (response : Agent → PMF Feature)
    (event : Agent × Label → Prop) [DecidablePred event]
    (statistic : StrategicResponseTrace Agent Label Feature → ℝ) :
    pmfConditionalExp (inducedAgentStrategicTraceLaw baseLaw response)
        (fun trace => event (trace.agent, trace.label)) statistic =
      pmfConditionalExp baseLaw event (fun datum =>
        pmfExp (response datum.1) fun changed =>
          statistic
            { agent := datum.1, label := datum.2,
              changedFeature := changed }) := by
  unfold pmfConditionalExp
  rw [pmfProb_inducedAgentStrategicTraceLaw_baseEvent,
    pmfIndicatorExp_inducedAgentStrategicTraceLaw_baseEvent]

/-- Expected realized score of one agent under a response kernel. -/
noncomputable def agentExpectedResponseScore
    {Agent Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (score : Feature → ℝ) (response : Agent → PMF Feature) (agent : Agent) : ℝ :=
  pmfExp (response agent) score

/-- Expected realized manipulation cost of one agent under a response kernel. -/
noncomputable def agentExpectedManipulationCost
    {Agent AgentType Feature : Type*}
    [Fintype Feature] [DecidableEq Feature]
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → PMF Feature) (agent : Agent) : ℝ :=
  pmfExp (response agent) (environment.cost agent)

/-- Expected strategic utility of one agent under a response kernel. -/
noncomputable def agentExpectedResponseUtility
    {Agent AgentType Feature : Type*}
    [Fintype Feature] [DecidableEq Feature]
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → PMF Feature) (agent : Agent) : ℝ :=
  pmfExp (response agent) (agentStrategicUtility score environment agent)

/-- Expected strategic utility is expected score minus expected manipulation cost. -/
theorem agentExpectedResponseUtility_eq_score_sub_cost
    {Agent AgentType Feature : Type*}
    [Fintype Feature] [DecidableEq Feature]
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → PMF Feature) (agent : Agent) :
    agentExpectedResponseUtility score environment response agent =
      agentExpectedResponseScore score response agent -
        agentExpectedManipulationCost environment response agent := by
  rw [agentExpectedResponseUtility, agentExpectedResponseScore,
    agentExpectedManipulationCost, ← pmfExp_sub]
  rfl

@[simp] theorem agentExpectedResponseScore_deterministicAgentResponseKernel
    {Agent Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (score : Feature → ℝ) (response : Agent → Feature) (agent : Agent) :
    agentExpectedResponseScore score
        (deterministicAgentResponseKernel response) agent =
      score (response agent) := by
  simp [agentExpectedResponseScore, deterministicAgentResponseKernel]

@[simp] theorem agentExpectedManipulationCost_deterministicAgentResponseKernel
    {Agent AgentType Feature : Type*}
    [Fintype Feature] [DecidableEq Feature]
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → Feature) (agent : Agent) :
    agentExpectedManipulationCost environment
        (deterministicAgentResponseKernel response) agent =
      environment.cost agent (response agent) := by
  simp [agentExpectedManipulationCost, deterministicAgentResponseKernel]

@[simp] theorem agentExpectedResponseUtility_deterministicAgentResponseKernel
    {Agent AgentType Feature : Type*}
    [Fintype Feature] [DecidableEq Feature]
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → Feature) (agent : Agent) :
    agentExpectedResponseUtility score environment
        (deterministicAgentResponseKernel response) agent =
      agentStrategicUtility score environment agent (response agent) := by
  simp [agentExpectedResponseUtility, deterministicAgentResponseKernel]

/-- Population expected realized score, evaluated on the joint response trace. -/
noncomputable def agentPopulationExpectedResponseScore
    {Agent Label Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Label] [DecidableEq Label]
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Agent × Label)) (score : Feature → ℝ)
    (response : Agent → PMF Feature) : ℝ :=
  pmfExp (inducedAgentStrategicTraceLaw baseLaw response)
    (fun trace => score trace.changedFeature)

/-- Population expected realized manipulation cost on the joint response trace. -/
noncomputable def agentPopulationExpectedManipulationCost
    {Agent AgentType Label Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Label] [DecidableEq Label]
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Agent × Label))
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → PMF Feature) : ℝ :=
  pmfExp (inducedAgentStrategicTraceLaw baseLaw response)
    (fun trace => environment.cost trace.agent trace.changedFeature)

/-- Population expected strategic utility on the joint response trace. -/
noncomputable def agentPopulationExpectedResponseUtility
    {Agent AgentType Label Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Label] [DecidableEq Label]
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Agent × Label)) (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → PMF Feature) : ℝ :=
  pmfExp (inducedAgentStrategicTraceLaw baseLaw response)
    (fun trace =>
      agentStrategicUtility score environment trace.agent trace.changedFeature)

theorem agentPopulationExpectedResponseScore_eq_tower
    {Agent Label Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Label] [DecidableEq Label]
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Agent × Label)) (score : Feature → ℝ)
    (response : Agent → PMF Feature) :
    agentPopulationExpectedResponseScore baseLaw score response =
      pmfExp baseLaw fun datum =>
        agentExpectedResponseScore score response datum.1 := by
  rw [agentPopulationExpectedResponseScore,
    pmfExp_inducedAgentStrategicTraceLaw]
  rfl

theorem agentPopulationExpectedManipulationCost_eq_tower
    {Agent AgentType Label Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Label] [DecidableEq Label]
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Agent × Label))
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → PMF Feature) :
    agentPopulationExpectedManipulationCost baseLaw environment response =
      pmfExp baseLaw fun datum =>
        agentExpectedManipulationCost environment response datum.1 := by
  rw [agentPopulationExpectedManipulationCost,
    pmfExp_inducedAgentStrategicTraceLaw]
  rfl

theorem agentPopulationExpectedResponseUtility_eq_tower
    {Agent AgentType Label Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Label] [DecidableEq Label]
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Agent × Label)) (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → PMF Feature) :
    agentPopulationExpectedResponseUtility baseLaw score environment response =
      pmfExp baseLaw fun datum =>
        agentExpectedResponseUtility score environment response datum.1 := by
  rw [agentPopulationExpectedResponseUtility,
    pmfExp_inducedAgentStrategicTraceLaw]
  rfl

/-- Population expected utility decomposes into expected score minus expected cost. -/
theorem agentPopulationExpectedResponseUtility_eq_score_sub_cost
    {Agent AgentType Label Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Label] [DecidableEq Label]
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Agent × Label)) (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → PMF Feature) :
    agentPopulationExpectedResponseUtility baseLaw score environment response =
      agentPopulationExpectedResponseScore baseLaw score response -
        agentPopulationExpectedManipulationCost baseLaw environment response := by
  unfold agentPopulationExpectedResponseUtility
    agentPopulationExpectedResponseScore
    agentPopulationExpectedManipulationCost
  rw [← pmfExp_sub]
  rfl

/-- Realized manipulation burden conditional on a positive ground-truth label. -/
noncomputable def agentResponseSocialBurden
    {Agent AgentType Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Agent × Bool))
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → PMF Feature) : ℝ :=
  pmfConditionalExp (inducedAgentStrategicTraceLaw population response)
    (fun trace => trace.label = true)
    (fun trace => environment.cost trace.agent trace.changedFeature)

/-- Realized positive-label burden equals the conditional mean of agent-level cost. -/
theorem agentResponseSocialBurden_eq_tower
    {Agent AgentType Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Agent × Bool))
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → PMF Feature) :
    agentResponseSocialBurden population environment response =
      pmfConditionalExp population (fun datum => datum.2 = true)
        (fun datum =>
          agentExpectedManipulationCost environment response datum.1) := by
  simpa [agentResponseSocialBurden, agentExpectedManipulationCost] using
    (pmfConditionalExp_inducedAgentStrategicTraceLaw_baseEvent
      population response (fun datum : Agent × Bool => datum.2 = true)
      (fun trace => environment.cost trace.agent trace.changedFeature))

/-- Realized burden conditional on a positive label and one economic agent type. -/
noncomputable def agentTypeResponseSocialBurden
    {Agent AgentType Feature : Type*}
    [Fintype Agent] [DecidableEq Agent] [DecidableEq AgentType]
    [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Agent × Bool))
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → PMF Feature) (agentType : AgentType) : ℝ :=
  pmfConditionalExp (inducedAgentStrategicTraceLaw population response)
    (fun trace => trace.label = true ∧
      environment.agentType trace.agent = agentType)
    (fun trace => environment.cost trace.agent trace.changedFeature)

theorem agentTypeResponseSocialBurden_eq_tower
    {Agent AgentType Feature : Type*}
    [Fintype Agent] [DecidableEq Agent] [DecidableEq AgentType]
    [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Agent × Bool))
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → PMF Feature) (agentType : AgentType) :
    agentTypeResponseSocialBurden population environment response agentType =
      pmfConditionalExp population
        (fun datum => datum.2 = true ∧
          environment.agentType datum.1 = agentType)
        (fun datum =>
          agentExpectedManipulationCost environment response datum.1) := by
  simpa [agentTypeResponseSocialBurden, agentExpectedManipulationCost] using
    (pmfConditionalExp_inducedAgentStrategicTraceLaw_baseEvent
      population response
      (fun datum : Agent × Bool => datum.2 = true ∧
        environment.agentType datum.1 = agentType)
      (fun trace => environment.cost trace.agent trace.changedFeature))

/-- Difference in realized response burden between two economic agent types. -/
noncomputable def agentTypeResponseSocialGap
    {Agent AgentType Feature : Type*}
    [Fintype Agent] [DecidableEq Agent] [DecidableEq AgentType]
    [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Agent × Bool))
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → PMF Feature) (first second : AgentType) : ℝ :=
  agentTypeResponseSocialBurden population environment response second -
    agentTypeResponseSocialBurden population environment response first

/-- Homogeneous specialization of realized response burden. -/
noncomputable def responseSocialBurden
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Feature × Bool)) (cost : Feature → Feature → ℝ)
    (response : Feature → PMF Feature) : ℝ :=
  agentResponseSocialBurden population
    (homogeneousStrategicAgentEnvironment cost) response

@[simp] theorem agentResponseSocialBurden_homogeneous
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Feature × Bool)) (cost : Feature → Feature → ℝ)
    (response : Feature → PMF Feature) :
    agentResponseSocialBurden population
        (homogeneousStrategicAgentEnvironment cost) response =
      responseSocialBurden population cost response :=
  rfl

@[simp] theorem agentResponseSocialBurden_deterministicAgentResponseKernel
    {Agent AgentType Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Agent × Bool))
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → Feature) :
    agentResponseSocialBurden population environment
        (deterministicAgentResponseKernel response) =
      pmfConditionalExp population (fun datum => datum.2 = true)
        (fun datum => environment.cost datum.1 (response datum.1)) := by
  rw [agentResponseSocialBurden_eq_tower]
  apply pmfConditionalExp_congr_on
  intro datum _
  simp

@[simp] theorem agentTypeResponseSocialBurden_deterministicAgentResponseKernel
    {Agent AgentType Feature : Type*}
    [Fintype Agent] [DecidableEq Agent] [DecidableEq AgentType]
    [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Agent × Bool))
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → Feature) (agentType : AgentType) :
    agentTypeResponseSocialBurden population environment
        (deterministicAgentResponseKernel response) agentType =
      pmfConditionalExp population
        (fun datum => datum.2 = true ∧
          environment.agentType datum.1 = agentType)
        (fun datum => environment.cost datum.1 (response datum.1)) := by
  rw [agentTypeResponseSocialBurden_eq_tower]
  apply pmfConditionalExp_congr_on
  intro datum _
  simp

/--
Every best-response tie-breaking kernel gives the agent the same expected
utility: all positive-mass actions attain the same maximum value.
-/
theorem agentExpectedResponseUtility_eq_selected_of_bestResponseKernel
    {Agent AgentType Feature : Type*}
    [Fintype Feature] [DecidableEq Feature]
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (response : Agent → PMF Feature)
    (hresponse :
      IsAgentStrategicBestResponseKernel score environment response)
    (agent : Agent) :
    agentExpectedResponseUtility score environment response agent =
      agentStrategicUtility score environment agent
        (selectedAgentStrategicBestResponse score environment agent) := by
  unfold agentExpectedResponseUtility
  apply pmfExp_eq_const_of_support_eq
  intro chosen hmass
  have hchosen_ne : response agent chosen ≠ 0 := by
    intro hzero
    rw [hzero] at hmass
    simp at hmass
  have hchosen : chosen ∈ (response agent).support :=
    (PMF.mem_support_iff (response agent) chosen).2 hchosen_ne
  have hchosen_best := hresponse agent chosen hchosen
  have hselected_best :=
    selectedAgentStrategicBestResponse_spec score environment agent
  exact le_antisymm
    (hselected_best chosen)
    (hchosen_best
      (selectedAgentStrategicBestResponse score environment agent))

/-- Expected utility is invariant across any two best-response tie-breaking rules. -/
theorem agentExpectedResponseUtility_eq_of_bestResponseKernels
    {Agent AgentType Feature : Type*}
    [Fintype Feature] [DecidableEq Feature]
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (first second : Agent → PMF Feature)
    (hfirst : IsAgentStrategicBestResponseKernel score environment first)
    (hsecond : IsAgentStrategicBestResponseKernel score environment second)
    (agent : Agent) :
    agentExpectedResponseUtility score environment first agent =
      agentExpectedResponseUtility score environment second agent := by
  rw [agentExpectedResponseUtility_eq_selected_of_bestResponseKernel
      score environment first hfirst agent,
    agentExpectedResponseUtility_eq_selected_of_bestResponseKernel
      score environment second hsecond agent]

/--
Across best-response tie breaking, any expected-score difference is exactly the
same as the expected manipulation-cost difference; utility itself is fixed.
-/
theorem agentExpectedResponseScore_sub_eq_cost_sub_of_bestResponseKernels
    {Agent AgentType Feature : Type*}
    [Fintype Feature] [DecidableEq Feature]
    (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (first second : Agent → PMF Feature)
    (hfirst : IsAgentStrategicBestResponseKernel score environment first)
    (hsecond : IsAgentStrategicBestResponseKernel score environment second)
    (agent : Agent) :
    agentExpectedResponseScore score first agent -
        agentExpectedResponseScore score second agent =
      agentExpectedManipulationCost environment first agent -
        agentExpectedManipulationCost environment second agent := by
  have hutility := agentExpectedResponseUtility_eq_of_bestResponseKernels
    score environment first second hfirst hsecond agent
  rw [agentExpectedResponseUtility_eq_score_sub_cost,
    agentExpectedResponseUtility_eq_score_sub_cost] at hutility
  linarith

/-- Population expected utility is invariant across best-response tie breaking. -/
theorem agentPopulationExpectedResponseUtility_eq_of_bestResponseKernels
    {Agent AgentType Label Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Label] [DecidableEq Label]
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Agent × Label)) (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (first second : Agent → PMF Feature)
    (hfirst : IsAgentStrategicBestResponseKernel score environment first)
    (hsecond : IsAgentStrategicBestResponseKernel score environment second) :
    agentPopulationExpectedResponseUtility baseLaw score environment first =
      agentPopulationExpectedResponseUtility baseLaw score environment second := by
  rw [agentPopulationExpectedResponseUtility_eq_tower,
    agentPopulationExpectedResponseUtility_eq_tower]
  apply pmfExp_congr
  intro datum
  exact agentExpectedResponseUtility_eq_of_bestResponseKernels
    score environment first second hfirst hsecond datum.1

/--
At population level, a change in best-response tie breaking changes expected
score by exactly the same amount as expected manipulation cost.  This is the
aggregate counterpart of agent-level utility invariance.
-/
theorem agentPopulationExpectedResponseScore_sub_eq_cost_sub_of_bestResponseKernels
    {Agent AgentType Label Feature : Type*}
    [Fintype Agent] [DecidableEq Agent]
    [Fintype Label] [DecidableEq Label]
    [Fintype Feature] [DecidableEq Feature]
    (baseLaw : PMF (Agent × Label)) (score : Feature → ℝ)
    (environment : StrategicAgentEnvironment Agent AgentType Feature)
    (first second : Agent → PMF Feature)
    (hfirst : IsAgentStrategicBestResponseKernel score environment first)
    (hsecond : IsAgentStrategicBestResponseKernel score environment second) :
    agentPopulationExpectedResponseScore baseLaw score first -
        agentPopulationExpectedResponseScore baseLaw score second =
      agentPopulationExpectedManipulationCost baseLaw environment first -
        agentPopulationExpectedManipulationCost baseLaw environment second := by
  have hutility :=
    agentPopulationExpectedResponseUtility_eq_of_bestResponseKernels
      baseLaw score environment first second hfirst hsecond
  rw [agentPopulationExpectedResponseUtility_eq_score_sub_cost,
    agentPopulationExpectedResponseUtility_eq_score_sub_cost] at hutility
  linarith

end AppliedModelingLib
