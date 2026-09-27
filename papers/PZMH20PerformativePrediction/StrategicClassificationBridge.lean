import PZMH20PerformativePrediction.Definitions

/-!
# General-measure strategic-classification bridge

Section 5 describes a baseline population on feature--label pairs and, for
each deployed classifier, a feature response selected from the agent's
utility-maximization problem.  The label is unchanged.  This file constructs
the induced distribution as the measurable pushforward of the baseline law
and identifies the institution's expected loss with performative risk.

The source writes `xBR ← arg max` without specifying how ties are broken.
Accordingly, the definitions below take one fixed supplied response family and
state its best-response property separately.  The Stackelberg statement is
relative to that same selection; no selection-invariance claim is made.
-/

namespace PZMH20PerformativePrediction

open AppliedModelingLib
open MeasureTheory

/-- The source data transformation: change the feature and preserve the label. -/
def strategicClassificationDataMap
    {Parameter Feature Label : Type*} {domain : Set Parameter}
    (response : domain → Feature → Feature) (parameter : domain) :
    Feature × Label → Feature × Label :=
  fun datum => (response parameter datum.1, datum.2)

/-- A measurable feature response induces a measurable feature--label map. -/
theorem measurable_strategicClassificationDataMap
    {Parameter Feature Label : Type*}
    [MeasurableSpace Feature] [MeasurableSpace Label]
    {domain : Set Parameter} (response : domain → Feature → Feature)
    (parameter : domain) (hresponse : Measurable (response parameter)) :
    Measurable (strategicClassificationDataMap (Label := Label) response parameter) :=
  (hresponse.comp measurable_fst).prodMk measurable_snd

/-- The strategic data transformation leaves every outcome label unchanged. -/
@[simp] theorem strategicClassificationDataMap_snd
    {Parameter Feature Label : Type*} {domain : Set Parameter}
    (response : domain → Feature → Feature) (parameter : domain)
    (datum : Feature × Label) :
    (strategicClassificationDataMap response parameter datum).2 = datum.2 :=
  rfl

/-- The distribution induced by a selected measurable strategic response. -/
noncomputable def strategicClassificationInducedLaw
    {Parameter Feature Label : Type*}
    [MeasurableSpace Feature] [MeasurableSpace Label]
    {domain : Set Parameter} (population : ProbabilityMeasure (Feature × Label))
    (response : domain → Feature → Feature)
    (hresponse : ∀ parameter, Measurable (response parameter))
    (parameter : domain) : ProbabilityMeasure (Feature × Label) :=
  population.map
    (measurable_strategicClassificationDataMap (Label := Label) response parameter
      (hresponse parameter)).aemeasurable

/--
A general-measure strategic-classification profile with a fixed response
selection.  Utility and cost determine whether that selection is behaviorally
valid; `loss_integrable` is exactly the cross-risk integrability required by
the domain-relative performative model.
-/
structure MeasureStrategicClassificationProfile
    (Parameter Feature Label : Type*)
    [MeasurableSpace Feature] [MeasurableSpace Label]
    (domain : Set Parameter) where
  population : ProbabilityMeasure (Feature × Label)
  response : domain → Feature → Feature
  utility : Feature → domain → ℝ
  cost : Feature → Feature → ℝ
  loss : (Feature × Label) → domain → ℝ
  response_measurable : ∀ parameter, Measurable (response parameter)
  loss_integrable : ∀ deployed evaluated,
    Integrable (fun datum => loss datum evaluated)
      (strategicClassificationInducedLaw population response response_measurable deployed :
        Measure (Feature × Label))

namespace MeasureStrategicClassificationProfile

variable {Parameter Feature Label : Type*}
  [MeasurableSpace Feature] [MeasurableSpace Label]
  {domain : Set Parameter}

/-- The induced law associated with the profile's fixed response selection. -/
noncomputable def inducedLaw
    (profile : MeasureStrategicClassificationProfile Parameter Feature Label domain)
    (parameter : domain) : ProbabilityMeasure (Feature × Label) :=
  strategicClassificationInducedLaw profile.population profile.response
    profile.response_measurable parameter

/--
The selected response solves every pointwise follower problem.  The cost order
is `cost chosen initial`, matching the optimization in Figure 2.
-/
def IsFollowerBestResponse
    (profile : MeasureStrategicClassificationProfile Parameter Feature Label domain) : Prop :=
  ∀ parameter initial alternative,
    profile.utility alternative parameter - profile.cost alternative initial ≤
      profile.utility (profile.response parameter initial) parameter -
        profile.cost (profile.response parameter initial) initial

/-- The domain-relative performative model induced by the strategic population. -/
noncomputable def performativeModelOn
    (profile : MeasureStrategicClassificationProfile Parameter Feature Label domain) :
    MeasurePerformativeModelOn Parameter (Feature × Label) domain where
  dataLaw := profile.inducedLaw
  loss := profile.loss
  loss_integrable := by
    intro deployed evaluated
    exact profile.loss_integrable deployed evaluated

/-- The institution's loss under the law induced by its deployed parameter. -/
noncomputable def leaderRisk
    (profile : MeasureStrategicClassificationProfile Parameter Feature Label domain)
    (parameter : domain) : ℝ :=
  profile.performativeModelOn.performativeRisk parameter

/-- Leader optimality for the fixed selected best-response family. -/
def IsLeaderOptimal
    (profile : MeasureStrategicClassificationProfile Parameter Feature Label domain)
    (parameter : domain) : Prop :=
  ∀ candidate, profile.leaderRisk parameter ≤ profile.leaderRisk candidate

/--
The Stackelberg condition keeps its two logical components visible: the whole
selected response family consists of follower best responses, and the leader
minimizes loss against the laws induced by that family.
-/
def IsStackelbergEquilibrium
    (profile : MeasureStrategicClassificationProfile Parameter Feature Label domain)
    (parameter : domain) : Prop :=
  profile.IsFollowerBestResponse ∧ profile.IsLeaderOptimal parameter

/-- Decoupled risk under the induced pushforward law is an expectation over
the original population with strategically transformed features. -/
theorem decoupledPerformativeRisk_eq_integral_response
    (profile : MeasureStrategicClassificationProfile Parameter Feature Label domain)
    (deployed evaluated : domain) :
    profile.performativeModelOn.decoupledPerformativeRisk deployed evaluated =
      ∫ datum, profile.loss
          (profile.response deployed datum.1, datum.2) evaluated
        ∂(profile.population : Measure (Feature × Label)) := by
  have hmap := measurable_strategicClassificationDataMap (Label := Label)
    profile.response deployed
    (profile.response_measurable deployed)
  have hloss := (profile.loss_integrable deployed evaluated).aestronglyMeasurable
  simpa [MeasurePerformativeModelOn.decoupledPerformativeRisk, performativeModelOn,
    inducedLaw, strategicClassificationInducedLaw, strategicClassificationDataMap] using
    (MeasureTheory.integral_map hmap.aemeasurable hloss)

/-- The leader's pushforward-law expectation is the source population
expectation after applying the selected strategic response. -/
theorem leaderRisk_eq_integral_response
    (profile : MeasureStrategicClassificationProfile Parameter Feature Label domain)
    (parameter : domain) :
    profile.leaderRisk parameter =
      ∫ datum, profile.loss
          (profile.response parameter datum.1, datum.2) parameter
        ∂(profile.population : Measure (Feature × Label)) := by
  simpa [leaderRisk, MeasurePerformativeModelOn.performativeRisk] using
    profile.decoupledPerformativeRisk_eq_integral_response parameter parameter

/-- For the same selected response family, leader optimality is exactly
performative optimality of the induced domain model. -/
theorem isLeaderOptimal_iff_isPerformativelyOptimal
    (profile : MeasureStrategicClassificationProfile Parameter Feature Label domain)
    (parameter : domain) :
    profile.IsLeaderOptimal parameter ↔
      profile.performativeModelOn.IsPerformativelyOptimal parameter := by
  rfl

/-- The exact Stackelberg--performative bridge, with the follower condition
retained as a separate conjunct rather than hidden in the equivalence. -/
theorem isStackelbergEquilibrium_iff
    (profile : MeasureStrategicClassificationProfile Parameter Feature Label domain)
    (parameter : domain) :
    profile.IsStackelbergEquilibrium parameter ↔
      profile.IsFollowerBestResponse ∧
        profile.performativeModelOn.IsPerformativelyOptimal parameter := by
  rw [IsStackelbergEquilibrium, isLeaderOptimal_iff_isPerformativelyOptimal]

/-- Once the displayed pointwise argmax condition is checked, the source's
Stackelberg condition is equivalent to performative optimality. -/
theorem isStackelbergEquilibrium_iff_isPerformativelyOptimal
    (profile : MeasureStrategicClassificationProfile Parameter Feature Label domain)
    (parameter : domain) (hresponse : profile.IsFollowerBestResponse) :
    profile.IsStackelbergEquilibrium parameter ↔
      profile.performativeModelOn.IsPerformativelyOptimal parameter := by
  rw [profile.isStackelbergEquilibrium_iff]
  simp only [hresponse, true_and]

end MeasureStrategicClassificationProfile

end PZMH20PerformativePrediction
