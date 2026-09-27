import PZMH20PerformativePrediction.Definitions
import Mathlib.Topology.TietzeExtension

/-!
# Domain-relative existence for Proposition 4.1

This file gives a compact-convex stable-point theorem while keeping every
analytic object on the parameter domain.  In particular, neither the law map
nor loss integrability is postulated outside `domain`, and continuity of
decoupled risk is required only on `domain × domain`.

The proof extends the *continuous risk function*, not the statistical model.
Tietze extension is therefore only a topological proof device: its off-domain
values have no statistical interpretation and do not strengthen the theorem's
premises.  A Dirac auxiliary model lets the existing Kakutani endpoint consume
that extension.  All conclusions are then transported back to the original
domain model.
-/

namespace PZMH20PerformativePrediction

open AppliedModelingLib
open MeasureTheory

/--
The pointwise loss of a domain model, viewed as an ambient function by assigning
zero away from the domain.  `ConvexOn` reads this function only on `domain`, so
the off-domain value is immaterial.
-/
noncomputable def measureLossOnDomain
    {Parameter Data : Type*} [MeasurableSpace Data] {domain : Set Parameter}
    (model : MeasurePerformativeModelOn Parameter Data domain)
    (datum : Data) (parameter : Parameter) : ℝ := by
  classical
  exact if hparameter : parameter ∈ domain then
    model.loss datum ⟨parameter, hparameter⟩ else 0

/--
Domain-relative arbitrary-law compact-convex existence for Proposition 4.1.

The loss-convexity hypothesis reads the displayed zero extension only at
points of `domain`, as prescribed by `ConvexOn`; consequently it assumes no
off-domain loss regularity.  Likewise, `hjoint` is continuity on the subtype
`domain × domain`, not on the ambient parameter product.
-/
theorem measureDomainCompactConvexStablePointExists
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    [FiniteDimensional ℝ Parameter] [MeasurableSpace Data]
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (hcompact : IsCompact domain) (hne : domain.Nonempty) (hconvex : Convex ℝ domain)
    (hjoint : Continuous (fun point : domain × domain =>
      model.decoupledPerformativeRisk point.1 point.2))
    (hlossConvex : ∀ datum, ConvexOn ℝ domain (measureLossOnDomain model datum)) :
    ∃ stable : domain, model.IsPerformativelyStable stable := by
  classical
  letI : Nonempty domain := Set.nonempty_coe_sort.mpr hne

  -- The restricted risk is the only object extended to the ambient product.
  let restrictedRisk : C(domain × domain, ℝ) :=
    ⟨fun point => model.decoupledPerformativeRisk point.1 point.2, hjoint⟩
  let inclusion : domain × domain → Parameter × Parameter :=
    Prod.map ((↑) : domain → Parameter) ((↑) : domain → Parameter)
  have hinclusion : Topology.IsClosedEmbedding inclusion := by
    exact hcompact.isClosed.isClosedEmbedding_subtypeVal.prodMap
      hcompact.isClosed.isClosedEmbedding_subtypeVal
  obtain ⟨extendedRisk, hextends⟩ :=
    ContinuousMap.exists_extension' hinclusion restrictedRisk
  have hextends_on (deployed evaluated : domain) :
      extendedRisk ((deployed : Parameter), (evaluated : Parameter)) =
        model.decoupledPerformativeRisk deployed evaluated := by
    have hagree := congr_fun hextends (deployed, evaluated)
    simpa [inclusion, restrictedRisk, Function.comp_def] using hagree

  -- A Dirac auxiliary model realizes the extended scalar function exactly as
  -- decoupled risk.  It carries no additional premise about the source model.
  letI : MeasurableSpace Parameter := borel Parameter
  letI : BorelSpace Parameter := ⟨rfl⟩
  let auxiliary : MeasurePerformativeModel Parameter Parameter :=
    { dataLaw := fun deployed => MeasureTheory.diracProba deployed
      loss := fun datum evaluated => extendedRisk (datum, evaluated)
      loss_integrable := by
        intro deployed evaluated
        simpa [MeasureTheory.diracProba] using
          (MeasureTheory.integrable_dirac
            (a := deployed) (f := fun datum => extendedRisk (datum, evaluated)) (by simp)) }
  have hauxiliaryRisk (deployed evaluated : Parameter) :
      measureDecoupledPerformativeRisk auxiliary deployed evaluated =
        extendedRisk (deployed, evaluated) := by
    simp [measureDecoupledPerformativeRisk, auxiliary, MeasureTheory.diracProba]
  have hauxiliaryContinuous : Continuous (fun point : Parameter × Parameter =>
      measureDecoupledPerformativeRisk auxiliary point.1 point.2) := by
    simpa only [hauxiliaryRisk] using extendedRisk.continuous

  -- On the feasible set the source loss agrees with the standard anchored
  -- extension.  Existing integration convexity can therefore be reused
  -- without imposing any property on the extension away from the domain.
  let anchor : domain := Classical.choice inferInstance
  have hextendedLossConvex : ∀ datum,
      ConvexOn ℝ domain ((model.extend anchor).loss datum) := by
    intro datum
    simpa [MeasurePerformativeModelOn.extend, measureLossOnDomain] using hlossConvex datum
  have hextendedFrozenConvex : ∀ deployed : domain,
      ConvexOn ℝ domain (fun candidate =>
        measureDecoupledPerformativeRisk (model.extend anchor) deployed candidate) :=
    convexOn_measureDecoupledPerformativeRisk_of_lossConvex
      (model.extend anchor) domain hconvex hextendedLossConvex
  have hauxiliaryFrozenConvex : ∀ deployed : domain,
      ConvexOn ℝ domain (fun candidate =>
        measureDecoupledPerformativeRisk auxiliary deployed candidate) := by
    intro deployed
    apply (hextendedFrozenConvex deployed).congr
    intro candidate hcandidate
    let evaluated : domain := ⟨candidate, hcandidate⟩
    calc
      measureDecoupledPerformativeRisk (model.extend anchor) deployed candidate =
          model.decoupledPerformativeRisk deployed evaluated :=
        model.decoupledPerformativeRisk_extend anchor deployed evaluated
      _ = extendedRisk ((deployed : Parameter), candidate) :=
        (hextends_on deployed evaluated).symm
      _ = measureDecoupledPerformativeRisk auxiliary deployed candidate :=
        (hauxiliaryRisk deployed candidate).symm

  obtain ⟨stable, hstable_mem, hstable⟩ :=
    exists_isMeasurePerformativelyStableOn_of_compact_convex auxiliary domain
      hcompact hne hconvex hauxiliaryContinuous hauxiliaryFrozenConvex
  let stableOn : domain := ⟨stable, hstable_mem⟩
  refine ⟨stableOn, ?_⟩
  intro candidate
  calc
    model.decoupledPerformativeRisk stableOn stableOn =
        extendedRisk ((stableOn : Parameter), (stableOn : Parameter)) :=
      (hextends_on stableOn stableOn).symm
    _ = measureDecoupledPerformativeRisk auxiliary stable stable :=
      (hauxiliaryRisk stable stable).symm
    _ ≤ measureDecoupledPerformativeRisk auxiliary stable candidate :=
      hstable.2 candidate candidate.property
    _ = extendedRisk (stable, (candidate : Parameter)) :=
      hauxiliaryRisk stable candidate
    _ = model.decoupledPerformativeRisk stableOn candidate :=
      hextends_on stableOn candidate

end PZMH20PerformativePrediction
