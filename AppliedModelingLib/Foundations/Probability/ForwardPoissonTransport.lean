import AppliedModelingLib.Foundations.Probability.ForwardPoisson

/-!
# Transporting a forward Poisson process along a measure-preserving map

This is a measure-theoretic transport lemma, not a new stochastic assumption.
It lets a canonical one-stream Poisson construction live as one coordinate of
a larger product probability space while preserving its increment laws.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory

noncomputable section

private theorem hasIndepIncrements_comp_measurePreserving
    {T Ω Ω' E : Type*} [Preorder T] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace E] [Sub E] [MeasurableSub₂ E]
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] (X : T → Ω → E)
    (hX_measurable : ∀ t, Measurable (X t))
    (hX : ProbabilityTheory.HasIndepIncrements X P)
    (f : Ω' → Ω) (hf : MeasurePreserving f P' P) :
    ProbabilityTheory.HasIndepIncrements (fun t ω => X t (f ω)) P' := by
  intro n t ht
  let increment : Fin n → Ω → E :=
    fun i ω => X (t i.succ) ω - X (t i.castSucc) ω
  have hincrement_meas : ∀ i, Measurable (increment i) := by
    intro i
    exact (hX_measurable _).sub (hX_measurable _)
  have hbase : ProbabilityTheory.iIndepFun increment P := by
    simpa [increment] using hX n t ht
  change ProbabilityTheory.iIndepFun (fun i => increment i ∘ f) P'
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun i => ((hincrement_meas i).comp hf.measurable).aemeasurable)]
  change P'.map ((fun ω i => increment i ω) ∘ f) =
    Measure.pi (fun i => P'.map (increment i ∘ f))
  rw [← Measure.map_map (measurable_pi_iff.2 hincrement_meas) hf.measurable,
    hf.map_eq,
    (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (hincrement_meas i).aemeasurable)).mp hbase]
  congr 1
  funext i
  rw [← Measure.map_map (hincrement_meas i) hf.measurable, hf.map_eq]

/-- Pull a forward homogeneous Poisson process back to any probability space
that maps measure-preservingly to its original carrier. -/
def ForwardHomogeneousPoissonCountingProcessByLaw.compMeasurePreserving
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (f : Ω' → Ω) (hf : MeasurePreserving f P' P) :
    ForwardHomogeneousPoissonCountingProcessByLaw Ω' P' where
  isProbability := by
    letI : IsProbabilityMeasure P := H.isProbability
    exact hf.hasLaw.isProbabilityMeasure
  rate := H.rate
  rate_pos := H.rate_pos
  count := fun t ω => H.count t (f ω)
  count_measurable := fun t => (H.count_measurable t).comp hf.measurable
  count_zero_ae := by
    simpa using hf.quasiMeasurePreserving.ae H.count_zero_ae
  count_mono_ae := by
    simpa using hf.quasiMeasurePreserving.ae H.count_mono_ae
  hasIndepIncrements := by
    letI : IsProbabilityMeasure P := H.isProbability
    letI : IsProbabilityMeasure P' := hf.hasLaw.isProbabilityMeasure
    exact hasIndepIncrements_comp_measurePreserving H.count H.count_measurable
      H.hasIndepIncrements f hf
  increment_hasLaw := by
    intro s t hst
    simpa [Function.comp_def] using (H.increment_hasLaw hst).comp hf.hasLaw

end

end AppliedModelingLib.Probability.PoissonProcess
