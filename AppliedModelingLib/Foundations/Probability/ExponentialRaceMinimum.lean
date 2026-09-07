import AppliedModelingLib.Foundations.Probability.ExponentialUnequalRateConvolution
import AppliedModelingLib.Foundations.Probability.ExponentialMoments
import Mathlib.Probability.HasLaw
import Mathlib.Tactic

/-!
# Minimum of two independent exponential clocks

For two independent positive-rate exponential clocks, the first clock to ring
has the exponential law at the sum of their rates.  The proof combines the two
explicit change-of-variables calculations for the branches on which either
coordinate is smaller.
-/

namespace AppliedModelingLib.Probability

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory

noncomputable section

/-- The time of the first event in a two-clock exponential race. -/
def exponentialRaceMinimum (p : ℝ × ℝ) : ℝ :=
  min p.1 p.2

theorem measurable_exponentialRaceMinimum :
    Measurable exponentialRaceMinimum := by
  exact measurable_fst.min measurable_snd

/-- The first event of two independent positive-rate exponential clocks has
the exponential law at the sum of their rates. -/
theorem map_exponentialRaceMinimum_expMeasure_prod
    {leftRate rightRate : ℝ} (hleft : 0 < leftRate) (hright : 0 < rightRate) :
    Measure.map exponentialRaceMinimum
      ((expMeasure leftRate).prod (expMeasure rightRate)) =
        expMeasure (leftRate + rightRate) := by
  letI : IsProbabilityMeasure (expMeasure leftRate) :=
    isProbabilityMeasure_expMeasure hleft
  letI : IsProbabilityMeasure (expMeasure rightRate) :=
    isProbabilityMeasure_expMeasure hright
  letI : IsProbabilityMeasure (expMeasure (leftRate + rightRate)) :=
    isProbabilityMeasure_expMeasure (add_pos hleft hright)
  let pair : Measure (ℝ × ℝ) :=
    (expMeasure leftRate).prod (expMeasure rightRate)
  let carrier : Set (ℝ × ℝ) := exponentialDifferencePositiveCarrier
  have hsplit : pair = pair.restrict carrier + pair.restrict carrierᶜ := by
    simpa [pair, carrier] using
      (Measure.restrict_add_restrict_compl
        (μ := (expMeasure leftRate).prod (expMeasure rightRate))
        measurableSet_exponentialDifferencePositiveCarrier).symm
  have hpositive :
      Measure.map exponentialRaceMinimum (pair.restrict carrier) =
        ENNReal.ofReal (rightRate / (leftRate + rightRate)) •
          expMeasure (leftRate + rightRate) := by
    calc
      Measure.map exponentialRaceMinimum (pair.restrict carrier) =
          Measure.map Prod.snd
            (Measure.map exponentialDifferenceUnshear (pair.restrict carrier)) := by
              rw [Measure.map_map measurable_snd
                measurable_exponentialDifferenceUnshear]
              apply Measure.map_congr
              filter_upwards [ae_restrict_mem
                measurableSet_exponentialDifferencePositiveCarrier] with p hp
              exact min_eq_right (le_of_lt hp)
      _ = Measure.map Prod.snd
          (ENNReal.ofReal (rightRate / (leftRate + rightRate)) •
            ((expMeasure leftRate).prod (expMeasure (leftRate + rightRate)))) := by
            rw [map_exponentialDifferenceUnshear_expMeasure_prod_restrict_positive
              hleft hright]
      _ = ENNReal.ofReal (rightRate / (leftRate + rightRate)) •
          expMeasure (leftRate + rightRate) := by
            rw [Measure.map_smul, Measure.map_snd_prod, measure_univ, one_smul]
  have hcomplement :
      Measure.map exponentialRaceMinimum (pair.restrict carrierᶜ) =
        ENNReal.ofReal (leftRate / (leftRate + rightRate)) •
          expMeasure (leftRate + rightRate) := by
    calc
      Measure.map exponentialRaceMinimum (pair.restrict carrierᶜ) =
          Measure.map Prod.fst
            (Measure.map exponentialDifferenceComplementUnshear
              (pair.restrict carrierᶜ)) := by
              rw [Measure.map_map measurable_fst
                measurable_exponentialDifferenceComplementUnshear]
              apply Measure.map_congr
              filter_upwards [ae_restrict_mem
                measurableSet_exponentialDifferencePositiveCarrier.compl] with p hp
              exact min_eq_left (le_of_not_gt hp)
      _ = Measure.map Prod.fst
          (ENNReal.ofReal (leftRate / (leftRate + rightRate)) •
            ((expMeasure (leftRate + rightRate)).prod (expMeasure rightRate))) := by
            rw [map_exponentialDifferenceComplementUnshear_expMeasure_prod_restrict_compl
              hleft hright]
      _ = ENNReal.ofReal (leftRate / (leftRate + rightRate)) •
          expMeasure (leftRate + rightRate) := by
            rw [Measure.map_smul, Measure.map_fst_prod, measure_univ, one_smul]
  have hsum_pos : 0 < leftRate + rightRate := add_pos hleft hright
  calc
    Measure.map exponentialRaceMinimum pair =
        Measure.map exponentialRaceMinimum
          (pair.restrict carrier + pair.restrict carrierᶜ) :=
            congrArg (Measure.map exponentialRaceMinimum) hsplit
    _ = Measure.map exponentialRaceMinimum (pair.restrict carrier) +
        Measure.map exponentialRaceMinimum (pair.restrict carrierᶜ) := by
          rw [Measure.map_add _ _ measurable_exponentialRaceMinimum]
    _ = ENNReal.ofReal (rightRate / (leftRate + rightRate)) •
          expMeasure (leftRate + rightRate) +
        ENNReal.ofReal (leftRate / (leftRate + rightRate)) •
          expMeasure (leftRate + rightRate) := by rw [hpositive, hcomplement]
    _ = (ENNReal.ofReal (rightRate / (leftRate + rightRate)) +
          ENNReal.ofReal (leftRate / (leftRate + rightRate))) •
          expMeasure (leftRate + rightRate) := by rw [add_smul]
    _ = expMeasure (leftRate + rightRate) := by
          have hright_nonneg : 0 ≤ rightRate / (leftRate + rightRate) :=
            div_nonneg hright.le hsum_pos.le
          have hleft_nonneg : 0 ≤ leftRate / (leftRate + rightRate) :=
            div_nonneg hleft.le hsum_pos.le
          rw [← ENNReal.ofReal_add hright_nonneg hleft_nonneg]
          have hsum : rightRate / (leftRate + rightRate) +
              leftRate / (leftRate + rightRate) = 1 := by
            field_simp [ne_of_gt hsum_pos]
            ring
          rw [hsum]
          simp

/-- Law form of the two-clock exponential-race minimum. -/
theorem exponentialRaceMinimum_hasLaw_expMeasure
    {leftRate rightRate : ℝ} (hleft : 0 < leftRate) (hright : 0 < rightRate) :
    ProbabilityTheory.HasLaw exponentialRaceMinimum (expMeasure (leftRate + rightRate))
      ((expMeasure leftRate).prod (expMeasure rightRate)) := by
  exact ⟨measurable_exponentialRaceMinimum.aemeasurable,
    map_exponentialRaceMinimum_expMeasure_prod hleft hright⟩

/-- The two-clock exponential-race holding time is integrable. -/
theorem integrable_exponentialRaceMinimum_expMeasure_prod
    {leftRate rightRate : ℝ} (hleft : 0 < leftRate) (hright : 0 < rightRate) :
    Integrable exponentialRaceMinimum
      ((expMeasure leftRate).prod (expMeasure rightRate)) := by
  let P : Measure (ℝ × ℝ) := (expMeasure leftRate).prod (expMeasure rightRate)
  let rate := leftRate + rightRate
  have hrate : 0 < rate := add_pos hleft hright
  have hLaw : ProbabilityTheory.HasLaw exponentialRaceMinimum (expMeasure rate) P := by
    simpa [P, rate] using exponentialRaceMinimum_hasLaw_expMeasure hleft hright
  have hmapInt : Integrable (fun x : ℝ => x)
      (Measure.map exponentialRaceMinimum P) := by
    rw [hLaw.map_eq]
    exact integrable_id_expMeasure hrate
  simpa [Function.comp_def] using
    (integrable_map_measure aestronglyMeasurable_id hLaw.aemeasurable).mp hmapInt

/-- The expected two-clock exponential-race holding time is the reciprocal of
the summed rate. -/
theorem integral_exponentialRaceMinimum_expMeasure_prod_eq_inv_sum
    {leftRate rightRate : ℝ} (hleft : 0 < leftRate) (hright : 0 < rightRate) :
    (∫ p, exponentialRaceMinimum p
      ∂((expMeasure leftRate).prod (expMeasure rightRate))) =
        1 / (leftRate + rightRate) := by
  have hrate : 0 < leftRate + rightRate := add_pos hleft hright
  calc
    (∫ p, exponentialRaceMinimum p
      ∂((expMeasure leftRate).prod (expMeasure rightRate))) =
        ∫ x, x ∂expMeasure (leftRate + rightRate) :=
          (exponentialRaceMinimum_hasLaw_expMeasure hleft hright).integral_eq
    _ = 1 / (leftRate + rightRate) := integral_id_expMeasure hrate

/-- The branch on which the left clock is no later than the right clock. -/
def exponentialRaceLeftWinnerCarrier (α : Type*) : Set (ℝ × (ℝ × α)) :=
  {z | z.1 ≤ z.2.1}

/-- On the left-winner branch, retain the winner time, subtract it from the
right clock, and leave an independent auxiliary coordinate untouched. -/
def exponentialRaceLeftWinnerResidual {α : Type*} :
    ℝ × (ℝ × α) -> ℝ × (ℝ × α) :=
  fun z => (z.1, (z.2.1 - z.1, z.2.2))

theorem measurable_exponentialRaceLeftWinnerResidual {α : Type*}
    [MeasurableSpace α] :
    Measurable (exponentialRaceLeftWinnerResidual (α := α)) := by
  exact measurable_fst.prodMk
    ((measurable_fst.comp measurable_snd).sub measurable_fst |>.prodMk
      (measurable_snd.comp measurable_snd))

theorem measurableSet_exponentialRaceLeftWinnerCarrier {α : Type*}
    [MeasurableSpace α] :
    MeasurableSet (exponentialRaceLeftWinnerCarrier α) := by
  exact measurableSet_le measurable_fst (measurable_fst.comp measurable_snd)

/-- Move the leading coordinate of a three-factor product past the next one,
while retaining the final coordinate. -/
def productFrontSwap {α β γ : Type*} : α × (β × γ) -> β × (α × γ) :=
  fun z => (z.2.1, (z.1, z.2.2))

theorem measurable_productFrontSwap {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    Measurable (productFrontSwap (α := α) (β := β) (γ := γ)) := by
  exact (measurable_fst.comp measurable_snd).prodMk
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

theorem map_productFrontSwap {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ξ : Measure γ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] :
    Measure.map (productFrontSwap (α := α) (β := β) (γ := γ))
      (μ.prod (ν.prod ξ)) = ν.prod (μ.prod ξ) := by
  calc
    Measure.map (productFrontSwap (α := α) (β := β) (γ := γ))
        (μ.prod (ν.prod ξ)) =
        Measure.map (MeasurableEquiv.prodAssoc : (β × α) × γ -> β × (α × γ))
          (Measure.map (Prod.map Prod.swap id)
            (Measure.map (MeasurableEquiv.prodAssoc.symm :
              α × (β × γ) -> (α × β) × γ) (μ.prod (ν.prod ξ)))) := by
            symm
            rw [Measure.map_map
                (measurable_swap.prodMap measurable_id)
                MeasurableEquiv.prodAssoc.symm.measurable,
              Measure.map_map MeasurableEquiv.prodAssoc.measurable
                ((measurable_swap.prodMap measurable_id).comp
                  MeasurableEquiv.prodAssoc.symm.measurable)]
            rfl
    _ = Measure.map (MeasurableEquiv.prodAssoc : (β × α) × γ -> β × (α × γ))
          (Measure.map (Prod.map Prod.swap id) ((μ.prod ν).prod ξ)) := by
            rw [(measurePreserving_prodAssoc μ ν ξ).symm.map_eq]
    _ = Measure.map (MeasurableEquiv.prodAssoc : (β × α) × γ -> β × (α × γ))
          ((ν.prod μ).prod ξ) := by
            rw [← Measure.map_prod_map (μ.prod ν) ξ measurable_swap measurable_id,
              Measure.prod_swap, Measure.map_id]
    _ = ν.prod (μ.prod ξ) := by
            exact (measurePreserving_prodAssoc ν μ ξ).map_eq

/-- On a left-winner race branch with an independently carried leading
coordinate, retain the elapsed winner time, the right-clock residual, and
both untouched coordinates. -/
def exponentialRaceLeftWinnerResidualWithLeadingAux {α β : Type*} :
    ((α × ℝ) × (ℝ × β)) -> ℝ × (ℝ × (α × β)) :=
  fun z => (z.2.1, (z.1.2 - z.2.1, (z.1.1, z.2.2)))

/-- The left-winner carrier for a race whose right-clock head follows an
independent leading coordinate. -/
def exponentialRaceLeftWinnerLeadingAuxCarrier {α β : Type*} :
    Set ((α × ℝ) × (ℝ × β)) :=
  {z | z.2.1 ≤ z.1.2}

theorem measurable_exponentialRaceLeftWinnerResidualWithLeadingAux {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (exponentialRaceLeftWinnerResidualWithLeadingAux (α := α) (β := β)) := by
  exact (measurable_fst.comp measurable_snd).prodMk
    (((measurable_snd.comp measurable_fst).sub (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_snd)))

theorem measurableSet_exponentialRaceLeftWinnerLeadingAuxCarrier {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] :
    MeasurableSet (exponentialRaceLeftWinnerLeadingAuxCarrier (α := α) (β := β)) := by
  exact measurableSet_le (measurable_fst.comp measurable_snd)
    (measurable_snd.comp measurable_fst)

/-- Restricting to the branch where the left exponential clock wins leaves a
fresh right-clock residual, jointly with any independent auxiliary input. -/
theorem map_exponentialRaceLeftWinnerResidual_expMeasure_prod_restrict
    {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    {leftRate rightRate : ℝ} (hleft : 0 < leftRate) (hright : 0 < rightRate) :
    Measure.map (exponentialRaceLeftWinnerResidual (α := α))
      (((expMeasure leftRate).prod ((expMeasure rightRate).prod ν)).restrict
        (exponentialRaceLeftWinnerCarrier α)) =
      ENNReal.ofReal (leftRate / (leftRate + rightRate)) •
        ((expMeasure (leftRate + rightRate)).prod ((expMeasure rightRate).prod ν)) := by
  let pair : Measure (ℝ × ℝ) := (expMeasure leftRate).prod (expMeasure rightRate)
  let base : Measure ((ℝ × ℝ) × α) := pair.prod ν
  let target : Measure (ℝ × (ℝ × α)) :=
    (expMeasure leftRate).prod ((expMeasure rightRate).prod ν)
  let carrier : Set (ℝ × ℝ) := exponentialDifferencePositiveCarrierᶜ
  let assoc : (ℝ × ℝ) × α -> ℝ × (ℝ × α) :=
    fun z => (z.1.1, (z.1.2, z.2))
  let lift : (ℝ × ℝ) × α -> (ℝ × ℝ) × α :=
    Prod.map exponentialDifferenceComplementUnshear id
  letI : IsProbabilityMeasure (expMeasure leftRate) :=
    isProbabilityMeasure_expMeasure hleft
  letI : IsProbabilityMeasure (expMeasure rightRate) :=
    isProbabilityMeasure_expMeasure hright
  letI : IsProbabilityMeasure (expMeasure (leftRate + rightRate)) :=
    isProbabilityMeasure_expMeasure (add_pos hleft hright)
  letI : IsProbabilityMeasure pair := by
    dsimp [pair]
    infer_instance
  letI : IsProbabilityMeasure base := by
    dsimp [base]
    infer_instance
  have hassoc : Measure.map assoc base = target := by
    simpa [assoc, base, pair, target] using
      (measurePreserving_prodAssoc (expMeasure leftRate) (expMeasure rightRate) ν).map_eq
  have hassoc_meas : Measurable assoc := by
    simpa [assoc] using (MeasurableEquiv.prodAssoc.measurable :
      Measurable (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × α ≃ᵐ ℝ × (ℝ × α)))
  have hcarrier_preimage : assoc ⁻¹' exponentialRaceLeftWinnerCarrier α =
      carrier ×ˢ Set.univ := by
    ext z
    rcases z with ⟨p, a⟩
    rcases p with ⟨x, y⟩
    simp [assoc, exponentialRaceLeftWinnerCarrier, carrier,
      exponentialDifferencePositiveCarrier, not_lt]
  have hresidual_comp :
      exponentialRaceLeftWinnerResidual (α := α) ∘ assoc =
        assoc ∘ lift := by
    funext z
    rcases z with ⟨p, a⟩
    rcases p with ⟨x, y⟩
    rfl
  have hlift_meas : Measurable lift := by
    exact measurable_exponentialDifferenceComplementUnshear.prodMap measurable_id
  have hrestricted :
      base.restrict (assoc ⁻¹' exponentialRaceLeftWinnerCarrier α) =
        (pair.restrict carrier).prod ν := by
    rw [hcarrier_preimage]
    exact (Measure.restrict_prod_eq_prod_univ (μ := pair) (ν := ν) carrier).symm
  have hpair :
      Measure.map exponentialDifferenceComplementUnshear (pair.restrict carrier) =
        ENNReal.ofReal (leftRate / (leftRate + rightRate)) •
          ((expMeasure (leftRate + rightRate)).prod (expMeasure rightRate)) := by
    simpa [pair, carrier] using
      (map_exponentialDifferenceComplementUnshear_expMeasure_prod_restrict_compl
        hleft hright)
  calc
    Measure.map (exponentialRaceLeftWinnerResidual (α := α))
        (target.restrict (exponentialRaceLeftWinnerCarrier α)) =
        Measure.map (exponentialRaceLeftWinnerResidual (α := α))
          ((Measure.map assoc base).restrict (exponentialRaceLeftWinnerCarrier α)) := by
            rw [hassoc]
    _ = Measure.map (exponentialRaceLeftWinnerResidual (α := α))
        (Measure.map assoc
          (base.restrict (assoc ⁻¹' exponentialRaceLeftWinnerCarrier α))) := by
            rw [← Measure.restrict_map
              hassoc_meas
              (measurableSet_exponentialRaceLeftWinnerCarrier (α := α))]
    _ = Measure.map
        (exponentialRaceLeftWinnerResidual (α := α) ∘ assoc)
        (base.restrict (assoc ⁻¹' exponentialRaceLeftWinnerCarrier α)) := by
          rw [← Measure.map_map
            (measurable_exponentialRaceLeftWinnerResidual (α := α))
            hassoc_meas]
    _ = Measure.map (assoc ∘ lift)
        (base.restrict (assoc ⁻¹' exponentialRaceLeftWinnerCarrier α)) := by
          rw [hresidual_comp]
    _ = Measure.map assoc
        (Measure.map lift
          (base.restrict (assoc ⁻¹' exponentialRaceLeftWinnerCarrier α))) := by
          rw [← Measure.map_map
            hassoc_meas hlift_meas]
    _ = Measure.map assoc (Measure.map lift ((pair.restrict carrier).prod ν)) := by
          rw [hrestricted]
    _ = Measure.map assoc
        ((Measure.map exponentialDifferenceComplementUnshear (pair.restrict carrier)).prod
          (Measure.map id ν)) := by
          rw [show lift = Prod.map exponentialDifferenceComplementUnshear id by rfl,
            ← Measure.map_prod_map (pair.restrict carrier) ν
              measurable_exponentialDifferenceComplementUnshear measurable_id]
    _ = Measure.map assoc
        ((ENNReal.ofReal (leftRate / (leftRate + rightRate)) •
          ((expMeasure (leftRate + rightRate)).prod (expMeasure rightRate))).prod ν) := by
          rw [hpair, Measure.map_id]
    _ = ENNReal.ofReal (leftRate / (leftRate + rightRate)) •
        ((expMeasure (leftRate + rightRate)).prod ((expMeasure rightRate).prod ν)) := by
          rw [Measure.prod_smul_left, Measure.map_smul]
          simpa [assoc] using congrArg
            (fun μ => ENNReal.ofReal (leftRate / (leftRate + rightRate)) • μ)
            (measurePreserving_prodAssoc
              (expMeasure (leftRate + rightRate)) (expMeasure rightRate) ν).map_eq

/-- Conditioning an exponential race while carrying an independent leading
auxiliary coordinate preserves that coordinate jointly with the residual. -/
theorem map_exponentialRaceLeftWinnerResidualWithLeadingAux_expMeasure_prod_restrict
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) (ξ : Measure β) [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
    {leftRate rightRate : ℝ} (hleft : 0 < leftRate) (hright : 0 < rightRate) :
    Measure.map (exponentialRaceLeftWinnerResidualWithLeadingAux (α := α) (β := β))
      (((ν.prod (expMeasure rightRate)).prod ((expMeasure leftRate).prod ξ)).restrict
        (exponentialRaceLeftWinnerLeadingAuxCarrier (α := α) (β := β))) =
      ENNReal.ofReal (leftRate / (leftRate + rightRate)) •
        ((expMeasure (leftRate + rightRate)).prod
          ((expMeasure rightRate).prod (ν.prod ξ))) := by
  let S := expMeasure rightRate
  let T := expMeasure leftRate
  let source : Measure ((α × ℝ) × (ℝ × β)) := (ν.prod S).prod (T.prod ξ)
  let target : Measure (ℝ × (ℝ × (α × β))) := T.prod (S.prod (ν.prod ξ))
  let reorder : ((α × ℝ) × (ℝ × β)) -> ℝ × (ℝ × (α × β)) :=
    fun z => (z.2.1, (z.1.2, (z.1.1, z.2.2)))
  let carrier := exponentialRaceLeftWinnerLeadingAuxCarrier (α := α) (β := β)
  letI : IsProbabilityMeasure S := by
    dsimp [S]
    exact isProbabilityMeasure_expMeasure hright
  letI : IsProbabilityMeasure T := by
    dsimp [T]
    exact isProbabilityMeasure_expMeasure hleft
  have hreorder_meas : Measurable reorder := by
    exact (measurable_fst.comp measurable_snd).prodMk
      ((measurable_snd.comp measurable_fst).prodMk
        ((measurable_fst.comp measurable_fst).prodMk
          (measurable_snd.comp measurable_snd)))
  have hstep1 : Measure.map (MeasurableEquiv.prodAssoc :
      (α × ℝ) × (ℝ × β) -> α × (ℝ × (ℝ × β))) source =
      ν.prod (S.prod (T.prod ξ)) := by
    simpa [source, S, T] using (measurePreserving_prodAssoc ν S (T.prod ξ)).map_eq
  have hstep2 : Measure.map
      (Prod.map id (productFrontSwap (α := ℝ) (β := ℝ) (γ := β)))
      (ν.prod (S.prod (T.prod ξ))) = ν.prod (T.prod (S.prod ξ)) := by
    rw [← Measure.map_prod_map ν (S.prod (T.prod ξ)) measurable_id
      (measurable_productFrontSwap (α := ℝ) (β := ℝ) (γ := β)),
      Measure.map_id, map_productFrontSwap S T ξ]
  have hstep3 : Measure.map
      (productFrontSwap (α := α) (β := ℝ) (γ := ℝ × β))
      (ν.prod (T.prod (S.prod ξ))) = T.prod (ν.prod (S.prod ξ)) := by
    exact map_productFrontSwap ν T (S.prod ξ)
  have hstep4 : Measure.map
      (Prod.map id (productFrontSwap (α := α) (β := ℝ) (γ := β)))
      (T.prod (ν.prod (S.prod ξ))) = T.prod (S.prod (ν.prod ξ)) := by
    rw [← Measure.map_prod_map T (ν.prod (S.prod ξ)) measurable_id
      (measurable_productFrontSwap (α := α) (β := ℝ) (γ := β)),
      Measure.map_id, map_productFrontSwap ν S ξ]
  have hreorder : Measure.map reorder source = target := by
    let f1 : ((α × ℝ) × (ℝ × β)) -> α × (ℝ × (ℝ × β)) :=
      MeasurableEquiv.prodAssoc
    let f2 : α × (ℝ × (ℝ × β)) -> α × (ℝ × (ℝ × β)) :=
      Prod.map id (productFrontSwap (α := ℝ) (β := ℝ) (γ := β))
    let f3 : α × (ℝ × (ℝ × β)) -> ℝ × (α × (ℝ × β)) :=
      productFrontSwap (α := α) (β := ℝ) (γ := ℝ × β)
    let f4 : ℝ × (α × (ℝ × β)) -> ℝ × (ℝ × (α × β)) :=
      Prod.map id (productFrontSwap (α := α) (β := ℝ) (γ := β))
    have hf1 : Measurable f1 := by
      exact MeasurableEquiv.prodAssoc.measurable
    have hf2 : Measurable f2 := by
      exact measurable_id.prodMap
        (measurable_productFrontSwap (α := ℝ) (β := ℝ) (γ := β))
    have hf3 : Measurable f3 := by
      exact measurable_productFrontSwap (α := α) (β := ℝ) (γ := ℝ × β)
    have hf4 : Measurable f4 := by
      exact measurable_id.prodMap
        (measurable_productFrontSwap (α := α) (β := ℝ) (γ := β))
    calc
      Measure.map reorder source =
          Measure.map f4 (Measure.map f3 (Measure.map f2 (Measure.map f1 source))) := by
            symm
            rw [Measure.map_map hf2 hf1,
              Measure.map_map hf3 (hf2.comp hf1),
              Measure.map_map hf4 (hf3.comp (hf2.comp hf1))]
            rfl
      _ = Measure.map f4 (Measure.map f3 (Measure.map f2 (ν.prod (S.prod (T.prod ξ))))) := by
            simpa [f1] using congrArg (fun μ => Measure.map f4 (Measure.map f3 (Measure.map f2 μ)))
              hstep1
      _ = Measure.map f4 (Measure.map f3 (ν.prod (T.prod (S.prod ξ)))) := by
            simpa [f2] using congrArg (fun μ => Measure.map f4 (Measure.map f3 μ)) hstep2
      _ = Measure.map f4 (T.prod (ν.prod (S.prod ξ))) := by
            simpa [f3] using congrArg (fun μ => Measure.map f4 μ) hstep3
      _ = target := by simpa [f4, target] using hstep4
  have hcarrier_preimage : reorder ⁻¹'
      (exponentialRaceLeftWinnerCarrier (α × β)) = carrier := by
    ext z
    simp [reorder, carrier, exponentialRaceLeftWinnerCarrier,
      exponentialRaceLeftWinnerLeadingAuxCarrier]
  calc
    Measure.map (exponentialRaceLeftWinnerResidualWithLeadingAux (α := α) (β := β))
        (source.restrict carrier) =
        Measure.map (exponentialRaceLeftWinnerResidual (α := α × β))
          (Measure.map reorder (source.restrict carrier)) := by
            rw [show exponentialRaceLeftWinnerResidualWithLeadingAux (α := α) (β := β) =
              exponentialRaceLeftWinnerResidual (α := α × β) ∘ reorder by rfl,
              Measure.map_map
                (measurable_exponentialRaceLeftWinnerResidual (α := α × β))
                hreorder_meas]
    _ = Measure.map (exponentialRaceLeftWinnerResidual (α := α × β))
        ((Measure.map reorder source).restrict
          (exponentialRaceLeftWinnerCarrier (α × β))) := by
            rw [← hcarrier_preimage, Measure.restrict_map hreorder_meas
              (measurableSet_exponentialRaceLeftWinnerCarrier (α := α × β))]
    _ = Measure.map (exponentialRaceLeftWinnerResidual (α := α × β))
        (target.restrict (exponentialRaceLeftWinnerCarrier (α × β))) := by rw [hreorder]
    _ = ENNReal.ofReal (leftRate / (leftRate + rightRate)) •
        ((expMeasure (leftRate + rightRate)).prod (S.prod (ν.prod ξ))) := by
          simpa [target, T] using
            (map_exponentialRaceLeftWinnerResidual_expMeasure_prod_restrict
              (ν := ν.prod ξ) hleft hright)
    _ = ENNReal.ofReal (leftRate / (leftRate + rightRate)) •
        ((expMeasure (leftRate + rightRate)).prod
          ((expMeasure rightRate).prod (ν.prod ξ))) := by rfl

end

end AppliedModelingLib.Probability
