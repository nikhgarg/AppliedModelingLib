import AppliedModelingLib.Foundations.Probability.PoissonEquilibriumHalves

/-!
# Product factors for the Poisson suspension bridge

This module gives the iid product decompositions that connect the local
residual/age split of the origin-straddling gap with the untouched positive
and negative tails of a two-sided Palm gap path.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The singleton head coordinate and the natural-number tail coordinate of
a one-sided iid path. -/
def headTailIndex : Fin 2 → Type :=
  Fin.cases PUnit (fun _ => ℕ)

instance (i : Fin 2) : MeasurableSpace (headTailIndex i) := by
  rcases i with ⟨i, hi⟩
  cases i with
  | zero =>
      change MeasurableSpace PUnit
      exact inferInstance
  | succ i =>
      change MeasurableSpace ℕ
      exact inferInstance

/-- Enumerate a singleton head followed by a natural-number tail. -/
def headTailIndexEquivNat : (Sigma headTailIndex) ≃ ℕ where
  toFun p := Fin.cases (fun _ : PUnit => 0) (fun _ (n : ℕ) => n + 1) p.1 p.2
  invFun n := match n with
    | 0 => ⟨0, PUnit.unit⟩
    | n + 1 => ⟨1, n⟩
  left_inv p := by
    rcases p with ⟨i, x⟩
    fin_cases i
    · cases x
      rfl
    · rfl
  right_inv n := by
    cases n <;> rfl

/-- Split a one-sided path into its head and its tail. -/
def headTail : (ℕ → ℝ) → ℝ × (ℕ → ℝ) :=
  fun f => (f 0, fun n => f (n + 1))

/-- `headTail` is a measurable equivalence, with inverse given by prepending
the displayed head to the displayed tail. -/
def headTailEquiv : (ℕ → ℝ) ≃ᵐ ℝ × (ℕ → ℝ) where
  toFun := headTail
  invFun := fun p n => match n with
    | 0 => p.1
    | n + 1 => p.2 n
  left_inv f := by
    funext n
    cases n <;> rfl
  right_inv p := by
    ext n <;> rfl
  measurable_toFun := by
    apply Measurable.prodMk
    · exact measurable_pi_apply _
    · exact measurable_pi_iff.2 fun n => measurable_pi_apply _
  measurable_invFun := by
    refine measurable_pi_iff.2 fun n => ?_
    cases n with
    | zero => exact measurable_fst
    | succ n => exact measurable_pi_apply n |>.comp measurable_snd

theorem measurable_headTail : Measurable headTail :=
  headTailEquiv.measurable

theorem headTail_piCongrLeft_eq
    (x : (Sigma headTailIndex) → ℝ) :
    headTail ((MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℝ) headTailIndexEquivNat) x) =
      Prod.map (MeasurableEquiv.funUnique PUnit ℝ) id
        ((MeasurableEquiv.piFinTwo (fun i : Fin 2 => headTailIndex i → ℝ))
          ((MeasurableEquiv.piCurry (fun _ : Fin 2 => fun _ : headTailIndex _ => ℝ)) x)) := by
  rw [MeasurableEquiv.piFinTwo_apply, MeasurableEquiv.coe_piCurry,
    MeasurableEquiv.coe_piCongrLeft, MeasurableEquiv.funUnique_apply]
  ext
  · change (Equiv.piCongrLeft (fun _ : ℕ => ℝ) headTailIndexEquivNat x) 0 =
      x ⟨0, PUnit.unit⟩
    simpa [headTailIndexEquivNat] using
      (Equiv.piCongrLeft_apply_apply (fun _ : ℕ => ℝ) headTailIndexEquivNat x
        ⟨0, PUnit.unit⟩)
  · rename_i n
    change (Equiv.piCongrLeft (fun _ : ℕ => ℝ) headTailIndexEquivNat x) (n + 1) =
      x ⟨1, n⟩
    simpa [headTailIndexEquivNat] using
      (Equiv.piCongrLeft_apply_apply (fun _ : ℕ => ℝ) headTailIndexEquivNat x ⟨1, n⟩)

/-- A one-sided iid exponential path factors into an exponential head and
an independent iid exponential tail. -/
theorem map_headTail_exponentialInterarrivalMeasure
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map headTail (exponentialInterarrivalMeasure rate) =
      (expMeasure rate).prod (exponentialInterarrivalMeasure rate) := by
  let μ : Measure ℝ := expMeasure rate
  let ρ : Measure ((Sigma headTailIndex) → ℝ) :=
    Measure.infinitePi (fun _ : Sigma headTailIndex => μ)
  let E : ((Sigma headTailIndex) → ℝ) ≃ᵐ (ℕ → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℝ) headTailIndexEquivNat
  let C : ((Sigma headTailIndex) → ℝ) ≃ᵐ
      ((i : Fin 2) → headTailIndex i → ℝ) :=
    MeasurableEquiv.piCurry (fun _ : Fin 2 => fun _ : headTailIndex _ => ℝ)
  let F : ((i : Fin 2) → headTailIndex i → ℝ) ≃ᵐ
      (PUnit → ℝ) × (ℕ → ℝ) :=
    MeasurableEquiv.piFinTwo (fun i : Fin 2 => headTailIndex i → ℝ)
  let U : (PUnit → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique PUnit ℝ
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hE : Measure.map E ρ = exponentialInterarrivalMeasure rate := by
    calc
      Measure.map E ρ = Measure.infinitePi (fun _ : ℕ => μ) := by
        exact Measure.infinitePi_map_piCongrLeft
          (fun _ : ℕ => μ) headTailIndexEquivNat
      _ = exponentialInterarrivalMeasure rate := by
        simp [μ, exponentialInterarrivalMeasure]
  have hC : Measure.map C ρ =
      Measure.infinitePi (fun i : Fin 2 =>
        Measure.infinitePi (fun _ : headTailIndex i => μ)) := by
    exact Measure.infinitePi_map_piCurry
      (fun _ : Fin 2 => fun _ : headTailIndex _ => μ)
  have hF : Measure.map F
      (Measure.infinitePi (fun i : Fin 2 =>
        Measure.infinitePi (fun _ : headTailIndex i => μ))) =
      (Measure.infinitePi (fun _ : PUnit => μ)).prod
        (Measure.infinitePi (fun _ : ℕ => μ)) := by
    rw [Measure.infinitePi_eq_pi]
    exact measurePreserving_piFinTwo
      (fun i : Fin 2 => Measure.infinitePi (fun _ : headTailIndex i => μ)) |>.map_eq
  have hU : Measure.map U (Measure.infinitePi (fun _ : PUnit => μ)) = μ := by
    rw [Measure.infinitePi_eq_pi]
    exact (measurePreserving_funUnique μ PUnit).map_eq
  have hUF : Measure.map (Prod.map U id)
      ((Measure.infinitePi (fun _ : PUnit => μ)).prod
        (Measure.infinitePi (fun _ : ℕ => μ))) =
      μ.prod (Measure.infinitePi (fun _ : ℕ => μ)) := by
    rw [← Measure.map_prod_map _ _ U.measurable measurable_id,
      hU, Measure.map_id]
  calc
    Measure.map headTail (exponentialInterarrivalMeasure rate) =
        Measure.map headTail (Measure.map E ρ) := by rw [hE]
    _ = Measure.map (headTail ∘ E) ρ := by
        rw [Measure.map_map measurable_headTail E.measurable]
    _ = Measure.map ((Prod.map U id) ∘ F ∘ C) ρ := by
        congr 1
    _ = Measure.map (Prod.map U id) (Measure.map F (Measure.map C ρ)) := by
        symm
        rw [Measure.map_map (U.measurable.prodMap measurable_id) F.measurable,
          Measure.map_map ((U.measurable.prodMap measurable_id).comp F.measurable)
            C.measurable]
        rfl
    _ = Measure.map (Prod.map U id)
        ((Measure.infinitePi (fun _ : PUnit => μ)).prod
          (Measure.infinitePi (fun _ : ℕ => μ))) := by
        rw [hC, hF]
    _ = μ.prod (Measure.infinitePi (fun _ : ℕ => μ)) := hUF
    _ = (expMeasure rate).prod (exponentialInterarrivalMeasure rate) := by
        rfl

/-- A two-sided Palm path decomposed into its central gap, its strictly
positive tail, and its strictly negative tail. -/
def twoSidedHeadPositiveNegative : (ℤ → ℝ) →
    (ℝ × (ℕ → ℝ)) × (ℕ → ℝ) :=
  (Prod.map headTail id) ∘ twoSidedToEquilibriumHalves

theorem twoSidedHeadPositiveNegative_apply (ω : ℤ → ℝ) :
    twoSidedHeadPositiveNegative ω =
      ((ω 0, fun n => ω (Int.ofNat (n + 1))),
        fun n => ω (Int.negSucc n)) := by
  rfl

theorem measurable_twoSidedHeadPositiveNegative :
    Measurable twoSidedHeadPositiveNegative := by
  exact (measurable_headTail.prodMap measurable_id).comp
    measurable_twoSidedToEquilibriumHalves

/-- The central Palm gap, positive tail, and negative tail are independent;
each displayed real or sequence factor has its iid exponential law. -/
theorem map_twoSidedHeadPositiveNegative_twoSidedInterarrivalMeasure
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map twoSidedHeadPositiveNegative
      (twoSidedInterarrivalMeasure rate) =
      ((expMeasure rate).prod (exponentialInterarrivalMeasure rate)).prod
        (exponentialInterarrivalMeasure rate) := by
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  calc
    Measure.map twoSidedHeadPositiveNegative
        (twoSidedInterarrivalMeasure rate) =
        Measure.map (Prod.map headTail id)
          (Measure.map twoSidedToEquilibriumHalves
            (twoSidedInterarrivalMeasure rate)) := by
          change Measure.map ((Prod.map headTail id) ∘
            twoSidedToEquilibriumHalves) (twoSidedInterarrivalMeasure rate) = _
          rw [← Measure.map_map
            (measurable_headTail.prodMap measurable_id)
            measurable_twoSidedToEquilibriumHalves]
    _ = Measure.map (Prod.map headTail id)
          (equilibriumTwoSidedBaseMeasure rate) := by
          rw [map_twoSidedToEquilibriumHalves_twoSidedInterarrivalMeasure hrate]
    _ = ((expMeasure rate).prod (exponentialInterarrivalMeasure rate)).prod
          (exponentialInterarrivalMeasure rate) := by
          rw [equilibriumTwoSidedBaseMeasure,
            ← Measure.map_prod_map _ _ measurable_headTail measurable_id,
            map_headTail_exponentialInterarrivalMeasure hrate, Measure.map_id]

end

end AppliedModelingLib.Probability.PoissonProcess
