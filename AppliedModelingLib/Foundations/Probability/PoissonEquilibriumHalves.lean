import AppliedModelingLib.Foundations.Probability.EquilibriumPoissonBase

/-!
# Two-sided Palm gaps as equilibrium halves

Splitting a two-sided iid gap path into its nonnegative and negative index
halves gives the product law used by the origin-split equilibrium base.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The concrete enumeration of signed integers by a `Fin 2` choice of sign
and a natural magnitude. Coordinate `0` is the nonnegative side; coordinate
`1` is the strictly negative side. -/
def finTwoNatEquivInt : Fin 2 × ℕ ≃ ℤ where
  toFun p := if p.1 = 0 then Int.ofNat p.2 else Int.negSucc p.2
  invFun z := match z with
    | Int.ofNat n => (0, n)
    | Int.negSucc n => (1, n)
  left_inv p := by
    rcases p with ⟨i, n⟩
    fin_cases i <;> simp
  right_inv z := by
    cases z <;> simp

@[simp] theorem finTwoNatEquivInt_symm_ofNat (n : ℕ) :
    finTwoNatEquivInt.symm (Int.ofNat n) = (0, n) := rfl

@[simp] theorem finTwoNatEquivInt_symm_negSucc (n : ℕ) :
    finTwoNatEquivInt.symm (Int.negSucc n) = (1, n) := rfl

/-- Read a two-sided Palm gap path as its forward and backward equilibrium
halves. -/
def twoSidedToEquilibriumHalves : (ℤ → ℝ) → (ℕ → ℝ) × (ℕ → ℝ) :=
  fun ω => (fun n => ω (Int.ofNat n), fun n => ω (Int.negSucc n))

theorem measurable_twoSidedToEquilibriumHalves :
    Measurable twoSidedToEquilibriumHalves := by
  apply Measurable.prodMk <;> refine measurable_pi_iff.2 fun n => ?_
  · exact measurable_pi_apply _
  · exact measurable_pi_apply _

theorem twoSidedToEquilibriumHalves_piCongrLeft_eq_piFinTwo_curry
    (x : (Fin 2 × ℕ) → ℝ) :
    twoSidedToEquilibriumHalves
      ((MeasurableEquiv.piCongrLeft (fun _ : ℤ => ℝ) finTwoNatEquivInt) x) =
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℕ → ℝ))
        ((MeasurableEquiv.curry (Fin 2) ℕ ℝ) x) := by
  ext n
  · change x (finTwoNatEquivInt.symm (Int.ofNat n)) = x (0, n)
    rw [finTwoNatEquivInt_symm_ofNat]
  · change x (finTwoNatEquivInt.symm (Int.negSucc n)) = x (1, n)
    rw [finTwoNatEquivInt_symm_negSucc]

/-- Splitting a two-sided iid exponential path into its sign halves gives
exactly the product of the forward-residual and backward-age iid laws used by
the equilibrium Poisson base. -/
theorem map_twoSidedToEquilibriumHalves_twoSidedInterarrivalMeasure
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map twoSidedToEquilibriumHalves (twoSidedInterarrivalMeasure rate) =
      equilibriumTwoSidedBaseMeasure rate := by
  let μ : Measure ℝ := expMeasure rate
  let ρ : Measure ((Fin 2 × ℕ) → ℝ) :=
    Measure.infinitePi (fun _ : Fin 2 × ℕ => μ)
  let E : ((Fin 2 × ℕ) → ℝ) ≃ᵐ (ℤ → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : ℤ => ℝ) finTwoNatEquivInt
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hE : Measure.map E ρ = twoSidedInterarrivalMeasure rate := by
    calc
      Measure.map E ρ = Measure.infinitePi (fun _ : ℤ => μ) := by
        exact Measure.infinitePi_map_piCongrLeft
          (fun _ : ℤ => μ) finTwoNatEquivInt
      _ = twoSidedInterarrivalMeasure rate := by
        simp [μ, twoSidedInterarrivalMeasure]
  have hcurried :
      Measure.map (MeasurableEquiv.curry (Fin 2) ℕ ℝ) ρ =
        Measure.infinitePi (fun _ : Fin 2 => exponentialInterarrivalMeasure rate) := by
    calc
      Measure.map (MeasurableEquiv.curry (Fin 2) ℕ ℝ) ρ =
          Measure.infinitePi (fun _ : Fin 2 =>
            Measure.infinitePi (fun _ : ℕ => μ)) := by
        exact Measure.infinitePi_map_curry (ι := Fin 2) (κ := ℕ)
          (fun _ _ => μ)
      _ = Measure.infinitePi (fun _ : Fin 2 => exponentialInterarrivalMeasure rate) := by
        simp [μ, exponentialInterarrivalMeasure]
  calc
    Measure.map twoSidedToEquilibriumHalves (twoSidedInterarrivalMeasure rate) =
        Measure.map twoSidedToEquilibriumHalves (Measure.map E ρ) := by rw [hE]
    _ = Measure.map (twoSidedToEquilibriumHalves ∘ E) ρ := by
        rw [Measure.map_map measurable_twoSidedToEquilibriumHalves E.measurable]
    _ = Measure.map
        ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℕ → ℝ)) ∘
          (MeasurableEquiv.curry (Fin 2) ℕ ℝ)) ρ := by
        congr 1
    _ = Measure.map (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℕ → ℝ))
        (Measure.map (MeasurableEquiv.curry (Fin 2) ℕ ℝ) ρ) := by
        rw [Measure.map_map
          (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℕ → ℝ)).measurable
          (MeasurableEquiv.curry (Fin 2) ℕ ℝ).measurable]
    _ = Measure.map (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℕ → ℝ))
        (Measure.infinitePi (fun _ : Fin 2 => exponentialInterarrivalMeasure rate)) := by
        rw [hcurried]
    _ = Measure.map (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℕ → ℝ))
        (Measure.pi (fun _ : Fin 2 => exponentialInterarrivalMeasure rate)) := by
        rw [← Measure.infinitePi_eq_pi]
    _ = equilibriumTwoSidedBaseMeasure rate := by
        exact measurePreserving_piFinTwo
          (fun _ : Fin 2 => exponentialInterarrivalMeasure rate) |>.map_eq

end

end AppliedModelingLib.Probability.PoissonProcess
