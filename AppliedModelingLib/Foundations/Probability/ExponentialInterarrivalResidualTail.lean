import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalDeterministicNoArrival
import AppliedModelingLib.Foundations.Probability.ExponentialMemoryless

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/-- Subtract `elapsed` from the initial interarrival gap, keeping every later gap unchanged.
On the event that the initial gap exceeds `elapsed`, this is the residual interarrival path. -/
def firstGapResidualTail (elapsed : ℝ) (ξ : ℕ → ℝ) : ℕ → ℝ
  | 0 => interarrival 0 ξ - elapsed
  | k + 1 => interarrival (k + 1) ξ

/-- The first-gap residual-tail transformation is measurable. -/
theorem measurable_firstGapResidualTail (elapsed : ℝ) :
    Measurable (firstGapResidualTail elapsed) := by
  apply measurable_pi_iff.2
  intro i
  cases i with
  | zero =>
      simpa [firstGapResidualTail] using (measurable_interarrival 0).sub measurable_const
  | succ i =>
      simpa [firstGapResidualTail] using measurable_interarrival (i + 1)

/-- The deterministic-clock residual tail is measurable, despite its random
renewal index.  The proof partitions over the measurable count fibers. -/
theorem measurable_residualTail (s : ℝ) :
    Measurable (residualTail s) := by
  apply measurable_pi_iff.2
  intro k
  let h : ∀ ω : ℕ → ℝ, ∃ n : ℕ, canonicalRenewalCount s ω = n :=
    fun ω => ⟨canonicalRenewalCount s ω, rfl⟩
  cases k with
  | zero =>
      have hmeas : Measurable (fun ω : ℕ → ℝ =>
          arrivalTime (Nat.find (h ω)) ω) :=
        Measurable.find
          (fun n => measurable_arrivalTime n)
          (fun n => (measurable_canonicalRenewalCount s)
            (measurableSet_singleton n))
          h
      have hfind : ∀ ω : ℕ → ℝ,
          Nat.find (h ω) = canonicalRenewalCount s ω := by
        intro ω
        exact (Nat.find_spec (h ω)).symm
      simpa [residualTail, hfind] using hmeas.sub measurable_const
  | succ k =>
      have hmeas : Measurable (fun ω : ℕ → ℝ =>
          interarrival (Nat.find (h ω) + (k + 1)) ω) :=
        Measurable.find
          (fun n => measurable_interarrival (n + (k + 1)))
          (fun n => (measurable_canonicalRenewalCount s)
            (measurableSet_singleton n))
          h
      have hfind : ∀ ω : ℕ → ℝ,
          Nat.find (h ω) = canonicalRenewalCount s ω := by
        intro ω
        exact (Nat.find_spec (h ω)).symm
      simpa [residualTail, hfind] using hmeas

private def prependInterarrival (x : ℝ) (tail : ℕ → ℝ) : ℕ → ℝ
  | 0 => x
  | k + 1 => tail k

private def firstGapTailPair (ξ : ℕ → ℝ) : ℝ × (ℕ → ℝ) :=
  (interarrival 0 ξ, futureInterarrival 1 ξ)

private theorem measurable_prependInterarrival :
    Measurable (fun p : ℝ × (ℕ → ℝ) => prependInterarrival p.1 p.2) := by
  apply measurable_pi_iff.2
  intro i
  cases i with
  | zero =>
      simpa [prependInterarrival] using measurable_fst
  | succ i =>
      simpa [prependInterarrival] using (measurable_pi_apply i).comp measurable_snd

private theorem measurable_firstGapTailPair : Measurable firstGapTailPair := by
  exact (measurable_interarrival 0).prodMk
    (measurable_pi_iff.2 fun k => measurable_futureInterarrival 1 k)

private theorem prepend_firstGapTailPair (ξ : ℕ → ℝ) :
    prependInterarrival (firstGapTailPair ξ).1 (firstGapTailPair ξ).2 = ξ := by
  funext k
  cases k with
  | zero => simp [prependInterarrival, firstGapTailPair, interarrival]
  | succ k =>
      simpa [prependInterarrival, firstGapTailPair, futureInterarrival, interarrival,
        Nat.add_comm]

private theorem firstGapResidualTail_eq_prepend_sub (elapsed : ℝ) :
    firstGapResidualTail elapsed = fun ξ =>
      prependInterarrival ((firstGapTailPair ξ).1 - elapsed) (firstGapTailPair ξ).2 := by
  funext ξ
  funext k
  cases k with
  | zero => simp [firstGapResidualTail, prependInterarrival, firstGapTailPair]
  | succ k =>
      simpa [firstGapResidualTail, prependInterarrival, firstGapTailPair,
        futureInterarrival, interarrival, Nat.add_comm]

private theorem firstGapTailPair_hasLaw_prod {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.HasLaw firstGapTailPair
      ((ProbabilityTheory.expMeasure rate).prod (exponentialInterarrivalMeasure rate))
      (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let X : (ℕ → ℝ) → ℝ := interarrival 0
  let Y : (ℕ → ℝ) → ℕ → ℝ := futureInterarrival 1
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hX : Measurable X := by simpa [X] using measurable_interarrival 0
  have hY : Measurable Y := by
    simpa [Y] using measurable_pi_iff.2 (fun k => measurable_futureInterarrival 1 k)
  have hIndep : ProbabilityTheory.IndepFun X Y μ := by
    simpa [μ, X, Y] using interarrival_zero_indep_futureInterarrival hrate
  have hYlaw : μ.map Y = μ := by
    simpa [μ, Y] using (futureInterarrival_hasLaw_path hrate 1).map_eq
  refine ⟨(hX.prodMk hY).aemeasurable, ?_⟩
  calc
    μ.map (fun ξ => (X ξ, Y ξ)) = (μ.map X).prod (μ.map Y) :=
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        hX.aemeasurable hY.aemeasurable).mp hIndep
    _ = (ProbabilityTheory.expMeasure rate).prod μ := by
      rw [show μ.map X = ProbabilityTheory.expMeasure rate by
        simpa [μ, X] using (interarrival_hasLaw hrate 0).map_eq,
        hYlaw]

/-- After conditioning an iid exponential interarrival path on survival past a fixed elapsed
time, subtracting that elapsed time from the first gap restores the original path law.  The
identity is stated for unnormalised restricted measures, so the survival probability appears as
a scalar. -/
theorem firstGapResidualTail_restrict_map_eq_smul
    {rate elapsed : ℝ} (hrate : 0 < rate) (helapsed : 0 ≤ elapsed) :
    ((exponentialInterarrivalMeasure rate).restrict
      {ξ | elapsed < interarrival 0 ξ}).map (firstGapResidualTail elapsed) =
      (ProbabilityTheory.expMeasure rate (Set.Ioi elapsed)) •
        exponentialInterarrivalMeasure rate := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let E : Measure ℝ := ProbabilityTheory.expMeasure rate
  let c : ℝ≥0∞ := E (Set.Ioi elapsed)
  let pair : (ℕ → ℝ) → ℝ × (ℕ → ℝ) := firstGapTailPair
  let prepend : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun p => prependInterarrival p.1 p.2
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure E := by
    simpa [E] using ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  have hpair : μ.map pair = E.prod μ := by
    simpa [μ, E, pair] using (firstGapTailPair_hasLaw_prod hrate).map_eq
  have hpair_meas : Measurable pair := by
    simpa [pair] using measurable_firstGapTailPair
  have hprepend_meas : Measurable prepend := by
    simpa [prepend] using measurable_prependInterarrival
  have hsub_meas : Measurable (fun x : ℝ => x - elapsed) := by fun_prop
  have hsurvival : pair ⁻¹' (Set.Ioi elapsed ×ˢ Set.univ) =
      {ξ | elapsed < interarrival 0 ξ} := by
    ext ξ
    simp [pair, firstGapTailPair]
  have hrestrict :
      (μ.restrict {ξ | elapsed < interarrival 0 ξ}).map pair =
        (E.restrict (Set.Ioi elapsed)).prod μ := by
    calc
      (μ.restrict {ξ | elapsed < interarrival 0 ξ}).map pair =
          (μ.map pair).restrict (Set.Ioi elapsed ×ˢ Set.univ) := by
            rw [Measure.restrict_map hpair_meas (measurableSet_Ioi.prod MeasurableSet.univ),
              hsurvival]
      _ = (E.prod μ).restrict (Set.Ioi elapsed ×ˢ Set.univ) := by rw [hpair]
      _ = (E.restrict (Set.Ioi elapsed)).prod μ := by
        exact (Measure.restrict_prod_eq_prod_univ (μ := E) (ν := μ) (Set.Ioi elapsed)).symm
  have hstep :
      Measure.map (Prod.map (fun x : ℝ => x - elapsed) id)
        ((E.restrict (Set.Ioi elapsed)).prod μ) =
        (c • E).prod μ := by
    rw [← Measure.map_prod_map (E.restrict (Set.Ioi elapsed)) μ hsub_meas measurable_id,
      AppliedModelingLib.Probability.Exponential.expMeasure_restrict_Ioi_map_sub_eq_smul
        hrate helapsed]
    rw [Measure.map_id]
  have hprepend : Measure.map prepend (E.prod μ) = μ := by
    rw [← hpair, Measure.map_map hprepend_meas hpair_meas]
    have hcomp : prepend ∘ pair = id := by
      funext ξ
      simp only [Function.comp_apply, id_eq]
      simpa [prepend, pair] using prepend_firstGapTailPair ξ
    rw [hcomp, Measure.map_id]
  have hprepend_smul : Measure.map prepend ((c • E).prod μ) = c • μ := by
    rw [Measure.prod_smul_left, Measure.map_smul, hprepend]
  rw [firstGapResidualTail_eq_prepend_sub]
  let shift : ℝ × (ℕ → ℝ) → ℝ × (ℕ → ℝ) :=
    Prod.map (fun x : ℝ => x - elapsed) id
  have hshift_meas : Measurable shift := by
    simpa [shift] using ((measurable_fst.sub measurable_const).prodMk measurable_snd)
  have hcomp :
      (fun ξ => prepend (Prod.map (fun x : ℝ => x - elapsed) id (pair ξ))) =
        (prepend ∘ shift) ∘ pair := by
    rfl
  change Measure.map (fun ξ => prepend (Prod.map (fun x : ℝ => x - elapsed) id (pair ξ)))
      (μ.restrict {ξ | elapsed < interarrival 0 ξ}) = c • μ
  rw [hcomp, ← Measure.map_map (hprepend_meas.comp hshift_meas) hpair_meas,
    ← Measure.map_map hprepend_meas hshift_meas, hrestrict]
  change Measure.map prepend
      (Measure.map (Prod.map (fun x : ℝ => x - elapsed) id)
        ((E.restrict (Set.Ioi elapsed)).prod μ)) = c • μ
  rw [hstep, hprepend_smul]

end
end AppliedModelingLib.Probability.PoissonProcess
