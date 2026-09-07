import AppliedModelingLib.Foundations.Probability.FiniteKL
import AppliedModelingLib.Foundations.Probability.FiniteSimplex
import AppliedModelingLib.Foundations.Math.FiniteOptimization

/-!
# Convex finite KL balls

This module gives the real finite-simplex form of a KL sublevel set.  It is
the compact-convex feasible domain needed by finite minimax arguments, while
keeping the PMF-level KL divergence as the paper-facing quantity.

## Main declarations

- `finiteKLDivergenceMass`
- `finiteKLBallMass`
- `finiteKLBallMass_convex`
- `finiteKLBallMass_isCompact`
-/

namespace AppliedModelingLib

open scoped BigOperators

noncomputable section

/-- Finite KL divergence evaluated on a real mass vector.  On the finite
probability simplex this is exactly `finiteKLDivergence` after conversion to
a PMF. -/
def finiteKLDivergenceMass {Outcome : Type*} [Fintype Outcome]
    (mass : Outcome → ℝ) (reference : PMF Outcome) : ℝ :=
  ∑ outcome : Outcome,
    mass outcome * (Real.log (mass outcome) - Real.log (reference outcome).toReal)

/-- A real finite probability vector in the KL ball around `reference`. -/
def finiteKLBallMass {Outcome : Type*} [Fintype Outcome]
    (reference : PMF Outcome) (radius : ℝ) : Set (Outcome → ℝ) :=
  {mass | FiniteProbabilitySimplex mass ∧
    finiteKLDivergenceMass mass reference ≤ radius}

/-- Convert an exact real finite probability mass vector into its corresponding PMF. -/
noncomputable def finiteProbabilityMassToPMF {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    (mass : Outcome → ℝ) (hmass : FiniteProbabilitySimplex mass) : PMF Outcome :=
  stdSimplexToPMF ⟨mass, hmass⟩

/-- The PMF converted from a finite real mass vector has those exact real coordinates. -/
@[simp] theorem finiteProbabilityMassToPMF_apply_toReal {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    (mass : Outcome → ℝ) (hmass : FiniteProbabilitySimplex mass) (outcome : Outcome) :
    (finiteProbabilityMassToPMF mass hmass outcome).toReal = mass outcome := by
  exact stdSimplexToPMF_apply_toReal ⟨mass, hmass⟩ outcome

/-- The real-mass expression agrees definitionally with the finite PMF KL
divergence. -/
theorem finiteKLDivergenceMass_pmf {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first reference : PMF Outcome) :
    finiteKLDivergenceMass (fun outcome => (first outcome).toReal) reference =
      finiteKLDivergence first reference := by
  rfl

/-- KL of a finite real mass vector agrees with KL after PMF conversion. -/
theorem finiteKLDivergence_finiteProbabilityMassToPMF {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    (mass : Outcome → ℝ) (hmass : FiniteProbabilitySimplex mass) (reference : PMF Outcome) :
    finiteKLDivergence (finiteProbabilityMassToPMF mass hmass) reference =
      finiteKLDivergenceMass mass reference := by
  rw [← finiteKLDivergenceMass_pmf]
  simp only [finiteProbabilityMassToPMF_apply_toReal]

/-- The finite real-mass KL expression is continuous. -/
theorem continuous_finiteKLDivergenceMass {Outcome : Type*} [Fintype Outcome]
    (reference : PMF Outcome) :
    Continuous (fun mass : Outcome → ℝ => finiteKLDivergenceMass mass reference) := by
  unfold finiteKLDivergenceMass
  apply continuous_finset_sum
  intro outcome _
  change Continuous (fun mass : Outcome → ℝ =>
    mass outcome * (Real.log (mass outcome) - Real.log (reference outcome).toReal))
  simpa only [mul_sub] using
    ((Real.continuous_mul_log.comp (continuous_apply outcome)).sub
      ((continuous_apply outcome).mul continuous_const))

/-- A finite KL ball is closed in raw real simplex coordinates. -/
theorem finiteKLBallMass_isClosed {Outcome : Type*} [Fintype Outcome]
    (reference : PMF Outcome) (radius : ℝ) :
    IsClosed (finiteKLBallMass reference radius) := by
  unfold finiteKLBallMass
  exact finiteProbabilitySimplex_isClosed.inter
    (isClosed_le (continuous_finiteKLDivergenceMass reference) continuous_const)

/-- A finite KL ball is compact in raw real simplex coordinates. -/
theorem finiteKLBallMass_isCompact {Outcome : Type*} [Fintype Outcome]
    (reference : PMF Outcome) (radius : ℝ) :
    IsCompact (finiteKLBallMass reference radius) := by
  apply finiteProbabilitySimplex_isCompact.of_isClosed_subset
    (finiteKLBallMass_isClosed reference radius)
  intro mass hmass
  exact hmass.1

/-- The reference PMF's real mass vector is a finite probability vector. -/
theorem finiteProbabilitySimplex_pmfMass {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) :
    FiniteProbabilitySimplex (fun outcome => (law outcome).toReal) := by
  constructor
  · intro outcome
    exact ENNReal.toReal_nonneg
  · exact pmfToRealSum law

/-- Returning a PMF to real coordinates and converting it back is the identity. -/
theorem finiteProbabilityMassToPMF_pmfMass {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome] (law : PMF Outcome) :
    finiteProbabilityMassToPMF (fun outcome => (law outcome).toReal)
      (finiteProbabilitySimplex_pmfMass law) = law := by
  change stdSimplexToPMF ⟨fun outcome => (law outcome).toReal,
    finiteProbabilitySimplex_pmfMass law⟩ = law
  have hsimplex :
      (⟨fun outcome => (law outcome).toReal,
        finiteProbabilitySimplex_pmfMass law⟩ : stdSimplex ℝ Outcome) =
        pmfToStdSimplex law := by
    apply Subtype.ext
    rfl
  rw [hsimplex]
  exact stdSimplexToPMF_pmfToStdSimplex law

/-- Every nonnegative-radius finite KL ball contains its reference mass vector. -/
theorem finiteKLBallMass_nonempty {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference : PMF Outcome) {radius : ℝ} (hradius : 0 ≤ radius) :
    (finiteKLBallMass reference radius).Nonempty := by
  refine ⟨fun outcome => (reference outcome).toReal, finiteProbabilitySimplex_pmfMass reference, ?_⟩
  rw [finiteKLDivergenceMass_pmf, finiteKLDivergence_self]
  exact hradius

/-- KL is convex in its first finite real mass-vector argument. -/
theorem finiteKLDivergenceMass_convexOn_nonneg {Outcome : Type*} [Fintype Outcome]
    (reference : PMF Outcome) :
    ConvexOn ℝ {mass : Outcome → ℝ | ∀ outcome, 0 ≤ mass outcome}
      (fun mass => finiteKLDivergenceMass mass reference) := by
  constructor
  · rw [convex_iff_add_mem]
    intro first hfirst second hsecond a b ha hb hab outcome
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hfirst outcome))
      (mul_nonneg hb (hsecond outcome))
  · intro first hfirst second hsecond a b ha hb hab
    unfold finiteKLDivergenceMass
    calc
      (∑ outcome : Outcome,
          (a • first + b • second) outcome *
            (Real.log ((a • first + b • second) outcome) -
              Real.log (reference outcome).toReal)) ≤
          ∑ outcome : Outcome,
            ((a * (first outcome * Real.log (first outcome)) +
                b * (second outcome * Real.log (second outcome))) -
              (a * first outcome + b * second outcome) *
                Real.log (reference outcome).toReal) := by
          apply Finset.sum_le_sum
          intro outcome _
          have hentropy := Real.convexOn_mul_log.2 (hfirst outcome) (hsecond outcome)
            ha hb hab
          have hentropy' :
              (a • first + b • second) outcome *
                  Real.log ((a • first + b • second) outcome) ≤
                a * (first outcome * Real.log (first outcome)) +
                  b * (second outcome * Real.log (second outcome)) := by
            simpa only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] using hentropy
          calc
            (a • first + b • second) outcome *
                (Real.log ((a • first + b • second) outcome) -
                  Real.log (reference outcome).toReal) =
                (a • first + b • second) outcome *
                    Real.log ((a • first + b • second) outcome) -
                  (a * first outcome + b * second outcome) *
                    Real.log (reference outcome).toReal := by
                  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
                  ring
            _ ≤ (a * (first outcome * Real.log (first outcome)) +
                  b * (second outcome * Real.log (second outcome))) -
                (a * first outcome + b * second outcome) *
                  Real.log (reference outcome).toReal := by
                  exact sub_le_sub_right hentropy' _
      _ = a * finiteKLDivergenceMass first reference +
          b * finiteKLDivergenceMass second reference := by
          unfold finiteKLDivergenceMass
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro outcome _
          ring

/-- A finite KL ball is convex. -/
theorem finiteKLBallMass_convex {Outcome : Type*} [Fintype Outcome]
    (reference : PMF Outcome) (radius : ℝ) :
    Convex ℝ (finiteKLBallMass reference radius) := by
  intro first hfirst second hsecond a b ha hb hab
  constructor
  · exact finiteProbabilitySimplex_convex hfirst.1 hsecond.1 ha hb hab
  · have hconvex := finiteKLDivergenceMass_convexOn_nonneg reference
    have hbound := hconvex.2 (fun outcome => hfirst.1.1 outcome)
      (fun outcome => hsecond.1.1 outcome) ha hb hab
    calc
      finiteKLDivergenceMass (a • first + b • second) reference ≤
          a * finiteKLDivergenceMass first reference +
            b * finiteKLDivergenceMass second reference := hbound
      _ ≤ a * radius + b * radius := by
          exact add_le_add (mul_le_mul_of_nonneg_left hfirst.2 ha)
            (mul_le_mul_of_nonneg_left hsecond.2 hb)
      _ = radius := by
          calc
            a * radius + b * radius = (a + b) * radius := by ring
            _ = radius := by rw [hab]; ring

end

end AppliedModelingLib
