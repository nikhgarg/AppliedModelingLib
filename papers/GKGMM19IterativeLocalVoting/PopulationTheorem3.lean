import AppliedModelingLib.Foundations.Probability.IidSequence
import GKGMM19IterativeLocalVoting.ProofInterface

open MeasureTheory
open AppliedModelingLib

namespace GKGMM19IterativeLocalVoting

/--
Coordinatewise continuity of the literal population field used in Theorem 3.
This deliberately does not assume a finite voter type: the only finiteness is
the paper's finite-dimensional decision space.
-/
def PopulationTheorem3DirectionalFieldCoordinateContinuity
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : PopulationTheorem3DirectionalFieldModel E) : Prop :=
  ∀ xstar i ε, 0 < ε →
    ∃ δ, 0 < δ ∧
      ∀ x : Coord → ℝ,
        finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
          |populationTheorem3DirectionalField M.population M.utilityGradient x i -
              populationTheorem3DirectionalField M.population M.utilityGradient
                xstar i| < ε

/--
The literal uniform-continuity premise of the population field in Theorem 3.
The coordinatewise continuity lemma below is a derived analytic consequence,
not the paper-facing replacement for this premise.
-/
def PopulationTheorem3DirectionalFieldUniformContinuity
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : PopulationTheorem3DirectionalFieldModel E) : Prop :=
  ∀ ε, 0 < ε →
    ∃ δ, 0 < δ ∧
      ∀ x y : Coord → ℝ,
        finiteCoordinateDistance SourceNorm.l2 x y < δ →
          finiteCoordinateDistance SourceNorm.l2
            (populationTheorem3DirectionalField M.population M.utilityGradient x)
            (populationTheorem3DirectionalField M.population M.utilityGradient y) < ε

/-- Uniform field continuity implies the coordinatewise continuity used by the
finite-dimensional drift argument. -/
theorem PopulationTheorem3DirectionalFieldUniformContinuity.to_coordinate_continuity
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : PopulationTheorem3DirectionalFieldModel E}
    (h : PopulationTheorem3DirectionalFieldUniformContinuity M) :
    PopulationTheorem3DirectionalFieldCoordinateContinuity M := by
  intro xstar i ε hε
  rcases h ε hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro x hx
  exact lt_of_le_of_lt
    (finiteCoordinateDistance_l2_coord_abs_le
      (populationTheorem3DirectionalField M.population M.utilityGradient x)
      (populationTheorem3DirectionalField M.population M.utilityGradient xstar) i)
    (hδ x xstar hx)

/--
Pointwise convergence of one outcome of a population-sampled trajectory.  It
is intentionally outcome-indexed rather than the older deterministic
`ILVEnvironment.trajectory` shorthand.
-/
def PopulationTheorem3OutcomeConvergesTo
    {Coord Omega : Type*} [Fintype Coord]
    (trajectory : ℕ → Omega → Coord → ℝ) (omega : Omega) (xstar : Coord → ℝ) : Prop :=
  ∀ i : Coord,
    Filter.Tendsto (fun n : ℕ => trajectory n omega i)
      Filter.atTop (nhds (xstar i))

theorem populationTheorem3DirectionalField_coordinate_tendsto_of_converges
    {Voter Coord Omega : Type*}
    [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : PopulationTheorem3DirectionalFieldModel E)
    (hcont : PopulationTheorem3DirectionalFieldCoordinateContinuity M)
    {trajectory : ℕ → Omega → Coord → ℝ} {omega : Omega} {xstar : Coord → ℝ}
    (hconverges : PopulationTheorem3OutcomeConvergesTo trajectory omega xstar)
    (i : Coord) :
    Filter.Tendsto
      (fun n : ℕ =>
        populationTheorem3DirectionalField M.population M.utilityGradient
          (trajectory n omega) i)
      Filter.atTop
      (nhds
        (populationTheorem3DirectionalField M.population M.utilityGradient
          xstar i)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rcases hcont xstar i ε hε with ⟨δ, hδpos, hδ⟩
  have hdist_tendsto :
      Filter.Tendsto
        (fun n : ℕ =>
          finiteCoordinateDistance SourceNorm.l2 (trajectory n omega) xstar)
        Filter.atTop (nhds 0) := by
    exact finiteCoordinateDistance_l2_tendsto_zero_of_coordinatewise hconverges
  have heventually_close :
      ∀ᶠ n in Filter.atTop,
        finiteCoordinateDistance SourceNorm.l2 (trajectory n omega) xstar < δ :=
    hdist_tendsto.eventually (eventually_lt_nhds hδpos)
  filter_upwards [heventually_close] with n hn
  simpa [Real.dist_eq] using hδ (trajectory n omega) hn

theorem populationTheorem3DirectionalField_finiteDot_tendsto_of_converges
    {Voter Coord Omega : Type*}
    [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : PopulationTheorem3DirectionalFieldModel E)
    (hcont : PopulationTheorem3DirectionalFieldCoordinateContinuity M)
    {trajectory : ℕ → Omega → Coord → ℝ} {omega : Omega} {xstar : Coord → ℝ}
    (hconverges : PopulationTheorem3OutcomeConvergesTo trajectory omega xstar) :
    Filter.Tendsto
      (fun n : ℕ =>
        finiteDot
          (populationTheorem3DirectionalField M.population M.utilityGradient xstar)
          (populationTheorem3DirectionalField M.population M.utilityGradient
            (trajectory n omega)))
      Filter.atTop
      (nhds
        (finiteDot
          (populationTheorem3DirectionalField M.population M.utilityGradient xstar)
          (populationTheorem3DirectionalField M.population M.utilityGradient xstar))) := by
  exact finiteDot_tendsto_of_coordinatewise
    (populationTheorem3DirectionalField M.population M.utilityGradient xstar)
    (fun i =>
      populationTheorem3DirectionalField_coordinate_tendsto_of_converges
        M hcont hconverges i)

/--
Near a nonzero population field at a convergent outcome, the scalar product of
the limiting field with the current population field is eventually uniformly
positive.  This is the deterministic drift half of the general-population
Theorem 3 proof; its stochastic half is supplied separately from the sampled
Algorithm 1 trace.
-/
theorem populationTheorem3DirectionalField_eventual_finiteDot_drift_of_converges
    {Voter Coord Omega : Type*}
    [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : PopulationTheorem3DirectionalFieldModel E)
    (hcont : PopulationTheorem3DirectionalFieldCoordinateContinuity M)
    {trajectory : ℕ → Omega → Coord → ℝ} {omega : Omega} {xstar : Coord → ℝ}
    (hconverges : PopulationTheorem3OutcomeConvergesTo trajectory omega xstar)
    (hne :
      populationTheorem3DirectionalField M.population M.utilityGradient xstar ≠
        fun _ => (0 : ℝ)) :
    ∃ N c, 0 < c ∧
      ∀ n : ℕ,
        c ≤
          finiteDot
            (populationTheorem3DirectionalField M.population M.utilityGradient xstar)
            (populationTheorem3DirectionalField M.population M.utilityGradient
              (trajectory (n + N) omega)) := by
  let a : Coord → ℝ :=
    populationTheorem3DirectionalField M.population M.utilityGradient xstar
  let L : ℝ := finiteDot a a
  have hLpos : 0 < L := by
    exact finiteDot_self_pos_of_ne_zero (by simpa [a] using hne)
  let c : ℝ := L / 2
  have hc : 0 < c := by
    dsimp [c]
    linarith
  have hc_lt_L : c < L := by
    dsimp [c]
    linarith
  have hdot_tendsto :
      Filter.Tendsto
        (fun n : ℕ =>
          finiteDot a
            (populationTheorem3DirectionalField M.population M.utilityGradient
              (trajectory n omega)))
        Filter.atTop (nhds L) := by
    simpa [a, L] using
      populationTheorem3DirectionalField_finiteDot_tendsto_of_converges
        M hcont hconverges
  have heventually_pos :
      ∀ᶠ n in Filter.atTop,
        c <
          finiteDot a
            (populationTheorem3DirectionalField M.population M.utilityGradient
              (trajectory n omega)) :=
    hdot_tendsto.eventually (Ioi_mem_nhds hc_lt_L)
  rcases Filter.eventually_atTop.1 heventually_pos with ⟨N, hN⟩
  refine ⟨N, c, hc, ?_⟩
  intro n
  exact le_of_lt (hN (n + N) (Nat.le_add_left N n))

/-- A finite-coordinate scalar projection distributes over an affine step. -/
theorem finiteDot_add_scaled_right
    {Coord : Type*} [Fintype Coord]
    (a x d : Coord → ℝ) (r : ℝ) :
    finiteDot a (fun i => x i + r * d i) =
      finiteDot a x + r * finiteDot a d := by
  unfold finiteDot
  change (∑ i : Coord, a i * (x i + r * d i)) =
    (∑ i : Coord, a i * x i) + r * (∑ i : Coord, a i * d i)
  calc
    (∑ i : Coord, a i * (x i + r * d i)) =
        ∑ i : Coord, (a i * x i + r * (a i * d i)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (∑ i : Coord, a i * x i) + ∑ i : Coord, r * (a i * d i) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i : Coord, a i * x i) + r * (∑ i : Coord, a i * d i) := by
          rw [Finset.mul_sum]

/-- The scalar projection of a normalized population direction is integrable.
This is derived coordinate-by-coordinate from the source population model; it
does not use a finite-support voter distribution. -/
theorem populationTheorem3_finiteDot_normalized_integrable
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : PopulationTheorem3DirectionalFieldModel E)
    (x a : Coord → ℝ) :
    Integrable (fun voter =>
      finiteDot a
        (modelBFiniteNormalizedDirection SourceNorm.l2
          (M.utilityGradient voter x))) M.population := by
  unfold finiteDot
  apply integrable_finset_sum
  intro i _
  simpa [mul_comm] using
    (M.normalized_gradient_integrable x i).const_mul (a i)

/-- The population expectation of the scalar Model B innovation, centered by
the exact population directional field, is zero. -/
theorem populationTheorem3_centered_integral_zero
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : PopulationTheorem3DirectionalFieldModel E)
    (x a : Coord → ℝ) (r : ℝ) :
    (∫ voter,
      r *
        (finiteDot a
          (populationTheorem3DirectionalField M.population M.utilityGradient x) -
          finiteDot a
            (modelBFiniteNormalizedDirection SourceNorm.l2
              (M.utilityGradient voter x))) ∂M.population) = 0 := by
  letI : IsProbabilityMeasure M.population := M.population_probability
  have hdot := populationTheorem3_finiteDot_normalized_integrable M x a
  have hfield := populationTheorem3DirectionalField_finiteDot_eq_integral
    M.population M.utilityGradient x a
    (fun i => M.normalized_gradient_integrable x i)
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub (integrable_const _) hdot,
    MeasureTheory.integral_const, probReal_univ]
  simp only [smul_eq_mul]
  rw [hfield]
  ring

/-- A scalar projection of the literal population field is bounded by the
Euclidean norm of that scalar direction.  This follows from the pointwise
unit bound on the source-defined normalized gradient and the fact that the
population measure is a probability measure. -/
theorem populationTheorem3_finiteDot_field_abs_le_l2_norm
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : PopulationTheorem3DirectionalFieldModel E)
    (x a : Coord → ℝ) :
    |finiteDot a
      (populationTheorem3DirectionalField M.population M.utilityGradient x)| ≤
      finiteCoordinateNorm SourceNorm.l2 a := by
  letI : IsProbabilityMeasure M.population := M.population_probability
  let direction : Voter → Coord → ℝ := fun voter =>
    modelBFiniteNormalizedDirection SourceNorm.l2 (M.utilityGradient voter x)
  have hdot_integrable : Integrable (fun voter => finiteDot a (direction voter))
      M.population :=
    populationTheorem3_finiteDot_normalized_integrable M x a
  have hfield :
      finiteDot a
        (populationTheorem3DirectionalField M.population M.utilityGradient x) =
        ∫ voter, finiteDot a (direction voter) ∂M.population := by
    simpa [direction] using
      (populationTheorem3DirectionalField_finiteDot_eq_integral
        M.population M.utilityGradient x a
        (fun i => M.normalized_gradient_integrable x i))
  rw [hfield]
  calc
    |∫ voter, finiteDot a (direction voter) ∂M.population| ≤
        ∫ voter, |finiteDot a (direction voter)| ∂M.population :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ _voter : Voter, finiteCoordinateNorm SourceNorm.l2 a ∂M.population := by
      apply MeasureTheory.integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => abs_nonneg _)
      · exact integrable_const _
      · exact Filter.Eventually.of_forall (fun voter =>
          (finiteDot_abs_le_l2_mul_l2 a (direction voter)).trans
            (mul_le_of_le_one_right (finiteCoordinateNorm_l2_nonneg a)
              (modelBFiniteNormalizedDirection_l2_norm_le_one
                (M.utilityGradient voter x))))
    _ = finiteCoordinateNorm SourceNorm.l2 a := by
      simp

/--
One scalar centered increment for a literal population-sampled Model B step.
The first term is the current population drift and the second is the realized
fresh-voter direction.  No finite-support approximation appears here.
-/
noncomputable def populationTheorem3CenteredIncrement
    {Voter Coord Omega : Type*}
    [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : PopulationTheorem3DirectionalFieldModel E)
    (r0 : ℝ) (trajectory : ℕ → Omega → Coord → ℝ)
    (sample : ℕ → Omega → Voter) (a : Coord → ℝ)
    (n : ℕ) (omega : Omega) : ℝ :=
  ilvRadius r0 (n + 1) *
    (finiteDot a
      (populationTheorem3DirectionalField M.population M.utilityGradient
        (trajectory n omega)) -
      finiteDot a
        (modelBFiniteNormalizedDirection SourceNorm.l2
          (M.utilityGradient (sample n omega) (trajectory n omega))) )

/-- The one-step scalar innovation written against an explicit finite iid
history and one fresh population draw.  This form is used solely to invoke the
generic iid conditioning theorem; it is definitionally the displayed Model B
centered increment once the state is recovered from its past history. -/
noncomputable def populationTheorem3PastCenteredTest
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : PopulationTheorem3DirectionalFieldModel E)
    (r : ℝ) (a state : Coord → ℝ) (voter : Voter) : ℝ :=
  r *
    (finiteDot a
      (populationTheorem3DirectionalField M.population M.utilityGradient state) -
      finiteDot a
        (modelBFiniteNormalizedDirection SourceNorm.l2
          (M.utilityGradient voter state)))

theorem populationTheorem3PastCenteredTest_integral_zero
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : PopulationTheorem3DirectionalFieldModel E)
    (r : ℝ) (a state : Coord → ℝ) :
    (∫ voter, populationTheorem3PastCenteredTest M r a state voter ∂M.population) = 0 := by
  exact populationTheorem3_centered_integral_zero M state a r

/-- The population Model B centered innovation has the standard deterministic
bound.  Unlike the former finite-voter adapter, this is proved directly from
the probability integral and the zero-safe unit-direction bound. -/
theorem populationTheorem3_centeredIncrement_abs_le
    {Voter Coord Omega : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : PopulationTheorem3DirectionalFieldModel E)
    (r0 : ℝ) (trajectory : ℕ → Omega → Coord → ℝ)
    (sample : ℕ → Omega → Voter) (a : Coord → ℝ) (n : ℕ) (omega : Omega)
    (hr0 : 0 < r0) :
    |populationTheorem3CenteredIncrement M r0 trajectory sample a n omega| ≤
      2 * (finiteCoordinateNorm SourceNorm.l2 a * ilvRadius r0 (n + 1)) := by
  let r : ℝ := ilvRadius r0 (n + 1)
  let x : Coord → ℝ := trajectory n omega
  let field : Coord → ℝ :=
    populationTheorem3DirectionalField M.population M.utilityGradient x
  let direction : Coord → ℝ :=
    modelBFiniteNormalizedDirection SourceNorm.l2 (M.utilityGradient (sample n omega) x)
  have hr : 0 ≤ r := ilvRadius_nonneg (le_of_lt hr0) (n + 1)
  have hfield : |finiteDot a field| ≤ finiteCoordinateNorm SourceNorm.l2 a := by
    exact populationTheorem3_finiteDot_field_abs_le_l2_norm M x a
  have hdirection : |finiteDot a direction| ≤ finiteCoordinateNorm SourceNorm.l2 a := by
    exact
      (finiteDot_abs_le_l2_mul_l2 a direction).trans
        (mul_le_of_le_one_right (finiteCoordinateNorm_l2_nonneg a)
          (modelBFiniteNormalizedDirection_l2_norm_le_one
            (M.utilityGradient (sample n omega) x)))
  change |r * (finiteDot a field - finiteDot a direction)| ≤
    2 * (finiteCoordinateNorm SourceNorm.l2 a * r)
  calc
    |r * (finiteDot a field - finiteDot a direction)| =
        r * |finiteDot a field - finiteDot a direction| := by
          rw [abs_mul, abs_of_nonneg hr]
    _ ≤ r * (|finiteDot a field| + |finiteDot a direction|) := by
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) hr
    _ ≤ r * (finiteCoordinateNorm SourceNorm.l2 a + finiteCoordinateNorm SourceNorm.l2 a) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hfield hdirection) hr
    _ = 2 * (finiteCoordinateNorm SourceNorm.l2 a * r) := by ring

/--
The literal general-population iid source for the full-space Theorem 3 route.
`state` exposes that the time-`n` iterate is determined by the finite history
through coordinate `n`; the next voter is the independent `(n+1)`st iid draw.
The remaining analytic fields are the standard well-definedness conditions
implicit in the source's iid sampling and probability-one convergence
language: the displayed finite-history recursion is measurable, adapted, and
integrable enough for its conditional expectations to be defined.  They are
not a convergence, stationarity, or martingale conclusion.  The martingale
conditional-mean equality is derived below from this data and the shared
iid-conditioning theorem.
-/
structure PopulationTheorem3IidTraceSource
    {Voter Coord : Type*} [MetricSpace Voter] [SecondCountableTopology Voter]
    [MeasurableSpace Voter] [BorelSpace Voter] [StandardBorelSpace Voter]
    [Nonempty Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : PopulationTheorem3DirectionalFieldModel E) where
  initial : Coord → ℝ
  trajectory : ℕ → (ℕ → Voter) → Coord → ℝ
  state : ∀ n, (Fin (n + 1) → Voter) → Coord → ℝ
  r0 : ℝ
  r0_pos : 0 < r0
  /-- This is the full-space branch of the approved Theorem 3 clarification.
  Consequently, the source projection is the identity and the displayed raw
  Model B update is the actual next iterate. -/
  solutionSpace_univ : E.solutionSpace = Set.univ
  field_continuity : PopulationTheorem3DirectionalFieldUniformContinuity M
  initial_eq : ∀ omega, trajectory 0 omega = initial
  trajectory_from_past : ∀ n omega,
    trajectory n omega = state n (iidSequencePastPrefix n omega)
  raw_update :
    ∀ n omega,
      trajectory (n + 1) omega =
        fun i => trajectory n omega i +
          ilvRadius r0 (n + 1) *
            modelBFiniteNormalizedDirection SourceNorm.l2
              (M.utilityGradient (iidSequenceSample n omega) (trajectory n omega)) i
  centered_test_integrable :
    ∀ (a : Coord → ℝ) n,
      Integrable (fun z : (Fin (n + 1) → Voter) × Voter =>
        populationTheorem3PastCenteredTest M (ilvRadius r0 (n + 1)) a
          (state n z.1) z.2)
        (Measure.map (fun omega =>
          (iidSequencePastPrefix n omega, iidSequenceSample n omega))
          (iidSequenceMeasure M.population))
  centered_partial_sum_adapted :
    ∀ a : Coord → ℝ,
      StronglyAdapted (iidSequenceNaturalFiltration (α := Voter))
        (fun n omega => ∑ i ∈ Finset.range n,
          populationTheorem3CenteredIncrement M r0 trajectory iidSequenceSample a i omega)
  centered_aestronglyMeasurable :
    ∀ (a : Coord → ℝ) (n : ℕ),
      AEStronglyMeasurable
        (populationTheorem3CenteredIncrement M r0 trajectory iidSequenceSample a n)
        (iidSequenceMeasure M.population)

/-- The displayed population trace is a literal source Model B response at
every step: the vector in its zero-safe update is certified as a subgradient of
the sampled voter's utility. -/
theorem PopulationTheorem3IidTraceSource.raw_update_is_modelB_response
    {Voter Coord : Type*} [MetricSpace Voter] [SecondCountableTopology Voter]
    [MeasurableSpace Voter] [BorelSpace Voter] [StandardBorelSpace Voter]
    [Nonempty Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : PopulationTheorem3DirectionalFieldModel E}
    (S : PopulationTheorem3IidTraceSource M) (n : ℕ) (omega : ℕ → Voter) :
    ModelBFiniteResponseWithSourceSubgradient
      (E.utility (iidSequenceSample n omega)) SourceNorm.l2
      (S.trajectory n omega) (ilvRadius S.r0 (n + 1))
      (S.trajectory (n + 1) omega) := by
  refine ⟨M.utilityGradient (iidSequenceSample n omega) (S.trajectory n omega),
    M.utilityGradient_source_subgradient (iidSequenceSample n omega)
      (S.trajectory n omega), ?_⟩
  rw [modelBFiniteResponseAt_formula, S.raw_update n omega]

theorem PopulationTheorem3IidTraceSource.centered_condExp_zero
    {Voter Coord : Type*} [MetricSpace Voter] [SecondCountableTopology Voter]
    [MeasurableSpace Voter] [BorelSpace Voter] [StandardBorelSpace Voter]
    [Nonempty Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : PopulationTheorem3DirectionalFieldModel E}
    (S : PopulationTheorem3IidTraceSource M) (a : Coord → ℝ) (n : ℕ) :
    (iidSequenceMeasure M.population)[fun omega =>
      populationTheorem3CenteredIncrement M S.r0 S.trajectory iidSequenceSample a n omega |
      iidSequenceNaturalFiltration (α := Voter) n] =ᵐ[iidSequenceMeasure M.population] 0 := by
  letI : IsProbabilityMeasure M.population := M.population_probability
  let test : (Fin (n + 1) → Voter) → Voter → ℝ :=
    fun history voter =>
      populationTheorem3PastCenteredTest M (ilvRadius S.r0 (n + 1)) a
        (S.state n history) voter
  have hcond := iidSequencePastPrefix_condExp_ae_eq_integral
    M.population n test (S.centered_test_integrable a n)
  have hcentered_eq :
      (fun omega =>
        populationTheorem3CenteredIncrement M S.r0 S.trajectory iidSequenceSample a n omega) =
        (fun omega => test (iidSequencePastPrefix n omega) (iidSequenceSample n omega)) := by
    funext omega
    simp [test, populationTheorem3PastCenteredTest,
      populationTheorem3CenteredIncrement, S.trajectory_from_past n omega]
  filter_upwards [hcond] with omega hcondomega
  rw [hcentered_eq, hcondomega]
  have hzero := populationTheorem3PastCenteredTest_integral_zero M
    (ilvRadius S.r0 (n + 1)) a (S.state n (iidSequencePastPrefix n omega))
  simpa [test, populationTheorem3PastCenteredTest, populationTheorem3CenteredIncrement,
    S.trajectory_from_past n omega] using hzero

/--
Outcome-indexed, unprojected Algorithm 1 source data for the population
version of Theorem 3.  `raw_update` is the literal Model B update in full
space.  The three martingale fields are measurable sampling facts about that
displayed increment, not convergence or equilibrium conclusions.  The
paper-facing `PopulationTheorem3IidTraceSource` constructs this generic proof
kernel from a finite history, a fresh iid population draw, and the population
integral.
-/
structure PopulationTheorem3FullspaceTrace
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : PopulationTheorem3DirectionalFieldModel E) where
  Omega : Type*
  measurableOmega : MeasurableSpace Omega
  mu : Measure Omega
  probability : IsProbabilityMeasure mu
  filtration : Filtration (Ω := Omega) ℕ measurableOmega
  initial : Coord → ℝ
  trajectory : ℕ → Omega → Coord → ℝ
  sample : ℕ → Omega → Voter
  r0 : ℝ
  r0_pos : 0 < r0
  field_continuity : PopulationTheorem3DirectionalFieldUniformContinuity M
  initial_eq : ∀ omega, trajectory 0 omega = initial
  raw_update :
    ∀ n omega,
      trajectory (n + 1) omega =
        fun i => trajectory n omega i +
          ilvRadius r0 (n + 1) *
            modelBFiniteNormalizedDirection SourceNorm.l2
              (M.utilityGradient (sample n omega) (trajectory n omega)) i
  centered_partial_sum_adapted :
    ∀ a : Coord → ℝ,
      StronglyAdapted filtration
        (fun n omega => ∑ i ∈ Finset.range n,
          populationTheorem3CenteredIncrement M r0 trajectory sample a i omega)
  centered_condExp_zero :
    ∀ (a : Coord → ℝ) (n : ℕ),
      mu[fun omega => populationTheorem3CenteredIncrement M r0 trajectory sample a n omega | filtration n] =ᵐ[mu] 0
  centered_aestronglyMeasurable :
    ∀ (a : Coord → ℝ) (n : ℕ),
      AEStronglyMeasurable
        (populationTheorem3CenteredIncrement M r0 trajectory sample a n) mu
  centered_abs_bound :
    ∀ (a : Coord → ℝ) (n : ℕ), ∀ᵐ omega ∂mu,
      |populationTheorem3CenteredIncrement M r0 trajectory sample a n omega| ≤
        2 * (finiteCoordinateNorm SourceNorm.l2 a * ilvRadius r0 (n + 1))

/-- The canonical iid source supplies the generic martingale proof kernel.
In particular, the conditional-mean-zero field is not trusted as a
theorem-shaped source premise: it is derived from the history/fresh-draw
factorization and the population integral. -/
noncomputable def PopulationTheorem3IidTraceSource.toFullspaceTrace
    {Voter Coord : Type*} [MetricSpace Voter] [SecondCountableTopology Voter]
    [MeasurableSpace Voter] [BorelSpace Voter] [StandardBorelSpace Voter]
    [Nonempty Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : PopulationTheorem3DirectionalFieldModel E}
    (S : PopulationTheorem3IidTraceSource M) :
    PopulationTheorem3FullspaceTrace M := by
  letI : IsProbabilityMeasure M.population := M.population_probability
  exact
    { Omega := ℕ → Voter
      measurableOmega := inferInstance
      mu := iidSequenceMeasure M.population
      probability := iidSequenceMeasure_isProbabilityMeasure M.population
      filtration := iidSequenceNaturalFiltration (α := Voter)
      initial := S.initial
      trajectory := S.trajectory
      sample := iidSequenceSample
      r0 := S.r0
      r0_pos := S.r0_pos
      field_continuity := S.field_continuity
      initial_eq := S.initial_eq
      raw_update := S.raw_update
      centered_partial_sum_adapted := S.centered_partial_sum_adapted
      centered_condExp_zero := S.centered_condExp_zero
      centered_aestronglyMeasurable := S.centered_aestronglyMeasurable
      centered_abs_bound := fun a n =>
        Filter.Eventually.of_forall (fun omega =>
          populationTheorem3_centeredIncrement_abs_le M S.r0 S.trajectory iidSequenceSample
            a n omega S.r0_pos) }

theorem PopulationTheorem3FullspaceTrace.centered_sum_identity
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : PopulationTheorem3DirectionalFieldModel E}
    (T : PopulationTheorem3FullspaceTrace M) (a : Coord → ℝ) :
    ∀ n omega,
      (∑ t ∈ Finset.range n,
        ilvRadius T.r0 (t + 1) *
          finiteDot a
            (populationTheorem3DirectionalField M.population M.utilityGradient
              (T.trajectory t omega))) +
        finiteDot a (T.trajectory 0 omega) -
          finiteDot a (T.trajectory n omega) =
        ∑ t ∈ Finset.range n,
          populationTheorem3CenteredIncrement M T.r0 T.trajectory T.sample a t omega := by
  intro n omega
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hstep :
          finiteDot a (T.trajectory (n + 1) omega) =
            finiteDot a (T.trajectory n omega) +
              ilvRadius T.r0 (n + 1) *
                finiteDot a
                  (modelBFiniteNormalizedDirection SourceNorm.l2
                    (M.utilityGradient (T.sample n omega) (T.trajectory n omega))) := by
        rw [T.raw_update]
        exact finiteDot_add_scaled_right a (T.trajectory n omega)
          (modelBFiniteNormalizedDirection SourceNorm.l2
            (M.utilityGradient (T.sample n omega) (T.trajectory n omega)))
          (ilvRadius T.r0 (n + 1))
      rw [hstep]
      calc
        (∑ t ∈ Finset.range n,
            ilvRadius T.r0 (t + 1) *
              finiteDot a
                (populationTheorem3DirectionalField M.population M.utilityGradient
                  (T.trajectory t omega))) +
              ilvRadius T.r0 (n + 1) *
                finiteDot a
                  (populationTheorem3DirectionalField M.population M.utilityGradient
                    (T.trajectory n omega)) +
              finiteDot a (T.trajectory 0 omega) -
                (finiteDot a (T.trajectory n omega) +
                  ilvRadius T.r0 (n + 1) *
                    finiteDot a
                      (modelBFiniteNormalizedDirection SourceNorm.l2
                        (M.utilityGradient (T.sample n omega) (T.trajectory n omega)))) =
            ((∑ t ∈ Finset.range n,
                ilvRadius T.r0 (t + 1) *
                  finiteDot a
                    (populationTheorem3DirectionalField M.population M.utilityGradient
                      (T.trajectory t omega))) +
                finiteDot a (T.trajectory 0 omega) -
                  finiteDot a (T.trajectory n omega)) +
              (ilvRadius T.r0 (n + 1) *
                finiteDot a
                  (populationTheorem3DirectionalField M.population M.utilityGradient
                    (T.trajectory n omega)) -
                ilvRadius T.r0 (n + 1) *
                  finiteDot a
                    (modelBFiniteNormalizedDirection SourceNorm.l2
                      (M.utilityGradient (T.sample n omega) (T.trajectory n omega)))) := by
              ring
        _ = (∑ t ∈ Finset.range n,
            populationTheorem3CenteredIncrement M T.r0 T.trajectory T.sample a t omega) +
              (ilvRadius T.r0 (n + 1) *
                finiteDot a
                  (populationTheorem3DirectionalField M.population M.utilityGradient
                    (T.trajectory n omega)) -
                ilvRadius T.r0 (n + 1) *
                  finiteDot a
                    (modelBFiniteNormalizedDirection SourceNorm.l2
                      (M.utilityGradient (T.sample n omega) (T.trajectory n omega)))) := by
              rw [ih]
        _ = (∑ t ∈ Finset.range n,
            populationTheorem3CenteredIncrement M T.r0 T.trajectory T.sample a t omega) +
              populationTheorem3CenteredIncrement M T.r0 T.trajectory T.sample a n omega := by
              unfold populationTheorem3CenteredIncrement
              ring

/-- The population trace has an almost-sure bounded martingale fluctuation in
every finite-coordinate scalar direction.  This is the probability step used
by the population form of Theorem 3; it is independent of any finite-voter
enumeration. -/
theorem PopulationTheorem3FullspaceTrace.eventual_finiteDot_fluctuation
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : PopulationTheorem3DirectionalFieldModel E}
    (T : PopulationTheorem3FullspaceTrace M) (a : Coord → ℝ) :
    ∀ᵐ omega ∂T.mu,
      ∃ fluctuationBound : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∑ t ∈ Finset.range n,
          ilvRadius T.r0 (t + 1) *
            finiteDot a
              (populationTheorem3DirectionalField M.population M.utilityGradient
                (T.trajectory t omega))) - fluctuationBound ≤
          -finiteDot a T.initial +
            finiteDot a (T.trajectory n omega) := by
  let Y : ℕ → T.Omega → ℝ :=
    fun n omega => populationTheorem3CenteredIncrement M T.r0 T.trajectory T.sample a n omega
  let c : ℕ → ℝ :=
    fun n => 2 * (finiteCoordinateNorm SourceNorm.l2 a * ilvRadius T.r0 (n + 1))
  let expected : ℕ → T.Omega → ℝ :=
    fun n omega => ∑ t ∈ Finset.range n,
      ilvRadius T.r0 (t + 1) *
        finiteDot a
          (populationTheorem3DirectionalField M.population M.utilityGradient
            (T.trajectory t omega))
  let realized : ℕ → T.Omega → ℝ := fun n omega => finiteDot a (T.trajectory n omega)
  let base : ℝ := -finiteDot a T.initial
  letI : IsProbabilityMeasure T.mu := T.probability
  have hcentered : ∀ n omega,
      expected n omega - base - realized n omega =
        ∑ i ∈ Finset.range n, Y i omega := by
    intro n omega
    simpa [expected, realized, base, Y, T.initial_eq omega] using
      T.centered_sum_identity a n omega
  simpa [expected, realized, base, Y, c] using
    (proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_boundedIncrement_summable_partialSumAdapted
      (μ := T.mu) (Y := Y) (c := c) (ℱ := T.filtration)
      (expected := expected) (realized := realized) (base := base)
      (T.centered_partial_sum_adapted a) (T.centered_condExp_zero a)
      (T.centered_aestronglyMeasurable a)
      (fun n => finiteDot_modelB_centered_response_increment_ilvRadius_bound_nonneg a T.r0_pos n)
      (T.centered_abs_bound a)
      (finiteDot_modelB_centered_response_increment_ilvRadius_bound_sq_summable a T.r0)
      hcentered)

/-- A convergent outcome of the literal population Model B recursion has zero
population directional field.  The proof combines the local positive drift of
a nonzero field with the square-summable martingale fluctuation and the
divergent harmonic step-size tail. -/
theorem PopulationTheorem3FullspaceTrace.population_field_eq_zero_of_converges
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : PopulationTheorem3DirectionalFieldModel E}
    (T : PopulationTheorem3FullspaceTrace M) {omega : T.Omega} {xstar : Coord → ℝ}
    (hfluctuation :
      ∃ fluctuationBound : ℝ, ∃ T0 : ℕ, ∀ n : ℕ, T0 ≤ n →
        (∑ t ∈ Finset.range n,
          ilvRadius T.r0 (t + 1) *
            finiteDot
              (populationTheorem3DirectionalField M.population M.utilityGradient xstar)
              (populationTheorem3DirectionalField M.population M.utilityGradient
                (T.trajectory t omega))) - fluctuationBound ≤
          -finiteDot
              (populationTheorem3DirectionalField M.population M.utilityGradient xstar)
              T.initial +
            finiteDot
              (populationTheorem3DirectionalField M.population M.utilityGradient xstar)
              (T.trajectory n omega))
    (hconverges : PopulationTheorem3OutcomeConvergesTo T.trajectory omega xstar) :
    populationTheorem3DirectionalField M.population M.utilityGradient xstar =
      fun _ => (0 : ℝ) := by
  by_contra hne
  let a : Coord → ℝ :=
    populationTheorem3DirectionalField M.population M.utilityGradient xstar
  rcases populationTheorem3DirectionalField_eventual_finiteDot_drift_of_converges
      M T.field_continuity.to_coordinate_continuity hconverges (by simpa [a] using hne) with
    ⟨N, c, hc, hdrift⟩
  rcases hfluctuation with ⟨fluctuationBound, T0, hfluctuation⟩
  let K : ℕ := N + T0
  let rawExpected : ℕ → ℝ := fun m =>
    ∑ t ∈ Finset.range m,
      ilvRadius T.r0 (t + 1) *
        finiteDot a
          (populationTheorem3DirectionalField M.population M.utilityGradient
            (T.trajectory t omega))
  let tailExpected : ℕ → ℝ := fun n =>
    ∑ t ∈ Finset.range n,
      ilvTailRadius T.r0 K t *
        finiteDot a
          (populationTheorem3DirectionalField M.population M.utilityGradient
            (T.trajectory (K + t) omega))
  have hraw_split : ∀ n : ℕ, rawExpected (K + n) = rawExpected K + tailExpected n := by
    intro n
    dsimp [rawExpected, tailExpected]
    rw [Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    simp [ilvTailRadius, Nat.add_assoc, Nat.add_comm]
  have htail_lower : ∀ n : ℕ,
      c * (∑ t ∈ Finset.range n, ilvTailRadius T.r0 K t) ≤ tailExpected n := by
    intro n
    calc
      c * (∑ t ∈ Finset.range n, ilvTailRadius T.r0 K t) =
          ∑ t ∈ Finset.range n, c * ilvTailRadius T.r0 K t := by
            rw [Finset.mul_sum]
      _ = ∑ t ∈ Finset.range n, ilvTailRadius T.r0 K t * c := by
            apply Finset.sum_congr rfl
            intro t _
            ring
      _ ≤ ∑ t ∈ Finset.range n, ilvTailRadius T.r0 K t *
          finiteDot a
            (populationTheorem3DirectionalField M.population M.utilityGradient
              (T.trajectory (K + t) omega)) := by
            apply Finset.sum_le_sum
            intro t _
            have hstep : c ≤ finiteDot a
                (populationTheorem3DirectionalField M.population M.utilityGradient
                  (T.trajectory (K + t) omega)) := by
              simpa [a, K, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                hdrift (T0 + t)
            exact mul_le_mul_of_nonneg_left hstep
              (ilvTailRadius_nonneg (le_of_lt T.r0_pos) K t)
      _ = tailExpected n := rfl
  let base : ℝ := rawExpected K - fluctuationBound + finiteDot a T.initial
  have hlower : ∀ n : ℕ,
      base + c * (∑ t ∈ Finset.range n, ilvTailRadius T.r0 K t) ≤
        finiteDot a (T.trajectory (K + n) omega) := by
    intro n
    have hK : T0 ≤ K + n := by
      dsimp [K]
      omega
    have hfluctuation_n := hfluctuation (K + n) hK
    have hfluctuation_n' :
        rawExpected (K + n) - fluctuationBound + finiteDot a T.initial ≤
          finiteDot a (T.trajectory (K + n) omega) := by
      calc
        rawExpected (K + n) - fluctuationBound + finiteDot a T.initial =
            finiteDot a T.initial + (rawExpected (K + n) - fluctuationBound) := by
              ring
        _ ≤ finiteDot a (T.trajectory (K + n) omega) := by
              simpa [rawExpected, a] using hfluctuation_n
    have htail := htail_lower n
    calc
      base + c * (∑ t ∈ Finset.range n, ilvTailRadius T.r0 K t) ≤
          rawExpected K - fluctuationBound + finiteDot a T.initial + tailExpected n := by
            dsimp [base]
            linarith
      _ = rawExpected (K + n) - fluctuationBound + finiteDot a T.initial := by
            rw [hraw_split]
            ring
      _ ≤ finiteDot a (T.trajectory (K + n) omega) := hfluctuation_n'
  have hscalar_converges :
      Filter.Tendsto (fun n : ℕ => finiteDot a (T.trajectory (K + n) omega))
        Filter.atTop (nhds (finiteDot a xstar)) := by
    have hshift : Filter.Tendsto (fun n : ℕ => K + n) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop.2 ?_
      intro m
      exact Filter.eventually_atTop.2
        ⟨m, fun n hn => by omega⟩
    exact (finiteDot_tendsto_of_coordinatewise a hconverges).comp
      hshift
  exact scalar_convergence_contradiction_of_accumulated_drift
    hc (ilvTailRadius_sum_tendsto_atTop T.r0_pos K) hlower hscalar_converges

/-- The population Theorem 3 conclusion holds on every outcome on which the
source recursion converges; in particular it holds almost surely whenever the
paper's convergence premise holds almost surely. -/
theorem PopulationTheorem3FullspaceTrace.ae_population_field_eq_zero_of_ae_converges
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : PopulationTheorem3DirectionalFieldModel E}
    (T : PopulationTheorem3FullspaceTrace M) (xstar : Coord → ℝ)
    (hconverges : ∀ᵐ omega ∂T.mu,
      PopulationTheorem3OutcomeConvergesTo T.trajectory omega xstar) :
    ∀ᵐ omega ∂T.mu,
      populationTheorem3DirectionalField M.population M.utilityGradient xstar =
        fun _ => (0 : ℝ) := by
  filter_upwards [T.eventual_finiteDot_fluctuation
    (populationTheorem3DirectionalField M.population M.utilityGradient xstar), hconverges]
    with omega hfluctuation homega
  exact T.population_field_eq_zero_of_converges hfluctuation homega

/-- The completed general-population Theorem 3 route.  It starts from the
literal iid population source, derives the conditional mean from that source,
and proves that every almost-sure limit has zero population directional field.
No finite voter enumeration or finite-support approximation is used. -/
theorem PopulationTheorem3IidTraceSource.ae_population_field_eq_zero_of_ae_converges
    {Voter Coord : Type*} [MetricSpace Voter] [SecondCountableTopology Voter]
    [MeasurableSpace Voter] [BorelSpace Voter] [StandardBorelSpace Voter]
    [Nonempty Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : PopulationTheorem3DirectionalFieldModel E}
    (S : PopulationTheorem3IidTraceSource M) (xstar : Coord → ℝ)
    (hconverges : ∀ᵐ omega ∂iidSequenceMeasure M.population,
      PopulationTheorem3OutcomeConvergesTo S.trajectory omega xstar) :
    ∀ᵐ omega ∂iidSequenceMeasure M.population,
      populationTheorem3DirectionalField M.population M.utilityGradient xstar =
        fun _ => (0 : ℝ) := by
  exact S.toFullspaceTrace.ae_population_field_eq_zero_of_ae_converges
    xstar hconverges

/-- The preceding population-field conclusion expressed in the paper's
directional-equilibrium vocabulary. -/
theorem PopulationTheorem3IidTraceSource.ae_isDirectionalEquilibrium_of_ae_converges
    {Voter Coord : Type*} [MetricSpace Voter] [SecondCountableTopology Voter]
    [MeasurableSpace Voter] [BorelSpace Voter] [StandardBorelSpace Voter]
    [Nonempty Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : PopulationTheorem3DirectionalFieldModel E}
    (S : PopulationTheorem3IidTraceSource M) (xstar : Coord → ℝ)
    (hconverges : ∀ᵐ omega ∂iidSequenceMeasure M.population,
      PopulationTheorem3OutcomeConvergesTo S.trajectory omega xstar) :
    ∀ᵐ omega ∂iidSequenceMeasure M.population,
      IsDirectionalEquilibrium E xstar := by
  filter_upwards [S.ae_population_field_eq_zero_of_ae_converges xstar hconverges]
    with omega hfield
  unfold IsDirectionalEquilibrium
  rw [M.directionalField_eq, M.zeroDirection_eq]
  exact hfield

/-- The general-population iid full-space theorem used by the paper-facing
Theorem 3 endpoint.  It remains a proof-layer theorem so the review surface
has one direct, fully displayed semantic target rather than a nested wrapper. -/
theorem populationTheorem3_iid_fullspace_directional_equilibrium
    {Voter Coord : Type*} [MetricSpace Voter] [SecondCountableTopology Voter]
    [MeasurableSpace Voter] [BorelSpace Voter] [StandardBorelSpace Voter]
    [Nonempty Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : PopulationTheorem3DirectionalFieldModel E)
    (S : PopulationTheorem3IidTraceSource M)
    (xstar : Coord → ℝ)
    (hconverges : ∀ᵐ omega ∂iidSequenceMeasure M.population,
      PopulationTheorem3OutcomeConvergesTo S.trajectory omega xstar) :
    ∀ᵐ omega ∂iidSequenceMeasure M.population,
      IsDirectionalEquilibrium E xstar := by
  exact S.ae_isDirectionalEquilibrium_of_ae_converges xstar hconverges

end GKGMM19IterativeLocalVoting
