import PKG25NoFreeLunch.JointSourceModel

/-!
# PKG25 source-domain collaboration strategies

The paper defines a collaboration strategy on the probability cube
`[0,1]^n`.  The older finite-witness proof surface totalized a strategy to all
real profiles for convenience.  This file makes the source domain exact and
supplies the explicit extension bridge used only to reuse that proof surface.
No source-facing result quantifies over the extension outside the cube.
-/

open MeasureTheory

namespace PKG25NoFreeLunch

/-- The source domain `[0,1]^n` for a vector of reported probabilities. -/
def UnitCubeProfile (n : ℕ) :=
  { p : Fin n → ℝ // ∀ i, 0 ≤ p i ∧ p i ≤ 1 }

/-- A deterministic source strategy `C : [0,1]^n → {0,1}`. -/
abbrev SourceCollaborationStrategy (n : ℕ) := UnitCubeProfile n → Label

/-- An interior profile is canonically a source-domain cube profile. -/
def Interior.toUnitCubeProfile {n : ℕ} (p : Fin n → ℝ) (hp : Interior p) :
    UnitCubeProfile n :=
  ⟨p, fun i => ⟨le_of_lt (hp i).1, le_of_lt (hp i).2⟩⟩

/-- Predictor values in a source setting form a cube profile. -/
def JointLawCollaborationSetting.sourcePredictionProfile {n : ℕ}
    (S : JointLawCollaborationSetting n) (x : S.X) : UnitCubeProfile n :=
  ⟨fun i => S.pred i x, fun i => S.pred_range i x⟩

/-- Extend a source strategy off its domain only to reuse finite witness proofs. -/
noncomputable def extendSourceStrategy {n : ℕ}
    (C : SourceCollaborationStrategy n) : CollaborationStrategy n :=
  fun p => if hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1 then C ⟨p, hp⟩ else false

/-- On the source cube, the proof-only extension is exactly the source strategy. -/
theorem extendSourceStrategy_apply_cube {n : ℕ}
    (C : SourceCollaborationStrategy n) (p : UnitCubeProfile n) :
    extendSourceStrategy C p.1 = C p := by
  simp [extendSourceStrategy, p.property]

/-- The classifier induced by a source-domain strategy. -/
def JointLawCollaborationSetting.sourceStrategyClassifier {n : ℕ}
    (S : JointLawCollaborationSetting n) (C : SourceCollaborationStrategy n)
    (x : S.X) : Label :=
  C (S.sourcePredictionProfile x)

/-- The source-domain strategy's accuracy under a raw joint law. -/
noncomputable def JointLawCollaborationSetting.sourceStrategyAccuracy {n : ℕ}
    (S : JointLawCollaborationSetting n) (C : SourceCollaborationStrategy n) : ℝ :=
  S.classifierAccuracy (S.sourceStrategyClassifier C)

/-- The source expectation-definedness convention for a source strategy. -/
def SourceStrategyWellFormed {n : ℕ} (S : JointLawCollaborationSetting n)
    (C : SourceCollaborationStrategy n) : Prop :=
  Integrable
    (fun z : S.X × Label =>
      if S.sourceStrategyClassifier C z.1 = z.2 then (1 : ℝ) else 0)
    S.joint

theorem JointLawCollaborationSetting.sourceStrategyClassifier_eq_extension
    {n : ℕ} (S : JointLawCollaborationSetting n)
    (C : SourceCollaborationStrategy n) (x : S.X) :
    S.sourceStrategyClassifier C x =
      S.strategyClassifier (extendSourceStrategy C) x := by
  change C (S.sourcePredictionProfile x) =
    extendSourceStrategy C (S.sourcePredictionProfile x).1
  exact (extendSourceStrategy_apply_cube C (S.sourcePredictionProfile x)).symm

theorem JointLawCollaborationSetting.sourceStrategyAccuracy_eq_extension
    {n : ℕ} (S : JointLawCollaborationSetting n)
    (C : SourceCollaborationStrategy n) :
    S.sourceStrategyAccuracy C = S.strategyAccuracy (extendSourceStrategy C) := by
  unfold JointLawCollaborationSetting.sourceStrategyAccuracy
    JointLawCollaborationSetting.strategyAccuracy
    JointLawCollaborationSetting.classifierAccuracy
  apply integral_congr_ae
  filter_upwards with z
  exact congrArg (fun y => if y = z.2 then (1 : ℝ) else 0)
    (S.sourceStrategyClassifier_eq_extension C z.1)

theorem sourceStrategyWellFormed_iff_extension {n : ℕ}
    (S : JointLawCollaborationSetting n) (C : SourceCollaborationStrategy n) :
    SourceStrategyWellFormed S C ↔ S.StrategyWellFormed (extendSourceStrategy C) := by
  unfold SourceStrategyWellFormed JointLawCollaborationSetting.StrategyWellFormed
  constructor <;> intro h
  · apply h.congr
    filter_upwards with z
    exact congrArg (fun y => if y = z.2 then (1 : ℝ) else 0)
      (S.sourceStrategyClassifier_eq_extension C z.1)
  · apply h.congr
    filter_upwards with z
    exact (congrArg (fun y => if y = z.2 then (1 : ℝ) else 0)
      (S.sourceStrategyClassifier_eq_extension C z.1)).symm

/-- Source reliability, with the user-approved nonempty-agent convention. -/
def SourceReliableJointLaw {n : ℕ} [Nonempty (Fin n)]
    (C : SourceCollaborationStrategy n) : Prop :=
  ∀ S : JointLawCollaborationSetting n,
    SourceStrategyWellFormed S C →
      ∃ i : Fin n, S.agentAccuracy i ≤ S.sourceStrategyAccuracy C

theorem reliableJointLaw_of_sourceReliableJointLaw {n : ℕ} [Nonempty (Fin n)]
    {C : SourceCollaborationStrategy n} (hrel : SourceReliableJointLaw C) :
    ReliableJointLaw (extendSourceStrategy C) := by
  intro S hwell
  rcases hrel S ((sourceStrategyWellFormed_iff_extension S C).mpr hwell) with
    ⟨i, hi⟩
  exact ⟨i, by simpa [S.sourceStrategyAccuracy_eq_extension C] using hi⟩

/-- Source Definition 4's fixed-agent, off-half clause on the exact cube. -/
def SourceDefersAwayFromHalf {n : ℕ} (C : SourceCollaborationStrategy n)
    (k : Fin n) : Prop :=
  ∀ p : UnitCubeProfile n, Interior p.1 → p.1 k ≠ (1 : ℝ) / 2 →
    C p = roundProb (p.1 k)

/-- Source Definition 4's fixed-label half-slice clause on the exact cube. -/
def SourceConstantOnHalfSlice {n : ℕ} (C : SourceCollaborationStrategy n)
    (k : Fin n) (alpha : Label) : Prop :=
  ∀ p : UnitCubeProfile n, Interior p.1 → p.1 k = (1 : ℝ) / 2 → C p = alpha

/-- The source's non-collaboration definition on `[0,1]^n`. -/
def SourceNonCollaborative {n : ℕ} (C : SourceCollaborationStrategy n) : Prop :=
  ∃ k : Fin n, ∃ alpha : Label,
    SourceDefersAwayFromHalf C k ∧ SourceConstantOnHalfSlice C k alpha

theorem sourceDefersAwayFromHalf_of_extension {n : ℕ}
    {C : SourceCollaborationStrategy n} {k : Fin n}
    (h : DefersAwayFromHalf (extendSourceStrategy C) k) :
    SourceDefersAwayFromHalf C k := by
  intro p hp hhalf
  rw [← extendSourceStrategy_apply_cube C p]
  exact h p.1 hp hhalf

theorem sourceConstantOnHalfSlice_of_extension {n : ℕ}
    {C : SourceCollaborationStrategy n} {k : Fin n} {alpha : Label}
    (h : ConstantOnHalfSlice (extendSourceStrategy C) k alpha) :
    SourceConstantOnHalfSlice C k alpha := by
  intro p hp hhalf
  rw [← extendSourceStrategy_apply_cube C p]
  exact h p.1 hp hhalf

theorem sourceNonCollaborative_of_extension {n : ℕ}
    {C : SourceCollaborationStrategy n}
    (h : NonCollaborative (extendSourceStrategy C)) : SourceNonCollaborative C := by
  rcases h with ⟨k, alpha, hdefer, hslice⟩
  exact ⟨k, alpha, sourceDefersAwayFromHalf_of_extension hdefer,
    sourceConstantOnHalfSlice_of_extension hslice⟩

theorem source_defers_of_reliable {n : ℕ} [Nonempty (Fin n)]
    {C : SourceCollaborationStrategy n} (hrel : SourceReliableJointLaw C) :
    ∃ k : Fin n, SourceDefersAwayFromHalf C k := by
  rcases reliableFinite_exists_defers_away
      (reliableFinite_of_reliableJointLaw
        (reliableJointLaw_of_sourceReliableJointLaw hrel)) with ⟨k, hk⟩
  exact ⟨k, sourceDefersAwayFromHalf_of_extension hk⟩

theorem source_constant_half_of_reliable {n : ℕ} [Nonempty (Fin n)]
    {C : SourceCollaborationStrategy n} (k : Fin n)
    (hrel : SourceReliableJointLaw C) (hk : SourceDefersAwayFromHalf C k) :
    ∃ alpha : Label, SourceConstantOnHalfSlice C k alpha := by
  have hrel' := reliableJointLaw_of_sourceReliableJointLaw hrel
  have hk' : DefersAwayFromHalf (extendSourceStrategy C) k := by
    intro p hp hhalf
    rw [show extendSourceStrategy C p =
      C (Interior.toUnitCubeProfile p hp) by
        exact extendSourceStrategy_apply_cube C (Interior.toUnitCubeProfile p hp)]
    exact hk (Interior.toUnitCubeProfile p hp) hp hhalf
  rcases reliableFinite_constant_on_half
      (reliableFinite_of_reliableJointLaw hrel') hk' with ⟨alpha, halpha⟩
  exact ⟨alpha, sourceConstantOnHalfSlice_of_extension halpha⟩

end PKG25NoFreeLunch
