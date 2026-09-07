import AppliedModelingLib.Foundations.Probability.IidPrefixStopping
import AppliedModelingLib.Foundations.Probability.MeasurableCountableEvaluation
import Mathlib.MeasureTheory.Constructions.Cylinders

/-!
# IID restart after an external-state prefix stop

This module records the elementary product-space factorization behind a
stopping rule that may inspect an arbitrary independent external state as
well as an IID prefix.  The finite block and complete tail after the stop have
the original IID law.  This is the form used when one input stream is stopped
while the other streams of a system are retained as external data.  The module
also gives an event-level factorization for explicitly prefix-measurable
stopped histories.  It does not package arbitrary stopped histories into a
separate measurable state or assert a continuous-time strong-Markov theorem.
-/

namespace AppliedModelingLib.Probability.IIDStream

open MeasureTheory ProbabilityTheory

noncomputable section

variable {σ α : Type*} [MeasurableSpace σ] [MeasurableSpace α]

/-- An external state together with an inspected IID prefix is independent of
every deterministic later IID block. -/
theorem indepFun_state_streamPrefix_block
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (n q : ℕ) :
    IndepFun
      (fun z : σ × (ℕ → α) => (z.1, streamPrefix (α := α) n z.2))
      (fun z : σ × (ℕ → α) => block (α := α) (n + 1) q z.2)
      (ρ.prod (measure μ)) := by
  let M : Measure (ℕ → α) := measure μ
  let p : (ℕ → α) → (Finset.range (n + 1) → α) := streamPrefix n
  let b : (ℕ → α) → (Fin q → α) := block (n + 1) q
  let X : σ × (ℕ → α) → σ × (Finset.range (n + 1) → α) :=
    fun z => (z.1, p z.2)
  let Y : σ × (ℕ → α) → Fin q → α := fun z => b z.2
  let pairPB : (ℕ → α) → (Finset.range (n + 1) → α) × (Fin q → α) :=
    fun ω => (p ω, b ω)
  have hM : IsProbabilityMeasure M := by
    dsimp [M, measure]
    infer_instance
  have hp : Measurable p := by
    simpa [p] using measurable_streamPrefix (α := α) n
  have hb : Measurable b := by
    simpa [b] using measurable_block (α := α) (n + 1) q
  have hpairPB : M.map pairPB = (M.map p).prod (M.map b) := by
    have hindep := indepFun_streamPrefix_block μ n q
    exact (indepFun_iff_map_prod_eq_prod_map_map
      hp.aemeasurable hb.aemeasurable).mp (by simpa [M, p, b, pairPB] using hindep)
  have hX : (ρ.prod M).map X = ρ.prod (M.map p) := by
    simpa [X] using (Measure.map_prod_map ρ M measurable_id hp).symm
  have hY : (ρ.prod M).map Y = M.map b := by
    calc
      (ρ.prod M).map Y = (ρ.prod M).map (b ∘ Prod.snd) := by rfl
      _ = ((ρ.prod M).map Prod.snd).map b := by
        rw [Measure.map_map hb measurable_snd]
      _ = M.map b := by
        rw [Measure.map_snd_prod, measure_univ, one_smul]
  apply (indepFun_iff_map_prod_eq_prod_map_map
    ((measurable_fst.prodMk (hp.comp measurable_snd)).aemeasurable)
    (hb.comp measurable_snd).aemeasurable).mpr
  calc
    (ρ.prod M).map (fun z => (X z, Y z)) =
        ((ρ.prod M).map (Prod.map id pairPB)).map
          (MeasurableEquiv.prodAssoc.symm :
            σ × ((Finset.range (n + 1) → α) × (Fin q → α)) →
              (σ × (Finset.range (n + 1) → α)) × (Fin q → α)) := by
          rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
            (measurable_id.prodMap (hp.prodMk hb))]
          rfl
    _ = (ρ.prod (M.map pairPB)).map
          (MeasurableEquiv.prodAssoc.symm :
            σ × ((Finset.range (n + 1) → α) × (Fin q → α)) →
              (σ × (Finset.range (n + 1) → α)) × (Fin q → α)) := by
          rw [← Measure.map_prod_map ρ M measurable_id (hp.prodMk hb)]
          rw [Measure.map_id]
    _ = (ρ.prod ((M.map p).prod (M.map b))).map
          (MeasurableEquiv.prodAssoc.symm :
            σ × ((Finset.range (n + 1) → α) × (Fin q → α)) →
              (σ × (Finset.range (n + 1) → α)) × (Fin q → α)) := by
          rw [hpairPB]
    _ = (ρ.prod (M.map p)).prod (M.map b) := by
          exact (measurePreserving_prodAssoc ρ (M.map p) (M.map b)).symm.map_eq
    _ = ((ρ.prod M).map X).prod ((ρ.prod M).map Y) := by
          rw [hX, hY]

/-- The visible external state together with the IID prefix through `n`. -/
def stateStreamPrefix (n : ℕ) :
    σ × (ℕ → α) → σ × (Finset.range (n + 1) → α) :=
  fun z => (z.1, streamPrefix (α := α) n z.2)

/-- The external-state/IID-prefix observation is Borel measurable. -/
theorem measurable_stateStreamPrefix (n : ℕ) :
    Measurable (stateStreamPrefix (σ := σ) (α := α) n) := by
  exact measurable_fst.prodMk ((measurable_streamPrefix (α := α) n).comp measurable_snd)

/-- The external state together with the first exactly `n` IID coordinates.
Unlike `stateStreamPrefix`, this convention has an empty prefix at `n = 0`.
It is the natural history convention when a random number of marks has been
consumed. -/
def stateInitialPrefix (n : ℕ) :
    σ × (ℕ → α) → σ × (Finset.range n → α) :=
  fun z => (z.1, fun i => coordinate (α := α) i z.2)

/-- The external-state/initial-IID-prefix observation is Borel measurable. -/
theorem measurable_stateInitialPrefix (n : ℕ) :
    Measurable (stateInitialPrefix (σ := σ) (α := α) n) := by
  apply measurable_fst.prodMk
  apply measurable_pi_lambda
  intro i
  exact (measurable_coordinate (α := α) (i : ℕ)).comp measurable_snd

/-- An external state together with the first exactly `n` IID coordinates is
independent of every deterministic block beginning at `n`. -/
theorem indepFun_stateInitialPrefix_block
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (n q : ℕ) :
    IndepFun
      (stateInitialPrefix (σ := σ) (α := α) n)
      (fun z : σ × (ℕ → α) => block (α := α) n q z.2)
      (ρ.prod (measure μ)) := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  cases n with
  | zero =>
      let emptyMarks : Finset.range 0 → α := fun i =>
        False.elim (Nat.not_lt_zero _ (Finset.mem_range.mp i.2))
      let g : σ → σ × (Finset.range 0 → α) := fun state => (state, emptyMarks)
      have hg : Measurable g := by
        exact measurable_id.prodMk measurable_const
      have hindep : IndepFun (fun z : σ × (ℕ → α) => g z.1)
          (fun z : σ × (ℕ → α) => block (α := α) 0 q z.2)
          (ρ.prod (measure μ)) := by
        exact indepFun_prod hg (measurable_block (α := α) 0 q)
      have hprefix : stateInitialPrefix (σ := σ) (α := α) 0 =
          fun z : σ × (ℕ → α) => g z.1 := by
        funext z
        apply Prod.ext
        · rfl
        · funext i
          exact False.elim (Nat.not_lt_zero _ (Finset.mem_range.mp i.2))
      rw [hprefix]
      exact hindep
  | succ n =>
      simpa [stateInitialPrefix, Nat.succ_eq_add_one] using
        (indepFun_state_streamPrefix_block ρ μ n q)

/-- Under a product measure, a measurable coordinate map with null fibers
cannot equal a measurable function of the other coordinate except on a null
set. -/
theorem measure_prod_apply_eq_graph_zero
    {β : Type*} [MeasurableSpace β]
    (ρ : Measure σ) (μ : Measure α) [SFinite μ]
    [MeasurableEq β] (h : α → β) (hh : Measurable h)
    (hzero : ∀ b : β, μ (h ⁻¹' {b}) = 0)
    (g : σ → β) (hg : Measurable g) :
    (ρ.prod μ) {z : σ × α | h z.2 = g z.1} = 0 := by
  let s : Set (σ × α) := {z | h z.2 = g z.1}
  change (ρ.prod μ) s = 0
  have hs : MeasurableSet s := by
    exact measurableSet_eq_fun (hh.comp measurable_snd) (hg.comp measurable_fst)
  rw [Measure.prod_apply hs]
  have hfiber : ∀ x : σ, μ (Prod.mk x ⁻¹' s) = 0 := by
    intro x
    have hpreimage : Prod.mk x ⁻¹' s = h ⁻¹' {g x} := by
      ext y
      simp [s]
    rw [hpreimage, hzero]
  simp_rw [hfiber]
  exact lintegral_zero

/-- Under a product measure, an atomless coordinate cannot agree with a
measurable function of the other coordinate except on a null set. -/
theorem measure_prod_graph_eq_zero
    (ρ : Measure σ) (μ : Measure α) [SFinite μ] [NoAtoms μ]
    [MeasurableEq α] (g : σ → α) (hg : Measurable g) :
    (ρ.prod μ) {z : σ × α | z.2 = g z.1} = 0 := by
  let s : Set (σ × α) := {z | z.2 = g z.1}
  change (ρ.prod μ) s = 0
  have hs : MeasurableSet s := by
    exact measurableSet_eq_fun measurable_snd (hg.comp measurable_fst)
  rw [Measure.prod_apply hs]
  have hfiber : ∀ x : σ, μ (Prod.mk x ⁻¹' s) = 0 := by
    intro x
    have hpreimage : Prod.mk x ⁻¹' s = {g x} := by
      ext y
      simp [s]
    rw [hpreimage, measure_singleton]
  simp_rw [hfiber]
  exact lintegral_zero

/-- If the first marginal assigns zero mass to a singleton, then so does the
preimage of that singleton under the first projection of a product with a
probability measure. -/
theorem measure_prod_fst_preimage_singleton_eq_zero
    {γ : Type*} [MeasurableSpace γ] [MeasurableSingletonClass α]
    (μ : Measure α) (ν : Measure γ) [IsProbabilityMeasure ν]
    (a : α) (hzero : μ {a} = 0) :
    (μ.prod ν) (Prod.fst ⁻¹' {a}) = 0 := by
  calc
    (μ.prod ν) (Prod.fst ⁻¹' {a}) = (Measure.map Prod.fst (μ.prod ν)) {a} := by
      rw [Measure.map_apply measurable_fst (measurableSet_singleton a)]
    _ = μ {a} := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    _ = 0 := hzero

/-- The next IID coordinate cannot equal an atomless measurable threshold of
an independent external state and the previously inspected IID prefix. -/
theorem measure_state_coordinate_eq_prefixFunction_zero
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    [NoAtoms μ] [MeasurableEq α] (n : ℕ)
    (g : σ × (Finset.range (n + 1) → α) → α) (hg : Measurable g) :
    (ρ.prod (measure μ)) {z | coordinate (n + 1) z.2 =
      g (stateStreamPrefix (σ := σ) (α := α) n z)} = 0 := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  let M : Measure (σ × (ℕ → α)) := ρ.prod (measure μ)
  let X : σ × (ℕ → α) → σ × (Finset.range (n + 1) → α) :=
    stateStreamPrefix (σ := σ) (α := α) n
  let Y : σ × (ℕ → α) → α := fun z => coordinate (n + 1) z.2
  let F : σ × (ℕ → α) →
      (σ × (Finset.range (n + 1) → α)) × α := fun z => (X z, Y z)
  let s : Set ((σ × (Finset.range (n + 1) → α)) × α) :=
    {p | p.2 = g p.1}
  have hX : Measurable X := by
    simpa [X] using measurable_stateStreamPrefix (σ := σ) (α := α) n
  have hY : Measurable Y := by
    simpa [Y] using (measurable_coordinate (α := α) (n + 1)).comp measurable_snd
  have hF : Measurable F := hX.prodMk hY
  have hindep : IndepFun X Y M := by
    have hblock := indepFun_state_streamPrefix_block ρ μ n 1
    have hcomp := hblock.comp measurable_id (measurable_pi_apply 0)
    simpa [M, X, Y, Function.comp_def, block, coordinate] using hcomp
  have hYlaw : M.map Y = μ := by
    dsimp [M, Y]
    calc
      (ρ.prod (measure μ)).map (fun z : σ × (ℕ → α) =>
          coordinate (n + 1) z.2) =
          ((ρ.prod (measure μ)).map Prod.snd).map (coordinate (n + 1)) := by
            symm
            rw [Measure.map_map (measurable_coordinate (α := α) (n + 1))
              measurable_snd]
            rfl
      _ = (measure μ).map (coordinate (n + 1)) := by
            rw [Measure.map_snd_prod, measure_univ, one_smul]
      _ = μ := (coordinate_hasLaw μ (n + 1)).map_eq
  have hpair : M.map F = (M.map X).prod μ := by
    calc
      M.map F = (M.map X).prod (M.map Y) := by
        exact (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp hindep
      _ = (M.map X).prod μ := by rw [hYlaw]
  have hs : MeasurableSet s := by
    exact measurableSet_eq_fun measurable_snd (hg.comp measurable_fst)
  change M {z | Y z = g (X z)} = 0
  change M (F ⁻¹' s) = 0
  rw [← Measure.map_apply hF hs, hpair]
  exact measure_prod_graph_eq_zero (M.map X) μ g hg

/-- Applying a measurable coordinate map with null fibers to the next IID
coordinate cannot equal a measurable threshold of an independent external
state and the previously inspected IID prefix. -/
theorem measure_state_coordinate_apply_eq_prefixFunction_zero
    {β : Type*} [MeasurableSpace β]
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    [MeasurableEq β] (h : α → β) (hh : Measurable h)
    (hzero : ∀ b : β, μ (h ⁻¹' {b}) = 0)
    (n : ℕ) (g : σ × (Finset.range (n + 1) → α) → β) (hg : Measurable g) :
    (ρ.prod (measure μ)) {z | h (coordinate (n + 1) z.2) =
      g (stateStreamPrefix (σ := σ) (α := α) n z)} = 0 := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  let M : Measure (σ × (ℕ → α)) := ρ.prod (measure μ)
  let X : σ × (ℕ → α) → σ × (Finset.range (n + 1) → α) :=
    stateStreamPrefix (σ := σ) (α := α) n
  let Y : σ × (ℕ → α) → α := fun z => coordinate (n + 1) z.2
  let F : σ × (ℕ → α) →
      (σ × (Finset.range (n + 1) → α)) × α := fun z => (X z, Y z)
  let s : Set ((σ × (Finset.range (n + 1) → α)) × α) :=
    {p | h p.2 = g p.1}
  have hX : Measurable X := by
    simpa [X] using measurable_stateStreamPrefix (σ := σ) (α := α) n
  have hY : Measurable Y := by
    simpa [Y] using (measurable_coordinate (α := α) (n + 1)).comp measurable_snd
  have hF : Measurable F := hX.prodMk hY
  have hindep : IndepFun X Y M := by
    have hblock := indepFun_state_streamPrefix_block ρ μ n 1
    have hcomp := hblock.comp measurable_id (measurable_pi_apply 0)
    simpa [M, X, Y, Function.comp_def, block, coordinate] using hcomp
  have hYlaw : M.map Y = μ := by
    dsimp [M, Y]
    calc
      (ρ.prod (measure μ)).map (fun z : σ × (ℕ → α) =>
          coordinate (n + 1) z.2) =
          ((ρ.prod (measure μ)).map Prod.snd).map (coordinate (n + 1)) := by
            symm
            rw [Measure.map_map (measurable_coordinate (α := α) (n + 1))
              measurable_snd]
            rfl
      _ = (measure μ).map (coordinate (n + 1)) := by
            rw [Measure.map_snd_prod, measure_univ, one_smul]
      _ = μ := (coordinate_hasLaw μ (n + 1)).map_eq
  have hpair : M.map F = (M.map X).prod μ := by
    calc
      M.map F = (M.map X).prod (M.map Y) := by
        exact (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp hindep
      _ = (M.map X).prod μ := by rw [hYlaw]
  have hs : MeasurableSet s := by
    exact measurableSet_eq_fun (hh.comp measurable_snd) (hg.comp measurable_fst)
  change M {z | h (Y z) = g (X z)} = 0
  change M (F ⁻¹' s) = 0
  rw [← Measure.map_apply hF hs, hpair]
  exact measure_prod_apply_eq_graph_zero (M.map X) μ h hh hzero g hg

/-- An arbitrary independent external state is independent of each one IID
coordinate. -/
theorem indepFun_state_coordinate
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ] (n : ℕ) :
    IndepFun (fun z : σ × (ℕ → α) => z.1)
      (fun z : σ × (ℕ → α) => coordinate n z.2)
      (ρ.prod (measure μ)) := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  apply (indepFun_iff_map_prod_eq_prod_map_map
    measurable_fst.aemeasurable
    ((measurable_coordinate (α := α) n).comp measurable_snd).aemeasurable).mpr
  calc
    Measure.map (fun z : σ × (ℕ → α) =>
        (z.1, coordinate n z.2)) (ρ.prod (measure μ)) =
        ρ.prod ((measure μ).map (coordinate n)) := by
          simpa [Prod.map] using
            (Measure.map_prod_map ρ (measure μ) measurable_id
              (measurable_coordinate (α := α) n)).symm
    _ = ρ.prod μ := by rw [(coordinate_hasLaw μ n).map_eq]
    _ = ((ρ.prod (measure μ)).map (fun z : σ × (ℕ → α) => z.1)).prod
        ((ρ.prod (measure μ)).map
          (fun z : σ × (ℕ → α) => coordinate n z.2)) := by
          have hfst : (ρ.prod (measure μ)).map
              (fun z : σ × (ℕ → α) => z.1) = ρ := by
            simpa using (Measure.map_fst_prod ρ (measure μ))
          have hsnd : (ρ.prod (measure μ)).map
              (fun z : σ × (ℕ → α) => coordinate n z.2) = μ := by
            calc
              (ρ.prod (measure μ)).map
                  (fun z : σ × (ℕ → α) => coordinate n z.2) =
                  ((ρ.prod (measure μ)).map Prod.snd).map (coordinate n) := by
                    symm
                    rw [Measure.map_map (measurable_coordinate (α := α) n)
                      measurable_snd]
                    rfl
              _ = ((measure μ).map (coordinate n)) := by
                    rw [Measure.map_snd_prod, measure_univ, one_smul]
              _ = μ := (coordinate_hasLaw μ n).map_eq
          rw [hfst, hsnd]

/-- Applying a measurable coordinate map with null fibers to the initial IID
coordinate cannot equal a measurable threshold of the independent external
state.  This is the zero-prefix companion to the general fresh-coordinate
graph lemma. -/
theorem measure_state_coordinate_zero_apply_eq_externalFunction_zero
    {β : Type*} [MeasurableSpace β]
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    [MeasurableEq β] (h : α → β) (hh : Measurable h)
    (hzero : ∀ b : β, μ (h ⁻¹' {b}) = 0)
    (g : σ → β) (hg : Measurable g) :
    (ρ.prod (measure μ)) {z | h (coordinate 0 z.2) = g z.1} = 0 := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  let M : Measure (σ × (ℕ → α)) := ρ.prod (measure μ)
  let X : σ × (ℕ → α) → σ := fun z => z.1
  let Y : σ × (ℕ → α) → α := fun z => coordinate 0 z.2
  let F : σ × (ℕ → α) → σ × α := fun z => (X z, Y z)
  let s : Set (σ × α) := {p | h p.2 = g p.1}
  have hX : Measurable X := by
    simpa [X] using (measurable_fst : Measurable (fun z : σ × (ℕ → α) => z.1))
  have hY : Measurable Y := by
    simpa [Y] using (measurable_coordinate (α := α) 0).comp measurable_snd
  have hF : Measurable F := hX.prodMk hY
  have hindep : IndepFun X Y M := by
    simpa [M, X, Y] using indepFun_state_coordinate ρ μ 0
  have hYlaw : M.map Y = μ := by
    dsimp [M, Y]
    calc
      (ρ.prod (measure μ)).map (fun z : σ × (ℕ → α) =>
          coordinate 0 z.2) =
          ((ρ.prod (measure μ)).map Prod.snd).map (coordinate 0) := by
            symm
            rw [Measure.map_map (measurable_coordinate (α := α) 0)
              measurable_snd]
            rfl
      _ = (measure μ).map (coordinate 0) := by
            rw [Measure.map_snd_prod, measure_univ, one_smul]
      _ = μ := (coordinate_hasLaw μ 0).map_eq
  have hpair : M.map F = (M.map X).prod μ := by
    calc
      M.map F = (M.map X).prod (M.map Y) := by
        exact (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp hindep
      _ = (M.map X).prod μ := by rw [hYlaw]
  have hs : MeasurableSet s := by
    exact measurableSet_eq_fun (hh.comp measurable_snd) (hg.comp measurable_fst)
  change M {z | h (Y z) = g (X z)} = 0
  change M (F ⁻¹' s) = 0
  rw [← Measure.map_apply hF hs, hpair]
  exact measure_prod_apply_eq_graph_zero (M.map X) μ h hh hzero g hg

/-- A total discrete stopping index may inspect arbitrary independent external
data as well as the IID coordinates through its reported index. -/
structure StatePrefixStoppingIndex where
  toFun : σ × (ℕ → α) → ℕ
  event_prefix_measurable : ∀ n,
    MeasurableSet[MeasurableSpace.comap
      (stateStreamPrefix (σ := σ) (α := α) n) inferInstance]
      {z | toFun z = n}

namespace StatePrefixStoppingIndex

instance : CoeFun (StatePrefixStoppingIndex (σ := σ) (α := α))
    (fun _ => σ × (ℕ → α) → ℕ) := ⟨StatePrefixStoppingIndex.toFun⟩

/-- A measurable index read from the external state alone is a valid
state-plus-prefix stopping index for any independent IID stream. -/
def externalStateStoppingIndex (index : σ → ℕ) (hindex : Measurable index) :
    StatePrefixStoppingIndex (σ := σ) (α := α) where
  toFun := fun z => index z.1
  event_prefix_measurable := by
    intro n
    refine ⟨{x | index x.1 = n},
      measurableSet_eq_fun (hindex.comp measurable_fst) measurable_const, ?_⟩
    ext z
    rfl

/-- The external-state stopping-index adapter preserves the given index
function. -/
theorem externalStateStoppingIndex_apply
    (index : σ → ℕ) (hindex : Measurable index) (z : σ × (ℕ → α)) :
    externalStateStoppingIndex (α := α) index hindex z = index z.1 := rfl

/-- The `n`th level event of an external-state prefix stopping index. -/
def event (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) (n : ℕ) :
    Set (σ × (ℕ → α)) :=
  {z | τ z = n}

/-- Every stopping-level event is Borel measurable. -/
theorem measurableSet_event (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (n : ℕ) : MeasurableSet (τ.event n) := by
  change MeasurableSet {z | τ z = n}
  rcases τ.event_prefix_measurable n with ⟨u, hu, hpre⟩
  rw [← hpre]
  exact (measurable_stateStreamPrefix (σ := σ) (α := α) n) hu

/-- A total state-plus-prefix stopping index is Borel measurable as a
natural-valued function. -/
theorem measurable (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) :
    Measurable τ := by
  intro s _
  have hpreimage : τ ⁻¹' s = ⋃ n ∈ s, τ.event n := by
    ext z
    simp [event]
  rw [hpreimage]
  exact MeasurableSet.biUnion (Set.to_countable s) fun n _ =>
    measurableSet_event τ n

/-- Distinct stopping-level events of an external-state prefix rule are
disjoint. -/
theorem event_pairwiseDisjoint
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) :
    Pairwise (Function.onFun Disjoint τ.event) := by
  intro n m hnm
  refine Set.disjoint_left.2 ?_
  intro z hzn hzm
  change τ z = n at hzn
  change τ z = m at hzm
  exact hnm (hzn.symm.trans hzm)

/-- A total external-state prefix stop takes one of its countably many levels
on every sample. -/
theorem iUnion_event_eq_univ
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) :
    ⋃ n, τ.event n = Set.univ := by
  ext z
  simp [event]

/-- Forget the last coordinates of a visible state-plus-prefix observation. -/
def statePrefixRestriction (m n : ℕ) (hmn : m ≤ n) :
    σ × (Finset.range (n + 1) → α) → σ × (Finset.range (m + 1) → α) :=
  fun x => (x.1, PrefixStoppingIndex.prefixRestriction (α := α) m n hmn x.2)

/-- Forgetting coordinates from a visible state-plus-prefix observation is
Borel measurable. -/
theorem measurable_statePrefixRestriction (m n : ℕ) (hmn : m ≤ n) :
    Measurable (statePrefixRestriction (σ := σ) (α := α) m n hmn) := by
  exact measurable_fst.prodMk
    ((PrefixStoppingIndex.measurable_prefixRestriction (α := α) m n hmn).comp
      measurable_snd)

/-- Restricting a longer visible observation recovers the earlier one. -/
theorem statePrefixRestriction_stateStreamPrefix (m n : ℕ) (hmn : m ≤ n) :
    statePrefixRestriction (σ := σ) (α := α) m n hmn ∘
      stateStreamPrefix (σ := σ) (α := α) n =
      stateStreamPrefix (σ := σ) (α := α) m := by
  funext z
  simp only [statePrefixRestriction, stateStreamPrefix, Function.comp_apply]
  congr 1

/-- An event observable from an earlier state-plus-prefix observation remains
observable from every longer observation. -/
theorem event_prefix_measurable_mono
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    {m n : ℕ} (hmn : m ≤ n) :
    MeasurableSet[MeasurableSpace.comap
      (stateStreamPrefix (σ := σ) (α := α) n) inferInstance]
      (τ.event m) := by
  rcases τ.event_prefix_measurable m with ⟨u, hu, hpre⟩
  refine ⟨(statePrefixRestriction (σ := σ) (α := α) m n hmn) ⁻¹' u,
    hu.preimage (measurable_statePrefixRestriction (σ := σ) (α := α) m n hmn), ?_⟩
  change stateStreamPrefix (σ := σ) (α := α) n ⁻¹'
      (statePrefixRestriction (σ := σ) (α := α) m n hmn ⁻¹' u) =
      {z | τ z = m}
  rw [← hpre]
  ext z
  simp only [Set.mem_preimage]
  change (statePrefixRestriction (σ := σ) (α := α) m n hmn ∘
      stateStreamPrefix (σ := σ) (α := α) n) z ∈ u ↔
    stateStreamPrefix (σ := σ) (α := α) m z ∈ u
  rw [statePrefixRestriction_stateStreamPrefix]

/-- A stopped-history event is one whose restriction to every stopping level
is observable from the external state and the IID prefix inspected at that
level. -/
def StoppedPrefixEvent
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (A : Set (σ × (ℕ → α))) : Prop :=
  ∀ n, MeasurableSet[MeasurableSpace.comap
    (stateStreamPrefix (σ := σ) (α := α) n) inferInstance]
    (A ∩ τ.event n)

/-- A stopped-prefix event is Borel on the full product carrier. -/
theorem StoppedPrefixEvent.measurableSet
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (A : Set (σ × (ℕ → α)))
    (hA : StoppedPrefixEvent τ A) :
    MeasurableSet A := by
  have hsplit : A = ⋃ n, A ∩ τ.event n := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, event, Set.mem_setOf_eq]
    constructor
    · intro hz
      exact ⟨τ z, hz, rfl⟩
    · rintro ⟨n, hz, _⟩
      exact hz
  rw [hsplit]
  apply MeasurableSet.iUnion
  intro n
  rcases hA n with ⟨u, hu, hpre⟩
  rw [← hpre]
  exact (measurable_stateStreamPrefix (σ := σ) (α := α) n) hu

/-- The event that a state-plus-prefix stopping index has not stopped before
`n`. -/
def continuationEvent (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (n : ℕ) : Set (σ × (ℕ → α)) := {z | n ≤ τ z}

/-- Not stopping before `n + 1` is observable from the external state and
the IID prefix through `n`. -/
theorem continuationEvent_succ_prefix_measurable
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) (n : ℕ) :
    MeasurableSet[MeasurableSpace.comap
      (stateStreamPrefix (σ := σ) (α := α) n) inferInstance]
      (τ.continuationEvent (n + 1)) := by
  let bad : Set (σ × (ℕ → α)) := ⋃ m ∈ Finset.range (n + 1), τ.event m
  have hbad : MeasurableSet[MeasurableSpace.comap
      (stateStreamPrefix (σ := σ) (α := α) n) inferInstance] bad := by
    exact Finset.measurableSet_biUnion (Finset.range (n + 1))
      (fun m hm => τ.event_prefix_measurable_mono
        (Nat.le_of_lt_succ (Finset.mem_range.mp hm)))
  have heq : τ.continuationEvent (n + 1) = badᶜ := by
    ext z
    simp only [continuationEvent, Set.mem_setOf_eq, Set.mem_compl_iff, bad,
      Set.mem_iUnion, event]
    constructor
    · intro h hbadMem
      rcases hbadMem with ⟨m, hm, hτ⟩
      have hnm : n + 1 ≤ m := by simpa [hτ] using h
      exact (Nat.not_lt_of_ge hnm) (Finset.mem_range.mp hm)
    · intro h
      by_contra hnot
      have hlt : τ z < n + 1 := Nat.lt_of_not_ge hnot
      exact h ⟨τ z, Finset.mem_range.mpr hlt, rfl⟩
  rw [heq]
  exact hbad.compl

/-- Every state-plus-prefix continuation event is Borel measurable. -/
theorem measurableSet_continuationEvent
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) (n : ℕ) :
    MeasurableSet (τ.continuationEvent n) := by
  cases n with
  | zero =>
      change MeasurableSet {z | 0 ≤ τ z}
      simp
  | succ n =>
      rcases τ.continuationEvent_succ_prefix_measurable n with ⟨u, hu, hpre⟩
      rw [← hpre]
      exact (measurable_stateStreamPrefix (σ := σ) (α := α) n) hu

/-- A coordinate reward is integrable on the independent product carrier
whenever its single-coordinate reward is integrable. -/
theorem integrable_state_coordinate
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (reward : α → ℝ) (hreward : Integrable reward μ) (n : ℕ) :
    Integrable (fun z : σ × (ℕ → α) => reward (coordinate n z.2))
      (ρ.prod (measure μ)) := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  have hprojection : MeasurePreserving
      (fun z : σ × (ℕ → α) => coordinate n z.2)
      (ρ.prod (measure μ)) μ := by
    exact (coordinate_measurePreserving μ n).comp
      (measurePreserving_snd : MeasurePreserving Prod.snd
        (ρ.prod (measure μ)) (measure μ))
  exact hprojection.integrable_comp_of_integrable hreward

/-- The next IID coordinate factors from the state-plus-prefix event that a
stopping rule has not already stopped. -/
theorem integral_continuationEvent_succ_indicator_mul_coordinate
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) (n : ℕ)
    (reward : α → ℝ) (hreward : Measurable reward) :
    ∫ z, (τ.continuationEvent (n + 1)).indicator (fun _ => (1 : ℝ)) z *
        reward (coordinate (n + 1) z.2) ∂(ρ.prod (measure μ)) =
      (ρ.prod (measure μ)).real (τ.continuationEvent (n + 1)) *
        ∫ x, reward x ∂μ := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  rcases τ.continuationEvent_succ_prefix_measurable n with ⟨u, hu, hpre⟩
  let F : (σ × (Finset.range (n + 1) → α)) → ℝ :=
    u.indicator (fun _ => (1 : ℝ))
  let G : (Fin 1 → α) → ℝ := fun block => reward (block 0)
  have hF : Measurable F := measurable_const.indicator hu
  have hG : Measurable G := hreward.comp (measurable_pi_apply 0)
  have hindep := indepFun_state_streamPrefix_block ρ μ n 1
  have hfactor := hindep.integral_comp_mul_comp
    (measurable_stateStreamPrefix (σ := σ) (α := α) n).aemeasurable
    ((measurable_block (α := α) (n + 1) 1).comp measurable_snd).aemeasurable
    hF.aestronglyMeasurable hG.aestronglyMeasurable
  have hleft :
      (fun z : σ × (ℕ → α) => F (stateStreamPrefix (σ := σ) (α := α) n z) *
          G (block (α := α) (n + 1) 1 z.2)) =
        fun z => (τ.continuationEvent (n + 1)).indicator (fun _ => (1 : ℝ)) z *
          reward (coordinate (n + 1) z.2) := by
    funext z
    have hmem : stateStreamPrefix (σ := σ) (α := α) n z ∈ u ↔
        z ∈ τ.continuationEvent (n + 1) := by
      change z ∈ stateStreamPrefix (σ := σ) (α := α) n ⁻¹' u ↔
        z ∈ τ.continuationEvent (n + 1)
      rw [hpre]
    by_cases h : stateStreamPrefix (σ := σ) (α := α) n z ∈ u
    · have hcont : z ∈ τ.continuationEvent (n + 1) := hmem.mp h
      simp [F, G, block, coordinate, Set.indicator, h, hcont]
    · have h' : z ∉ τ.continuationEvent (n + 1) := by
        intro hcont
        exact h (hmem.mpr hcont)
      simp [F, G, block, coordinate, Set.indicator, h, h']
  have hprefix :
      (∫ z : σ × (ℕ → α), F (stateStreamPrefix (σ := σ) (α := α) n z)
        ∂(ρ.prod (measure μ))) =
        (ρ.prod (measure μ)).real (τ.continuationEvent (n + 1)) := by
    calc
      (∫ z : σ × (ℕ → α), F (stateStreamPrefix (σ := σ) (α := α) n z)
          ∂(ρ.prod (measure μ))) =
          ∫ z : σ × (ℕ → α),
            (τ.continuationEvent (n + 1)).indicator (fun _ => (1 : ℝ)) z
              ∂(ρ.prod (measure μ)) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
            change u.indicator (fun _ => (1 : ℝ))
              (stateStreamPrefix (σ := σ) (α := α) n z) = _
            have hmem : stateStreamPrefix (σ := σ) (α := α) n z ∈ u ↔
                z ∈ τ.continuationEvent (n + 1) := by
              change z ∈ stateStreamPrefix (σ := σ) (α := α) n ⁻¹' u ↔
                z ∈ τ.continuationEvent (n + 1)
              rw [hpre]
            by_cases h : stateStreamPrefix (σ := σ) (α := α) n z ∈ u
            · have hcont : z ∈ τ.continuationEvent (n + 1) := hmem.mp h
              simp [Set.indicator, h, hcont]
            · have h' : z ∉ τ.continuationEvent (n + 1) := by
                intro hcont
                exact h (hmem.mpr hcont)
              simp [Set.indicator, h, h']
      _ = (ρ.prod (measure μ)).real (τ.continuationEvent (n + 1)) := by
        rw [MeasureTheory.integral_indicator
          (τ.measurableSet_continuationEvent (n + 1)),
          MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
  have hrewardIntegral :
      (∫ z : σ × (ℕ → α), G (block (α := α) (n + 1) 1 z.2)
        ∂(ρ.prod (measure μ))) = ∫ x, reward x ∂μ := by
    exact ((coordinate_measurePreserving μ (n + 1)).comp
      (measurePreserving_snd : MeasurePreserving Prod.snd
        (ρ.prod (measure μ)) (measure μ))).hasLaw.integral_comp
          hreward.aestronglyMeasurable
  calc
    ∫ z, (τ.continuationEvent (n + 1)).indicator (fun _ => (1 : ℝ)) z *
        reward (coordinate (n + 1) z.2) ∂(ρ.prod (measure μ)) =
        ∫ z : σ × (ℕ → α), F (stateStreamPrefix (σ := σ) (α := α) n z) *
          G (block (α := α) (n + 1) 1 z.2) ∂(ρ.prod (measure μ)) := by
          rw [hleft]
    _ = (∫ z : σ × (ℕ → α), F (stateStreamPrefix (σ := σ) (α := α) n z)
          ∂(ρ.prod (measure μ))) *
          ∫ z : σ × (ℕ → α), G (block (α := α) (n + 1) 1 z.2)
            ∂(ρ.prod (measure μ)) := by
          simpa only [Function.comp_apply] using hfactor
    _ = (ρ.prod (measure μ)).real (τ.continuationEvent (n + 1)) *
          ∫ x, reward x ∂μ := by rw [hprefix, hrewardIntegral]

/-- The reward accrued at inspected coordinates up to a deterministic cap. -/
def truncatedStoppedReward (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (reward : α → ℝ) (cap : ℕ) : σ × (ℕ → α) → ℝ :=
  fun z => ∑ n ∈ Finset.range (cap + 1),
    if n ≤ τ z then reward (coordinate n z.2) else 0

/-- The finite stopped-reward identity remains valid when a stopping rule can
inspect arbitrary independent external data. -/
theorem integral_truncatedStoppedReward
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (reward : α → ℝ) (hreward : Measurable reward)
    (hintegrable : Integrable reward μ) (cap : ℕ) :
    ∫ z, truncatedStoppedReward τ reward cap z ∂(ρ.prod (measure μ)) =
      (∑ n ∈ Finset.range (cap + 1),
        (ρ.prod (measure μ)).real (τ.continuationEvent n)) * ∫ x, reward x ∂μ := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  unfold truncatedStoppedReward
  rw [MeasureTheory.integral_finset_sum]
  · have htermIntegral (n : ℕ) :
        ∫ z, (if n ≤ τ z then reward (coordinate n z.2) else 0)
          ∂(ρ.prod (measure μ)) =
          (ρ.prod (measure μ)).real (τ.continuationEvent n) * ∫ x, reward x ∂μ := by
      cases n with
      | zero =>
          have hcoord :
              ∫ z : σ × (ℕ → α), reward (coordinate 0 z.2)
                ∂(ρ.prod (measure μ)) = ∫ x, reward x ∂μ := by
            exact ((coordinate_measurePreserving μ 0).comp
              (measurePreserving_snd : MeasurePreserving Prod.snd
                (ρ.prod (measure μ)) (measure μ))).hasLaw.integral_comp
                  hreward.aestronglyMeasurable
          calc
            ∫ z, (if 0 ≤ τ z then reward (coordinate 0 z.2) else 0)
                ∂(ρ.prod (measure μ)) =
                ∫ z : σ × (ℕ → α), reward (coordinate 0 z.2)
                  ∂(ρ.prod (measure μ)) := by simp
            _ = ∫ x, reward x ∂μ := hcoord
            _ = (ρ.prod (measure μ)).real (τ.continuationEvent 0) *
                ∫ x, reward x ∂μ := by
                  change (∫ x, reward x ∂μ) =
                    (ρ.prod (measure μ)).real {z | 0 ≤ τ z} * ∫ x, reward x ∂μ
                  rw [show {z : σ × (ℕ → α) | 0 ≤ τ z} = Set.univ by
                    ext z; simp,
                    MeasureTheory.measureReal_def, measure_univ]
                  simp
      | succ n =>
          have hterm := integral_continuationEvent_succ_indicator_mul_coordinate
            ρ μ τ n reward hreward
          simpa [continuationEvent, Set.indicator] using hterm
    simp_rw [htermIntegral]
    rw [Finset.sum_mul]
  · intro n _
    have hcoord := integrable_state_coordinate ρ μ reward hintegrable n
    have hindicator := hcoord.indicator (τ.measurableSet_continuationEvent n)
    have heq :
        (fun z => if n ≤ τ z then reward (coordinate n z.2) else 0) =
        (τ.continuationEvent n).indicator
          (fun z => reward (coordinate n z.2)) := by
      funext z
      simp [continuationEvent, Set.indicator]
    rw [heq]
    exact hindicator

/-- The first `q` IID coordinates uninspected after an external-state prefix
stop.  The external state may determine the stop but is not part of this
restarted suffix. -/
def postBlock (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) (q : ℕ) :
    σ × (ℕ → α) → Fin q → α :=
  fun z i => coordinate (τ z + 1 + i) z.2

private theorem measurable_postBlock_coordinate
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) (q : ℕ) (i : Fin q) :
    Measurable (fun z => postBlock τ q z i) := by
  let h : ∀ z : σ × (ℕ → α), ∃ n, τ z = n := fun z => ⟨τ z, rfl⟩
  have hmeas : Measurable (fun z => coordinate (Nat.find (h z) + 1 + i) z.2) :=
    Measurable.find
      (fun n => (measurable_coordinate (α := α) (n + 1 + i)).comp measurable_snd)
      (fun n => τ.measurableSet_event n)
      h
  convert hmeas using 1
  funext z
  have hfind : Nat.find (h z) = τ z := (Nat.find_spec (h z)).symm
  simp [postBlock, hfind]

/-- The finite IID block after an external-state prefix stop is Borel. -/
theorem measurable_postBlock (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (q : ℕ) : Measurable (postBlock τ q) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_postBlock_coordinate τ q i

/-- At a fixed stopping level, the uninspected IID block factors from the
external state and inspected prefix. -/
theorem event_inter_block_measure_eq_mul
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) (n q : ℕ)
    (s : Fin q → Set α) (hs : ∀ i, MeasurableSet (s i)) :
    (ρ.prod (measure μ)) (τ.event n ∩
      {z | ∀ i, block (α := α) (n + 1) q z.2 i ∈ s i}) =
      (ρ.prod (measure μ)) (τ.event n) * ∏ i : Fin q, μ (s i) := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  have hindep := indepFun_state_streamPrefix_block ρ μ n q
  have hrect : {z : σ × (ℕ → α) | ∀ i,
      block (α := α) (n + 1) q z.2 i ∈ s i} =
      (fun z : σ × (ℕ → α) => block (α := α) (n + 1) q z.2) ⁻¹'
        Set.univ.pi s := by
    ext z
    simp
  have hright : MeasurableSet[MeasurableSpace.comap
      (fun z : σ × (ℕ → α) => block (α := α) (n + 1) q z.2) inferInstance]
      {z | ∀ i, block (α := α) (n + 1) q z.2 i ∈ s i} := by
    rw [hrect]
    exact MeasurableSpace.measurableSet_comap.2
      ⟨Set.univ.pi s, MeasurableSet.univ_pi hs, rfl⟩
  have hfactor := hindep.meas_inter (τ.event_prefix_measurable n) hright
  calc
    (ρ.prod (measure μ)) (τ.event n ∩
        {z | ∀ i, block (α := α) (n + 1) q z.2 i ∈ s i}) =
        (ρ.prod (measure μ)) (τ.event n) *
          (ρ.prod (measure μ))
            {z | ∀ i, block (α := α) (n + 1) q z.2 i ∈ s i} := hfactor
    _ = (ρ.prod (measure μ)) (τ.event n) * ∏ i : Fin q, μ (s i) := by
      congr 1
      let hblock : (ℕ → α) → Fin q → α := block (n + 1) q
      have hblock_meas : MeasurableSet {ω | ∀ i, hblock ω i ∈ s i} := by
        have hblock_rect : {ω | ∀ i, hblock ω i ∈ s i} =
            hblock ⁻¹' Set.univ.pi s := by
          ext ω
          simp
        rw [hblock_rect]
        exact (measurable_block (α := α) (n + 1) q)
          (MeasurableSet.univ_pi hs)
      have hpreimage :
          {z : σ × (ℕ → α) | ∀ i, block (α := α) (n + 1) q z.2 i ∈ s i} =
            Prod.snd ⁻¹' {ω | ∀ i, hblock ω i ∈ s i} := by
          ext z
          rfl
      calc
        (ρ.prod (measure μ))
            {z | ∀ i, block (α := α) (n + 1) q z.2 i ∈ s i} =
            (ρ.prod (measure μ)).map Prod.snd
              {ω | ∀ i, hblock ω i ∈ s i} := by
              rw [hpreimage]
              exact (Measure.map_apply measurable_snd hblock_meas).symm
        _ = (measure μ) {ω | ∀ i, hblock ω i ∈ s i} := by
              rw [Measure.map_snd_prod, measure_univ, one_smul]
        _ = ∏ i : Fin q, μ (s i) := by
              exact measure_block_mem_eq μ (n + 1) q s hs

/-- At a fixed stopping level, every explicitly stopped-prefix-measurable
history event factors from the uninspected deterministic IID block. -/
theorem stoppedPrefixEvent_inter_block_measure_eq_mul
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (A : Set (σ × (ℕ → α))) (hA : StoppedPrefixEvent τ A)
    (n q : ℕ) (s : Fin q → Set α) (hs : ∀ i, MeasurableSet (s i)) :
    (ρ.prod (measure μ)) (A ∩ τ.event n ∩
      {z | ∀ i, block (α := α) (n + 1) q z.2 i ∈ s i}) =
      (ρ.prod (measure μ)) (A ∩ τ.event n) * ∏ i : Fin q, μ (s i) := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  have hindep := indepFun_state_streamPrefix_block ρ μ n q
  have hrect : {z : σ × (ℕ → α) | ∀ i,
      block (α := α) (n + 1) q z.2 i ∈ s i} =
      (fun z : σ × (ℕ → α) => block (α := α) (n + 1) q z.2) ⁻¹'
        Set.univ.pi s := by
    ext z
    simp
  have hright : MeasurableSet[MeasurableSpace.comap
      (fun z : σ × (ℕ → α) => block (α := α) (n + 1) q z.2) inferInstance]
      {z | ∀ i, block (α := α) (n + 1) q z.2 i ∈ s i} := by
    rw [hrect]
    exact MeasurableSpace.measurableSet_comap.2
      ⟨Set.univ.pi s, MeasurableSet.univ_pi hs, rfl⟩
  have hfactor := hindep.meas_inter (hA n) hright
  calc
    (ρ.prod (measure μ)) (A ∩ τ.event n ∩
        {z | ∀ i, block (α := α) (n + 1) q z.2 i ∈ s i}) =
        (ρ.prod (measure μ)) (A ∩ τ.event n) *
          (ρ.prod (measure μ))
            {z | ∀ i, block (α := α) (n + 1) q z.2 i ∈ s i} := hfactor
    _ = (ρ.prod (measure μ)) (A ∩ τ.event n) * ∏ i : Fin q, μ (s i) := by
      congr 1
      let hblock : (ℕ → α) → Fin q → α := block (n + 1) q
      have hblock_meas : MeasurableSet {ω | ∀ i, hblock ω i ∈ s i} := by
        have hblock_rect : {ω | ∀ i, hblock ω i ∈ s i} =
            hblock ⁻¹' Set.univ.pi s := by
          ext ω
          simp
        rw [hblock_rect]
        exact (measurable_block (α := α) (n + 1) q)
          (MeasurableSet.univ_pi hs)
      have hpreimage :
          {z : σ × (ℕ → α) | ∀ i, block (α := α) (n + 1) q z.2 i ∈ s i} =
            Prod.snd ⁻¹' {ω | ∀ i, hblock ω i ∈ s i} := by
          ext z
          rfl
      calc
        (ρ.prod (measure μ))
            {z | ∀ i, block (α := α) (n + 1) q z.2 i ∈ s i} =
            (ρ.prod (measure μ)).map Prod.snd
              {ω | ∀ i, hblock ω i ∈ s i} := by
              rw [hpreimage]
              exact (Measure.map_apply measurable_snd hblock_meas).symm
        _ = (measure μ) {ω | ∀ i, hblock ω i ∈ s i} := by
              rw [Measure.map_snd_prod, measure_univ, one_smul]
        _ = ∏ i : Fin q, μ (s i) := by
              exact measure_block_mem_eq μ (n + 1) q s hs

/-- Every finite IID block after an external-state prefix stop factors from
any event observable from the stopped history.  This is an event-level
restart identity; it does not assert a separate state-valued strong-Markov
property. -/
theorem measure_stoppedPrefixEvent_inter_postBlock_mem_eq_mul
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (A : Set (σ × (ℕ → α))) (hA : StoppedPrefixEvent τ A)
    (q : ℕ) (s : Fin q → Set α) (hs : ∀ i, MeasurableSet (s i)) :
    (ρ.prod (measure μ)) (A ∩ {z | ∀ i, postBlock τ q z i ∈ s i}) =
      (ρ.prod (measure μ)) A * ∏ i : Fin q, μ (s i) := by
  let ν : Measure (σ × (ℕ → α)) := ρ.prod (measure μ)
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  let pieces : ℕ → Set (σ × (ℕ → α)) := fun n =>
    A ∩ τ.event n ∩ {z | ∀ i, block (α := α) (n + 1) q z.2 i ∈ s i}
  have hblock_meas : ∀ n, MeasurableSet
      {z : σ × (ℕ → α) | ∀ i,
        block (α := α) (n + 1) q z.2 i ∈ s i} := by
    intro n
    have hrect : {z : σ × (ℕ → α) | ∀ i,
        block (α := α) (n + 1) q z.2 i ∈ s i} =
        (fun z : σ × (ℕ → α) => block (α := α) (n + 1) q z.2) ⁻¹'
          Set.univ.pi s := by
      ext z
      simp
    rw [hrect]
    exact ((measurable_block (α := α) (n + 1) q).comp measurable_snd)
      (MeasurableSet.univ_pi hs)
  have hhistory_meas : ∀ n, MeasurableSet (A ∩ τ.event n) := by
    intro n
    rcases hA n with ⟨u, hu, hpre⟩
    rw [← hpre]
    exact (measurable_stateStreamPrefix (σ := σ) (α := α) n) hu
  have hpieces_meas : ∀ n, MeasurableSet (pieces n) := by
    intro n
    exact (hhistory_meas n).inter (hblock_meas n)
  have hpieces_disjoint : Pairwise (Function.onFun Disjoint pieces) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    intro z hzn hzm
    have hEn : z ∈ τ.event n := hzn.1.2
    have hEm : z ∈ τ.event m := hzm.1.2
    change τ z = n at hEn
    change τ z = m at hEm
    exact hnm (hEn.symm.trans hEm)
  have hpieces_union :
      ⋃ n, pieces n = A ∩ {z | ∀ i, postBlock τ q z i ∈ s i} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, pieces, event, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, ⟨hA, hτ⟩, hblock⟩
      refine ⟨hA, ?_⟩
      simpa [postBlock, block, hτ] using hblock
    · rintro ⟨hA, hpost⟩
      refine ⟨τ z, ⟨hA, rfl⟩, ?_⟩
      simpa [postBlock, block] using hpost
  have hmeasure_pieces :
      ν (A ∩ {z | ∀ i, postBlock τ q z i ∈ s i}) = ∑' n, ν (pieces n) := by
    rw [← hpieces_union]
    exact measure_iUnion hpieces_disjoint hpieces_meas
  have hAevent_disjoint : Pairwise (Function.onFun Disjoint fun n => A ∩ τ.event n) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    intro z hzn hzm
    have hEn : z ∈ τ.event n := hzn.2
    have hEm : z ∈ τ.event m := hzm.2
    change τ z = n at hEn
    change τ z = m at hEm
    exact hnm (hEn.symm.trans hEm)
  have hA_union : ⋃ n, A ∩ τ.event n = A := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, event, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hA, _⟩
      exact hA
    · intro hA
      exact ⟨τ z, hA, rfl⟩
  have hsum_A : ∑' n, ν (A ∩ τ.event n) = ν A := by
    calc
      ∑' n, ν (A ∩ τ.event n) = ν (⋃ n, A ∩ τ.event n) :=
        (measure_iUnion hAevent_disjoint hhistory_meas).symm
      _ = ν A := congrArg ν hA_union
  have hpieces_factor :
      (∑' n, ν (pieces n)) =
        ∑' n, ν (A ∩ τ.event n) * ∏ i : Fin q, μ (s i) := by
    apply tsum_congr
    intro n
    exact τ.stoppedPrefixEvent_inter_block_measure_eq_mul ρ μ A hA n q s hs
  change ν (A ∩ {z | ∀ i, postBlock τ q z i ∈ s i}) = _
  calc
    ν (A ∩ {z | ∀ i, postBlock τ q z i ∈ s i}) = ∑' n, ν (pieces n) :=
      hmeasure_pieces
    _ = ∑' n, ν (A ∩ τ.event n) * ∏ i : Fin q, μ (s i) := hpieces_factor
    _ = (∑' n, ν (A ∩ τ.event n)) * ∏ i : Fin q, μ (s i) := by
      exact ENNReal.tsum_mul_right
    _ = ν A * ∏ i : Fin q, μ (s i) := by rw [hsum_A]

/-- Every measurable rectangular event in a finite IID block after an
external-state prefix stop has the original product probability. -/
theorem measure_postBlock_mem_eq
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) (q : ℕ)
    (s : Fin q → Set α) (hs : ∀ i, MeasurableSet (s i)) :
    (ρ.prod (measure μ)) {z | ∀ i, postBlock τ q z i ∈ s i} =
      ∏ i : Fin q, μ (s i) := by
  let ν : Measure (σ × (ℕ → α)) := ρ.prod (measure μ)
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  let pieces : ℕ → Set (σ × (ℕ → α)) := fun n =>
    τ.event n ∩ {z | ∀ i, block (α := α) (n + 1) q z.2 i ∈ s i}
  have hblock_meas : ∀ n, MeasurableSet
      {z : σ × (ℕ → α) | ∀ i,
        block (α := α) (n + 1) q z.2 i ∈ s i} := by
    intro n
    have hrect : {z : σ × (ℕ → α) | ∀ i,
        block (α := α) (n + 1) q z.2 i ∈ s i} =
        (fun z : σ × (ℕ → α) => block (α := α) (n + 1) q z.2) ⁻¹'
          Set.univ.pi s := by
      ext z
      simp
    rw [hrect]
    exact ((measurable_block (α := α) (n + 1) q).comp measurable_snd)
      (MeasurableSet.univ_pi hs)
  have hpieces_meas : ∀ n, MeasurableSet (pieces n) := by
    intro n
    exact (τ.measurableSet_event n).inter (hblock_meas n)
  have hpieces_disjoint : Pairwise (Function.onFun Disjoint pieces) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    intro z hzn hzm
    have hEn : z ∈ τ.event n := hzn.1
    have hEm : z ∈ τ.event m := hzm.1
    change τ z = n at hEn
    change τ z = m at hEm
    exact hnm (hEn.symm.trans hEm)
  have hpieces_union :
      ⋃ n, pieces n = {z | ∀ i, postBlock τ q z i ∈ s i} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, pieces, event, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hτ, hblock⟩
      simpa [postBlock, block, hτ] using hblock
    · intro hmem
      refine ⟨τ z, rfl, ?_⟩
      simpa [postBlock, block] using hmem
  have hmeasure_pieces :
      ν {z | ∀ i, postBlock τ q z i ∈ s i} = ∑' n, ν (pieces n) := by
    rw [← hpieces_union]
    exact measure_iUnion hpieces_disjoint hpieces_meas
  have hsum_event : ∑' n, ν (τ.event n) = 1 := by
    calc
      ∑' n, ν (τ.event n) = ν (⋃ n, τ.event n) :=
        (measure_iUnion τ.event_pairwiseDisjoint τ.measurableSet_event).symm
      _ = ν Set.univ := congrArg ν τ.iUnion_event_eq_univ
      _ = 1 := measure_univ
  have hpieces_factor :
      (∑' n, ν (pieces n)) =
        ∑' n, ν (τ.event n) * ∏ i : Fin q, μ (s i) := by
    apply tsum_congr
    intro n
    exact τ.event_inter_block_measure_eq_mul ρ μ n q s hs
  change ν {z | ∀ i, postBlock τ q z i ∈ s i} = _
  calc
    ν {z | ∀ i, postBlock τ q z i ∈ s i} = ∑' n, ν (pieces n) :=
      hmeasure_pieces
    _ = ∑' n, ν (τ.event n) * ∏ i : Fin q, μ (s i) := hpieces_factor
    _ = (∑' n, ν (τ.event n)) * ∏ i : Fin q, μ (s i) := by
      exact ENNReal.tsum_mul_right
    _ = ∏ i : Fin q, μ (s i) := by simp [hsum_event]

/-- The finite IID block after an external-state prefix stop has its original
product law. -/
theorem postBlock_hasLaw
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) (q : ℕ) :
    HasLaw (postBlock τ q) (Measure.pi (fun _ : Fin q => μ))
      (ρ.prod (measure μ)) := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  refine ⟨(measurable_postBlock τ q).aemeasurable, ?_⟩
  apply (Measure.pi_eq (μ := fun _ : Fin q => μ)
    (μ' := (ρ.prod (measure μ)).map (postBlock τ q)) ?_).symm
  intro s hs
  have hrect : postBlock τ q ⁻¹' Set.univ.pi s =
      {z | ∀ i, postBlock τ q z i ∈ s i} := by
    ext z
    simp
  calc
    (ρ.prod (measure μ)).map (postBlock τ q) (Set.univ.pi s) =
        (ρ.prod (measure μ)) (postBlock τ q ⁻¹' Set.univ.pi s) :=
      Measure.map_apply (measurable_postBlock τ q) (MeasurableSet.univ_pi hs)
    _ = (ρ.prod (measure μ)) {z | ∀ i, postBlock τ q z i ∈ s i} :=
      congrArg _ hrect
    _ = ∏ i : Fin q, μ (s i) :=
      measure_postBlock_mem_eq ρ μ τ q s hs

/-- The complete IID suffix uninspected after an external-state prefix stop. -/
def postTail (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) :
    σ × (ℕ → α) → ℕ → α :=
  fun z n => coordinate (τ z + 1 + n) z.2

/-- The complete uninspected IID suffix is Borel. -/
theorem measurable_postTail
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) :
    Measurable (postTail τ) := by
  apply measurable_pi_lambda
  intro n
  simpa [postTail, postBlock] using
    (measurable_postBlock_coordinate τ (n + 1)
      (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)))

/-- The finite restrictions of the whole uninspected suffix are precisely the
corresponding finite post-stop blocks. -/
theorem postTail_restrict_eq_postBlock
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (q : ℕ) (z : σ × (ℕ → α)) :
    (fun i : Fin q => postTail τ z i) = postBlock τ q z := by
  funext i
  rfl

/-- An IID suffix remains distributed according to its original product law
after a total stop that may inspect an independent external state and the
reported IID prefix. -/
theorem postTail_hasLaw
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) :
    HasLaw (postTail τ) (measure μ) (ρ.prod (measure μ)) := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  refine ⟨(measurable_postTail τ).aemeasurable, ?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  by_cases hs : s.Nonempty
  · let q : ℕ := s.max' hs + 1
    let u : Fin q → Set α := fun i =>
      if (i : ℕ) ∈ s then t i else Set.univ
    have hq : ∀ i, i ∈ s → i < q := by
      intro i hi
      dsimp [q]
      exact Nat.lt_succ_of_le (Finset.le_max' s i hi)
    have hu : ∀ i, MeasurableSet (u i) := by
      intro i
      by_cases hi : (i : ℕ) ∈ s
      · simpa [u, hi] using ht i
      · simp [u, hi]
    have hevent :
        postTail τ ⁻¹' Set.pi s t =
          postBlock τ q ⁻¹' Set.univ.pi u := by
      ext z
      simp only [Set.mem_preimage, Set.mem_pi]
      constructor
      · intro h i
        by_cases hi : (i : ℕ) ∈ s
        · have hmem := h i hi
          simpa [postTail, postBlock, u, hi] using hmem
        · simp [u, hi]
      · intro h i hi
        let ii : Fin q := ⟨i, hq i hi⟩
        have hmem : postBlock τ q z ii ∈ u ii := h ii (by simp)
        change coordinate (τ z + 1 + i) z.2 ∈ t i
        change coordinate (τ z + 1 + i) z.2 ∈
          (if (ii : ℕ) ∈ s then t ii else Set.univ) at hmem
        have hii : (ii : ℕ) ∈ s := by simpa [ii] using hi
        have hmem' : coordinate (τ z + 1 + i) z.2 ∈ t (ii : ℕ) := by
          simpa [hii] using hmem
        simpa [ii] using hmem'
    calc
      (ρ.prod (measure μ)).map (postTail τ) (Set.pi s t) =
          (ρ.prod (measure μ)) (postTail τ ⁻¹' Set.pi s t) :=
        Measure.map_apply (measurable_postTail τ)
          (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))
      _ = (ρ.prod (measure μ)) (postBlock τ q ⁻¹' Set.univ.pi u) := by
        rw [hevent]
      _ = (ρ.prod (measure μ)).map (postBlock τ q) (Set.univ.pi u) :=
        (Measure.map_apply (measurable_postBlock τ q)
          (MeasurableSet.univ_pi hu)).symm
      _ = Measure.pi (fun _ : Fin q => μ) (Set.univ.pi u) := by
        rw [(postBlock_hasLaw ρ μ τ q).map_eq]
      _ = ∏ i : Fin q, μ (u i) := by
        rw [Measure.pi_pi]
      _ = ∏ i ∈ s, μ (t i) := by
        calc
          ∏ i : Fin q, μ (u i) =
              ∏ i : Fin q, (if (i : ℕ) ∈ s then μ (t i) else 1) := by
            apply Finset.prod_congr rfl
            intro i _
            dsimp [u]
            split_ifs <;> simp
          _ = ∏ i ∈ Finset.range q, if i ∈ s then μ (t i) else 1 :=
            (Finset.prod_range (fun i : ℕ =>
              if i ∈ s then μ (t i) else 1)).symm
        rw [Finset.prod_ite_mem]
        congr 2
        apply Finset.inter_eq_right.mpr
        intro i hi
        exact Finset.mem_range.mpr (hq i hi)
  · have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hs_empty]
    simpa only [Finset.coe_empty, Set.empty_pi, Finset.prod_empty,
      Set.preimage_univ, measure_univ] using
      (Measure.map_apply (μ := ρ.prod (measure μ)) (measurable_postTail τ)
        (MeasurableSet.univ))

/-- A stopped-history event factors from every finite cylinder of the complete
post-stop IID tail. -/
theorem measure_stoppedPrefixEvent_inter_postTail_preimage_pi_eq_mul
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (A : Set (σ × (ℕ → α))) (hA : StoppedPrefixEvent τ A)
    (s : Finset ℕ) (t : ℕ → Set α) (ht : ∀ i, MeasurableSet (t i)) :
    (ρ.prod (measure μ)) (A ∩ postTail τ ⁻¹' Set.pi s t) =
      (ρ.prod (measure μ)) A * (measure μ) (Set.pi s t) := by
  classical
  let ν : Measure (σ × (ℕ → α)) := ρ.prod (measure μ)
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  by_cases hs : s.Nonempty
  · let q : ℕ := s.max' hs + 1
    let u : Fin q → Set α := fun i =>
      if (i : ℕ) ∈ s then t i else Set.univ
    have hq : ∀ i, i ∈ s → i < q := by
      intro i hi
      dsimp [q]
      exact Nat.lt_succ_of_le (Finset.le_max' s i hi)
    have hu : ∀ i, MeasurableSet (u i) := by
      intro i
      by_cases hi : (i : ℕ) ∈ s
      · simpa [u, hi] using ht i
      · simp [u, hi]
    have hevent :
        A ∩ postTail τ ⁻¹' Set.pi s t =
          A ∩ postBlock τ q ⁻¹' Set.univ.pi u := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi]
      constructor
      · rintro ⟨hmem, htail⟩
        refine ⟨hmem, ?_⟩
        intro i _
        by_cases hi : (i : ℕ) ∈ s
        · have hmem' := htail i hi
          simpa [postTail, postBlock, u, hi] using hmem'
        · simp [u, hi]
      · rintro ⟨hmem, hblock⟩
        refine ⟨hmem, ?_⟩
        intro i hi
        let ii : Fin q := ⟨i, hq i hi⟩
        have hmem' : postBlock τ q z ii ∈ u ii := hblock ii (by simp)
        change coordinate (τ z + 1 + i) z.2 ∈ t i
        change coordinate (τ z + 1 + i) z.2 ∈
          (if (ii : ℕ) ∈ s then t ii else Set.univ) at hmem'
        have hii : (ii : ℕ) ∈ s := by simpa [ii] using hi
        have hmem'' : coordinate (τ z + 1 + i) z.2 ∈ t (ii : ℕ) := by
          simpa [hii] using hmem'
        simpa [ii] using hmem''
    change ν (A ∩ postTail τ ⁻¹' Set.pi s t) = ν A * (measure μ) (Set.pi s t)
    rw [hevent]
    calc
      ν (A ∩ postBlock τ q ⁻¹' Set.univ.pi u) =
          ν (A ∩ {z | ∀ i, postBlock τ q z i ∈ u i}) := by
        congr 2
        ext z
        simp
      _ = ν A * ∏ i : Fin q, μ (u i) := by
        exact τ.measure_stoppedPrefixEvent_inter_postBlock_mem_eq_mul
          ρ μ A hA q u hu
      ν A * ∏ i : Fin q, μ (u i) =
          ν A * ∏ i ∈ s, μ (t i) := by
        congr 1
        calc
          ∏ i : Fin q, μ (u i) =
              ∏ i : Fin q, (if (i : ℕ) ∈ s then μ (t i) else 1) := by
            apply Finset.prod_congr rfl
            intro i _
            dsimp [u]
            split_ifs <;> simp
          _ = ∏ i ∈ Finset.range q, if i ∈ s then μ (t i) else 1 :=
            (Finset.prod_range (fun i : ℕ =>
              if i ∈ s then μ (t i) else 1)).symm
        rw [Finset.prod_ite_mem]
        congr 2
        apply Finset.inter_eq_right.mpr
        intro i hi
        exact Finset.mem_range.mpr (hq i hi)
      _ = ν A * (measure μ) (Set.pi s t) := by
        change ν A * ∏ i ∈ s, μ (t i) =
          ν A * Measure.infinitePi (fun _ : ℕ => μ) (Set.pi s t)
        rw [Measure.infinitePi_pi (fun _ : ℕ => μ) (fun i hi => ht i)]
  · have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hs_empty]
    simp

/-- Restricting the source law to a stopped-history event leaves the entire
post-stop IID tail distributed as the original product law, scaled by the
event probability. -/
theorem map_postTail_restrict_eq_smul
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (A : Set (σ × (ℕ → α))) (hA : StoppedPrefixEvent τ A) :
    Measure.map (postTail τ) ((ρ.prod (measure μ)).restrict A) =
      (ρ.prod (measure μ)) A • (measure μ) := by
  classical
  let ν : Measure (σ × (ℕ → α)) := ρ.prod (measure μ)
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  let C : Set (Set (ℕ → α)) :=
    squareCylinders
      (fun _ : ℕ => {s : Set α | MeasurableSet s})
  refine ext_of_generate_finite C ?_ ?_ ?_ ?_
  · exact generateFrom_squareCylinders.symm
  · exact isPiSystem_squareCylinders
      (fun _ => MeasurableSpace.isPiSystem_measurableSet) (by simp)
  · rintro S ⟨s, t, ht, rfl⟩
    have ht' : ∀ i, MeasurableSet (t i) := by
      intro i
      exact ht i (Set.mem_univ i)
    have hpi : MeasurableSet ((s : Set ℕ).pi t) :=
      MeasurableSet.pi (Finset.countable_toSet s) (fun i _ => ht' i)
    change Measure.map (postTail τ) (ν.restrict A) ((s : Set ℕ).pi t) =
      (ν A • (measure μ)) ((s : Set ℕ).pi t)
    rw [Measure.map_apply (measurable_postTail τ) hpi,
      Measure.restrict_apply' (hA.measurableSet),
      Measure.smul_apply]
    simpa [Set.inter_comm] using
      (τ.measure_stoppedPrefixEvent_inter_postTail_preimage_pi_eq_mul
        ρ μ A hA s t ht')
  · rw [Measure.map_apply (measurable_postTail τ) MeasurableSet.univ,
      Measure.restrict_apply' (hA.measurableSet), Measure.smul_apply]
    simp

/-- A full stopped-prefix event factors from every measurable event of the
complete post-stop IID tail. -/
theorem measure_stoppedPrefixEvent_inter_postTail_preimage_eq_mul
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (A : Set (σ × (ℕ → α))) (hA : StoppedPrefixEvent τ A)
    (T : Set (ℕ → α)) (hT : MeasurableSet T) :
    (ρ.prod (measure μ)) (A ∩ postTail τ ⁻¹' T) =
      (ρ.prod (measure μ)) A * (measure μ) T := by
  let ν : Measure (σ × (ℕ → α)) := ρ.prod (measure μ)
  have hmap := τ.map_postTail_restrict_eq_smul ρ μ A hA
  have hpreimage : MeasurableSet (postTail τ ⁻¹' T) :=
    hT.preimage (measurable_postTail τ)
  change ν (A ∩ postTail τ ⁻¹' T) = ν A * (measure μ) T
  calc
    ν (A ∩ postTail τ ⁻¹' T) =
        Measure.map (postTail τ) (ν.restrict A) T := by
      rw [Measure.map_apply (measurable_postTail τ) hT, Measure.restrict_apply hpreimage]
      exact congrArg ν (Set.inter_comm _ _)
    _ = (ν A • (measure μ)) T := by rw [hmap]
    _ = ν A * (measure μ) T := by
      rw [Measure.smul_apply]
      rfl

/-- Any observable whose measurable preimages are determined by a stopped IID
prefix is independent of the complete IID tail after that prefix. -/
theorem indepFun_of_stoppedPrefixEvent_postTail
    {β : Type*} [MeasurableSpace β]
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (f : σ × (ℕ → α) → β)
    (hf : ∀ S : Set β, MeasurableSet S → StoppedPrefixEvent τ (f ⁻¹' S)) :
    IndepFun f (postTail τ) (ρ.prod (measure μ)) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro S T hS hT
  calc
    (ρ.prod (measure μ)) (f ⁻¹' S ∩ postTail τ ⁻¹' T) =
        (ρ.prod (measure μ)) (f ⁻¹' S) * (measure μ) T :=
      τ.measure_stoppedPrefixEvent_inter_postTail_preimage_eq_mul
        ρ μ (f ⁻¹' S) (hf S hS) T hT
    _ = (ρ.prod (measure μ)) (f ⁻¹' S) *
        (ρ.prod (measure μ)) (postTail τ ⁻¹' T) := by
      congr 1
      rw [← Measure.map_apply (measurable_postTail τ) hT,
        (postTail_hasLaw ρ μ τ).map_eq]

end StatePrefixStoppingIndex

/-- The deterministic IID suffix beginning at `n`. -/
def deterministicIndexTail (n : ℕ) : (ℕ → α) → ℕ → α :=
  fun marks i => coordinate (n + i) marks

/-- A deterministic IID suffix is Borel measurable. -/
theorem measurable_deterministicIndexTail (n : ℕ) :
    Measurable (deterministicIndexTail (α := α) n) := by
  apply measurable_pi_lambda
  intro i
  simpa [deterministicIndexTail] using
    measurable_coordinate (α := α) (n + i)

/-- A deterministic IID suffix has the original whole-product law. -/
theorem deterministicIndexTail_hasLaw
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) :
    HasLaw (deterministicIndexTail (α := α) n) (measure μ) (measure μ) := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  apply hasLaw_iidPath_of_hasLaw_positive_prefixes μ
    (deterministicIndexTail (α := α) n)
    (measurable_deterministicIndexTail (α := α) n)
  intro q hq
  simpa [deterministicIndexTail, block] using (block_hasLaw μ n q)

/-- A finite IID block beginning at an index selected by an independent
external state. -/
def externalIndexBlock (index : σ → ℕ) (q : ℕ) :
    σ × (ℕ → α) → Fin q → α :=
  fun z i => coordinate (index z.1 + i) z.2

/-- The externally indexed finite IID block is Borel measurable. -/
theorem measurable_externalIndexBlock
    (index : σ → ℕ) (hindex : Measurable index) (q : ℕ) :
    Measurable (externalIndexBlock (α := α) index q) := by
  apply measurable_pi_lambda
  intro i
  refine measurable_apply_of_measurable_countable_index
    (fun z : σ × (ℕ → α) => fun n => coordinate (α := α) n z.2) ?_
    (fun z => index z.1 + (i : ℕ)) ?_
  · intro n
    exact (measurable_coordinate (α := α) n).comp measurable_snd
  · exact (hindex.comp measurable_fst).add_const i

/-- An IID finite block beginning at a measurable external index has its
ordinary iid product law. -/
theorem externalIndexBlock_hasLaw
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (index : σ → ℕ) (hindex : Measurable index) (q : ℕ) :
    HasLaw (externalIndexBlock (α := α) index q)
      (Measure.pi (fun _ : Fin q => μ)) (ρ.prod (measure μ)) := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  let blockAt : σ × (ℕ → α) → Fin q → α :=
    externalIndexBlock (α := α) index q
  have hblockAt : Measurable blockAt := by
    simpa [blockAt] using measurable_externalIndexBlock (α := α) index hindex q
  refine ⟨hblockAt.aemeasurable, ?_⟩
  apply (Measure.pi_eq (μ := fun _ : Fin q => μ)
    (μ' := (ρ.prod (measure μ)).map blockAt) ?_).symm
  intro s hs
  let rectangle : Set (Fin q → α) := Set.univ.pi s
  have hrectangle : MeasurableSet rectangle := MeasurableSet.univ_pi hs
  have hpreimage : MeasurableSet (blockAt ⁻¹' rectangle) :=
    hrectangle.preimage hblockAt
  rw [Measure.map_apply hblockAt hrectangle, Measure.prod_apply hpreimage]
  have hfiber (state : σ) :
      measure μ (Prod.mk state ⁻¹' (blockAt ⁻¹' rectangle)) =
        ∏ i : Fin q, μ (s i) := by
    have hset :
        Prod.mk state ⁻¹' (blockAt ⁻¹' rectangle) =
          block (α := α) (index state) q ⁻¹' rectangle := by
      ext marks
      simp [blockAt, externalIndexBlock, block, coordinate, rectangle]
    rw [hset, ← Measure.map_apply (measurable_block (α := α) (index state) q)
      hrectangle, (block_hasLaw μ (index state) q).map_eq, Measure.pi_pi]
  calc
    ∫⁻ state, measure μ (Prod.mk state ⁻¹' (blockAt ⁻¹' rectangle)) ∂ρ =
        ∫⁻ _ : σ, ∏ i : Fin q, μ (s i) ∂ρ := by
          apply lintegral_congr_ae
          filter_upwards [] with state
          exact hfiber state
    _ = (∏ i : Fin q, μ (s i)) * ρ Set.univ := lintegral_const _
    _ = ∏ i : Fin q, μ (s i) := by simp

/-- The complete IID tail beginning at an index selected by an independent
external state. -/
def externalIndexTail (index : σ → ℕ) :
    σ × (ℕ → α) → ℕ → α :=
  fun z i => coordinate (index z.1 + i) z.2

/-- The externally indexed IID tail is Borel measurable. -/
theorem measurable_externalIndexTail
    (index : σ → ℕ) (hindex : Measurable index) :
    Measurable (externalIndexTail (α := α) index) := by
  apply measurable_pi_lambda
  intro i
  refine measurable_apply_of_measurable_countable_index
    (fun z : σ × (ℕ → α) => fun n => coordinate (α := α) n z.2) ?_
    (fun z => index z.1 + i) ?_
  · intro n
    exact (measurable_coordinate (α := α) n).comp measurable_snd
  · exact (hindex.comp measurable_fst).add_const i

/-- An IID tail beginning at a measurable external index has the original
whole iid product law. -/
theorem externalIndexTail_hasLaw
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (index : σ → ℕ) (hindex : Measurable index) :
    HasLaw (externalIndexTail (α := α) index) (measure μ)
      (ρ.prod (measure μ)) := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  letI : IsProbabilityMeasure (ρ.prod (measure μ)) := by
    infer_instance
  apply hasLaw_iidPath_of_hasLaw_positive_prefixes μ
    (externalIndexTail (α := α) index)
    (measurable_externalIndexTail (α := α) index hindex)
  intro q hq
  simpa [externalIndexTail, externalIndexBlock] using
    (externalIndexBlock_hasLaw ρ μ index hindex q)

/-- An event is observable before an IID tail selected by an external index
when, on each index fiber, it is determined by the external state and exactly
the first `n` IID coordinates.  This is deliberately an event-level premise:
it avoids claiming a broader state-valued strong-Markov property. -/
def ExternalIndexPrefixEvent (index : σ → ℕ)
    (A : Set (σ × (ℕ → α))) : Prop :=
  ∀ n : ℕ, ∃ u : Set (σ × (Finset.range n → α)), MeasurableSet u ∧
    A ∩ {z | index z.1 = n} =
      stateInitialPrefix (σ := σ) (α := α) n ⁻¹' u ∩
        {z | index z.1 = n}

/-- A measurable observation whose value on every external-index fiber is a
measurable function of the external state and consumed IID prefix has
external-index prefix-measurable preimages. -/
theorem externalIndexPrefixEvent_preimage_of_initialPrefixFactor
    {β : Type*} [MeasurableSpace β]
    (index : σ → ℕ)
    (prefixValue : ∀ n : ℕ, σ × (Finset.range n → α) → β)
    (hprefixValue : ∀ n, Measurable (prefixValue n))
    (f : σ × (ℕ → α) → β)
    (hfactor : ∀ z, f z =
      prefixValue (index z.1)
        (stateInitialPrefix (σ := σ) (α := α) (index z.1) z))
    (S : Set β) (hS : MeasurableSet S) :
    ExternalIndexPrefixEvent index (f ⁻¹' S) := by
  intro n
  refine ⟨(prefixValue n) ⁻¹' S, hS.preimage (hprefixValue n), ?_⟩
  ext z
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz, hindex⟩
    refine ⟨?_, hindex⟩
    rw [← hindex]
    rwa [hfactor z] at hz
  · rintro ⟨hz, hindex⟩
    refine ⟨?_, hindex⟩
    rw [hfactor z, hindex]
    exact hz

/-- On a fixed external-index fiber, an explicitly prefix-observable event
factors from the following deterministic IID block. -/
theorem externalIndexPrefixEvent_inter_block_measure_eq_mul
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (index : σ → ℕ) (hindex : Measurable index)
    (A : Set (σ × (ℕ → α))) (hA : ExternalIndexPrefixEvent index A)
    (n q : ℕ) (s : Fin q → Set α) (hs : ∀ i, MeasurableSet (s i)) :
    (ρ.prod (measure μ)) (A ∩ {z | index z.1 = n} ∩
      {z | ∀ i, block (α := α) n q z.2 i ∈ s i}) =
      (ρ.prod (measure μ)) (A ∩ {z | index z.1 = n}) *
        ∏ i : Fin q, μ (s i) := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  have hindep := indepFun_stateInitialPrefix_block ρ μ n q
  have hrect : {z : σ × (ℕ → α) | ∀ i,
      block (α := α) n q z.2 i ∈ s i} =
      (fun z : σ × (ℕ → α) => block (α := α) n q z.2) ⁻¹'
        Set.univ.pi s := by
    ext z
    simp
  have hright : MeasurableSet[MeasurableSpace.comap
      (fun z : σ × (ℕ → α) => block (α := α) n q z.2) inferInstance]
      {z | ∀ i, block (α := α) n q z.2 i ∈ s i} := by
    rw [hrect]
    exact MeasurableSpace.measurableSet_comap.2
      ⟨Set.univ.pi s, MeasurableSet.univ_pi hs, rfl⟩
  have hleft : MeasurableSet[MeasurableSpace.comap
      (stateInitialPrefix (σ := σ) (α := α) n) inferInstance]
      (A ∩ {z | index z.1 = n}) := by
    rcases hA n with ⟨u, hu, hpre⟩
    have hfiber : MeasurableSet {state : σ | index state = n} :=
      measurableSet_eq_fun hindex measurable_const
    refine MeasurableSpace.measurableSet_comap.2
      ⟨u ∩ Prod.fst ⁻¹' {state | index state = n},
        hu.inter (measurable_fst hfiber), ?_⟩
    rw [hpre]
    ext z
    simp [stateInitialPrefix]
  have hfactor := hindep.meas_inter hleft hright
  calc
    (ρ.prod (measure μ)) (A ∩ {z | index z.1 = n} ∩
        {z | ∀ i, block (α := α) n q z.2 i ∈ s i}) =
        (ρ.prod (measure μ)) (A ∩ {z | index z.1 = n}) *
          (ρ.prod (measure μ))
            {z | ∀ i, block (α := α) n q z.2 i ∈ s i} := hfactor
    _ = (ρ.prod (measure μ)) (A ∩ {z | index z.1 = n}) *
        ∏ i : Fin q, μ (s i) := by
      congr 1
      let hblock : (ℕ → α) → Fin q → α := block n q
      have hblock_meas : MeasurableSet {ω | ∀ i, hblock ω i ∈ s i} := by
        have hblock_rect : {ω | ∀ i, hblock ω i ∈ s i} =
            hblock ⁻¹' Set.univ.pi s := by
          ext ω
          simp
        rw [hblock_rect]
        exact (measurable_block (α := α) n q) (MeasurableSet.univ_pi hs)
      have hpreimage :
          {z : σ × (ℕ → α) | ∀ i, block (α := α) n q z.2 i ∈ s i} =
            Prod.snd ⁻¹' {ω | ∀ i, hblock ω i ∈ s i} := by
          ext z
          rfl
      calc
        (ρ.prod (measure μ))
            {z : σ × (ℕ → α) | ∀ i, block (α := α) n q z.2 i ∈ s i} =
            (ρ.prod (measure μ)).map Prod.snd
              {ω | ∀ i, hblock ω i ∈ s i} := by
              rw [hpreimage]
              exact (Measure.map_apply measurable_snd hblock_meas).symm
        _ = (measure μ) {ω | ∀ i, hblock ω i ∈ s i} := by
              rw [Measure.map_snd_prod, measure_univ, one_smul]
        _ = ∏ i : Fin q, μ (s i) := by
              exact measure_block_mem_eq μ n q s hs

/-- An explicitly external-index-prefix-observable event factors from every
finite cylinder of the complete IID tail beginning at that index. -/
theorem measure_externalIndexPrefixEvent_inter_tail_preimage_pi_eq_mul
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (index : σ → ℕ) (hindex : Measurable index)
    (A : Set (σ × (ℕ → α))) (hA : ExternalIndexPrefixEvent index A)
    (s : Finset ℕ) (t : ℕ → Set α) (ht : ∀ i, MeasurableSet (t i)) :
    (ρ.prod (measure μ))
        (A ∩ externalIndexTail (α := α) index ⁻¹' Set.pi s t) =
      (ρ.prod (measure μ)) A * (measure μ) (Set.pi s t) := by
  classical
  let ν : Measure (σ × (ℕ → α)) := ρ.prod (measure μ)
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  by_cases hs : s.Nonempty
  · let q : ℕ := s.max' hs + 1
    let u : Fin q → Set α := fun i =>
      if (i : ℕ) ∈ s then t i else Set.univ
    have hq : ∀ i, i ∈ s → i < q := by
      intro i hi
      dsimp [q]
      exact Nat.lt_succ_of_le (Finset.le_max' s i hi)
    have hu : ∀ i, MeasurableSet (u i) := by
      intro i
      by_cases hi : (i : ℕ) ∈ s
      · simpa [u, hi] using ht i
      · simp [u, hi]
    let pieces : ℕ → Set (σ × (ℕ → α)) := fun n =>
      A ∩ {z | index z.1 = n} ∩
        {z | ∀ i, block (α := α) n q z.2 i ∈ u i}
    have hblock_meas : ∀ n, MeasurableSet
        {z : σ × (ℕ → α) | ∀ i,
          block (α := α) n q z.2 i ∈ u i} := by
      intro n
      have hrect : {z : σ × (ℕ → α) | ∀ i,
          block (α := α) n q z.2 i ∈ u i} =
          (fun z : σ × (ℕ → α) => block (α := α) n q z.2) ⁻¹'
            Set.univ.pi u := by
        ext z
        simp
      rw [hrect]
      exact ((measurable_block (α := α) n q).comp measurable_snd)
        (MeasurableSet.univ_pi hu)
    have hhistory_meas : ∀ n, MeasurableSet (A ∩ {z | index z.1 = n}) := by
      intro n
      rcases hA n with ⟨v, hv, hpre⟩
      rw [hpre]
      exact ((measurable_stateInitialPrefix (σ := σ) (α := α) n) hv).inter
        (measurableSet_eq_fun (hindex.comp measurable_fst) measurable_const)
    have hpieces_meas : ∀ n, MeasurableSet (pieces n) := by
      intro n
      exact (hhistory_meas n).inter (hblock_meas n)
    have hpieces_disjoint : Pairwise (Function.onFun Disjoint pieces) := by
      intro n m hnm
      refine Set.disjoint_left.2 ?_
      intro z hzn hzm
      have hEn : index z.1 = n := hzn.1.2
      have hEm : index z.1 = m := hzm.1.2
      exact hnm (hEn.symm.trans hEm)
    have hpieces_union :
        ⋃ n, pieces n =
          A ∩ externalIndexTail (α := α) index ⁻¹' Set.pi s t := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_inter_iff, pieces, Set.mem_preimage,
        Set.mem_pi, Set.mem_setOf_eq]
      constructor
      · rintro ⟨n, ⟨hA, hindexn⟩, hblock⟩
        refine ⟨hA, ?_⟩
        intro i hi
        let ii : Fin q := ⟨i, hq i hi⟩
        have hblock' : ∀ j : Fin q, block (α := α) n q z.2 j ∈ u j := by
          exact hblock
        have hmem : block (α := α) n q z.2 ii ∈ u ii := hblock' ii
        change coordinate (index z.1 + i) z.2 ∈ t i
        change coordinate (n + i) z.2 ∈
          (if (ii : ℕ) ∈ s then t ii else Set.univ) at hmem
        have hii : (ii : ℕ) ∈ s := by simpa [ii] using hi
        have hmem' : coordinate (n + i) z.2 ∈ t (ii : ℕ) := by
          simpa [hii] using hmem
        simpa [hindexn, ii] using hmem'
      · rintro ⟨hA, htail⟩
        refine ⟨index z.1, ⟨⟨hA, rfl⟩, ?_⟩⟩
        show ∀ i : Fin q, block (α := α) (index z.1) q z.2 i ∈ u i
        intro i
        by_cases hi : (i : ℕ) ∈ s
        · have hmem := htail (i : ℕ) hi
          change coordinate (index z.1 + (i : ℕ)) z.2 ∈ t (i : ℕ) at hmem
          simpa [u, hi] using hmem
        · simp [u, hi]
    have hmeasure_pieces :
        ν (A ∩ externalIndexTail (α := α) index ⁻¹' Set.pi s t) =
          ∑' n, ν (pieces n) := by
      rw [← hpieces_union]
      exact measure_iUnion hpieces_disjoint hpieces_meas
    have hAevent_disjoint : Pairwise (Function.onFun Disjoint
        fun n => A ∩ {z : σ × (ℕ → α) | index z.1 = n}) := by
      intro n m hnm
      refine Set.disjoint_left.2 ?_
      intro z hzn hzm
      exact hnm (hzn.2.symm.trans hzm.2)
    have hA_union : ⋃ n, A ∩ {z : σ × (ℕ → α) | index z.1 = n} = A := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨n, hA, _⟩
        exact hA
      · intro hA
        exact ⟨index z.1, hA, rfl⟩
    have hsum_A : ∑' n, ν (A ∩ {z : σ × (ℕ → α) | index z.1 = n}) = ν A := by
      calc
        ∑' n, ν (A ∩ {z : σ × (ℕ → α) | index z.1 = n}) =
            ν (⋃ n, A ∩ {z : σ × (ℕ → α) | index z.1 = n}) :=
          (measure_iUnion hAevent_disjoint hhistory_meas).symm
        _ = ν A := congrArg ν hA_union
    have hpieces_factor :
        (∑' n, ν (pieces n)) =
          ∑' n, ν (A ∩ {z | index z.1 = n}) * ∏ i : Fin q, μ (u i) := by
      apply tsum_congr
      intro n
      exact externalIndexPrefixEvent_inter_block_measure_eq_mul
        ρ μ index hindex A hA n q u hu
    change ν (A ∩ externalIndexTail (α := α) index ⁻¹' Set.pi s t) = _
    calc
      ν (A ∩ externalIndexTail (α := α) index ⁻¹' Set.pi s t) =
          ∑' n, ν (pieces n) := hmeasure_pieces
      _ = ∑' n, ν (A ∩ {z | index z.1 = n}) * ∏ i : Fin q, μ (u i) :=
        hpieces_factor
      _ = (∑' n, ν (A ∩ {z | index z.1 = n})) * ∏ i : Fin q, μ (u i) := by
        exact ENNReal.tsum_mul_right
      _ = ν A * ∏ i : Fin q, μ (u i) := by rw [hsum_A]
      _ = ν A * ∏ i ∈ s, μ (t i) := by
        congr 1
        calc
          ∏ i : Fin q, μ (u i) =
              ∏ i : Fin q, (if (i : ℕ) ∈ s then μ (t i) else 1) := by
            apply Finset.prod_congr rfl
            intro i _
            dsimp [u]
            split_ifs <;> simp
          _ = ∏ i ∈ Finset.range q, if i ∈ s then μ (t i) else 1 :=
            (Finset.prod_range (fun i : ℕ =>
              if i ∈ s then μ (t i) else 1)).symm
        rw [Finset.prod_ite_mem]
        congr 2
        apply Finset.inter_eq_right.mpr
        intro i hi
        exact Finset.mem_range.mpr (hq i hi)
      _ = ν A * (measure μ) (Set.pi s t) := by
        change ν A * ∏ i ∈ s, μ (t i) =
          ν A * Measure.infinitePi (fun _ : ℕ => μ) (Set.pi s t)
        rw [Measure.infinitePi_pi (fun _ : ℕ => μ) (fun i hi => ht i)]
  · have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hs_empty]
    simp

/-- Restricting the source law to an external-index-prefix event leaves the
complete selected IID tail distributed as the original product law, scaled by
the event probability. -/
theorem map_externalIndexTail_restrict_eq_smul
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (index : σ → ℕ) (hindex : Measurable index)
    (A : Set (σ × (ℕ → α))) (hA : ExternalIndexPrefixEvent index A) :
    Measure.map (externalIndexTail (α := α) index)
        ((ρ.prod (measure μ)).restrict A) =
      (ρ.prod (measure μ)) A • (measure μ) := by
  classical
  let ν : Measure (σ × (ℕ → α)) := ρ.prod (measure μ)
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  let C : Set (Set (ℕ → α)) :=
    squareCylinders
      (fun _ : ℕ => {s : Set α | MeasurableSet s})
  refine ext_of_generate_finite C ?_ ?_ ?_ ?_
  · exact generateFrom_squareCylinders.symm
  · exact isPiSystem_squareCylinders
      (fun _ => MeasurableSpace.isPiSystem_measurableSet) (by simp)
  · rintro S ⟨s, t, ht, rfl⟩
    have ht' : ∀ i, MeasurableSet (t i) := by
      intro i
      exact ht i (Set.mem_univ i)
    have hpi : MeasurableSet ((s : Set ℕ).pi t) :=
      MeasurableSet.pi (Finset.countable_toSet s) (fun i _ => ht' i)
    change Measure.map (externalIndexTail (α := α) index) (ν.restrict A)
        ((s : Set ℕ).pi t) = (ν A • (measure μ)) ((s : Set ℕ).pi t)
    rw [Measure.map_apply (measurable_externalIndexTail (α := α) index hindex) hpi,
      Measure.restrict_apply' ?_, Measure.smul_apply]
    · simpa [Set.inter_comm] using
        (measure_externalIndexPrefixEvent_inter_tail_preimage_pi_eq_mul
          ρ μ index hindex A hA s t ht')
    · have hmeas : MeasurableSet A := by
        let pieces : ℕ → Set (σ × (ℕ → α)) := fun n =>
          A ∩ {z | index z.1 = n}
        have hpieces_meas : ∀ n, MeasurableSet (pieces n) := by
          intro n
          rcases hA n with ⟨u, hu, hpre⟩
          change MeasurableSet (A ∩ {z : σ × (ℕ → α) | index z.1 = n})
          rw [hpre]
          exact ((measurable_stateInitialPrefix (σ := σ) (α := α) n) hu).inter
            (measurableSet_eq_fun (hindex.comp measurable_fst) measurable_const)
        have hpieces_disjoint : Pairwise (Function.onFun Disjoint pieces) := by
          intro n m hnm
          refine Set.disjoint_left.2 ?_
          intro z hzn hzm
          exact hnm (hzn.2.symm.trans hzm.2)
        have hpieces_union : ⋃ n, pieces n = A := by
          ext z
          simp only [Set.mem_iUnion, Set.mem_inter_iff, pieces, Set.mem_setOf_eq]
          constructor
          · rintro ⟨n, hA, _⟩
            exact hA
          · intro hA
            exact ⟨index z.1, hA, rfl⟩
        rw [← hpieces_union]
        exact MeasurableSet.iUnion hpieces_meas
      exact hmeas
  · rw [Measure.map_apply (measurable_externalIndexTail (α := α) index hindex)
      MeasurableSet.univ, Measure.restrict_apply' ?_, Measure.smul_apply]
    · simp
    · let pieces : ℕ → Set (σ × (ℕ → α)) := fun n =>
        A ∩ {z | index z.1 = n}
      have hpieces_meas : ∀ n, MeasurableSet (pieces n) := by
        intro n
        rcases hA n with ⟨u, hu, hpre⟩
        change MeasurableSet (A ∩ {z : σ × (ℕ → α) | index z.1 = n})
        rw [hpre]
        exact ((measurable_stateInitialPrefix (σ := σ) (α := α) n) hu).inter
          (measurableSet_eq_fun (hindex.comp measurable_fst) measurable_const)
      have hpieces_union : ⋃ n, pieces n = A := by
        ext z
        simp only [Set.mem_iUnion, Set.mem_inter_iff, pieces, Set.mem_setOf_eq]
        constructor
        · rintro ⟨n, hA, _⟩
          exact hA
        · intro hA
          exact ⟨index z.1, hA, rfl⟩
      rw [← hpieces_union]
      exact MeasurableSet.iUnion hpieces_meas

/-- An external-index prefix event is measurable in the product source space.
The event description may vary with the selected prefix length, but each
fiber is a measurable finite-prefix event. -/
theorem measurableSet_externalIndexPrefixEvent
    (index : σ → ℕ) (hindex : Measurable index)
    (A : Set (σ × (ℕ → α))) (hA : ExternalIndexPrefixEvent index A) :
    MeasurableSet A := by
  let pieces : ℕ → Set (σ × (ℕ → α)) := fun n =>
    A ∩ {z | index z.1 = n}
  have hpieces_meas : ∀ n, MeasurableSet (pieces n) := by
    intro n
    rcases hA n with ⟨u, hu, hpre⟩
    change MeasurableSet (A ∩ {z : σ × (ℕ → α) | index z.1 = n})
    rw [hpre]
    exact ((measurable_stateInitialPrefix (σ := σ) (α := α) n) hu).inter
      (measurableSet_eq_fun (hindex.comp measurable_fst) measurable_const)
  have hpieces_union : ⋃ n, pieces n = A := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, pieces, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hA, _⟩
      exact hA
    · intro hA
      exact ⟨index z.1, hA, rfl⟩
  rw [← hpieces_union]
  exact MeasurableSet.iUnion hpieces_meas

/-- No mark in a measurable set has appeared among the IID coordinates
strictly before an externally selected index. -/
def externalIndexNoHit (index : σ → ℕ) (s : Set α) : Set (σ × (ℕ → α)) :=
  {z | ∀ i, i < index z.1 → z.2 i ∉ s}

/-- The no-hit event before an externally selected index is an
external-index-prefix event. -/
theorem externalIndexNoHit_prefixEvent
    (index : σ → ℕ) (s : Set α) (hs : MeasurableSet s) :
    ExternalIndexPrefixEvent index (externalIndexNoHit (α := α) index s) := by
  intro n
  let u : Set (σ × (Finset.range n → α)) :=
    {z | ∀ i, z.2 i ∉ s}
  have hu : MeasurableSet u := by
    let t : Finset.range n → Set α := fun _ => sᶜ
    have hu_eq : u = Set.univ ×ˢ Set.univ.pi t := by
      ext z
      simp [u, t]
    rw [hu_eq]
    exact MeasurableSet.univ.prod
      (MeasurableSet.univ_pi (fun _ => by simpa [t] using hs.compl))
  refine ⟨u, hu, ?_⟩
  ext z
  constructor
  · rintro ⟨hnoHit, hindex⟩
    refine ⟨?_, hindex⟩
    change ∀ i : Finset.range n, z.2 i ∉ s
    intro i
    apply hnoHit i
    rw [hindex]
    exact Finset.mem_range.mp i.2
  · rintro ⟨hprefix, hindex⟩
    refine ⟨?_, hindex⟩
    change ∀ i, i < index z.1 → z.2 i ∉ s
    intro i hi
    have hi' : i < n := by
      rw [← hindex]
      exact hi
    let iFin : Finset.range n := ⟨i, Finset.mem_range.mpr hi'⟩
    change ∀ i : Finset.range n, z.2 i ∉ s at hprefix
    have hprefix' : z.2 iFin ∉ s := hprefix iFin
    simpa using hprefix'

/-- A source event observable before an externally selected IID suffix leaves
that suffix independent of the event-bearing external coordinate.  Unlike the
tail-marginal result, this retains the actual restricted external coordinate,
which is needed when a later stopped construction reuses its clock. -/
theorem map_externalIndexTail_withState_restrict_eq_prod
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (index : σ → ℕ) (hindex : Measurable index)
    (A : Set (σ × (ℕ → α))) (hA : ExternalIndexPrefixEvent index A) :
    Measure.map (fun z : σ × (ℕ → α) =>
      (z.1, externalIndexTail (α := α) index z))
      ((ρ.prod (measure μ)).restrict A) =
      (Measure.map Prod.fst ((ρ.prod (measure μ)).restrict A)).prod (measure μ) := by
  let M : Measure (ℕ → α) := measure μ
  let source : Measure (σ × (ℕ → α)) := ρ.prod M
  let tail : σ × (ℕ → α) -> Nat -> α := externalIndexTail (α := α) index
  let joint : σ × (ℕ → α) -> σ × (Nat -> α) := fun z => (z.1, tail z)
  letI : IsProbabilityMeasure M := by
    dsimp [M, measure]
    infer_instance
  have htail : Measurable tail := by
    simpa [tail] using measurable_externalIndexTail (α := α) index hindex
  have hjoint : Measurable joint := measurable_fst.prodMk htail
  have hAmeas : MeasurableSet A :=
    measurableSet_externalIndexPrefixEvent index hindex A hA
  symm
  apply Measure.prod_eq
  intro S T hS hT
  let AS : Set (σ × (ℕ → α)) := A ∩ Prod.fst ⁻¹' S
  have hAS : ExternalIndexPrefixEvent index AS := by
    intro n
    rcases hA n with ⟨u, hu, hAu⟩
    refine ⟨u ∩ Prod.fst ⁻¹' S, hu.inter (measurable_fst hS), ?_⟩
    change (A ∩ Prod.fst ⁻¹' S) ∩ {z | index z.1 = n} =
      stateInitialPrefix (σ := σ) (α := α) n ⁻¹' (u ∩ Prod.fst ⁻¹' S) ∩
        {z | index z.1 = n}
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨hzA, hzS⟩, hzindex⟩
      have hprefix := (Set.ext_iff.mp hAu z).mp ⟨hzA, hzindex⟩
      exact ⟨⟨hprefix.1, by simpa [stateInitialPrefix] using hzS⟩, hprefix.2⟩
    · rintro ⟨⟨hzprefix, hzS⟩, hzindex⟩
      have hprefix : z ∈ stateInitialPrefix (σ := σ) (α := α) n ⁻¹' u ∩
          {z | index z.1 = n} :=
        ⟨hzprefix, hzindex⟩
      have hzA := (Set.ext_iff.mp hAu z).mpr hprefix
      exact ⟨⟨hzA.1, by simpa [stateInitialPrefix] using hzS⟩, hzA.2⟩
  have hASmeas : MeasurableSet AS :=
    measurableSet_externalIndexPrefixEvent index hindex AS hAS
  have hjointPre : MeasurableSet (joint ⁻¹' (S ×ˢ T)) :=
    (hS.prod hT).preimage hjoint
  have htailPre : MeasurableSet (tail ⁻¹' T) := hT.preimage htail
  have hfactor := map_externalIndexTail_restrict_eq_smul
    ρ μ index hindex AS hAS
  change Measure.map joint (source.restrict A) (S ×ˢ T) =
    Measure.map Prod.fst (source.restrict A) S * M T
  calc
    Measure.map joint (source.restrict A) (S ×ˢ T) =
        source (A ∩ joint ⁻¹' (S ×ˢ T)) := by
          rw [Measure.map_apply hjoint (hS.prod hT),
            Measure.restrict_apply hjointPre]
          exact congrArg source (Set.inter_comm _ _)
    _ = source (AS ∩ tail ⁻¹' T) := by
          congr 1
          ext z
          simp only [AS, joint, tail, Set.mem_inter_iff, Set.mem_preimage,
            Set.mem_prod]
          tauto
    _ = source AS * M T := by
          calc
            source (AS ∩ tail ⁻¹' T) =
                Measure.map tail (source.restrict AS) T := by
                  rw [Measure.map_apply htail hT,
                    Measure.restrict_apply htailPre]
                  exact congrArg source (Set.inter_comm _ _)
            _ = (source AS • M) T := by
                  simpa [source, M] using congrArg (fun m : Measure (Nat -> α) => m T)
                    hfactor
            _ = source AS * M T := by
                  rw [Measure.smul_apply]
                  rfl
    _ = Measure.map Prod.fst (source.restrict A) S * M T := by
          congr 1
          rw [Measure.map_apply measurable_fst hS,
            Measure.restrict_apply (hS.preimage measurable_fst)]
          congr 1
          ext z
          simp [AS, Set.inter_comm]

/-- A selected IID tail remains fresh jointly with both the actual restricted
external state and an independent companion coordinate.  Unlike the
companion-only form, the result retains the event-bearing state so it can be
used for stopped-history/tail regeneration. -/
theorem map_externalIndexTail_withStateAndCompanion_restrict_eq_prod
    {γ : Type*} [MeasurableSpace γ]
    (ρ : Measure σ) (κ : Measure γ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure κ] [IsProbabilityMeasure μ]
    (index : σ → ℕ) (hindex : Measurable index)
    (A : Set (σ × (ℕ → α))) (hA : ExternalIndexPrefixEvent index A) :
    Measure.map (fun z : ((σ × γ) × (ℕ → α)) =>
      (z.1.1, (externalIndexTail (α := α) index (z.1.1, z.2), z.1.2)))
      (((ρ.prod κ).prod (measure μ)).restrict
        {z | (z.1.1, z.2) ∈ A}) =
      (Measure.map Prod.fst ((ρ.prod (measure μ)).restrict A)).prod
        ((measure μ).prod κ) := by
  let M : Measure (Nat -> α) := measure μ
  let source : Measure ((σ × γ) × (Nat -> α)) := (ρ.prod κ).prod M
  let markedSource : Measure (σ × (Nat -> α)) := ρ.prod M
  let reorder : ((σ × γ) × (Nat -> α)) -> (σ × (Nat -> α)) × γ :=
    fun z => ((z.1.1, z.2), z.1.2)
  let carrier : Set ((σ × (Nat -> α)) × γ) := A ×ˢ Set.univ
  let lifted : Set ((σ × γ) × (Nat -> α)) := {z | (z.1.1, z.2) ∈ A}
  let tail : σ × (Nat -> α) -> Nat -> α := externalIndexTail (α := α) index
  let jointState : σ × (Nat -> α) -> σ × (Nat -> α) := fun z => (z.1, tail z)
  let output : (σ × (Nat -> α)) × γ -> σ × ((Nat -> α) × γ) := fun z =>
    (z.1.1, (tail z.1, z.2))
  letI : IsProbabilityMeasure M := by
    dsimp [M, measure]
    infer_instance
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  letI : IsProbabilityMeasure markedSource := by
    dsimp [markedSource]
    infer_instance
  let p1 := measurePreserving_prodAssoc ρ κ M
  let swap : MeasurePreserving (Prod.swap : γ × (Nat -> α) ->
      (Nat -> α) × γ) (κ.prod M) (M.prod κ) :=
    ⟨measurable_swap, Measure.prod_swap⟩
  let p2 := MeasurePreserving.prod (MeasurePreserving.id ρ) swap
  let p3 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc ρ M κ)
  have hsource : MeasurePreserving reorder source (markedSource.prod κ) := by
    simpa [source, markedSource, reorder, M] using (p3.comp (p2.comp p1))
  have htail : Measurable tail := by
    simpa [tail] using measurable_externalIndexTail (α := α) index hindex
  have hjointState : Measurable jointState :=
    measurable_fst.prodMk htail
  have houtput : Measurable output := by
    exact (measurable_fst.comp measurable_fst).prodMk
      ((htail.comp measurable_fst).prodMk measurable_snd)
  have hcarrier : MeasurableSet carrier :=
    (measurableSet_externalIndexPrefixEvent index hindex A hA).prod MeasurableSet.univ
  have hpreimage : reorder ⁻¹' carrier = lifted := by
    ext z
    simp [reorder, carrier, lifted]
  have hrestrict :
      Measure.map reorder (source.restrict lifted) =
        (markedSource.prod κ).restrict carrier := by
    calc
      Measure.map reorder (source.restrict lifted) =
          Measure.map reorder (source.restrict (reorder ⁻¹' carrier)) := by
            rw [hpreimage]
      _ = (Measure.map reorder source).restrict carrier := by
            rw [Measure.restrict_map hsource.measurable hcarrier]
      _ = (markedSource.prod κ).restrict carrier := by
            rw [hsource.map_eq]
  have hpaired : Measurable (fun z : (σ × (Nat -> α)) × γ =>
      (jointState z.1, z.2)) :=
    (hjointState.comp measurable_fst).prodMk measurable_snd
  have houtput_comp : output = MeasurableEquiv.prodAssoc ∘
      (fun z : (σ × (Nat -> α)) × γ => (jointState z.1, z.2)) := by
    funext z
    rfl
  have hstate := map_externalIndexTail_withState_restrict_eq_prod
    ρ μ index hindex A hA
  calc
    Measure.map (fun z : ((σ × γ) × (Nat -> α)) =>
        (z.1.1, (externalIndexTail (α := α) index (z.1.1, z.2), z.1.2)))
        (((ρ.prod κ).prod (measure μ)).restrict {z | (z.1.1, z.2) ∈ A}) =
        Measure.map output (Measure.map reorder (source.restrict lifted)) := by
          rw [show (fun z : ((σ × γ) × (Nat -> α)) =>
              (z.1.1, (externalIndexTail (α := α) index (z.1.1, z.2), z.1.2))) =
              output ∘ reorder by
                funext z
                rfl,
            Measure.map_map houtput hsource.measurable]
    _ = Measure.map output ((markedSource.prod κ).restrict carrier) := by
          rw [hrestrict]
    _ = Measure.map output ((markedSource.restrict A).prod κ) := by
          rw [Measure.restrict_prod_eq_prod_univ]
    _ = Measure.map MeasurableEquiv.prodAssoc
        (Measure.map (fun z : (σ × (Nat -> α)) × γ => (jointState z.1, z.2))
          ((markedSource.restrict A).prod κ)) := by
            rw [houtput_comp, Measure.map_map MeasurableEquiv.prodAssoc.measurable hpaired]
    _ = Measure.map MeasurableEquiv.prodAssoc
        ((Measure.map jointState (markedSource.restrict A)).prod κ) := by
          congr 1
          simpa [jointState] using
            (Measure.map_prod_map (markedSource.restrict A) κ hjointState measurable_id).symm
    _ = Measure.map MeasurableEquiv.prodAssoc
        (((Measure.map Prod.fst (markedSource.restrict A)).prod M).prod κ) := by
          rw [hstate]
    _ = (Measure.map Prod.fst (markedSource.restrict A)).prod (M.prod κ) := by
          simpa [M] using
            (measurePreserving_prodAssoc
              (Measure.map Prod.fst (markedSource.restrict A)) M κ).map_eq
    _ = (Measure.map Prod.fst ((ρ.prod (measure μ)).restrict A)).prod
        ((measure μ).prod κ) := by rfl

/-- If a prefix event concerns an externally indexed IID mark stream but not
an independent companion coordinate, its selected IID tail remains fresh
jointly with that companion.  The result is an unnormalized restricted-law
identity, so it supports actual stopped-process branches without inserting a
conditional resampling assumption. -/
theorem map_externalIndexTail_withCompanion_restrict_eq_smul
    {γ : Type*} [MeasurableSpace γ]
    (ρ : Measure σ) (κ : Measure γ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure κ] [IsProbabilityMeasure μ]
    (index : σ → ℕ) (hindex : Measurable index)
    (A : Set (σ × (ℕ → α))) (hA : ExternalIndexPrefixEvent index A) :
    Measure.map (fun z : ((σ × γ) × (ℕ → α)) =>
      (externalIndexTail (α := α) index (z.1.1, z.2), z.1.2))
      (((ρ.prod κ).prod (measure μ)).restrict
        {z | (z.1.1, z.2) ∈ A}) =
      ((ρ.prod (measure μ)) A) • ((measure μ).prod κ) := by
  let M : Measure (ℕ → α) := measure μ
  let source : Measure ((σ × γ) × (ℕ → α)) := (ρ.prod κ).prod M
  let markedSource : Measure (σ × (ℕ → α)) := ρ.prod M
  let reorder : ((σ × γ) × (ℕ → α)) -> (σ × (ℕ → α)) × γ :=
    fun z => ((z.1.1, z.2), z.1.2)
  let carrier : Set ((σ × (ℕ → α)) × γ) := A ×ˢ Set.univ
  let lifted : Set ((σ × γ) × (ℕ → α)) := {z | (z.1.1, z.2) ∈ A}
  let tail : σ × (ℕ → α) -> Nat -> α := externalIndexTail (α := α) index
  let output : (σ × (ℕ → α)) × γ -> (Nat -> α) × γ :=
    fun z => (tail z.1, z.2)
  letI : IsProbabilityMeasure M := by
    dsimp [M, measure]
    infer_instance
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  letI : IsProbabilityMeasure markedSource := by
    dsimp [markedSource]
    infer_instance
  let p1 := measurePreserving_prodAssoc ρ κ M
  let swap : MeasurePreserving (Prod.swap : γ × (Nat -> α) ->
      (Nat -> α) × γ) (κ.prod M) (M.prod κ) :=
    ⟨measurable_swap, Measure.prod_swap⟩
  let p2 := MeasurePreserving.prod (MeasurePreserving.id ρ) swap
  let p3 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc ρ M κ)
  have hsource : MeasurePreserving reorder source (markedSource.prod κ) := by
    simpa [source, markedSource, reorder, M] using (p3.comp (p2.comp p1))
  have htail : Measurable tail := by
    simpa [tail] using measurable_externalIndexTail (α := α) index hindex
  have houtput : Measurable output := by
    exact (htail.comp measurable_fst).prodMk measurable_snd
  have hcarrier : MeasurableSet carrier :=
    (measurableSet_externalIndexPrefixEvent index hindex A hA).prod MeasurableSet.univ
  have hpreimage : reorder ⁻¹' carrier = lifted := by
    ext z
    simp [reorder, carrier, lifted]
  have hrestrict :
      Measure.map reorder (source.restrict lifted) =
        (markedSource.prod κ).restrict carrier := by
    calc
      Measure.map reorder (source.restrict lifted) =
          Measure.map reorder (source.restrict (reorder ⁻¹' carrier)) := by
            rw [hpreimage]
      _ = (Measure.map reorder source).restrict carrier := by
            rw [Measure.restrict_map hsource.measurable hcarrier]
      _ = (markedSource.prod κ).restrict carrier := by
            rw [hsource.map_eq]
  have hmap :
      Measure.map (fun z : ((σ × γ) × (ℕ → α)) =>
        (externalIndexTail (α := α) index (z.1.1, z.2), z.1.2))
        (source.restrict lifted) =
        Measure.map output (Measure.map reorder (source.restrict lifted)) := by
    have houtput_comp :
        (fun z : ((σ × γ) × (ℕ → α)) =>
          (externalIndexTail (α := α) index (z.1.1, z.2), z.1.2)) =
          output ∘ reorder := by
      funext z
      rfl
    rw [houtput_comp, Measure.map_map houtput hsource.measurable]
  calc
    Measure.map (fun z : ((σ × γ) × (ℕ → α)) =>
        (externalIndexTail (α := α) index (z.1.1, z.2), z.1.2))
        (((ρ.prod κ).prod (measure μ)).restrict {z | (z.1.1, z.2) ∈ A}) =
        Measure.map output (Measure.map reorder (source.restrict lifted)) := by
          simpa [source, lifted] using hmap
    _ = Measure.map output ((markedSource.prod κ).restrict carrier) := by
          rw [hrestrict]
    _ = Measure.map output ((markedSource.restrict A).prod κ) := by
          rw [Measure.restrict_prod_eq_prod_univ]
    _ = (Measure.map tail (markedSource.restrict A)).prod κ := by
          rw [show output = Prod.map tail id by rfl,
            ← Measure.map_prod_map (markedSource.restrict A) κ htail measurable_id,
            Measure.map_id]
    _ = ((ρ.prod M) A) • (M.prod κ) := by
          rw [map_externalIndexTail_restrict_eq_smul ρ μ index hindex A hA,
            Measure.prod_smul_left]
    _ = ((ρ.prod (measure μ)) A) • ((measure μ).prod κ) := by rfl

/-- A full external-index-prefix event factors from every measurable event of
the complete selected IID tail. -/
theorem measure_externalIndexPrefixEvent_inter_tail_preimage_eq_mul
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (index : σ → ℕ) (hindex : Measurable index)
    (A : Set (σ × (ℕ → α))) (hA : ExternalIndexPrefixEvent index A)
    (T : Set (ℕ → α)) (hT : MeasurableSet T) :
    (ρ.prod (measure μ))
        (A ∩ externalIndexTail (α := α) index ⁻¹' T) =
      (ρ.prod (measure μ)) A * (measure μ) T := by
  let ν : Measure (σ × (ℕ → α)) := ρ.prod (measure μ)
  have hmap := map_externalIndexTail_restrict_eq_smul
    ρ μ index hindex A hA
  have hpreimage : MeasurableSet
      (externalIndexTail (α := α) index ⁻¹' T) :=
    hT.preimage (measurable_externalIndexTail (α := α) index hindex)
  change ν (A ∩ externalIndexTail (α := α) index ⁻¹' T) =
    ν A * (measure μ) T
  calc
    ν (A ∩ externalIndexTail (α := α) index ⁻¹' T) =
        Measure.map (externalIndexTail (α := α) index) (ν.restrict A) T := by
          rw [Measure.map_apply
            (measurable_externalIndexTail (α := α) index hindex) hT,
            Measure.restrict_apply hpreimage]
          exact congrArg ν (Set.inter_comm _ _)
    _ = (ν A • (measure μ)) T := by rw [hmap]
    _ = ν A * (measure μ) T := by
      rw [Measure.smul_apply]
      rfl

/-- Any observable whose measurable preimages are determined by an externally
selected IID prefix is independent of the complete IID tail after that
prefix. -/
theorem indepFun_of_externalIndexPrefixEvent_tail
    {β : Type*} [MeasurableSpace β]
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (index : σ → ℕ) (hindex : Measurable index)
    (f : σ × (ℕ → α) → β)
    (hf : ∀ S : Set β, MeasurableSet S →
      ExternalIndexPrefixEvent index (f ⁻¹' S)) :
    IndepFun f (externalIndexTail (α := α) index) (ρ.prod (measure μ)) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro S T hS hT
  calc
    (ρ.prod (measure μ))
        (f ⁻¹' S ∩ externalIndexTail (α := α) index ⁻¹' T) =
        (ρ.prod (measure μ)) (f ⁻¹' S) * (measure μ) T :=
      measure_externalIndexPrefixEvent_inter_tail_preimage_eq_mul
        ρ μ index hindex (f ⁻¹' S) (hf S hS) T hT
    _ = (ρ.prod (measure μ)) (f ⁻¹' S) *
        (ρ.prod (measure μ)) (externalIndexTail (α := α) index ⁻¹' T) := by
      congr 1
      rw [← Measure.map_apply
        (measurable_externalIndexTail (α := α) index hindex) hT,
        (externalIndexTail_hasLaw ρ μ index hindex).map_eq]

/-- A suffix selected from an IID stream by an independent external state is
independent of every measurable observation of that external state. -/
theorem indepFun_externalIndexTail
    {β : Type*} [MeasurableSpace β]
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (index : σ → ℕ) (hindex : Measurable index)
    (g : σ → β) (hg : Measurable g) :
    IndepFun (fun z : σ × (ℕ → α) => g z.1)
      (externalIndexTail (α := α) index) (ρ.prod (measure μ)) := by
  classical
  let M : Measure (ℕ → α) := measure μ
  let source : Measure (σ × (ℕ → α)) := ρ.prod M
  let first : σ × (ℕ → α) → β := fun z => g z.1
  let tail : σ × (ℕ → α) → ℕ → α := externalIndexTail (α := α) index
  letI : IsProbabilityMeasure M := by
    dsimp [M, measure]
    infer_instance
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hfirst : Measurable first := by
    exact hg.comp measurable_fst
  have htail : Measurable tail := by
    simpa [tail] using measurable_externalIndexTail (α := α) index hindex
  have hfirstlaw : source.map first = ρ.map g := by
    calc
      source.map first = (source.map Prod.fst).map g := by
        rw [Measure.map_map hg measurable_fst]
        rfl
      _ = ρ.map g := by
        rw [Measure.map_fst_prod, measure_univ, one_smul]
  have htaillaw : source.map tail = M := by
    simpa [source, tail, M] using
      (externalIndexTail_hasLaw ρ μ index hindex).map_eq
  apply (indepFun_iff_map_prod_eq_prod_map_map
    hfirst.aemeasurable htail.aemeasurable).mpr
  symm
  apply Measure.prod_eq
  intro S T hS hT
  rw [hfirstlaw, htaillaw,
    Measure.map_apply hg hS]
  have hpair : Measurable (fun z : σ × (ℕ → α) => (first z, tail z)) :=
    hfirst.prodMk htail
  have hpreimage : MeasurableSet
      ((fun z : σ × (ℕ → α) => (first z, tail z)) ⁻¹' (S ×ˢ T)) :=
    (hS.prod hT).preimage hpair
  rw [Measure.map_apply hpair (hS.prod hT), Measure.prod_apply hpreimage]
  have htailAt (state : σ) :
      M (deterministicIndexTail (α := α) (index state) ⁻¹' T) = M T := by
    rw [← Measure.map_apply
      (measurable_deterministicIndexTail (α := α) (index state)) hT,
      (deterministicIndexTail_hasLaw μ (index state)).map_eq]
  have hfiber (state : σ) :
      M (Prod.mk state ⁻¹'
        ((fun z : σ × (ℕ → α) => (first z, tail z)) ⁻¹' (S ×ˢ T))) =
          if g state ∈ S then M T else 0 := by
    by_cases hstate : g state ∈ S
    · have hset :
          Prod.mk state ⁻¹'
            ((fun z : σ × (ℕ → α) => (first z, tail z)) ⁻¹' (S ×ˢ T)) =
              deterministicIndexTail (α := α) (index state) ⁻¹' T := by
          change
            (fun marks => (g state,
              deterministicIndexTail (α := α) (index state) marks)) ⁻¹' (S ×ˢ T) =
              deterministicIndexTail (α := α) (index state) ⁻¹' T
          ext marks
          simp [hstate]
      rw [hset, htailAt]
      simp [hstate]
    · have hset :
          Prod.mk state ⁻¹'
            ((fun z : σ × (ℕ → α) => (first z, tail z)) ⁻¹' (S ×ˢ T)) = ∅ := by
          change
            (fun marks => (g state,
              deterministicIndexTail (α := α) (index state) marks)) ⁻¹' (S ×ˢ T) = ∅
          ext marks
          simp [hstate]
      rw [hset]
      simp [hstate]
  calc
    ∫⁻ state, M (Prod.mk state ⁻¹'
        ((fun z : σ × (ℕ → α) => (first z, tail z)) ⁻¹' (S ×ˢ T))) ∂ρ =
        ∫⁻ state, (g ⁻¹' S).indicator (fun _ => M T) state ∂ρ := by
          apply lintegral_congr_ae
          filter_upwards [] with state
          rw [hfiber]
          simp [Set.indicator]
    _ = ∫⁻ _ in g ⁻¹' S, M T ∂ρ := by
          rw [lintegral_indicator (hg hS)]
    _ = M T * ρ (g ⁻¹' S) := by
          rw [lintegral_const]
          simp
    _ = ρ (g ⁻¹' S) * M T := mul_comm _ _

/-- The joint law of a measurable external observation and an IID suffix
selected by that external state is the corresponding product law. -/
theorem externalIndexTail_joint_hasLaw
    {β : Type*} [MeasurableSpace β]
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (index : σ → ℕ) (hindex : Measurable index)
    (g : σ → β) (hg : Measurable g) :
    HasLaw (fun z : σ × (ℕ → α) =>
      (g z.1, externalIndexTail (α := α) index z))
      ((ρ.map g).prod (measure μ)) (ρ.prod (measure μ)) := by
  let M : Measure (ℕ → α) := measure μ
  let source : Measure (σ × (ℕ → α)) := ρ.prod M
  let first : σ × (ℕ → α) → β := fun z => g z.1
  let tail : σ × (ℕ → α) → ℕ → α := externalIndexTail (α := α) index
  letI : IsProbabilityMeasure M := by
    dsimp [M, measure]
    infer_instance
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hfirst : Measurable first := hg.comp measurable_fst
  have htail : Measurable tail := by
    simpa [tail] using measurable_externalIndexTail (α := α) index hindex
  have hfirstlaw : source.map first = ρ.map g := by
    calc
      source.map first = (source.map Prod.fst).map g := by
        rw [Measure.map_map hg measurable_fst]
        rfl
      _ = ρ.map g := by
        rw [Measure.map_fst_prod, measure_univ, one_smul]
  have htaillaw : source.map tail = M := by
    simpa [source, tail, M] using
      (externalIndexTail_hasLaw ρ μ index hindex).map_eq
  refine ⟨(hfirst.prodMk htail).aemeasurable, ?_⟩
  calc
    source.map (fun z => (first z, tail z)) =
        (source.map first).prod (source.map tail) := by
          exact (indepFun_iff_map_prod_eq_prod_map_map
            hfirst.aemeasurable htail.aemeasurable).mp
            (indepFun_externalIndexTail ρ μ index hindex g hg)
    _ = (ρ.map g).prod M := by rw [hfirstlaw, htaillaw]
    _ = (ρ.map g).prod (measure μ) := by rfl

end

end AppliedModelingLib.Probability.IIDStream
