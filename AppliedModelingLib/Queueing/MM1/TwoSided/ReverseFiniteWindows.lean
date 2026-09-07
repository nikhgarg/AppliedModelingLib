import AppliedModelingLib.Queueing.MM1.TwoSided.ReverseTrajectory

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory Preorder

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- The finite forward window `X_0, ..., X_(n+1)`. -/
def forwardWindow (n : ℕ) (x : ℤ → α) : Fin (n + 2) → α :=
  fun i => x (i : ℕ)

/-- The finite cross-zero window `X_-1, X_0, ..., X_n`. -/
def crossZeroWindow (n : ℕ) (x : ℤ → α) : Fin (n + 2) → α :=
  Fin.cases (x (-1 : ℤ)) (fun i => x (i : ℕ))

theorem measurable_forwardWindow (n : ℕ) :
    Measurable (forwardWindow (α := α) n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

theorem measurable_crossZeroWindow (n : ℕ) :
    Measurable (crossZeroWindow (α := α) n) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_pi_apply _
  · exact measurable_pi_apply _

/-- Append a state to the right end of a finite window. -/
def snocWindow {n : ℕ} (w : Fin n → α) (a : α) : Fin (n + 1) → α :=
  Fin.snoc w a

theorem measurable_snocWindow (n : ℕ) :
    Measurable (fun p : (Fin n → α) × α => snocWindow p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [snocWindow] using measurable_snd
  · simpa [snocWindow] using (measurable_pi_apply j).comp measurable_fst

theorem crossZeroWindow_succ (n : ℕ) (x : ℤ → α) :
    crossZeroWindow (n + 1) x = snocWindow (crossZeroWindow n x) (x (n + 1 : ℕ)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hlast : Fin.last (n + 2) = Fin.succ (Fin.last (n + 1)) := by
      ext
      simp
    simp only [snocWindow, Fin.snoc_last]
    rw [hlast]
    simp only [crossZeroWindow, Fin.cases_succ]
    change x ((Fin.last (n + 1) : Fin (n + 2)).val : ℤ) =
      x ((n : ℤ) + 1)
    simp
  · rcases j with ⟨j, hj⟩
    simp only [snocWindow, Fin.snoc_castSucc]
    cases j with
    | zero => simp [crossZeroWindow]
    | succ j => simp [crossZeroWindow]

theorem forwardWindow_succ (n : ℕ) (x : ℤ → α) :
    forwardWindow (n + 1) x = snocWindow (forwardWindow n x) (x (n + 2 : ℕ)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [forwardWindow, snocWindow]
  · simp [forwardWindow, snocWindow]

/-- The initial `n + 1` coordinates of a one-sided natural-time path. -/
def natPrefix (n : ℕ) (x : ℕ → α) : Fin (n + 1) → α :=
  fun i => x i

theorem measurable_natPrefix (n : ℕ) :
    Measurable (natPrefix (α := α) n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

/-- Reindex the `Iic n` history used by the Ionescu--Tulcea recurrence as a
plain `Fin (n + 1)` tuple. -/
def iicToFin (n : ℕ) (y : (i : Finset.Iic n) → α) : Fin (n + 1) → α :=
  fun i => y ⟨i, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt)⟩

theorem measurable_iicToFin (n : ℕ) :
    Measurable (iicToFin (α := α) n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

theorem iicToFin_frestrictLe (n : ℕ) (x : ℕ → α) :
    iicToFin n (Preorder.frestrictLe n x) = natPrefix n x := by
  funext i
  rfl

theorem iicToFin_last (n : ℕ) (y : (i : Finset.Iic n) → α) :
    iicToFin n y (Fin.last n) = y ⟨n, Finset.mem_Iic.mpr le_rfl⟩ := by
  rfl

theorem natPrefix_succ (n : ℕ) (x : ℕ → α) :
    natPrefix (n + 1) x = snocWindow (natPrefix n x) (x (n + 1)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [natPrefix, snocWindow]
  · simp [natPrefix, snocWindow]

/-- The ordinary forward finite prefix obeys the Markov one-step recurrence
after reindexing the history as a `Fin` tuple. -/
theorem stationaryTrajMeasure_natPrefix_succ
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α}
    [IsMarkovKernel K] (n : ℕ) :
    (stationaryTrajMeasure π K).map (natPrefix (α := α) (n + 1)) =
      ((stationaryTrajMeasure π K).map (natPrefix n) ⊗ₘ
        (K ∘ₖ Kernel.deterministic
          (fun w : Fin (n + 1) → α => w (Fin.last n))
          (measurable_pi_apply _))).map
            (fun p => snocWindow p.1 p.2) := by
  have hprob : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := hprob
  let hist : (ℕ → α) → (i : Finset.Iic n) → α := Preorder.frestrictLe n
  let prefixNext : (ℕ → α) → (Fin (n + 1) → α) × α :=
    fun x => (natPrefix n x, x (n + 1))
  let historyNext : (ℕ → α) → ((i : Finset.Iic n) → α) × α :=
    fun x => (hist x, x (n + 1))
  let mapHistoryNext : ((i : Finset.Iic n) → α) × α →
      (Fin (n + 1) → α) × α :=
    fun p => (iicToFin n p.1, p.2)
  have hhist : Measurable hist := measurable_frestrictLe n
  have hpref : Measurable (natPrefix (α := α) n) := measurable_natPrefix n
  have hprefixNext : Measurable prefixNext := hpref.prodMk (measurable_pi_apply _)
  have hhistoryNext : Measurable historyNext := hhist.prodMk (measurable_pi_apply _)
  have hmapHistoryNext : Measurable mapHistoryNext :=
    (measurable_iicToFin n).comp measurable_fst |>.prodMk measurable_snd
  have hrec := stationaryTrajMeasure_prefix_succ (π := π) (K := K) n
  have hlast :
      (fun y : (i : Finset.Iic n) → α =>
          y ⟨n, Finset.mem_Iic.mpr le_rfl⟩) =
        (fun w : Fin (n + 1) → α => w (Fin.last n)) ∘ iicToFin n := by
    funext y
    symm
    exact iicToFin_last n y
  have hkernel :
      K ∘ₖ Kernel.deterministic
          (fun y : (i : Finset.Iic n) → α =>
            y ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
          (measurable_pi_apply _) =
        K ∘ₖ Kernel.deterministic
          ((fun w : Fin (n + 1) → α => w (Fin.last n)) ∘ iicToFin n)
          ((measurable_pi_apply _).comp (measurable_iicToFin n)) := by
    exact congrArg (fun L => K ∘ₖ L) (Kernel.deterministic_congr hlast)
  have hprefixfun : iicToFin n ∘ hist = natPrefix n := by
    funext x
    exact iicToFin_frestrictLe n x
  have hnextfun : prefixNext = mapHistoryNext ∘ historyNext := by
    funext x
    apply Prod.ext
    · exact iicToFin_frestrictLe n x
    · rfl
  have hprefixlaw :
      ((stationaryTrajMeasure π K).map hist).map (iicToFin n) =
        (stationaryTrajMeasure π K).map (natPrefix n) := by
    rw [Measure.map_map (measurable_iicToFin n) hhist]
    rw [hprefixfun]
  calc
    (stationaryTrajMeasure π K).map (natPrefix (α := α) (n + 1)) =
        ((stationaryTrajMeasure π K).map prefixNext).map
          (fun p => snocWindow p.1 p.2) := by
          rw [Measure.map_map (measurable_snocWindow (n + 1)) hprefixNext]
          congr 1
          funext x
          simpa [prefixNext, Function.comp_def] using natPrefix_succ n x
    _ =
        (((stationaryTrajMeasure π K).map historyNext).map mapHistoryNext).map
          (fun p => snocWindow p.1 p.2) := by
          congr 1
          rw [Measure.map_map hmapHistoryNext hhistoryNext]
          rw [hnextfun]
    _ = (((stationaryTrajMeasure π K).map hist ⊗ₘ
          (K ∘ₖ Kernel.deterministic
            (fun y : (i : Finset.Iic n) → α =>
              y ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
            (measurable_pi_apply _))).map mapHistoryNext).map
              (fun p => snocWindow p.1 p.2) := by
          rw [hrec]
    _ = (((((stationaryTrajMeasure π K).map hist).map (iicToFin n)) ⊗ₘ
          (K ∘ₖ Kernel.deterministic
            (fun w : Fin (n + 1) → α => w (Fin.last n))
            (measurable_pi_apply _))).map
              (fun p => snocWindow p.1 p.2)) := by
          rw [hkernel]
          simpa [mapHistoryNext] using congrArg (fun ν => ν.map (fun p => snocWindow p.1 p.2))
            (Measure.compProd_map_through _ K (iicToFin n)
            (measurable_iicToFin n)
            (fun w : Fin (n + 1) → α => w (Fin.last n))
            (measurable_pi_apply _))
    _ = ((stationaryTrajMeasure π K).map (natPrefix n) ⊗ₘ
          (K ∘ₖ Kernel.deterministic
            (fun w : Fin (n + 1) → α => w (Fin.last n))
            (measurable_pi_apply _))).map
              (fun p => snocWindow p.1 p.2) := by
          rw [hprefixlaw]

/-- Before appending the last coordinate, the finite forward prefix has the
raw pair-valued one-step Markov recurrence. -/
theorem stationaryTrajMeasure_natPrefix_next
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α}
    [IsMarkovKernel K] (n : ℕ) :
    (stationaryTrajMeasure π K).map
        (fun x => (natPrefix n x, x (n + 1)) ) =
      (stationaryTrajMeasure π K).map (natPrefix n) ⊗ₘ
        (K ∘ₖ Kernel.deterministic
          (fun w : Fin (n + 1) → α => w (Fin.last n))
          (measurable_pi_apply _)) := by
  have hprob : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := hprob
  let hist : (ℕ → α) → (i : Finset.Iic n) → α := Preorder.frestrictLe n
  let pairNext : (ℕ → α) → (Fin (n + 1) → α) × α :=
    fun x => (natPrefix n x, x (n + 1))
  let historyNext : (ℕ → α) → ((i : Finset.Iic n) → α) × α :=
    fun x => (hist x, x (n + 1))
  let mapHistoryNext : ((i : Finset.Iic n) → α) × α →
      (Fin (n + 1) → α) × α :=
    fun p => (iicToFin n p.1, p.2)
  have hhist : Measurable hist := measurable_frestrictLe n
  have hhistoryNext : Measurable historyNext := hhist.prodMk (measurable_pi_apply _)
  have hmapHistoryNext : Measurable mapHistoryNext :=
    (measurable_iicToFin n).comp measurable_fst |>.prodMk measurable_snd
  have hrec := stationaryTrajMeasure_prefix_succ (π := π) (K := K) n
  have hlast :
      (fun y : (i : Finset.Iic n) → α =>
          y ⟨n, Finset.mem_Iic.mpr le_rfl⟩) =
        (fun w : Fin (n + 1) → α => w (Fin.last n)) ∘ iicToFin n := by
    funext y
    symm
    exact iicToFin_last n y
  have hkernel :
      K ∘ₖ Kernel.deterministic
          (fun y : (i : Finset.Iic n) → α =>
            y ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
          (measurable_pi_apply _) =
        K ∘ₖ Kernel.deterministic
          ((fun w : Fin (n + 1) → α => w (Fin.last n)) ∘ iicToFin n)
          ((measurable_pi_apply _).comp (measurable_iicToFin n)) := by
    exact congrArg (fun L => K ∘ₖ L) (Kernel.deterministic_congr hlast)
  have hprefixfun : iicToFin n ∘ hist = natPrefix n := by
    funext x
    exact iicToFin_frestrictLe n x
  have hnextfun : pairNext = mapHistoryNext ∘ historyNext := by
    funext x
    apply Prod.ext
    · exact iicToFin_frestrictLe n x
    · rfl
  have hprefixlaw :
      ((stationaryTrajMeasure π K).map hist).map (iicToFin n) =
        (stationaryTrajMeasure π K).map (natPrefix n) := by
    rw [Measure.map_map (measurable_iicToFin n) hhist]
    rw [hprefixfun]
  calc
    (stationaryTrajMeasure π K).map
        (fun x => (natPrefix n x, x (n + 1))) =
        ((stationaryTrajMeasure π K).map historyNext).map mapHistoryNext := by
          rw [Measure.map_map hmapHistoryNext hhistoryNext]
          change (stationaryTrajMeasure π K).map pairNext = _
          rw [hnextfun]
    _ = ((stationaryTrajMeasure π K).map hist ⊗ₘ
          (K ∘ₖ Kernel.deterministic
            (fun y : (i : Finset.Iic n) → α =>
              y ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
            (measurable_pi_apply _))).map mapHistoryNext := by
          rw [hrec]
    _ = ((stationaryTrajMeasure π K).map hist).map (iicToFin n) ⊗ₘ
          (K ∘ₖ Kernel.deterministic
            (fun w : Fin (n + 1) → α => w (Fin.last n))
            (measurable_pi_apply _)) := by
          rw [hkernel]
          simpa [mapHistoryNext] using
            (Measure.compProd_map_through _ K (iicToFin n)
              (measurable_iicToFin n)
              (fun w : Fin (n + 1) → α => w (Fin.last n))
              (measurable_pi_apply _))
    _ = (stationaryTrajMeasure π K).map (natPrefix n) ⊗ₘ
          (K ∘ₖ Kernel.deterministic
            (fun w : Fin (n + 1) → α => w (Fin.last n))
            (measurable_pi_apply _)) := by
          rw [hprefixlaw]

/-- Sampling two conditionally independent branches, retaining the first
branch and then the second, is the usual product kernel. -/
private theorem fw_compProd_prodMkRight_eq_prod
    {β γ δ : Type*} [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (A : Kernel β γ) (B : Kernel β δ) [IsMarkovKernel A] [IsMarkovKernel B] :
    A ⊗ₖ B.prodMkRight γ = A ×ₖ B := by
  ext x s hs
  rw [Kernel.compProd_apply hs, Kernel.prod_apply' A B x hs]
  simp only [Kernel.prodMkRight_apply]

private def fw_swapBranchOutputs
    {β γ δ : Type*} (p : (β × γ) × δ) : (β × δ) × γ :=
  ((p.1.1, p.2), p.1.2)

private theorem measurable_fw_swapBranchOutputs
    {β γ δ : Type*} [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ] :
    Measurable (fw_swapBranchOutputs (β := β) (γ := γ) (δ := δ)) := by
  exact ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
    (measurable_snd.comp measurable_fst)

private def fw_swapInnerBranches
    {β γ δ : Type*} (p : β × (γ × δ)) : β × (δ × γ) :=
  (p.1, (p.2.2, p.2.1))

private theorem measurable_fw_swapInnerBranches
    {β γ δ : Type*} [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ] :
    Measurable (fw_swapInnerBranches (β := β) (γ := γ) (δ := δ)) := by
  exact measurable_fst.prodMk
    ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))

/-- Conditional Fubini for two Markov kernels drawn from the same input. -/
private theorem fw_conditional_fubini_branches
    {β γ δ : Type*} [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    {μ : Measure β} [IsProbabilityMeasure μ]
    (A : Kernel β γ) (B : Kernel β δ) [IsMarkovKernel A] [IsMarkovKernel B] :
    ((μ ⊗ₘ A) ⊗ₘ B.prodMkRight γ).map
        (fw_swapBranchOutputs (β := β) (γ := γ) (δ := δ)) =
      (μ ⊗ₘ B) ⊗ₘ A.prodMkRight δ := by
  have hA : (μ ⊗ₘ A) ⊗ₘ B.prodMkRight γ =
      (μ ⊗ₘ (A ×ₖ B)).map MeasurableEquiv.prodAssoc.symm := by
    calc
      (μ ⊗ₘ A) ⊗ₘ B.prodMkRight γ =
          (μ ⊗ₘ (A ⊗ₖ B.prodMkRight γ)).map MeasurableEquiv.prodAssoc.symm := by
            symm
            exact Measure.compProd_assoc
      _ = (μ ⊗ₘ (A ×ₖ B)).map MeasurableEquiv.prodAssoc.symm := by
            rw [fw_compProd_prodMkRight_eq_prod]
  have hB : (μ ⊗ₘ B) ⊗ₘ A.prodMkRight δ =
      (μ ⊗ₘ (B ×ₖ A)).map MeasurableEquiv.prodAssoc.symm := by
    calc
      (μ ⊗ₘ B) ⊗ₘ A.prodMkRight δ =
          (μ ⊗ₘ (B ⊗ₖ A.prodMkRight δ)).map MeasurableEquiv.prodAssoc.symm := by
            symm
            exact Measure.compProd_assoc
      _ = (μ ⊗ₘ (B ×ₖ A)).map MeasurableEquiv.prodAssoc.symm := by
            rw [fw_compProd_prodMkRight_eq_prod]
  have hswap : (μ ⊗ₘ (A ×ₖ B)).map
      (fw_swapInnerBranches (β := β) (γ := γ) (δ := δ)) = μ ⊗ₘ (B ×ₖ A) := by
    calc
      (μ ⊗ₘ (A ×ₖ B)).map
          (fw_swapInnerBranches (β := β) (γ := γ) (δ := δ)) =
          (μ ⊗ₘ (A ×ₖ B)).map (Prod.map id Prod.swap) := by rfl
      _ = μ ⊗ₘ (A ×ₖ B).map Prod.swap := by
            rw [← Measure.compProd_map measurable_swap]
      _ = μ ⊗ₘ (B ×ₖ A) := by rw [Kernel.map_prod_swap]
  have hcompat :
      (fw_swapBranchOutputs (β := β) (γ := γ) (δ := δ) ∘
        MeasurableEquiv.prodAssoc.symm) =
        MeasurableEquiv.prodAssoc.symm ∘
          fw_swapInnerBranches (β := β) (γ := γ) (δ := δ) := by
    funext q
    rcases q with ⟨x, y, z⟩
    rfl
  calc
    ((μ ⊗ₘ A) ⊗ₘ B.prodMkRight γ).map
        (fw_swapBranchOutputs (β := β) (γ := γ) (δ := δ)) =
        ((μ ⊗ₘ (A ×ₖ B)).map MeasurableEquiv.prodAssoc.symm).map
          (fw_swapBranchOutputs (β := β) (γ := γ) (δ := δ)) := by rw [hA]
    _ = (μ ⊗ₘ (A ×ₖ B)).map
          (fw_swapBranchOutputs (β := β) (γ := γ) (δ := δ) ∘
            MeasurableEquiv.prodAssoc.symm) := by
          rw [Measure.map_map measurable_fw_swapBranchOutputs
            MeasurableEquiv.prodAssoc.symm.measurable]
    _ = (μ ⊗ₘ (A ×ₖ B)).map
          (MeasurableEquiv.prodAssoc.symm ∘
            fw_swapInnerBranches (β := β) (γ := γ) (δ := δ)) := by rw [hcompat]
    _ = ((μ ⊗ₘ (A ×ₖ B)).map
          (fw_swapInnerBranches (β := β) (γ := γ) (δ := δ))).map
            MeasurableEquiv.prodAssoc.symm := by
          symm
          rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
            measurable_fw_swapInnerBranches]
    _ = (μ ⊗ₘ (B ×ₖ A)).map MeasurableEquiv.prodAssoc.symm := by rw [hswap]
    _ = (μ ⊗ₘ B) ⊗ₘ A.prodMkRight δ := by rw [hB]

/-- Put a new leftmost coordinate in front of a finite tuple. -/
def prependWindow {n : ℕ} (a : α) (w : Fin n → α) : Fin (n + 1) → α :=
  Matrix.vecCons a w

theorem measurable_prependWindow (n : ℕ) :
    Measurable (fun p : α × (Fin n → α) => prependWindow p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [prependWindow] using measurable_fst
  · simpa [prependWindow] using (measurable_pi_apply j).comp measurable_snd

def prefixFirst {n : ℕ} (w : Fin (n + 1) → α) : α := w 0

theorem measurable_prefixFirst (n : ℕ) :
    Measurable (prefixFirst (α := α) (n := n)) := by
  exact measurable_pi_apply 0

def prefixLast (n : ℕ) (w : Fin (n + 1) → α) : α := w (Fin.last n)

theorem measurable_prefixLast (n : ℕ) :
    Measurable (prefixLast (α := α) n) := by
  exact measurable_pi_apply _

def sourcePrefix (n : ℕ) (z : (ℕ → α) × (ℕ → α)) : Fin (n + 1) → α :=
  natPrefix n z.1

theorem measurable_sourcePrefix (n : ℕ) :
    Measurable (sourcePrefix (α := α) n) := by
  exact (measurable_natPrefix n).comp measurable_fst

def sourceReverseOne (z : (ℕ → α) × (ℕ → α)) : α := z.2 1

theorem measurable_sourceReverseOne :
    Measurable (sourceReverseOne (α := α)) := by
  exact (measurable_pi_apply 1).comp measurable_snd

def pairedCrossWindow (n : ℕ) (z : (ℕ → α) × (ℕ → α)) : Fin (n + 2) → α :=
  prependWindow (sourceReverseOne z) (sourcePrefix n z)

theorem measurable_pairedCrossWindow (n : ℕ) :
    Measurable (pairedCrossWindow (α := α) n) := by
  exact (measurable_prependWindow (α := α) (n + 1)).comp
    (measurable_sourceReverseOne.prodMk (measurable_sourcePrefix n))

theorem crossZeroWindow_spliceForwardReverse (n : ℕ)
    (z : (ℕ → α) × (ℕ → α)) :
    crossZeroWindow n (spliceForwardReverse z) = pairedCrossWindow n z := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- Turn a forward prefix and its reverse one-step state into temporal
cross-zero order. -/
def prefixReverseToCross {n : ℕ} (p : (Fin (n + 1) → α) × α) :
    Fin (n + 2) → α :=
  prependWindow p.2 p.1

theorem measurable_prefixReverseToCross (n : ℕ) :
    Measurable (prefixReverseToCross (α := α) (n := n)) := by
  exact (measurable_prependWindow (α := α) (n + 1)).comp
    (measurable_snd.prodMk measurable_fst)

theorem prefixReverseToCross_last (n : ℕ) (p : (Fin (n + 1) → α) × α) :
    prefixReverseToCross p (Fin.last (n + 1)) = prefixLast n p.1 := by
  change Matrix.vecCons p.2 p.1 (Fin.last (n + 1)) = p.1 (Fin.last n)
  rw [← Fin.succ_last, Matrix.cons_val_succ]

theorem pairedCrossWindow_eq_prefixReverseToCross (n : ℕ)
    (z : (ℕ → α) × (ℕ → α)) :
    pairedCrossWindow n z =
      prefixReverseToCross (sourcePrefix n z, sourceReverseOne z) := by
  rfl

/-- Before the pair-balance assumption is used, the cross-zero finite window
is obtained by drawing its forward prefix and then a reverse one-step branch
from the first prefix coordinate. -/
theorem forwardReverseTwoSidedSourceMeasure_prefix_reverseOne
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] (n : ℕ) :
    (forwardReverseTwoSidedSourceMeasure π K Kr).map
        (fun z => (sourcePrefix n z, sourceReverseOne z)) =
      ((stationaryTrajMeasure π K).map (natPrefix n)) ⊗ₘ
        (Kr ∘ₖ Kernel.deterministic (prefixFirst (α := α) (n := n))
          (measurable_prefixFirst n)) := by
  have hprob : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := hprob
  let μ : Measure (ℕ → α) := stationaryTrajMeasure π K
  let f : (ℕ → α) → Fin (n + 1) → α := natPrefix n
  let g : (Fin (n + 1) → α) → α := prefixFirst
  let e : ((ℕ → α) × (ℕ → α)) → (ℕ → α) × α :=
    Prod.map id (fun x : ℕ → α => x 1)
  have hf : Measurable f := measurable_natPrefix n
  have hg : Measurable g := measurable_prefixFirst n
  have he : Measurable e := measurable_id.prodMap (measurable_pi_apply 1)
  have hpair : Measurable (fun p : (ℕ → α) × α => (f p.1, p.2)) :=
    hf.comp measurable_fst |>.prodMk measurable_snd
  have hgf : g ∘ f = fun x : ℕ → α => x 0 := by
    funext x
    rfl
  calc
    (forwardReverseTwoSidedSourceMeasure π K Kr).map
        (fun z => (sourcePrefix n z, sourceReverseOne z)) =
        ((forwardReverseTwoSidedSourceMeasure π K Kr).map e).map
          (fun p => (f p.1, p.2)) := by
          symm
          rw [Measure.map_map hpair he]
          rfl
    _ = (μ ⊗ₘ (conditionalReverseTailKernel Kr).map (fun x : ℕ → α => x 1)).map
          (fun p => (f p.1, p.2)) := by
          unfold forwardReverseTwoSidedSourceMeasure
          rw [← Measure.compProd_map (μ := μ) (κ := conditionalReverseTailKernel Kr)
            (measurable_pi_apply 1)]
    _ = (μ ⊗ₘ (Kr ∘ₖ Kernel.deterministic (g ∘ f) (hg.comp hf))).map
          (fun p => (f p.1, p.2)) := by
          rw [conditionalReverseTailKernel_map_one]
          rfl
    _ = (μ.map f) ⊗ₘ (Kr ∘ₖ Kernel.deterministic g hg) := by
          exact Measure.compProd_map_through μ Kr f hf g hg
    _ = ((stationaryTrajMeasure π K).map (natPrefix n)) ⊗ₘ
          (Kr ∘ₖ Kernel.deterministic (prefixFirst (α := α) (n := n))
            (measurable_prefixFirst n)) := by
          rfl

theorem forwardReverseTwoSidedSourceMeasure_crossWindow_law
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] (n : ℕ) :
    (forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedCrossWindow n) =
      (((stationaryTrajMeasure π K).map (natPrefix n) ⊗ₘ
        (Kr ∘ₖ Kernel.deterministic (prefixFirst (α := α) (n := n))
          (measurable_prefixFirst n))).map
          (prefixReverseToCross (α := α) (n := n))) := by
  let pair : ((ℕ → α) × (ℕ → α)) → (Fin (n + 1) → α) × α :=
    fun z => (sourcePrefix n z, sourceReverseOne z)
  have hpair : Measurable pair :=
    (measurable_sourcePrefix n).prodMk measurable_sourceReverseOne
  have hpairCross : pairedCrossWindow n =
      prefixReverseToCross (α := α) (n := n) ∘ pair := by
    funext z
    exact pairedCrossWindow_eq_prefixReverseToCross n z
  calc
    (forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedCrossWindow n) =
        ((forwardReverseTwoSidedSourceMeasure π K Kr).map pair).map
          (prefixReverseToCross (α := α) (n := n)) := by
          rw [Measure.map_map (measurable_prefixReverseToCross n) hpair]
          rw [hpairCross]
    _ = (((stationaryTrajMeasure π K).map (natPrefix n) ⊗ₘ
          (Kr ∘ₖ Kernel.deterministic (prefixFirst (α := α) (n := n))
            (measurable_prefixFirst n))).map
            (prefixReverseToCross (α := α) (n := n))) := by
          simpa [pair] using congrArg
            (fun ν => ν.map (prefixReverseToCross (α := α) (n := n)))
            (forwardReverseTwoSidedSourceMeasure_prefix_reverseOne
              (π := π) (K := K) (Kr := Kr) n)

theorem forwardReverseTwoSidedTrajMeasure_crossWindow_law
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] (n : ℕ) :
    (forwardReverseTwoSidedTrajMeasure π K Kr).map (crossZeroWindow n) =
      (((stationaryTrajMeasure π K).map (natPrefix n) ⊗ₘ
        (Kr ∘ₖ Kernel.deterministic (prefixFirst (α := α) (n := n))
          (measurable_prefixFirst n))).map
          (prefixReverseToCross (α := α) (n := n))) := by
  unfold forwardReverseTwoSidedTrajMeasure
  rw [Measure.map_map (measurable_crossZeroWindow n) measurable_spliceForwardReverse]
  change (forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedCrossWindow n) = _
  rw [forwardReverseTwoSidedSourceMeasure_crossWindow_law]

def sourceCrossNext (n : ℕ) (z : (ℕ → α) × (ℕ → α)) :
    (Fin (n + 2) → α) × α :=
  (pairedCrossWindow n z, z.1 (n + 1))

theorem measurable_sourceCrossNext (n : ℕ) :
    Measurable (sourceCrossNext (α := α) n) := by
  exact (measurable_pairedCrossWindow n).prodMk
    ((measurable_pi_apply _).comp measurable_fst)

def swappedPrefixReverseNextToCrossNext {n : ℕ}
    (p : ((Fin (n + 1) → α) × α) × α) : (Fin (n + 2) → α) × α :=
  (prefixReverseToCross p.1, p.2)

theorem measurable_swappedPrefixReverseNextToCrossNext (n : ℕ) :
    Measurable (swappedPrefixReverseNextToCrossNext (α := α) (n := n)) := by
  exact (measurable_prefixReverseToCross n).comp measurable_fst |>.prodMk measurable_snd

theorem sourceCrossNext_factor (n : ℕ) (z : (ℕ → α) × (ℕ → α)) :
    sourceCrossNext n z =
      swappedPrefixReverseNextToCrossNext
        (fw_swapBranchOutputs
          ((sourcePrefix n z, z.1 (n + 1)), sourceReverseOne z)) := by
  rfl

def sourcePrefixNext (n : ℕ) (z : (ℕ → α) × (ℕ → α)) :
    (Fin (n + 1) → α) × α :=
  (sourcePrefix n z, z.1 (n + 1))

theorem measurable_sourcePrefixNext (n : ℕ) :
    Measurable (sourcePrefixNext (α := α) n) := by
  exact (measurable_sourcePrefix n).prodMk
    ((measurable_pi_apply _).comp measurable_fst)

/-- The source law with a finite forward prefix, its next forward state, and
the reverse one-step branch.  The reverse branch still reads only the first
prefix coordinate. -/
theorem forwardReverseTwoSidedSourceMeasure_prefix_next_reverseOne
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] (n : ℕ) :
    (forwardReverseTwoSidedSourceMeasure π K Kr).map
        (fun z => (sourcePrefixNext n z, sourceReverseOne z)) =
      (((stationaryTrajMeasure π K).map (natPrefix n) ⊗ₘ
        (K ∘ₖ Kernel.deterministic (prefixLast (α := α) n)
          (measurable_prefixLast n))) ⊗ₘ
        (Kr ∘ₖ Kernel.deterministic (prefixFirst (α := α) (n := n))
          (measurable_prefixFirst n)).prodMkRight α) := by
  have hprob : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := hprob
  let μ : Measure (ℕ → α) := stationaryTrajMeasure π K
  let f : (ℕ → α) → (Fin (n + 1) → α) × α :=
    fun x => (natPrefix n x, x (n + 1))
  let g : ((Fin (n + 1) → α) × α) → α :=
    fun p => prefixFirst p.1
  let e : ((ℕ → α) × (ℕ → α)) → (ℕ → α) × α :=
    Prod.map id (fun x : ℕ → α => x 1)
  have hf : Measurable f := (measurable_natPrefix n).prodMk (measurable_pi_apply _)
  have hg : Measurable g := (measurable_prefixFirst n).comp measurable_fst
  have he : Measurable e := measurable_id.prodMap (measurable_pi_apply 1)
  have hpair : Measurable (fun p : (ℕ → α) × α => (f p.1, p.2)) :=
    hf.comp measurable_fst |>.prodMk measurable_snd
  have hgf : g ∘ f = fun x : ℕ → α => x 0 := by
    funext x
    rfl
  have hforward : μ.map f =
      (μ.map (natPrefix n) ⊗ₘ
        (K ∘ₖ Kernel.deterministic (prefixLast (α := α) n)
          (measurable_prefixLast n))) := by
    simpa [μ, f, prefixLast] using
      (stationaryTrajMeasure_natPrefix_next (π := π) (K := K) n)
  have hKrprod :
      Kr ∘ₖ Kernel.deterministic g hg =
        (Kr ∘ₖ Kernel.deterministic (prefixFirst (α := α) (n := n))
          (measurable_prefixFirst n)).prodMkRight α := by
    ext p s hs
    simp [g, Kernel.comp_deterministic_eq_comap, Kernel.comap_apply,
      Kernel.prodMkRight_apply]
  calc
    (forwardReverseTwoSidedSourceMeasure π K Kr).map
        (fun z => (sourcePrefixNext n z, sourceReverseOne z)) =
        ((forwardReverseTwoSidedSourceMeasure π K Kr).map e).map
          (fun p => (f p.1, p.2)) := by
          symm
          rw [Measure.map_map hpair he]
          rfl
    _ = (μ ⊗ₘ (conditionalReverseTailKernel Kr).map (fun x : ℕ → α => x 1)).map
          (fun p => (f p.1, p.2)) := by
          unfold forwardReverseTwoSidedSourceMeasure
          rw [← Measure.compProd_map (μ := μ) (κ := conditionalReverseTailKernel Kr)
            (measurable_pi_apply 1)]
    _ = (μ ⊗ₘ (Kr ∘ₖ Kernel.deterministic (g ∘ f) (hg.comp hf))).map
          (fun p => (f p.1, p.2)) := by
          rw [conditionalReverseTailKernel_map_one]
          rfl
    _ = (μ.map f) ⊗ₘ (Kr ∘ₖ Kernel.deterministic g hg) := by
          exact Measure.compProd_map_through μ Kr f hf g hg
    _ = (((stationaryTrajMeasure π K).map (natPrefix n) ⊗ₘ
          (K ∘ₖ Kernel.deterministic (prefixLast (α := α) n)
            (measurable_prefixLast n))) ⊗ₘ
          (Kr ∘ₖ Kernel.deterministic (prefixFirst (α := α) (n := n))
            (measurable_prefixFirst n)).prodMkRight α) := by
          rw [hforward, hKrprod]

/-- Every cross-zero finite window has the ordinary forward Markov
one-step recurrence.  This is the induction engine for arbitrary finite
window shift invariance. -/
theorem forwardReverseTwoSidedSourceMeasure_crossWindow_next
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] (n : ℕ) :
    (forwardReverseTwoSidedSourceMeasure π K Kr).map (sourceCrossNext n) =
      (forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedCrossWindow n) ⊗ₘ
        (K ∘ₖ Kernel.deterministic
          (fun w : Fin (n + 2) → α => w (Fin.last (n + 1)))
          (measurable_pi_apply _)) := by
  have hprob : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := hprob
  let P : Measure (Fin (n + 1) → α) := (stationaryTrajMeasure π K).map (natPrefix n)
  have hP : IsProbabilityMeasure P := by
    dsimp [P]
    exact Measure.isProbabilityMeasure_map (measurable_natPrefix n).aemeasurable
  letI : IsProbabilityMeasure P := hP
  let A : Kernel (Fin (n + 1) → α) α :=
    K ∘ₖ Kernel.deterministic (prefixLast (α := α) n) (measurable_prefixLast n)
  let B : Kernel (Fin (n + 1) → α) α :=
    Kr ∘ₖ Kernel.deterministic (prefixFirst (α := α) (n := n))
      (measurable_prefixFirst n)
  have hA : IsMarkovKernel A := by
    dsimp [A]
    infer_instance
  letI : IsMarkovKernel A := hA
  have hB : IsMarkovKernel B := by
    dsimp [B]
    infer_instance
  letI : IsMarkovKernel B := hB
  let triple : ((ℕ → α) × (ℕ → α)) → ((Fin (n + 1) → α) × α) × α :=
    fun z => ((sourcePrefix n z, z.1 (n + 1)), sourceReverseOne z)
  let qswap : ((Fin (n + 1) → α) × α) × α →
      ((Fin (n + 1) → α) × α) × α :=
    fw_swapBranchOutputs
  let qcross : ((Fin (n + 1) → α) × α) × α →
      (Fin (n + 2) → α) × α :=
    swappedPrefixReverseNextToCrossNext
  let fCross : (Fin (n + 1) → α) × α → Fin (n + 2) → α :=
    prefixReverseToCross
  let gCross : (Fin (n + 2) → α) → α :=
    fun w => w (Fin.last (n + 1))
  have htriple : Measurable triple :=
    (((measurable_sourcePrefix n).prodMk
      ((measurable_pi_apply _).comp measurable_fst)).prodMk
        measurable_sourceReverseOne)
  have hqswap : Measurable qswap := measurable_fw_swapBranchOutputs
  have hqcross : Measurable qcross := measurable_swappedPrefixReverseNextToCrossNext n
  have hfCross : Measurable fCross := measurable_prefixReverseToCross n
  have hgCross : Measurable gCross := measurable_pi_apply _
  have hfactor : sourceCrossNext n = qcross ∘ qswap ∘ triple := by
    funext z
    exact sourceCrossNext_factor n z
  have htripleLaw :
      (forwardReverseTwoSidedSourceMeasure π K Kr).map triple =
        ((P ⊗ₘ A) ⊗ₘ B.prodMkRight α) := by
    simpa [P, A, B, triple] using
      (forwardReverseTwoSidedSourceMeasure_prefix_next_reverseOne
        (π := π) (K := K) (Kr := Kr) n)
  have hfubini :
      ((P ⊗ₘ A) ⊗ₘ B.prodMkRight α).map qswap =
        (P ⊗ₘ B) ⊗ₘ A.prodMkRight α := by
    exact fw_conditional_fubini_branches (μ := P) A B
  have hAprod : A.prodMkRight α =
      K ∘ₖ Kernel.deterministic (gCross ∘ fCross) (hgCross.comp hfCross) := by
    ext p s hs
    simp [A, fCross, gCross, Kernel.comp_deterministic_eq_comap,
      Kernel.comap_apply, Kernel.prodMkRight_apply, prefixReverseToCross_last]
  have htransport :
      ((P ⊗ₘ B) ⊗ₘ
        (K ∘ₖ Kernel.deterministic (gCross ∘ fCross) (hgCross.comp hfCross))).map
          (fun p => (fCross p.1, p.2)) =
        ((P ⊗ₘ B).map fCross) ⊗ₘ
          (K ∘ₖ Kernel.deterministic gCross hgCross) := by
    exact Measure.compProd_map_through (P ⊗ₘ B) K fCross hfCross gCross hgCross
  have hcrossLaw :
      (forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedCrossWindow n) =
        (P ⊗ₘ B).map fCross := by
    simpa [P, B, fCross] using
      (forwardReverseTwoSidedSourceMeasure_crossWindow_law
        (π := π) (K := K) (Kr := Kr) n)
  calc
    (forwardReverseTwoSidedSourceMeasure π K Kr).map (sourceCrossNext n) =
        (((forwardReverseTwoSidedSourceMeasure π K Kr).map triple).map qswap).map
          qcross := by
          rw [Measure.map_map hqcross hqswap, Measure.map_map (hqcross.comp hqswap) htriple]
          rw [hfactor]
          rfl
    _ = (((P ⊗ₘ A) ⊗ₘ B.prodMkRight α).map qswap).map qcross := by
          rw [htripleLaw]
    _ = ((P ⊗ₘ B) ⊗ₘ A.prodMkRight α).map qcross := by
          rw [hfubini]
    _ = ((P ⊗ₘ B) ⊗ₘ
          (K ∘ₖ Kernel.deterministic (gCross ∘ fCross)
            (hgCross.comp hfCross))).map (fun p => (fCross p.1, p.2)) := by
          rw [hAprod]
          rfl
    _ = ((P ⊗ₘ B).map fCross) ⊗ₘ
          (K ∘ₖ Kernel.deterministic gCross hgCross) := by
          exact htransport
    _ = (forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedCrossWindow n) ⊗ₘ
          (K ∘ₖ Kernel.deterministic
            (fun w : Fin (n + 2) → α => w (Fin.last (n + 1)))
            (measurable_pi_apply _)) := by
          rw [hcrossLaw]

theorem forwardReverseTwoSidedTrajMeasure_crossWindow_next
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] (n : ℕ) :
    (forwardReverseTwoSidedTrajMeasure π K Kr).map
        (fun x => (crossZeroWindow n x, x (n + 1 : ℕ))) =
      (forwardReverseTwoSidedTrajMeasure π K Kr).map (crossZeroWindow n) ⊗ₘ
        (K ∘ₖ Kernel.deterministic
          (fun w : Fin (n + 2) → α => w (Fin.last (n + 1)))
          (measurable_pi_apply _)) := by
  have hpair : Measurable (fun x : ℤ → α =>
      (crossZeroWindow n x, x (n + 1 : ℕ))) :=
    (measurable_crossZeroWindow n).prodMk (measurable_pi_apply _)
  have hcross :
      (forwardReverseTwoSidedTrajMeasure π K Kr).map (crossZeroWindow n) =
        (forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedCrossWindow n) := by
    unfold forwardReverseTwoSidedTrajMeasure
    rw [Measure.map_map (measurable_crossZeroWindow n) measurable_spliceForwardReverse]
    have hfun : (crossZeroWindow (α := α) n) ∘
        (spliceForwardReverse (α := α)) = pairedCrossWindow (α := α) n := by
      funext z
      exact crossZeroWindow_spliceForwardReverse n z
    rw [hfun]
  unfold forwardReverseTwoSidedTrajMeasure
  rw [Measure.map_map hpair measurable_spliceForwardReverse]
  change (forwardReverseTwoSidedSourceMeasure π K Kr).map (sourceCrossNext n) = _
  rw [forwardReverseTwoSidedSourceMeasure_crossWindow_next]
  congr 1
  exact hcross.symm

theorem forwardReverseTwoSidedTrajMeasure_crossWindow_succ_factor
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] (n : ℕ) :
    (forwardReverseTwoSidedTrajMeasure π K Kr).map (crossZeroWindow (n + 1)) =
      ((forwardReverseTwoSidedTrajMeasure π K Kr).map (crossZeroWindow n) ⊗ₘ
        (K ∘ₖ Kernel.deterministic
          (fun w : Fin (n + 2) → α => w (Fin.last (n + 1)))
          (measurable_pi_apply _))).map
            (fun p => snocWindow p.1 p.2) := by
  let pair : (ℤ → α) → (Fin (n + 2) → α) × α :=
    fun x => (crossZeroWindow n x, x (n + 1 : ℕ))
  have hpair : Measurable pair :=
    (measurable_crossZeroWindow n).prodMk (measurable_pi_apply _)
  have hsnoc : Measurable (fun p : (Fin (n + 2) → α) × α => snocWindow p.1 p.2) :=
    measurable_snocWindow (n + 2)
  have hfun : crossZeroWindow (n + 1) =
      (fun p => snocWindow p.1 p.2) ∘ pair := by
    funext x
    exact crossZeroWindow_succ n x
  calc
    (forwardReverseTwoSidedTrajMeasure π K Kr).map (crossZeroWindow (n + 1)) =
        ((forwardReverseTwoSidedTrajMeasure π K Kr).map pair).map
          (fun p => snocWindow p.1 p.2) := by
          rw [Measure.map_map hsnoc hpair]
          rw [hfun]
    _ = ((forwardReverseTwoSidedTrajMeasure π K Kr).map (crossZeroWindow n) ⊗ₘ
          (K ∘ₖ Kernel.deterministic
            (fun w : Fin (n + 2) → α => w (Fin.last (n + 1)))
            (measurable_pi_apply _))).map
              (fun p => snocWindow p.1 p.2) := by
          rw [forwardReverseTwoSidedTrajMeasure_crossWindow_next]

theorem forwardWindow_spliceForwardReverse (n : ℕ)
    (z : (ℕ → α) × (ℕ → α)) :
    forwardWindow n (spliceForwardReverse z) = natPrefix (n + 1) z.1 := by
  funext i
  rfl

theorem forwardReverseTwoSidedTrajMeasure_forwardWindow_law
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] (n : ℕ) :
    (forwardReverseTwoSidedTrajMeasure π K Kr).map (forwardWindow n) =
      (stationaryTrajMeasure π K).map (natPrefix (n + 1)) := by
  have hfun : (forwardWindow (α := α) n) ∘ (spliceForwardReverse (α := α)) =
      (natPrefix (α := α) (n + 1)) ∘ Prod.fst := by
    funext z
    exact forwardWindow_spliceForwardReverse n z
  unfold forwardReverseTwoSidedTrajMeasure
  rw [Measure.map_map (measurable_forwardWindow n) measurable_spliceForwardReverse, hfun]
  calc
    (forwardReverseTwoSidedSourceMeasure π K Kr).map
        ((natPrefix (α := α) (n + 1)) ∘ Prod.fst) =
        ((forwardReverseTwoSidedSourceMeasure π K Kr).map Prod.fst).map
          (natPrefix (n + 1)) := by
          symm
          rw [Measure.map_map (measurable_natPrefix (n + 1)) measurable_fst]
    _ = (stationaryTrajMeasure π K).map (natPrefix (n + 1)) := by
          rw [forwardReverseTwoSidedSourceMeasure_map_forward]

theorem forwardReverseTwoSidedTrajMeasure_forwardWindow_succ_factor
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] (n : ℕ) :
    (forwardReverseTwoSidedTrajMeasure π K Kr).map (forwardWindow (n + 1)) =
      ((forwardReverseTwoSidedTrajMeasure π K Kr).map (forwardWindow n) ⊗ₘ
        (K ∘ₖ Kernel.deterministic
          (fun w : Fin (n + 2) → α => w (Fin.last (n + 1)))
          (measurable_pi_apply _))).map
            (fun p => snocWindow p.1 p.2) := by
  calc
    (forwardReverseTwoSidedTrajMeasure π K Kr).map (forwardWindow (n + 1)) =
        (stationaryTrajMeasure π K).map (natPrefix ((n + 1) + 1)) := by
          exact forwardReverseTwoSidedTrajMeasure_forwardWindow_law (π := π) (K := K)
            (Kr := Kr) (n + 1)
    _ = ((stationaryTrajMeasure π K).map (natPrefix (n + 1)) ⊗ₘ
          (K ∘ₖ Kernel.deterministic
            (fun w : Fin (n + 2) → α => w (Fin.last (n + 1)))
            (measurable_pi_apply _))).map
              (fun p => snocWindow p.1 p.2) := by
          simpa using (stationaryTrajMeasure_natPrefix_succ (π := π) (K := K) (n + 1))
    _ = ((forwardReverseTwoSidedTrajMeasure π K Kr).map (forwardWindow n) ⊗ₘ
          (K ∘ₖ Kernel.deterministic
            (fun w : Fin (n + 2) → α => w (Fin.last (n + 1)))
            (measurable_pi_apply _))).map
              (fun p => snocWindow p.1 p.2) := by
          rw [← forwardReverseTwoSidedTrajMeasure_forwardWindow_law (π := π) (K := K)
            (Kr := Kr) n]

def pairWindow (p : α × α) : Fin 2 → α :=
  Fin.cases p.1 (fun _ => p.2)

theorem measurable_pairWindow : Measurable (pairWindow (α := α)) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_fst
  · exact measurable_snd

theorem crossZeroWindow_zero_eq_pairWindow (x : ℤ → α) :
    crossZeroWindow 0 x = pairWindow (x (-1 : ℤ), x 0) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · fin_cases j
    rfl

theorem forwardWindow_zero_eq_pairWindow (x : ℤ → α) :
    forwardWindow 0 x = pairWindow (x 0, x (1 : ℤ)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · fin_cases j
    rfl

/-- Arbitrary-length one-step cross-zero window shift.  This is the direct
generalization of the existing pair/triple/quad results; it has exactly one
negative coordinate and is not, by itself, full all-integer path invariance. -/
theorem Kernel.ReversePairBalance.forwardReverseTwoSidedTrajMeasure_crossZeroWindow_shift
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr]
    (hbalance : Kernel.ReversePairBalance π K Kr)
    (hstationary : Kernel.Invariant K π) (n : ℕ) :
    (forwardReverseTwoSidedTrajMeasure π K Kr).map (crossZeroWindow n) =
      (forwardReverseTwoSidedTrajMeasure π K Kr).map (forwardWindow n) := by
  induction n with
  | zero =>
      let crossPair : (ℤ → α) → α × α := fun x => (x (-1 : ℤ), x 0)
      let forwardPair : (ℤ → α) → α × α := fun x => (x 0, x (1 : ℤ))
      have hcrossPair : Measurable crossPair :=
        (measurable_pi_apply _).prodMk (measurable_pi_apply _)
      have hforwardPair : Measurable forwardPair :=
        (measurable_pi_apply _).prodMk (measurable_pi_apply _)
      have hcrossfun : crossZeroWindow 0 = pairWindow (α := α) ∘ crossPair := by
        funext x
        exact crossZeroWindow_zero_eq_pairWindow x
      have hforwardfun : forwardWindow 0 = pairWindow (α := α) ∘ forwardPair := by
        funext x
        exact forwardWindow_zero_eq_pairWindow x
      calc
        (forwardReverseTwoSidedTrajMeasure π K Kr).map (crossZeroWindow 0) =
            ((forwardReverseTwoSidedTrajMeasure π K Kr).map crossPair).map
              (pairWindow (α := α)) := by
              rw [Measure.map_map measurable_pairWindow hcrossPair, hcrossfun]
        _ = ((forwardReverseTwoSidedTrajMeasure π K Kr).map forwardPair).map
              (pairWindow (α := α)) := by
              rw [hbalance.forwardReverseTwoSidedTrajMeasure_adjacent_shift hstationary]
        _ = (forwardReverseTwoSidedTrajMeasure π K Kr).map (forwardWindow 0) := by
              symm
              rw [Measure.map_map measurable_pairWindow hforwardPair, hforwardfun]
  | succ n ih =>
      calc
        (forwardReverseTwoSidedTrajMeasure π K Kr).map (crossZeroWindow (n + 1)) =
            ((forwardReverseTwoSidedTrajMeasure π K Kr).map (crossZeroWindow n) ⊗ₘ
              (K ∘ₖ Kernel.deterministic
                (fun w : Fin (n + 2) → α => w (Fin.last (n + 1)))
                (measurable_pi_apply _))).map
                  (fun p => snocWindow p.1 p.2) := by
                    exact forwardReverseTwoSidedTrajMeasure_crossWindow_succ_factor n
        _ = ((forwardReverseTwoSidedTrajMeasure π K Kr).map (forwardWindow n) ⊗ₘ
              (K ∘ₖ Kernel.deterministic
                (fun w : Fin (n + 2) → α => w (Fin.last (n + 1)))
                (measurable_pi_apply _))).map
                  (fun p => snocWindow p.1 p.2) := by
                    rw [ih]
        _ = (forwardReverseTwoSidedTrajMeasure π K Kr).map (forwardWindow (n + 1)) := by
                    symm
                    exact forwardReverseTwoSidedTrajMeasure_forwardWindow_succ_factor n

end

end AppliedModelingLib.Probability.Queueing

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory Preorder

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- Reverse the coordinate order of a finite path window. -/
def reverseWindow (n : ℕ) (w : Fin (n + 1) → α) : Fin (n + 1) → α :=
  fun i => w i.rev

theorem measurable_reverseWindow (n : ℕ) :
    Measurable (reverseWindow (α := α) n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply i.rev

/-- The temporal reversal of the first `n + 1` coordinates of a natural-time path. -/
def reverseNatPrefix (n : ℕ) (x : ℕ → α) : Fin (n + 1) → α :=
  reverseWindow n (natPrefix n x)

/-- The same reversed prefix written in the arithmetic indexing form used by
the trajectory-block statement. -/
def reverseNatPrefixSub (n : ℕ) (x : ℕ → α) : Fin (n + 1) → α :=
  fun i => x (n - i.1)

theorem reverseNatPrefix_eq_sub (n : ℕ) :
    reverseNatPrefix (α := α) n = reverseNatPrefixSub n := by
  funext x i
  simp only [reverseNatPrefix, reverseNatPrefixSub, reverseWindow, natPrefix,
    Fin.val_rev]
  congr 1
  omega

theorem measurable_reverseNatPrefix (n : ℕ) :
    Measurable (reverseNatPrefix (α := α) n) := by
  exact (measurable_reverseWindow n).comp (measurable_natPrefix n)

theorem reverseWindow_snoc (n : ℕ) (w : Fin (n + 1) → α) (a : α) :
    reverseWindow (n + 1) (snocWindow w a) =
      prependWindow a (reverseWindow n w) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [reverseWindow, snocWindow, prependWindow, Fin.rev_zero]
  · simp [reverseWindow, snocWindow, prependWindow, Fin.rev_succ]

theorem reverseNatPrefix_succ (n : ℕ) (x : ℕ → α) :
    reverseNatPrefix (n + 1) x =
      prependWindow (x (n + 1)) (reverseNatPrefix n x) := by
  simp only [reverseNatPrefix, natPrefix_succ, reverseWindow_snoc]

theorem prefixFirst_reverseWindow (n : ℕ) (w : Fin (n + 1) → α) :
    prefixFirst (reverseWindow n w) = prefixLast n w := by
  simp [prefixFirst, prefixLast, reverseWindow, Fin.rev_zero]

/-- After pair balance, prepending one `Kr` transition to a forward `K`
prefix has the law of the next forward `K` prefix. -/
theorem stationaryTrajMeasure_prepend_reverse_eq_forwardPrefix_succ
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr]
    (hbalance : Kernel.ReversePairBalance π K Kr)
    (hstationary : Kernel.Invariant K π) (n : ℕ) :
    (((stationaryTrajMeasure π K).map (natPrefix n) ⊗ₘ
      (Kr ∘ₖ Kernel.deterministic (prefixFirst (α := α) (n := n))
        (measurable_prefixFirst n))).map
        (fun p => prependWindow p.2 p.1)) =
      (stationaryTrajMeasure π K).map (natPrefix (n + 1)) := by
  calc
    (((stationaryTrajMeasure π K).map (natPrefix n) ⊗ₘ
      (Kr ∘ₖ Kernel.deterministic (prefixFirst (α := α) (n := n))
        (measurable_prefixFirst n))).map
        (fun p => prependWindow p.2 p.1)) =
        (forwardReverseTwoSidedTrajMeasure π K Kr).map (crossZeroWindow n) := by
          symm
          simpa [prefixReverseToCross] using
            (forwardReverseTwoSidedTrajMeasure_crossWindow_law
              (π := π) (K := K) (Kr := Kr) n)
    _ = (forwardReverseTwoSidedTrajMeasure π K Kr).map (forwardWindow n) := by
          exact hbalance.forwardReverseTwoSidedTrajMeasure_crossZeroWindow_shift
            hstationary n
    _ = (stationaryTrajMeasure π K).map (natPrefix (n + 1)) := by
          exact forwardReverseTwoSidedTrajMeasure_forwardWindow_law
            (π := π) (K := K) (Kr := Kr) n

/-- Reversing a one-step-longer `Kr` prefix means prepending its newly drawn
state to the previously reversed prefix.  The `Kr` transition is evaluated at
the first coordinate of that reversed prefix. -/
theorem stationaryTrajMeasure_reverseNatPrefix_succ
    {π : Measure α} [IsProbabilityMeasure π] {Kr : Kernel α α}
    [IsMarkovKernel Kr] (n : ℕ) :
    (stationaryTrajMeasure π Kr).map (reverseNatPrefix (α := α) (n + 1)) =
      (((stationaryTrajMeasure π Kr).map (reverseNatPrefix n) ⊗ₘ
        (Kr ∘ₖ Kernel.deterministic (prefixFirst (α := α) (n := n))
          (measurable_prefixFirst n))).map
          (fun p => prependWindow p.2 p.1)) := by
  have htrajprob : IsProbabilityMeasure (stationaryTrajMeasure π Kr) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure (stationaryTrajMeasure π Kr) := htrajprob
  let μ : Measure (Fin (n + 1) → α) :=
    (stationaryTrajMeasure π Kr).map (natPrefix n)
  have hμ : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact Measure.isProbabilityMeasure_map (measurable_natPrefix n).aemeasurable
  letI : IsProbabilityMeasure μ := hμ
  let f : (Fin (n + 1) → α) → Fin (n + 1) → α := reverseWindow n
  let g : (Fin (n + 1) → α) → α := prefixFirst
  let h : (Fin (n + 1) → α) × α → (Fin (n + 1) → α) × α :=
    fun p => (f p.1, p.2)
  have hf : Measurable f := measurable_reverseWindow n
  have hg : Measurable g := measurable_prefixFirst n
  have hh : Measurable h := hf.comp measurable_fst |>.prodMk measurable_snd
  have hprepend : Measurable (fun p : (Fin (n + 1) → α) × α =>
      prependWindow p.2 p.1) :=
    (measurable_prependWindow (α := α) (n + 1)).comp
      (measurable_snd.prodMk measurable_fst)
  have hkernel :
      Kr ∘ₖ Kernel.deterministic (prefixLast (α := α) n)
        (measurable_prefixLast n) =
      Kr ∘ₖ Kernel.deterministic (g ∘ f) (hg.comp hf) := by
    ext w s hs
    simp [f, g, Kernel.comp_deterministic_eq_comap, Kernel.comap_apply,
      Function.comp_apply, prefixFirst_reverseWindow]
  have htransport :
      ((μ ⊗ₘ (Kr ∘ₖ Kernel.deterministic (g ∘ f) (hg.comp hf))).map h) =
        (μ.map f) ⊗ₘ (Kr ∘ₖ Kernel.deterministic g hg) := by
    exact Measure.compProd_map_through μ Kr f hf g hg
  have hsnocreverse :
      (reverseWindow (n + 1)) ∘ (fun p : (Fin (n + 1) → α) × α =>
        snocWindow p.1 p.2) =
      (fun p : (Fin (n + 1) → α) × α => prependWindow p.2 p.1) ∘ h := by
    funext p
    exact reverseWindow_snoc n p.1 p.2
  have hprefix :
      ((stationaryTrajMeasure π Kr).map (natPrefix n)).map f =
        (stationaryTrajMeasure π Kr).map (reverseNatPrefix n) := by
    rw [Measure.map_map hf (measurable_natPrefix n)]
    rfl
  calc
    (stationaryTrajMeasure π Kr).map (reverseNatPrefix (n + 1)) =
        ((stationaryTrajMeasure π Kr).map (natPrefix (n + 1))).map
          (reverseWindow (n + 1)) := by
            rw [Measure.map_map (measurable_reverseWindow (n + 1))
              (measurable_natPrefix (n + 1))]
            rfl
    _ = ((((stationaryTrajMeasure π Kr).map (natPrefix n) ⊗ₘ
          (Kr ∘ₖ Kernel.deterministic (prefixLast (α := α) n)
            (measurable_prefixLast n))).map
              (fun p => snocWindow p.1 p.2)).map
                (reverseWindow (n + 1))) := by
            simpa [prefixLast] using congrArg
              (fun ν => ν.map (reverseWindow (n + 1)))
              (stationaryTrajMeasure_natPrefix_succ (π := π) (K := Kr) n)
    _ = (((stationaryTrajMeasure π Kr).map (natPrefix n) ⊗ₘ
          (Kr ∘ₖ Kernel.deterministic (prefixLast (α := α) n)
            (measurable_prefixLast n))).map h).map
              (fun p => prependWindow p.2 p.1) := by
            rw [Measure.map_map (measurable_reverseWindow (n + 1))
              (measurable_snocWindow (n + 1)), Measure.map_map hprepend hh,
              hsnocreverse]
    _ = (((stationaryTrajMeasure π Kr).map (natPrefix n) ⊗ₘ
          (Kr ∘ₖ Kernel.deterministic (g ∘ f) (hg.comp hf))).map h).map
              (fun p => prependWindow p.2 p.1) := by
            rw [hkernel]
    _ = (((stationaryTrajMeasure π Kr).map (natPrefix n)).map f ⊗ₘ
          (Kr ∘ₖ Kernel.deterministic g hg)).map
              (fun p => prependWindow p.2 p.1) := by
            exact congrArg (fun ν => ν.map (fun p => prependWindow p.2 p.1))
              htransport
    _ = (((stationaryTrajMeasure π Kr).map (reverseNatPrefix n) ⊗ₘ
          (Kr ∘ₖ Kernel.deterministic (prefixFirst (α := α) (n := n))
            (measurable_prefixFirst n))).map
              (fun p => prependWindow p.2 p.1)) := by
            rw [hprefix]

/-- The reversed one-point prefix has the common initial law, independently
of which Markov kernel generates the trajectory. -/
theorem stationaryTrajMeasure_reverseNatPrefix_zero
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] :
    (stationaryTrajMeasure π Kr).map (reverseNatPrefix (α := α) 0) =
      (stationaryTrajMeasure π K).map (natPrefix 0) := by
  let singleton : α → Fin 1 → α := fun a _ => a
  have hsingleton : Measurable singleton := by
    apply measurable_pi_lambda
    intro i
    exact measurable_id
  have hrev : reverseNatPrefix (α := α) 0 =
      singleton ∘ (fun x : ℕ → α => x 0) := by
    funext x i
    fin_cases i
    rfl
  have hforward : natPrefix (α := α) 0 =
      singleton ∘ (fun x : ℕ → α => x 0) := by
    funext x i
    fin_cases i
    rfl
  calc
    (stationaryTrajMeasure π Kr).map (reverseNatPrefix (α := α) 0) =
        ((stationaryTrajMeasure π Kr).map (fun x : ℕ → α => x 0)).map singleton := by
          rw [Measure.map_map hsingleton (measurable_pi_apply 0), hrev]
    _ = π.map singleton := by
          rw [stationaryTrajMeasure_zero_marginal]
    _ = ((stationaryTrajMeasure π K).map (fun x : ℕ → α => x 0)).map singleton := by
          rw [stationaryTrajMeasure_zero_marginal]
    _ = (stationaryTrajMeasure π K).map (natPrefix 0) := by
          rw [Measure.map_map hsingleton (measurable_pi_apply 0), hforward]

/-- Finite-dimensional time reversal: a stationary `Kr` trajectory, read in
reverse order on its first `n + 1` states, has the same law as a forward
stationary `K` prefix. -/
theorem Kernel.ReversePairBalance.stationaryTrajMeasure_reverseNatPrefix_eq
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr]
    (hbalance : Kernel.ReversePairBalance π K Kr)
    (hstationary : Kernel.Invariant K π) (n : ℕ) :
    (stationaryTrajMeasure π Kr).map (reverseNatPrefix (α := α) n) =
      (stationaryTrajMeasure π K).map (natPrefix n) := by
  induction n with
  | zero =>
      exact stationaryTrajMeasure_reverseNatPrefix_zero (π := π) (K := K) (Kr := Kr)
  | succ n ih =>
      calc
        (stationaryTrajMeasure π Kr).map (reverseNatPrefix (α := α) (n + 1)) =
            (((stationaryTrajMeasure π Kr).map (reverseNatPrefix n) ⊗ₘ
              (Kr ∘ₖ Kernel.deterministic (prefixFirst (α := α) (n := n))
                (measurable_prefixFirst n))).map
                (fun p => prependWindow p.2 p.1)) := by
                  exact stationaryTrajMeasure_reverseNatPrefix_succ (π := π) (Kr := Kr) n
        _ = (((stationaryTrajMeasure π K).map (natPrefix n) ⊗ₘ
              (Kr ∘ₖ Kernel.deterministic (prefixFirst (α := α) (n := n))
                (measurable_prefixFirst n))).map
                (fun p => prependWindow p.2 p.1)) := by
                  rw [ih]
        _ = (stationaryTrajMeasure π K).map (natPrefix (n + 1)) := by
                  exact stationaryTrajMeasure_prepend_reverse_eq_forwardPrefix_succ
                    hbalance hstationary n

/-- Arithmetic-indexed form of finite-dimensional time reversal. -/
theorem Kernel.ReversePairBalance.stationaryTrajMeasure_reverseNatPrefixSub_eq
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr]
    (hbalance : Kernel.ReversePairBalance π K Kr)
    (hstationary : Kernel.Invariant K π) (n : ℕ) :
    (stationaryTrajMeasure π Kr).map (reverseNatPrefixSub (α := α) n) =
      (stationaryTrajMeasure π K).map (natPrefix n) := by
  rw [← reverseNatPrefix_eq_sub]
  exact hbalance.stationaryTrajMeasure_reverseNatPrefix_eq hstationary n

end

end AppliedModelingLib.Probability.Queueing
