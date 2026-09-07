import AppliedModelingLib.Queueing.MM1.TwoSided.ReverseFiniteWindows

/-!
# Full two-sided stationarity from forward/reverse balance

This self-contained staging module develops finite mixed integer windows for
the forward/reverse construction, upgrades them to all finite integer
intervals, and closes the proof with the two-sided cylinder criterion.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory Preorder

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- Marginally, the reverse tail in the source construction is the stationary
trajectory for the supplied reverse kernel. -/
theorem forwardReverseTwoSidedSourceMeasure_map_reverse
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] :
    (forwardReverseTwoSidedSourceMeasure π K Kr).map Prod.snd =
      stationaryTrajMeasure π Kr := by
  have hprob : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := hprob
  calc
    (forwardReverseTwoSidedSourceMeasure π K Kr).map Prod.snd =
        conditionalReverseTailKernel Kr ∘ₘ (stationaryTrajMeasure π K) := by
          change (forwardReverseTwoSidedSourceMeasure π K Kr).snd = _
          unfold forwardReverseTwoSidedSourceMeasure
          rw [Measure.snd_compProd]
    _ = conditionalHomogeneousTrajKernel Kr ∘ₘ
          ((stationaryTrajMeasure π K).map (fun x : ℕ → α => x 0)) := by
          unfold conditionalReverseTailKernel
          rw [← Measure.comp_assoc, Measure.deterministic_comp_eq_map]
    _ = conditionalHomogeneousTrajKernel Kr ∘ₘ π := by
          rw [stationaryTrajMeasure_zero_marginal]
    _ = stationaryTrajMeasure π Kr := by
          exact conditionalHomogeneousTrajKernel_comp_eq_stationaryTrajMeasure

/-- The strictly negative coordinates, listed chronologically from time `-m`
through time `-1`. -/
def reverseStrictPrefix (m : ℕ)
    (z : (ℕ → α) × (ℕ → α)) : Fin m → α :=
  fun i => z.2 (m - i.1)

theorem measurable_reverseStrictPrefix (m : ℕ) :
    Measurable (reverseStrictPrefix (α := α) m) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply _).comp measurable_snd

/-- The strictly positive part `X_1, ..., X_n` of the forward branch. -/
def futureStrictPrefix (n : ℕ) (z : (ℕ → α) × (ℕ → α)) : Fin n → α :=
  fun i => z.1 (i.1 + 1)

theorem measurable_futureStrictPrefix (n : ℕ) :
    Measurable (futureStrictPrefix (α := α) n) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply _).comp measurable_fst

/-- A chronological finite block `X_{-m}, ..., X_n`. -/
def twoSidedWindow (m n : ℕ) (x : ℤ → α) : Fin ((m + 1) + n) → α :=
  fun i => x ((i.1 : ℤ) - m)

theorem measurable_twoSidedWindow (m n : ℕ) :
    Measurable (twoSidedWindow (α := α) m n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

/-- The nonpositive part `X_{-m}, ..., X_0` of a paired forward/reverse path. -/
def pairedPastWindow (m : ℕ) (z : (ℕ → α) × (ℕ → α)) : Fin (m + 1) → α :=
  snocWindow (reverseStrictPrefix m z) (z.1 0)

theorem measurable_pairedPastWindow (m : ℕ) :
    Measurable (pairedPastWindow (α := α) m) := by
  exact (measurable_snocWindow (α := α) m).comp
    ((measurable_reverseStrictPrefix m).prodMk
      ((measurable_pi_apply 0).comp measurable_fst))

/-- The paired-path realization split into past and strict-future pieces. -/
def pairedTwoSidedWindow (m n : ℕ) (z : (ℕ → α) × (ℕ → α)) :
    Fin ((m + 1) + n) → α :=
  Fin.append (pairedPastWindow m z) (futureStrictPrefix n z)

theorem measurable_pairedTwoSidedWindow (m n : ℕ) :
    Measurable (pairedTwoSidedWindow (α := α) m n) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa [pairedTwoSidedWindow] using
      (measurable_pi_apply _).comp (measurable_pairedPastWindow m)
  · simpa [pairedTwoSidedWindow] using
      (measurable_pi_apply _).comp (measurable_futureStrictPrefix n)

theorem twoSidedWindow_spliceForwardReverse (m n : ℕ)
    (z : (ℕ → α) × (ℕ → α)) :
    twoSidedWindow m n (spliceForwardReverse z) = pairedTwoSidedWindow m n z := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [pairedTwoSidedWindow, Fin.append_left]
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [pairedPastWindow, snocWindow, twoSidedWindow, spliceForwardReverse]
    · simp only [pairedPastWindow, snocWindow, Fin.snoc_castSucc]
      change (spliceForwardReverse z) ((k.1 : ℤ) - m) = z.2 (m - k.1)
      have hk : k.1 < m := k.isLt
      rw [show (k.1 : ℤ) - m = Int.negSucc (m - k.1 - 1) by omega]
      simp only [spliceForwardReverse]
      exact congrArg z.2
        (Nat.sub_add_cancel (Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hk)))
  · simp only [pairedTwoSidedWindow, Fin.append_right]
    change (spliceForwardReverse z) (((m + 1 + j.1 : ℕ) : ℤ) - m) = z.1 (j.1 + 1)
    have hindex : ((m + 1 + j.1 : ℕ) : ℤ) - m = (j.1 + 1 : ℕ) := by
      omega
    rw [hindex]
    rfl

/-- Extract the chronological strict-past block from a reverse tail. -/
def reverseStrictMap (m : ℕ) (r : ℕ → α) : Fin m → α :=
  fun i => r (m - i.1)

theorem measurable_reverseStrictMap (m : ℕ) :
    Measurable (reverseStrictMap (α := α) m) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

theorem reverseStrictPrefix_eq_map (m : ℕ) :
    reverseStrictPrefix (α := α) m = reverseStrictMap m ∘ Prod.snd := by
  rfl

/-- The mixed finite window together with its next forward state. -/
def sourceTwoSidedNext (m n : ℕ) (z : (ℕ → α) × (ℕ → α)) :
    (Fin ((m + 1) + n) → α) × α :=
  (pairedTwoSidedWindow m n z, z.1 (n + 1))

theorem measurable_sourceTwoSidedNext (m n : ℕ) :
    Measurable (sourceTwoSidedNext (α := α) m n) := by
  exact (measurable_pairedTwoSidedWindow m n).prodMk
    ((measurable_pi_apply _).comp measurable_fst)

theorem twoSidedWindow_succ (m n : ℕ) (x : ℤ → α) :
    twoSidedWindow m (n + 1) x =
      snocWindow (twoSidedWindow m n x) (x (n + 1 : ℕ)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · unfold twoSidedWindow snocWindow
    simp only [Fin.snoc]
    split
    · rename_i h
      simp at h
    · change x (((m + 1 + n : ℕ) : ℤ) - m) = x (n + 1 : ℕ)
      congr 1
      omega
  · unfold twoSidedWindow snocWindow
    rw [Fin.snoc_castSucc]
    simp only [Fin.val_castSucc]

theorem pairedTwoSidedWindow_succ (m n : ℕ)
    (z : (ℕ → α) × (ℕ → α)) :
    pairedTwoSidedWindow m (n + 1) z =
      snocWindow (pairedTwoSidedWindow m n z) (z.1 (n + 1)) := by
  rw [← twoSidedWindow_spliceForwardReverse m (n + 1) z,
    ← twoSidedWindow_spliceForwardReverse m n z, twoSidedWindow_succ]
  rfl

theorem sourceTwoSidedNext_factor (m n : ℕ)
    (z : (ℕ → α) × (ℕ → α)) :
    sourceTwoSidedNext m n z =
      (pairedTwoSidedWindow m n z, z.1 (n + 1)) := by
  rfl

private theorem mixed_compProd_prodMkRight_eq_prod
    {β γ δ : Type*} [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (A : Kernel β γ) (B : Kernel β δ) [IsMarkovKernel A] [IsMarkovKernel B] :
    A ⊗ₖ B.prodMkRight γ = A ×ₖ B := by
  ext x s hs
  rw [Kernel.compProd_apply hs, Kernel.prod_apply' A B x hs]
  simp only [Kernel.prodMkRight_apply]

private def mixed_swapBranchOutputs
    {β γ δ : Type*} (p : (β × γ) × δ) : (β × δ) × γ :=
  ((p.1.1, p.2), p.1.2)

private theorem measurable_mixed_swapBranchOutputs
    {β γ δ : Type*} [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ] :
    Measurable (mixed_swapBranchOutputs (β := β) (γ := γ) (δ := δ)) := by
  exact ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
    (measurable_snd.comp measurable_fst)

private def mixed_swapInnerBranches
    {β γ δ : Type*} (p : β × (γ × δ)) : β × (δ × γ) :=
  (p.1, (p.2.2, p.2.1))

private theorem measurable_mixed_swapInnerBranches
    {β γ δ : Type*} [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ] :
    Measurable (mixed_swapInnerBranches (β := β) (γ := γ) (δ := δ)) := by
  exact measurable_fst.prodMk
    ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))

/-- Conditional Fubini for a forward next-state branch and an arbitrary
strict-past branch drawn from their common finite-prefix input. -/
private theorem mixed_conditional_fubini_branches
    {β γ δ : Type*} [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    {μ : Measure β} [IsProbabilityMeasure μ]
    (A : Kernel β γ) (B : Kernel β δ) [IsMarkovKernel A] [IsMarkovKernel B] :
    ((μ ⊗ₘ A) ⊗ₘ B.prodMkRight γ).map
        (mixed_swapBranchOutputs (β := β) (γ := γ) (δ := δ)) =
      (μ ⊗ₘ B) ⊗ₘ A.prodMkRight δ := by
  have hA : (μ ⊗ₘ A) ⊗ₘ B.prodMkRight γ =
      (μ ⊗ₘ (A ×ₖ B)).map MeasurableEquiv.prodAssoc.symm := by
    calc
      (μ ⊗ₘ A) ⊗ₘ B.prodMkRight γ =
          (μ ⊗ₘ (A ⊗ₖ B.prodMkRight γ)).map MeasurableEquiv.prodAssoc.symm := by
            symm
            exact Measure.compProd_assoc
      _ = (μ ⊗ₘ (A ×ₖ B)).map MeasurableEquiv.prodAssoc.symm := by
            rw [mixed_compProd_prodMkRight_eq_prod]
  have hB : (μ ⊗ₘ B) ⊗ₘ A.prodMkRight δ =
      (μ ⊗ₘ (B ×ₖ A)).map MeasurableEquiv.prodAssoc.symm := by
    calc
      (μ ⊗ₘ B) ⊗ₘ A.prodMkRight δ =
          (μ ⊗ₘ (B ⊗ₖ A.prodMkRight δ)).map MeasurableEquiv.prodAssoc.symm := by
            symm
            exact Measure.compProd_assoc
      _ = (μ ⊗ₘ (B ×ₖ A)).map MeasurableEquiv.prodAssoc.symm := by
            rw [mixed_compProd_prodMkRight_eq_prod]
  have hswap : (μ ⊗ₘ (A ×ₖ B)).map
      (mixed_swapInnerBranches (β := β) (γ := γ) (δ := δ)) = μ ⊗ₘ (B ×ₖ A) := by
    calc
      (μ ⊗ₘ (A ×ₖ B)).map
          (mixed_swapInnerBranches (β := β) (γ := γ) (δ := δ)) =
          (μ ⊗ₘ (A ×ₖ B)).map (Prod.map id Prod.swap) := by rfl
      _ = μ ⊗ₘ (A ×ₖ B).map Prod.swap := by
            rw [← Measure.compProd_map measurable_swap]
      _ = μ ⊗ₘ (B ×ₖ A) := by rw [Kernel.map_prod_swap]
  have hcompat :
      (mixed_swapBranchOutputs (β := β) (γ := γ) (δ := δ) ∘
        MeasurableEquiv.prodAssoc.symm) =
        MeasurableEquiv.prodAssoc.symm ∘
          mixed_swapInnerBranches (β := β) (γ := γ) (δ := δ) := by
    funext q
    rcases q with ⟨x, y, z⟩
    rfl
  calc
    ((μ ⊗ₘ A) ⊗ₘ B.prodMkRight γ).map
        (mixed_swapBranchOutputs (β := β) (γ := γ) (δ := δ)) =
        ((μ ⊗ₘ (A ×ₖ B)).map MeasurableEquiv.prodAssoc.symm).map
          (mixed_swapBranchOutputs (β := β) (γ := γ) (δ := δ)) := by rw [hA]
    _ = (μ ⊗ₘ (A ×ₖ B)).map
          (mixed_swapBranchOutputs (β := β) (γ := γ) (δ := δ) ∘
            MeasurableEquiv.prodAssoc.symm) := by
          rw [Measure.map_map measurable_mixed_swapBranchOutputs
            MeasurableEquiv.prodAssoc.symm.measurable]
    _ = (μ ⊗ₘ (A ×ₖ B)).map
          (MeasurableEquiv.prodAssoc.symm ∘
            mixed_swapInnerBranches (β := β) (γ := γ) (δ := δ)) := by rw [hcompat]
    _ = ((μ ⊗ₘ (A ×ₖ B)).map
          (mixed_swapInnerBranches (β := β) (γ := γ) (δ := δ))).map
            MeasurableEquiv.prodAssoc.symm := by
          symm
          rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
            measurable_mixed_swapInnerBranches]
    _ = (μ ⊗ₘ (B ×ₖ A)).map MeasurableEquiv.prodAssoc.symm := by rw [hswap]
    _ = (μ ⊗ₘ B) ⊗ₘ A.prodMkRight δ := by rw [hB]

/-- Reassemble a finite past branch and a finite forward prefix into temporal
order `X_{-m},...,X_n`. -/
def mixedBranchesToWindow (m n : ℕ)
    (p : (Fin (n + 1) → α) × (Fin m → α)) : Fin ((m + 1) + n) → α :=
  Fin.append (snocWindow p.2 (p.1 0))
    (fun i => p.1 ⟨i.1 + 1, by omega⟩)

theorem measurable_mixedBranchesToWindow (m n : ℕ) :
    Measurable (mixedBranchesToWindow (α := α) m n) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa [mixedBranchesToWindow, snocWindow] using
        (measurable_pi_apply 0).comp measurable_fst
    · simpa [mixedBranchesToWindow, snocWindow] using
        (measurable_pi_apply k).comp measurable_snd
  · simpa [mixedBranchesToWindow] using
      (measurable_pi_apply (⟨j.1 + 1, by omega⟩ : Fin (n + 1))).comp measurable_fst

theorem mixedBranchesToWindow_source (m n : ℕ)
    (z : (ℕ → α) × (ℕ → α)) :
    mixedBranchesToWindow m n (sourcePrefix n z, reverseStrictPrefix m z) =
      pairedTwoSidedWindow m n z := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [mixedBranchesToWindow, pairedTwoSidedWindow, pairedPastWindow,
        snocWindow, sourcePrefix, natPrefix]
    · simp [mixedBranchesToWindow, pairedTwoSidedWindow, pairedPastWindow,
        snocWindow, sourcePrefix, natPrefix, reverseStrictPrefix]
  · simp [mixedBranchesToWindow, pairedTwoSidedWindow, futureStrictPrefix,
      sourcePrefix, natPrefix]

def mixedBranchesNextToWindowNext (m n : ℕ)
    (p : ((Fin (n + 1) → α) × (Fin m → α)) × α) :
    (Fin ((m + 1) + n) → α) × α :=
  (mixedBranchesToWindow m n p.1, p.2)

theorem measurable_mixedBranchesNextToWindowNext (m n : ℕ) :
    Measurable (mixedBranchesNextToWindowNext (α := α) m n) := by
  exact (measurable_mixedBranchesToWindow m n).comp measurable_fst |>.prodMk
    measurable_snd

theorem mixedBranchesNextToWindowNext_source (m n : ℕ)
    (z : (ℕ → α) × (ℕ → α)) :
    mixedBranchesNextToWindowNext m n
      (mixed_swapBranchOutputs
        ((sourcePrefix n z, z.1 (n + 1)), reverseStrictPrefix m z)) =
      sourceTwoSidedNext m n z := by
  apply Prod.ext
  · exact mixedBranchesToWindow_source m n z
  · rfl

/-- The final coordinate of a mixed window has natural index `m + n`. -/
def mixedWindowLast (m n : ℕ) : Fin ((m + 1) + n) :=
  ⟨m + n, by omega⟩

theorem mixedBranchesToWindow_last (m n : ℕ)
    (p : (Fin (n + 1) → α) × (Fin m → α)) :
    mixedBranchesToWindow m n p (mixedWindowLast m n) = prefixLast n p.1 := by
  cases n with
  | zero =>
      have hidx : mixedWindowLast m 0 = Fin.last m := by
        apply Fin.ext
        simp [mixedWindowLast]
      rw [hidx]
      have hlast : (Fin.last m : Fin ((m + 1) + 0)) =
          Fin.castAdd 0 (Fin.last m) := by
        apply Fin.ext
        rfl
      rw [hlast]
      unfold mixedBranchesToWindow
      rw [Fin.append_left]
      simp [snocWindow, prefixLast]
  | succ n =>
      have hidx : mixedWindowLast m (n + 1) =
          Fin.natAdd (m + 1) (Fin.last n) := by
        apply Fin.ext
        simp [mixedWindowLast]
        omega
      rw [hidx]
      unfold mixedBranchesToWindow
      rw [Fin.append_right]
      change p.1 ⟨(Fin.last n).1 + 1, by omega⟩ = p.1 (Fin.last (n + 1))
      congr 1

/-- A source-level triple: forward prefix, next forward state, and all
strict-past coordinates. -/
def sourceMixedTriple (m n : ℕ) (z : (ℕ → α) × (ℕ → α)) :
    ((Fin (n + 1) → α) × α) × (Fin m → α) :=
  ((sourcePrefix n z, z.1 (n + 1)), reverseStrictPrefix m z)

theorem measurable_sourceMixedTriple (m n : ℕ) :
    Measurable (sourceMixedTriple (α := α) m n) := by
  exact (((measurable_sourcePrefix n).prodMk
    ((measurable_pi_apply _).comp measurable_fst)).prodMk
      (measurable_reverseStrictPrefix m))

/-- The forward prefix-next branch and the finite strict-past branch are
conditionally independent given the forward prefix's first coordinate. -/
theorem forwardReverseTwoSidedSourceMeasure_prefix_next_reverseStrict
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] (m n : ℕ) :
    (forwardReverseTwoSidedSourceMeasure π K Kr).map (sourceMixedTriple m n) =
      (((stationaryTrajMeasure π K).map (natPrefix n) ⊗ₘ
        (K ∘ₖ Kernel.deterministic (prefixLast (α := α) n)
          (measurable_prefixLast n))) ⊗ₘ
        ((conditionalHomogeneousTrajKernel Kr).map (reverseStrictMap (α := α) m) ∘ₖ
          Kernel.deterministic (prefixFirst (α := α) (n := n))
            (measurable_prefixFirst (α := α) n)).prodMkRight α) := by
  have hprob : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := hprob
  let μ : Measure (ℕ → α) := stationaryTrajMeasure π K
  let f : (ℕ → α) → (Fin (n + 1) → α) × α :=
    fun x => (natPrefix n x, x (n + 1))
  let r : (ℕ → α) → Fin m → α := reverseStrictMap m
  let D : Kernel α (Fin m → α) := (conditionalHomogeneousTrajKernel Kr).map r
  let g : ((Fin (n + 1) → α) × α) → α :=
    fun p => prefixFirst p.1
  let e : ((ℕ → α) × (ℕ → α)) → (ℕ → α) × (Fin m → α) :=
    Prod.map id r
  have hf : Measurable f := (measurable_natPrefix n).prodMk (measurable_pi_apply _)
  have hr : Measurable r := measurable_reverseStrictMap m
  have hg : Measurable g := (measurable_prefixFirst (α := α) n).comp measurable_fst
  have he : Measurable e := measurable_id.prodMap hr
  have hpair : Measurable (fun p : (ℕ → α) × (Fin m → α) => (f p.1, p.2)) :=
    hf.comp measurable_fst |>.prodMk measurable_snd
  have hgf : g ∘ f = fun x : ℕ → α => x 0 := by
    funext x
    rfl
  have hzero : Measurable (fun x : ℕ → α => x 0) := measurable_pi_apply _
  have htailmap :
      (conditionalReverseTailKernel Kr).map r =
        D ∘ₖ Kernel.deterministic (fun x : ℕ → α => x 0) hzero := by
    unfold conditionalReverseTailKernel
    rw [Kernel.map_comp]
  have hDcomp :
      D ∘ₖ Kernel.deterministic (fun x : ℕ → α => x 0) hzero =
        D ∘ₖ Kernel.deterministic (g ∘ f) (hg.comp hf) := by
    exact congrArg (fun L => D ∘ₖ L)
      (Kernel.deterministic_congr hgf.symm)
  have hforward : μ.map f =
      (μ.map (natPrefix n) ⊗ₘ
        (K ∘ₖ Kernel.deterministic (prefixLast (α := α) n)
          (measurable_prefixLast n))) := by
    simpa [μ, f, prefixLast] using
      (stationaryTrajMeasure_natPrefix_next (π := π) (K := K) n)
  let B : Kernel (Fin (n + 1) → α) (Fin m → α) :=
    D ∘ₖ Kernel.deterministic (prefixFirst (α := α) (n := n))
      (measurable_prefixFirst (α := α) n)
  have hBprod : D ∘ₖ Kernel.deterministic g hg = B.prodMkRight α := by
    ext p s hs
    simp [g, B, Kernel.comp_deterministic_eq_comap, Kernel.comap_apply,
      Kernel.prodMkRight_apply]
  calc
    (forwardReverseTwoSidedSourceMeasure π K Kr).map (sourceMixedTriple m n) =
        ((forwardReverseTwoSidedSourceMeasure π K Kr).map e).map
          (fun p => (f p.1, p.2)) := by
          symm
          rw [Measure.map_map hpair he]
          rfl
    _ = (μ ⊗ₘ (conditionalReverseTailKernel Kr).map r).map
          (fun p => (f p.1, p.2)) := by
          unfold forwardReverseTwoSidedSourceMeasure
          rw [← Measure.compProd_map (μ := μ) (κ := conditionalReverseTailKernel Kr) hr]
    _ = (μ ⊗ₘ (D ∘ₖ Kernel.deterministic
          (fun x : ℕ → α => x 0) hzero)).map
          (fun p => (f p.1, p.2)) := by
          rw [htailmap]
    _ = (μ ⊗ₘ (D ∘ₖ Kernel.deterministic (g ∘ f) (hg.comp hf))).map
          (fun p => (f p.1, p.2)) := by
          rw [hDcomp]
    _ = (μ.map f) ⊗ₘ (D ∘ₖ Kernel.deterministic g hg) := by
          exact Measure.compProd_map_through μ D f hf g hg
    _ = (((stationaryTrajMeasure π K).map (natPrefix n) ⊗ₘ
          (K ∘ₖ Kernel.deterministic (prefixLast (α := α) n)
            (measurable_prefixLast n))) ⊗ₘ
          ((conditionalHomogeneousTrajKernel Kr).map (reverseStrictMap (α := α) m) ∘ₖ
            Kernel.deterministic (prefixFirst (α := α) (n := n))
              (measurable_prefixFirst (α := α) n)).prodMkRight α) := by
          rw [hforward, hBprod]

def sourcePrefixReverseStrict (m n : ℕ) (z : (ℕ → α) × (ℕ → α)) :
    (Fin (n + 1) → α) × (Fin m → α) :=
  (sourcePrefix n z, reverseStrictPrefix m z)

theorem measurable_sourcePrefixReverseStrict (m n : ℕ) :
    Measurable (sourcePrefixReverseStrict (α := α) m n) := by
  exact (measurable_sourcePrefix n).prodMk (measurable_reverseStrictPrefix m)

/-- The finite forward prefix and finite strict-past branch have the expected
conditional-product law. -/
theorem forwardReverseTwoSidedSourceMeasure_prefix_reverseStrict
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] (m n : ℕ) :
    (forwardReverseTwoSidedSourceMeasure π K Kr).map
        (sourcePrefixReverseStrict m n) =
      ((stationaryTrajMeasure π K).map (natPrefix n) ⊗ₘ
        ((conditionalHomogeneousTrajKernel Kr).map (reverseStrictMap (α := α) m) ∘ₖ
          Kernel.deterministic (prefixFirst (α := α) (n := n))
            (measurable_prefixFirst (α := α) n))) := by
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
  let B : Kernel (Fin (n + 1) → α) (Fin m → α) :=
    (conditionalHomogeneousTrajKernel Kr).map (reverseStrictMap (α := α) m) ∘ₖ
      Kernel.deterministic (prefixFirst (α := α) (n := n))
        (measurable_prefixFirst (α := α) n)
  have hA : IsMarkovKernel A := by
    dsimp [A]
    infer_instance
  letI : IsMarkovKernel A := hA
  have hD : IsMarkovKernel
      ((conditionalHomogeneousTrajKernel Kr).map (reverseStrictMap (α := α) m)) := by
    exact Kernel.IsMarkovKernel.map _ (measurable_reverseStrictMap m)
  letI : IsMarkovKernel
      ((conditionalHomogeneousTrajKernel Kr).map (reverseStrictMap (α := α) m)) := hD
  have hB : IsMarkovKernel B := by
    dsimp [B]
    infer_instance
  letI : IsMarkovKernel B := hB
  let triple : ((ℕ → α) × (ℕ → α)) → ((Fin (n + 1) → α) × α) × (Fin m → α) :=
    sourceMixedTriple m n
  let qswap : ((Fin (n + 1) → α) × α) × (Fin m → α) →
      ((Fin (n + 1) → α) × (Fin m → α)) × α :=
    mixed_swapBranchOutputs
  let pair : ((ℕ → α) × (ℕ → α)) → (Fin (n + 1) → α) × (Fin m → α) :=
    sourcePrefixReverseStrict m n
  have htriple : Measurable triple := measurable_sourceMixedTriple m n
  have hqswap : Measurable qswap := measurable_mixed_swapBranchOutputs
  have hpair : Measurable pair := measurable_sourcePrefixReverseStrict m n
  have hpairfun : pair = Prod.fst ∘ qswap ∘ triple := by
    funext z
    rfl
  have htripleLaw :
      (forwardReverseTwoSidedSourceMeasure π K Kr).map triple =
        ((P ⊗ₘ A) ⊗ₘ B.prodMkRight α) := by
    simpa [P, A, B, triple] using
      (forwardReverseTwoSidedSourceMeasure_prefix_next_reverseStrict
        (π := π) (K := K) (Kr := Kr) m n)
  have hfubini :
      ((P ⊗ₘ A) ⊗ₘ B.prodMkRight α).map qswap =
        (P ⊗ₘ B) ⊗ₘ A.prodMkRight (Fin m → α) := by
    exact mixed_conditional_fubini_branches (μ := P) A B
  calc
    (forwardReverseTwoSidedSourceMeasure π K Kr).map pair =
        (((forwardReverseTwoSidedSourceMeasure π K Kr).map triple).map qswap).map Prod.fst := by
          rw [Measure.map_map measurable_fst hqswap,
            Measure.map_map (measurable_fst.comp hqswap) htriple]
          simpa only [Function.comp_assoc] using congrArg
            (fun h => (forwardReverseTwoSidedSourceMeasure π K Kr).map h) hpairfun
    _ = (((P ⊗ₘ A) ⊗ₘ B.prodMkRight α).map qswap).map Prod.fst := by
          rw [htripleLaw]
    _ = ((P ⊗ₘ B) ⊗ₘ A.prodMkRight (Fin m → α)).map Prod.fst := by
          rw [hfubini]
    _ = P ⊗ₘ B := by
          change ((P ⊗ₘ B) ⊗ₘ A.prodMkRight (Fin m → α)).fst = _
          rw [Measure.fst_compProd]
    _ = ((stationaryTrajMeasure π K).map (natPrefix n) ⊗ₘ
          ((conditionalHomogeneousTrajKernel Kr).map (reverseStrictMap (α := α) m) ∘ₖ
            Kernel.deterministic (prefixFirst (α := α) (n := n))
              (measurable_prefixFirst (α := α) n))) := by
          rfl

theorem measurable_mixedWindowLast (m n : ℕ) :
    Measurable (fun w : Fin ((m + 1) + n) → α => w (mixedWindowLast m n)) := by
  exact measurable_pi_apply _

/-- Every finite mixed window has the ordinary forward one-step recurrence:
once the entire past-through-present block is fixed, the next state is drawn
from `K` at its final coordinate. -/
theorem forwardReverseTwoSidedSourceMeasure_mixedWindow_next
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] (m n : ℕ) :
    (forwardReverseTwoSidedSourceMeasure π K Kr).map (sourceTwoSidedNext m n) =
      (forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedTwoSidedWindow m n) ⊗ₘ
        (K ∘ₖ Kernel.deterministic
          (fun w : Fin ((m + 1) + n) → α => w (mixedWindowLast m n))
          (measurable_mixedWindowLast m n)) := by
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
  let B : Kernel (Fin (n + 1) → α) (Fin m → α) :=
    (conditionalHomogeneousTrajKernel Kr).map (reverseStrictMap (α := α) m) ∘ₖ
      Kernel.deterministic (prefixFirst (α := α) (n := n))
        (measurable_prefixFirst (α := α) n)
  have hA : IsMarkovKernel A := by
    dsimp [A]
    infer_instance
  letI : IsMarkovKernel A := hA
  have hD : IsMarkovKernel
      ((conditionalHomogeneousTrajKernel Kr).map (reverseStrictMap (α := α) m)) := by
    exact Kernel.IsMarkovKernel.map _ (measurable_reverseStrictMap m)
  letI : IsMarkovKernel
      ((conditionalHomogeneousTrajKernel Kr).map (reverseStrictMap (α := α) m)) := hD
  have hB : IsMarkovKernel B := by
    dsimp [B]
    infer_instance
  letI : IsMarkovKernel B := hB
  let triple : ((ℕ → α) × (ℕ → α)) → ((Fin (n + 1) → α) × α) × (Fin m → α) :=
    sourceMixedTriple m n
  let qswap : ((Fin (n + 1) → α) × α) × (Fin m → α) →
      ((Fin (n + 1) → α) × (Fin m → α)) × α :=
    mixed_swapBranchOutputs
  let qwindow : ((Fin (n + 1) → α) × (Fin m → α)) × α →
      (Fin ((m + 1) + n) → α) × α :=
    mixedBranchesNextToWindowNext m n
  let fwindow : (Fin (n + 1) → α) × (Fin m → α) → Fin ((m + 1) + n) → α :=
    mixedBranchesToWindow m n
  let gwindow : (Fin ((m + 1) + n) → α) → α :=
    fun w => w (mixedWindowLast m n)
  let pair : ((ℕ → α) × (ℕ → α)) → (Fin (n + 1) → α) × (Fin m → α) :=
    sourcePrefixReverseStrict m n
  have htriple : Measurable triple := measurable_sourceMixedTriple m n
  have hqswap : Measurable qswap := measurable_mixed_swapBranchOutputs
  have hqwindow : Measurable qwindow := measurable_mixedBranchesNextToWindowNext m n
  have hfwindow : Measurable fwindow := measurable_mixedBranchesToWindow m n
  have hgwindow : Measurable gwindow := measurable_mixedWindowLast m n
  have hpair : Measurable pair := measurable_sourcePrefixReverseStrict m n
  have hfactor : sourceTwoSidedNext m n = qwindow ∘ qswap ∘ triple := by
    funext z
    exact mixedBranchesNextToWindowNext_source m n z
  have hwindowfun : pairedTwoSidedWindow m n = fwindow ∘ pair := by
    funext z
    exact mixedBranchesToWindow_source m n z
  have htripleLaw :
      (forwardReverseTwoSidedSourceMeasure π K Kr).map triple =
        ((P ⊗ₘ A) ⊗ₘ B.prodMkRight α) := by
    simpa [P, A, B, triple] using
      (forwardReverseTwoSidedSourceMeasure_prefix_next_reverseStrict
        (π := π) (K := K) (Kr := Kr) m n)
  have hfubini :
      ((P ⊗ₘ A) ⊗ₘ B.prodMkRight α).map qswap =
        (P ⊗ₘ B) ⊗ₘ A.prodMkRight (Fin m → α) := by
    exact mixed_conditional_fubini_branches (μ := P) A B
  have hAprod : A.prodMkRight (Fin m → α) =
      K ∘ₖ Kernel.deterministic (gwindow ∘ fwindow) (hgwindow.comp hfwindow) := by
    ext p s hs
    simp [A, fwindow, gwindow, Kernel.comp_deterministic_eq_comap,
      Kernel.comap_apply, Kernel.prodMkRight_apply, mixedBranchesToWindow_last]
  have htransport :
      ((P ⊗ₘ B) ⊗ₘ
        (K ∘ₖ Kernel.deterministic (gwindow ∘ fwindow)
          (hgwindow.comp hfwindow))).map
          (fun p => (fwindow p.1, p.2)) =
        ((P ⊗ₘ B).map fwindow) ⊗ₘ
          (K ∘ₖ Kernel.deterministic gwindow hgwindow) := by
    exact Measure.compProd_map_through (P ⊗ₘ B) K fwindow hfwindow gwindow hgwindow
  have hwindowLaw :
      (forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedTwoSidedWindow m n) =
        (P ⊗ₘ B).map fwindow := by
    calc
      (forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedTwoSidedWindow m n) =
          ((forwardReverseTwoSidedSourceMeasure π K Kr).map pair).map fwindow := by
            rw [Measure.map_map hfwindow hpair]
            rw [hwindowfun]
      _ = (P ⊗ₘ B).map fwindow := by
            simpa [P, B, pair] using congrArg (fun ν => ν.map fwindow)
              (forwardReverseTwoSidedSourceMeasure_prefix_reverseStrict
                (π := π) (K := K) (Kr := Kr) m n)
  calc
    (forwardReverseTwoSidedSourceMeasure π K Kr).map (sourceTwoSidedNext m n) =
        (((forwardReverseTwoSidedSourceMeasure π K Kr).map triple).map qswap).map qwindow := by
          rw [Measure.map_map hqwindow hqswap,
            Measure.map_map (hqwindow.comp hqswap) htriple]
          simpa only [Function.comp_assoc] using congrArg
            (fun h => (forwardReverseTwoSidedSourceMeasure π K Kr).map h) hfactor
    _ = (((P ⊗ₘ A) ⊗ₘ B.prodMkRight α).map qswap).map qwindow := by
          rw [htripleLaw]
    _ = ((P ⊗ₘ B) ⊗ₘ A.prodMkRight (Fin m → α)).map qwindow := by
          rw [hfubini]
    _ = ((P ⊗ₘ B) ⊗ₘ
          (K ∘ₖ Kernel.deterministic (gwindow ∘ fwindow)
            (hgwindow.comp hfwindow))).map (fun p => (fwindow p.1, p.2)) := by
          rw [hAprod]
          rfl
    _ = ((P ⊗ₘ B).map fwindow) ⊗ₘ
          (K ∘ₖ Kernel.deterministic gwindow hgwindow) := by
          exact htransport
    _ = (forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedTwoSidedWindow m n) ⊗ₘ
          (K ∘ₖ Kernel.deterministic
            (fun w : Fin ((m + 1) + n) → α => w (mixedWindowLast m n))
            (measurable_mixedWindowLast m n)) := by
          rw [hwindowLaw]

/-- A homogeneous trajectory kernel started from a fixed state is its
stationary trajectory law with a Dirac initial measure. -/
theorem conditionalHomogeneousTrajKernel_apply_eq_stationaryTrajMeasure_dirac
    {Kr : Kernel α α} [IsMarkovKernel Kr] (a : α) :
    conditionalHomogeneousTrajKernel Kr a =
      stationaryTrajMeasure (Measure.dirac a) Kr := by
  have h := conditionalHomogeneousTrajKernel_comp_eq_stationaryTrajMeasure
    (π := Measure.dirac a) (K := Kr)
  have hdirac : conditionalHomogeneousTrajKernel Kr ∘ₘ Measure.dirac a =
      conditionalHomogeneousTrajKernel Kr a := by
    change Measure.bind (Measure.dirac a)
      (fun x => conditionalHomogeneousTrajKernel Kr x) = _
    rw [Measure.dirac_bind (Kernel.measurable _)]
  exact hdirac.symm.trans h

theorem conditionalHomogeneousTrajKernel_map_zero
    {Kr : Kernel α α} [IsMarkovKernel Kr] :
    (conditionalHomogeneousTrajKernel Kr).map (fun y : ℕ → α => y 0) =
      Kernel.id := by
  ext a s hs
  rw [Kernel.map_apply _ (measurable_pi_apply 0)]
  rw [conditionalHomogeneousTrajKernel_apply_eq_stationaryTrajMeasure_dirac]
  rw [stationaryTrajMeasure_zero_marginal]
  rw [Kernel.id_apply]

theorem conditionalReverseTailKernel_map_zero
    {Kr : Kernel α α} [IsMarkovKernel Kr] :
    (conditionalReverseTailKernel Kr).map (fun y : ℕ → α => y 0) =
      Kernel.deterministic (fun x : ℕ → α => x 0) (measurable_pi_apply 0) := by
  unfold conditionalReverseTailKernel
  rw [Kernel.map_comp, conditionalHomogeneousTrajKernel_map_zero, Kernel.id_comp]

theorem ae_conditionalReverseTailKernel_zero_eq
    {Kr : Kernel α α} [IsMarkovKernel Kr] [MeasurableEq α]
    (x : ℕ → α) :
    ∀ᵐ y ∂conditionalReverseTailKernel Kr x, y 0 = x 0 := by
  have hmap : (conditionalReverseTailKernel Kr x).map (fun y : ℕ → α => y 0) =
      Measure.dirac (x 0) := by
    rw [← Kernel.map_apply _ (measurable_pi_apply 0)]
    rw [conditionalReverseTailKernel_map_zero, Kernel.deterministic_apply]
  refine ae_of_ae_map (μ := conditionalReverseTailKernel Kr x)
    (f := fun y : ℕ → α => y 0) (p := fun a : α => a = x 0)
    (measurable_pi_apply 0).aemeasurable ?_
  rw [hmap]
  exact (ae_dirac_iff
    (measurableSet_eq_fun measurable_id measurable_const)).2 rfl

/-- The source coupling identifies both time-zero coordinates almost surely. -/
theorem ae_forwardReverseTwoSidedSourceMeasure_reverse_zero_eq_forward_zero
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] [MeasurableEq α] :
    ∀ᵐ z ∂forwardReverseTwoSidedSourceMeasure π K Kr, z.2 0 = z.1 0 := by
  have hprob : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := hprob
  let μ : Measure (ℕ → α) := stationaryTrajMeasure π K
  let L : Kernel (ℕ → α) (ℕ → α) := conditionalReverseTailKernel Kr
  change ∀ᵐ z ∂μ ⊗ₘ L, z.2 0 = z.1 0
  have hmeas : MeasurableSet {z : (ℕ → α) × (ℕ → α) | z.2 0 = z.1 0} :=
    measurableSet_eq_fun
      ((measurable_pi_apply 0).comp measurable_snd)
      ((measurable_pi_apply 0).comp measurable_fst)
  refine Measure.ae_compProd_of_ae_ae hmeas ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  simpa [L] using ae_conditionalReverseTailKernel_zero_eq (Kr := Kr) x

theorem pairedPastWindow_eq_reverseNatPrefixSub_of_anchor
    (m : ℕ) (z : (ℕ → α) × (ℕ → α)) (hzero : z.2 0 = z.1 0) :
    pairedPastWindow m z = reverseNatPrefixSub m z.2 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [pairedPastWindow, snocWindow, reverseNatPrefixSub, hzero]
  · simp [pairedPastWindow, snocWindow, reverseNatPrefixSub, reverseStrictPrefix]

theorem ae_pairedPastWindow_eq_reverseNatPrefix
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] [MeasurableEq α] (m : ℕ) :
    pairedPastWindow (α := α) m =ᵐ[forwardReverseTwoSidedSourceMeasure π K Kr]
      fun z => reverseNatPrefix m z.2 := by
  filter_upwards [ae_forwardReverseTwoSidedSourceMeasure_reverse_zero_eq_forward_zero
    (π := π) (K := K) (Kr := Kr)] with z hzero
  rw [reverseNatPrefix_eq_sub]
  exact pairedPastWindow_eq_reverseNatPrefixSub_of_anchor m z hzero

/-- Under reverse-pair balance, every paired past window has the ordinary
forward stationary-prefix law. -/
theorem forwardReverseTwoSidedMeasure_pairedPastWindow
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] [MeasurableEq α]
    (hbalance : Kernel.ReversePairBalance π K Kr)
    (hstationary : Kernel.Invariant K π) (m : ℕ) :
    (forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedPastWindow m) =
      (stationaryTrajMeasure π K).map (natPrefix m) := by
  calc
    (forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedPastWindow m) =
        (forwardReverseTwoSidedSourceMeasure π K Kr).map
          (fun z => reverseNatPrefix m z.2) := by
            exact Measure.map_congr
              (ae_pairedPastWindow_eq_reverseNatPrefix
                (π := π) (K := K) (Kr := Kr) m)
    _ = ((forwardReverseTwoSidedSourceMeasure π K Kr).map Prod.snd).map
          (reverseNatPrefix m) := by
            symm
            rw [Measure.map_map (measurable_reverseNatPrefix m) measurable_snd]
            rfl
    _ = (stationaryTrajMeasure π Kr).map (reverseNatPrefix m) := by
            rw [forwardReverseTwoSidedSourceMeasure_map_reverse]
    _ = (stationaryTrajMeasure π K).map (natPrefix m) := by
            exact hbalance.stationaryTrajMeasure_reverseNatPrefix_eq hstationary m

/-- The ordinary forward prefix, presented with the same finite-index type as
a mixed window of depth `m` and right length `n`. -/
def forwardMixedWindow (m n : ℕ) (x : ℕ → α) : Fin ((m + 1) + n) → α :=
  fun i => x i.1

theorem measurable_forwardMixedWindow (m n : ℕ) :
    Measurable (forwardMixedWindow (α := α) m n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

theorem forwardMixedWindow_zero (m : ℕ) (x : ℕ → α) :
    forwardMixedWindow m 0 x = natPrefix m x := by
  funext i
  rfl

theorem forwardMixedWindow_succ (m n : ℕ) (x : ℕ → α) :
    forwardMixedWindow m (n + 1) x =
      snocWindow (forwardMixedWindow m n x) (x (m + n + 1)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · unfold forwardMixedWindow snocWindow
    simp only [Fin.snoc]
    split
    · rename_i h
      simp at h
    · change x (m + 1 + n) = x (m + n + 1)
      congr 1
      omega
  · unfold forwardMixedWindow snocWindow
    rw [Fin.snoc_castSucc]
    simp only [Fin.val_castSucc]

theorem stationaryTrajMeasure_forwardMixedWindow_next
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α}
    [IsMarkovKernel K] (m n : ℕ) :
    (stationaryTrajMeasure π K).map
        (fun x => (forwardMixedWindow m n x, x (m + n + 1))) =
      (stationaryTrajMeasure π K).map (forwardMixedWindow m n) ⊗ₘ
        (K ∘ₖ Kernel.deterministic
          (fun w : Fin ((m + 1) + n) → α => w (mixedWindowLast m n))
          (measurable_mixedWindowLast m n)) := by
  have hprob : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := hprob
  let r : ℕ := m + n
  let f : (Fin (r + 1) → α) → Fin ((m + 1) + n) → α :=
    fun w i => w ⟨i.1, by omega⟩
  let g : (Fin ((m + 1) + n) → α) → α :=
    fun w => w (mixedWindowLast m n)
  let pairNat : (ℕ → α) → (Fin (r + 1) → α) × α :=
    fun x => (natPrefix r x, x (r + 1))
  let pairMixed : (ℕ → α) → (Fin ((m + 1) + n) → α) × α :=
    fun x => (forwardMixedWindow m n x, x (m + n + 1))
  let mapPair : (Fin (r + 1) → α) × α →
      (Fin ((m + 1) + n) → α) × α :=
    fun p => (f p.1, p.2)
  have hf : Measurable f := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply _
  have hg : Measurable g := measurable_mixedWindowLast m n
  have hpairNat : Measurable pairNat :=
    (measurable_natPrefix r).prodMk (measurable_pi_apply _)
  have hpairMixed : Measurable pairMixed :=
    (measurable_forwardMixedWindow m n).prodMk (measurable_pi_apply _)
  have hmapPair : Measurable mapPair := hf.comp measurable_fst |>.prodMk measurable_snd
  have hpairfun : pairMixed = mapPair ∘ pairNat := by
    funext x
    apply Prod.ext
    · funext i
      rfl
    · dsimp [r]
  have hlast : (fun w : Fin (r + 1) → α => w (Fin.last r)) = g ∘ f := by
    funext w
    dsimp [g, f, r, mixedWindowLast]
    congr 1
  have hkernel :
      K ∘ₖ Kernel.deterministic (fun w : Fin (r + 1) → α => w (Fin.last r))
          (measurable_pi_apply _) =
        K ∘ₖ Kernel.deterministic (g ∘ f) (hg.comp hf) := by
    exact congrArg (fun L => K ∘ₖ L) (Kernel.deterministic_congr hlast)
  have hprefixfun : f ∘ natPrefix r = forwardMixedWindow m n := by
    funext x
    funext i
    rfl
  have hprefixlaw :
      ((stationaryTrajMeasure π K).map (natPrefix r)).map f =
        (stationaryTrajMeasure π K).map (forwardMixedWindow m n) := by
    rw [Measure.map_map hf (measurable_natPrefix r)]
    rw [hprefixfun]
  calc
    (stationaryTrajMeasure π K).map pairMixed =
        ((stationaryTrajMeasure π K).map pairNat).map mapPair := by
          rw [Measure.map_map hmapPair hpairNat]
          rw [hpairfun]
    _ = (((stationaryTrajMeasure π K).map (natPrefix r) ⊗ₘ
          (K ∘ₖ Kernel.deterministic (fun w : Fin (r + 1) → α => w (Fin.last r))
            (measurable_pi_apply _))).map mapPair) := by
          rw [stationaryTrajMeasure_natPrefix_next (π := π) (K := K) r]
    _ = (((stationaryTrajMeasure π K).map (natPrefix r) ⊗ₘ
          (K ∘ₖ Kernel.deterministic (g ∘ f) (hg.comp hf))).map mapPair) := by
          rw [hkernel]
    _ = ((stationaryTrajMeasure π K).map (natPrefix r)).map f ⊗ₘ
          (K ∘ₖ Kernel.deterministic g hg) := by
          exact Measure.compProd_map_through _ K f hf g hg
    _ = (stationaryTrajMeasure π K).map (forwardMixedWindow m n) ⊗ₘ
          (K ∘ₖ Kernel.deterministic
            (fun w : Fin ((m + 1) + n) → α => w (mixedWindowLast m n))
            (measurable_mixedWindowLast m n)) := by
          rw [hprefixlaw]

theorem stationaryTrajMeasure_forwardMixedWindow_succ_factor
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α}
    [IsMarkovKernel K] (m n : ℕ) :
    (stationaryTrajMeasure π K).map (forwardMixedWindow m (n + 1)) =
      ((stationaryTrajMeasure π K).map (forwardMixedWindow m n) ⊗ₘ
        (K ∘ₖ Kernel.deterministic
          (fun w : Fin ((m + 1) + n) → α => w (mixedWindowLast m n))
          (measurable_mixedWindowLast m n))).map
            (fun p => snocWindow p.1 p.2) := by
  let pair : (ℕ → α) → (Fin ((m + 1) + n) → α) × α :=
    fun x => (forwardMixedWindow m n x, x (m + n + 1))
  have hpair : Measurable pair :=
    (measurable_forwardMixedWindow m n).prodMk (measurable_pi_apply _)
  have hsnoc : Measurable (fun p : (Fin ((m + 1) + n) → α) × α =>
      snocWindow p.1 p.2) := measurable_snocWindow ((m + 1) + n)
  have hfun : forwardMixedWindow m (n + 1) =
      (fun p => snocWindow p.1 p.2) ∘ pair := by
    funext x
    exact forwardMixedWindow_succ m n x
  calc
    (stationaryTrajMeasure π K).map (forwardMixedWindow m (n + 1)) =
        ((stationaryTrajMeasure π K).map pair).map (fun p => snocWindow p.1 p.2) := by
          rw [Measure.map_map hsnoc hpair]
          rw [hfun]
    _ = ((stationaryTrajMeasure π K).map (forwardMixedWindow m n) ⊗ₘ
          (K ∘ₖ Kernel.deterministic
            (fun w : Fin ((m + 1) + n) → α => w (mixedWindowLast m n))
            (measurable_mixedWindowLast m n))).map
              (fun p => snocWindow p.1 p.2) := by
          rw [stationaryTrajMeasure_forwardMixedWindow_next (π := π) (K := K) m n]

theorem pairedTwoSidedWindow_zero (m : ℕ)
    (z : (ℕ → α) × (ℕ → α)) :
    pairedTwoSidedWindow m 0 z = pairedPastWindow m z := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · unfold pairedTwoSidedWindow
    rw [Fin.append_left]
    simp
  · exact Fin.elim0 j

theorem forwardReverseTwoSidedSourceMeasure_mixedWindow_succ_factor
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] (m n : ℕ) :
    (forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedTwoSidedWindow m (n + 1)) =
      ((forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedTwoSidedWindow m n) ⊗ₘ
        (K ∘ₖ Kernel.deterministic
          (fun w : Fin ((m + 1) + n) → α => w (mixedWindowLast m n))
          (measurable_mixedWindowLast m n))).map
            (fun p => snocWindow p.1 p.2) := by
  let pair : ((ℕ → α) × (ℕ → α)) → (Fin ((m + 1) + n) → α) × α :=
    sourceTwoSidedNext m n
  have hpair : Measurable pair := measurable_sourceTwoSidedNext m n
  have hsnoc : Measurable (fun p : (Fin ((m + 1) + n) → α) × α =>
      snocWindow p.1 p.2) := measurable_snocWindow ((m + 1) + n)
  have hfun : pairedTwoSidedWindow m (n + 1) =
      (fun p => snocWindow p.1 p.2) ∘ pair := by
    funext z
    exact pairedTwoSidedWindow_succ m n z
  calc
    (forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedTwoSidedWindow m (n + 1)) =
        ((forwardReverseTwoSidedSourceMeasure π K Kr).map pair).map
          (fun p => snocWindow p.1 p.2) := by
          rw [Measure.map_map hsnoc hpair]
          rw [hfun]
    _ = ((forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedTwoSidedWindow m n) ⊗ₘ
          (K ∘ₖ Kernel.deterministic
            (fun w : Fin ((m + 1) + n) → α => w (mixedWindowLast m n))
            (measurable_mixedWindowLast m n))).map
              (fun p => snocWindow p.1 p.2) := by
          rw [forwardReverseTwoSidedSourceMeasure_mixedWindow_next
            (π := π) (K := K) (Kr := Kr) m n]

/-- Every chronological finite source window has the same law as the
corresponding ordinary forward stationary prefix. -/
theorem Kernel.ReversePairBalance.forwardReverseTwoSidedSourceMeasure_mixedWindow_law
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] [MeasurableEq α]
    (hbalance : Kernel.ReversePairBalance π K Kr)
    (hstationary : Kernel.Invariant K π) (m n : ℕ) :
    (forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedTwoSidedWindow m n) =
      (stationaryTrajMeasure π K).map (forwardMixedWindow m n) := by
  induction n with
  | zero =>
      calc
        (forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedTwoSidedWindow m 0) =
            (forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedPastWindow m) := by
              congr 1
              funext z
              exact pairedTwoSidedWindow_zero m z
        _ = (stationaryTrajMeasure π K).map (natPrefix m) := by
              exact forwardReverseTwoSidedMeasure_pairedPastWindow
                hbalance hstationary m
        _ = (stationaryTrajMeasure π K).map (forwardMixedWindow m 0) := by
              symm
              have hfun : forwardMixedWindow (α := α) m 0 = natPrefix m := by
                funext x
                exact forwardMixedWindow_zero m x
              rw [hfun]
  | succ n ih =>
      calc
        (forwardReverseTwoSidedSourceMeasure π K Kr).map
            (pairedTwoSidedWindow m (n + 1)) =
            ((forwardReverseTwoSidedSourceMeasure π K Kr).map (pairedTwoSidedWindow m n) ⊗ₘ
              (K ∘ₖ Kernel.deterministic
                (fun w : Fin ((m + 1) + n) → α => w (mixedWindowLast m n))
                (measurable_mixedWindowLast m n))).map
                  (fun p => snocWindow p.1 p.2) := by
                    exact forwardReverseTwoSidedSourceMeasure_mixedWindow_succ_factor
                      (π := π) (K := K) (Kr := Kr) m n
        _ = ((stationaryTrajMeasure π K).map (forwardMixedWindow m n) ⊗ₘ
              (K ∘ₖ Kernel.deterministic
                (fun w : Fin ((m + 1) + n) → α => w (mixedWindowLast m n))
                (measurable_mixedWindowLast m n))).map
                  (fun p => snocWindow p.1 p.2) := by
                    rw [ih]
        _ = (stationaryTrajMeasure π K).map (forwardMixedWindow m (n + 1)) := by
                    symm
                    exact stationaryTrajMeasure_forwardMixedWindow_succ_factor
                      (π := π) (K := K) m n

/-- The corresponding finite-window law after the forward/reverse branches are spliced
into an integer-indexed trajectory. -/
theorem Kernel.ReversePairBalance.forwardReverseTwoSidedTrajMeasure_mixedWindow_law
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] [MeasurableEq α]
    (hbalance : Kernel.ReversePairBalance π K Kr)
    (hstationary : Kernel.Invariant K π) (m n : ℕ) :
    (forwardReverseTwoSidedTrajMeasure π K Kr).map (twoSidedWindow m n) =
      (stationaryTrajMeasure π K).map (forwardMixedWindow m n) := by
  unfold forwardReverseTwoSidedTrajMeasure
  rw [Measure.map_map (measurable_twoSidedWindow m n) measurable_spliceForwardReverse]
  have hfun : twoSidedWindow (α := α) m n ∘ spliceForwardReverse =
      pairedTwoSidedWindow m n := by
    funext z
    exact twoSidedWindow_spliceForwardReverse m n z
  rw [hfun]
  exact hbalance.forwardReverseTwoSidedSourceMeasure_mixedWindow_law hstationary m n

/-- The finite nonnegative prefix of an integer-indexed path. -/
def intForwardPrefix (n : ℕ) (x : ℤ → α) : Fin (n + 1) → α :=
  fun i => x (i.1 : ℤ)

theorem measurable_intForwardPrefix (n : ℕ) :
    Measurable (intForwardPrefix (α := α) n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

theorem intForwardPrefix_spliceForwardReverse (n : ℕ)
    (z : (ℕ → α) × (ℕ → α)) :
    intForwardPrefix n (spliceForwardReverse z) = natPrefix n z.1 := by
  funext i
  rfl

theorem forwardReverseTwoSidedTrajMeasure_intForwardPrefix_law
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] (n : ℕ) :
    (forwardReverseTwoSidedTrajMeasure π K Kr).map (intForwardPrefix n) =
      (stationaryTrajMeasure π K).map (natPrefix n) := by
  unfold forwardReverseTwoSidedTrajMeasure
  rw [Measure.map_map (measurable_intForwardPrefix n) measurable_spliceForwardReverse]
  have hfun : intForwardPrefix (α := α) n ∘ spliceForwardReverse =
      natPrefix n ∘ Prod.fst := by
    funext z
    exact intForwardPrefix_spliceForwardReverse n z
  rw [hfun]
  calc
    (forwardReverseTwoSidedSourceMeasure π K Kr).map (natPrefix n ∘ Prod.fst) =
        ((forwardReverseTwoSidedSourceMeasure π K Kr).map Prod.fst).map (natPrefix n) := by
          symm
          rw [Measure.map_map (measurable_natPrefix n) measurable_fst]
    _ = (stationaryTrajMeasure π K).map (natPrefix n) := by
          rw [forwardReverseTwoSidedSourceMeasure_map_forward]

/-- Drop the leftmost coordinate of a window of length `n + 2`. -/
def dropFirstMixedWindow (n : ℕ) (w : Fin (2 + n) → α) : Fin (n + 1) → α :=
  fun i => w ⟨i.1 + 1, by omega⟩

theorem measurable_dropFirstMixedWindow (n : ℕ) :
    Measurable (dropFirstMixedWindow (α := α) n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

/-- The one-step-shifted finite natural prefix. -/
def natShiftOnePrefix (n : ℕ) (x : ℕ → α) : Fin (n + 1) → α :=
  fun i => x (i.1 + 1)

theorem measurable_natShiftOnePrefix (n : ℕ) :
    Measurable (natShiftOnePrefix (α := α) n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

theorem dropFirstMixedWindow_twoSided (n : ℕ) (x : ℤ → α) :
    dropFirstMixedWindow n (twoSidedWindow 1 n x) = intForwardPrefix n x := by
  funext i
  change x (((i.1 + 1 : ℕ) : ℤ) - 1) = x (i.1 : ℤ)
  congr 1
  omega

theorem dropFirstMixedWindow_forwardMixed (n : ℕ) (x : ℕ → α) :
    dropFirstMixedWindow n (forwardMixedWindow 1 n x) = natShiftOnePrefix n x := by
  funext i
  rfl

/-- A stationary forward trajectory has the same finite prefixes after one
natural-time shift.  This follows from the newly formalized two-sided law by
dropping the `-1` coordinate. -/
theorem Kernel.ReversePairBalance.stationaryTrajMeasure_natShiftOnePrefix_eq
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] [MeasurableEq α]
    (hbalance : Kernel.ReversePairBalance π K Kr)
    (hstationary : Kernel.Invariant K π) (n : ℕ) :
    (stationaryTrajMeasure π K).map (natShiftOnePrefix n) =
      (stationaryTrajMeasure π K).map (natPrefix n) := by
  have hmix := hbalance.forwardReverseTwoSidedTrajMeasure_mixedWindow_law
    hstationary 1 n
  have hleft :
      ((forwardReverseTwoSidedTrajMeasure π K Kr).map (twoSidedWindow 1 n)).map
          (dropFirstMixedWindow n) =
        (forwardReverseTwoSidedTrajMeasure π K Kr).map (intForwardPrefix n) := by
    rw [Measure.map_map (measurable_dropFirstMixedWindow n) (measurable_twoSidedWindow 1 n)]
    congr 1
    funext x
    exact dropFirstMixedWindow_twoSided n x
  have hright :
      ((stationaryTrajMeasure π K).map (forwardMixedWindow 1 n)).map
          (dropFirstMixedWindow n) =
        (stationaryTrajMeasure π K).map (natShiftOnePrefix n) := by
    rw [Measure.map_map (measurable_dropFirstMixedWindow n)
      (measurable_forwardMixedWindow 1 n)]
    congr 1
  calc
    (stationaryTrajMeasure π K).map (natShiftOnePrefix n) =
        ((stationaryTrajMeasure π K).map (forwardMixedWindow 1 n)).map
          (dropFirstMixedWindow n) := by
            symm
            exact hright
    _ = ((forwardReverseTwoSidedTrajMeasure π K Kr).map (twoSidedWindow 1 n)).map
          (dropFirstMixedWindow n) := by
            rw [hmix]
    _ = (forwardReverseTwoSidedTrajMeasure π K Kr).map (intForwardPrefix n) := hleft
    _ = (stationaryTrajMeasure π K).map (natPrefix n) := by
            exact forwardReverseTwoSidedTrajMeasure_intForwardPrefix_law
              (π := π) (K := K) (Kr := Kr) n

/-- Shift a natural-indexed path forward by a fixed number of coordinates. -/
def natPathShift (s : ℕ) (x : ℕ → α) : ℕ → α :=
  fun i => x (s + i)

theorem measurable_natPathShift (s : ℕ) :
    Measurable (natPathShift (α := α) s) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

theorem natPathShift_one_prefix (n : ℕ) (x : ℕ → α) :
    natPrefix n (natPathShift 1 x) = natShiftOnePrefix n x := by
  funext i
  change x (1 + i.1) = x (i.1 + 1)
  congr 1
  omega

theorem natPathShift_comp (s t : ℕ) (x : ℕ → α) :
    natPathShift t (natPathShift s x) = natPathShift (s + t) x := by
  funext i
  simp [natPathShift, Nat.add_assoc]

/-- The empty-coordinate restriction is determined by total mass, for natural
path measures. -/
theorem nat_map_empty_restrict_eq_of_univ
    {μ ν : Measure (ℕ → α)}
    (huniv : μ Set.univ = ν Set.univ) :
    μ.map (∅ : Finset ℕ).restrict = ν.map (∅ : Finset ℕ).restrict := by
  apply Measure.ext
  intro s hs
  rcases Set.eq_empty_or_nonempty s with hzero | ⟨x, hx⟩
  · simp [hzero]
  have hs_univ : s = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    rw [show y = x by exact Subsingleton.elim _ _]
    exact hx
  calc
    μ.map (∅ : Finset ℕ).restrict s = μ Set.univ := by
      rw [hs_univ, Measure.map_apply (Finset.measurable_restrict (∅ : Finset ℕ))
        MeasurableSet.univ, Set.preimage_univ]
    _ = ν Set.univ := huniv
    _ = ν.map (∅ : Finset ℕ).restrict s := by
      rw [hs_univ, Measure.map_apply (Finset.measurable_restrict (∅ : Finset ℕ))
        MeasurableSet.univ, Set.preimage_univ]

/-- Equality of all initial finite natural prefixes determines a probability
law on natural-indexed paths. -/
theorem nat_measure_eq_of_all_prefix
    {μ ν : Measure (ℕ → α)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ n : ℕ, μ.map (natPrefix n) = ν.map (natPrefix n)) : μ = ν := by
  refine ext_of_generate_finite (measurableCylinders fun _ : ℕ => α)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ (by simp)
  intro s hs
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hs
  have hI : μ.map I.restrict = ν.map I.restrict := by
    by_cases hzero : I = ∅
    · subst I
      exact nat_map_empty_restrict_eq_of_univ (by simp)
    · let hne : I.Nonempty := Finset.nonempty_of_ne_empty hzero
      let n : ℕ := I.max' hne
      let J : Finset ℕ := Finset.Iic n
      have hIJ : I ⊆ J := by
        intro i hi
        exact Finset.mem_Iic.mpr (Finset.le_max' I i hi)
      let rJ : (ℕ → α) → (J → α) := @Finset.restrict ℕ (fun _ : ℕ => α) J
      let rIJ : (J → α) → (I → α) :=
        @Finset.restrict₂ ℕ (fun _ : ℕ => α) I J hIJ
      let prefixToJ : (Fin (n + 1) → α) → (J → α) :=
        fun w j => w ⟨j.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp j.2)⟩
      have hrJ : Measurable rJ := Finset.measurable_restrict J
      have hrIJ : Measurable rIJ := Finset.measurable_restrict₂ hIJ
      have hprefJ : Measurable prefixToJ := by
        apply measurable_pi_lambda
        intro j
        exact measurable_pi_apply _
      have hcomp : rIJ ∘ rJ = I.restrict := by
        exact Finset.restrict₂_comp_restrict hIJ
      have hprefcomp : prefixToJ ∘ natPrefix n = rJ := by
        funext x
        funext j
        rfl
      have hJ : μ.map rJ = ν.map rJ := by
        calc
          μ.map rJ = (μ.map (natPrefix n)).map prefixToJ := by
            symm
            rw [Measure.map_map hprefJ (measurable_natPrefix n), hprefcomp]
          _ = (ν.map (natPrefix n)).map prefixToJ := by rw [h n]
          _ = ν.map rJ := by
            rw [Measure.map_map hprefJ (measurable_natPrefix n), hprefcomp]
      calc
        μ.map I.restrict = (μ.map rJ).map rIJ := by
          symm
          rw [Measure.map_map hrIJ hrJ, hcomp]
        _ = (ν.map rJ).map rIJ := by rw [hJ]
        _ = ν.map I.restrict := by
          rw [Measure.map_map hrIJ hrJ, hcomp]
  rw [cylinder, ← Measure.map_apply _ hS, hI, Measure.map_apply _ hS]
  · exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  · exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/-- One-step natural shifting preserves the stationary forward trajectory law. -/
theorem Kernel.ReversePairBalance.natPathShift_one_measurePreserving
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] [MeasurableEq α]
    (hbalance : Kernel.ReversePairBalance π K Kr)
    (hstationary : Kernel.Invariant K π) :
    MeasurePreserving (natPathShift (α := α) 1)
      (stationaryTrajMeasure π K) (stationaryTrajMeasure π K) := by
  have hprob : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := hprob
  refine ⟨measurable_natPathShift 1, ?_⟩
  letI : IsProbabilityMeasure ((stationaryTrajMeasure π K).map
      (natPathShift (α := α) 1)) :=
    Measure.isProbabilityMeasure_map (measurable_natPathShift 1).aemeasurable
  refine nat_measure_eq_of_all_prefix (μ := (stationaryTrajMeasure π K).map
    (natPathShift (α := α) 1)) (ν := stationaryTrajMeasure π K) ?_
  intro n
  rw [Measure.map_map (measurable_natPrefix n) (measurable_natPathShift 1)]
  have hfun : natPrefix n ∘ natPathShift (α := α) 1 = natShiftOnePrefix n := by
    funext x
    exact natPathShift_one_prefix n x
  rw [hfun]
  exact hbalance.stationaryTrajMeasure_natShiftOnePrefix_eq hstationary n

/-- All nonnegative natural-time shifts preserve the stationary forward path
law. -/
theorem Kernel.ReversePairBalance.natPathShift_measurePreserving
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] [MeasurableEq α]
    (hbalance : Kernel.ReversePairBalance π K Kr)
    (hstationary : Kernel.Invariant K π) (s : ℕ) :
    MeasurePreserving (natPathShift (α := α) s)
      (stationaryTrajMeasure π K) (stationaryTrajMeasure π K) := by
  induction s with
  | zero =>
      refine ⟨measurable_natPathShift 0, ?_⟩
      have hfun : natPathShift (α := α) 0 = id := by
        funext x i
        change x (0 + i) = x i
        simp
      rw [hfun, Measure.map_id]
  | succ s ih =>
      have hone := hbalance.natPathShift_one_measurePreserving hstationary
      have hcomp := hone.comp ih
      have hfun : natPathShift (α := α) 1 ∘ natPathShift s = natPathShift (s + 1) := by
        funext x
        exact natPathShift_comp s 1 x
      simpa [Nat.succ_eq_add_one, hfun] using hcomp

/-- A finite integer window of length `l + 1`, read in chronological order. -/
def intWindow (a : ℤ) (l : ℕ) (x : ℤ → α) : Fin (l + 1) → α :=
  fun i => x (a + i.1)

theorem measurable_intWindow (a : ℤ) (l : ℕ) :
    Measurable (intWindow (α := α) a l) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

/-- The nonnegative portion of an integer-indexed path as a natural path. -/
def intNonnegativePath (x : ℤ → α) : ℕ → α :=
  fun i => x (i : ℤ)

theorem measurable_intNonnegativePath :
    Measurable (intNonnegativePath (α := α)) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

theorem natPrefix_intNonnegativePath (n : ℕ) (x : ℤ → α) :
    natPrefix n (intNonnegativePath x) = intForwardPrefix n x := by
  funext i
  rfl

theorem forwardReverseTwoSidedTrajMeasure_intNonnegativePath_law
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] :
    (forwardReverseTwoSidedTrajMeasure π K Kr).map (intNonnegativePath (α := α)) =
      stationaryTrajMeasure π K := by
  have hT : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := hT
  have hsource : IsProbabilityMeasure (forwardReverseTwoSidedSourceMeasure π K Kr) := by
    unfold forwardReverseTwoSidedSourceMeasure
    infer_instance
  letI : IsProbabilityMeasure (forwardReverseTwoSidedSourceMeasure π K Kr) := hsource
  have hP : IsProbabilityMeasure (forwardReverseTwoSidedTrajMeasure π K Kr) := by
    unfold forwardReverseTwoSidedTrajMeasure
    exact Measure.isProbabilityMeasure_map measurable_spliceForwardReverse.aemeasurable
  letI : IsProbabilityMeasure (forwardReverseTwoSidedTrajMeasure π K Kr) := hP
  letI : IsProbabilityMeasure
      ((forwardReverseTwoSidedTrajMeasure π K Kr).map (intNonnegativePath (α := α))) :=
    Measure.isProbabilityMeasure_map measurable_intNonnegativePath.aemeasurable
  refine nat_measure_eq_of_all_prefix ?_
  intro n
  rw [Measure.map_map (measurable_natPrefix n) measurable_intNonnegativePath]
  have hfun : natPrefix n ∘ intNonnegativePath (α := α) = intForwardPrefix n := by
    funext x
    exact natPrefix_intNonnegativePath n x
  rw [hfun]
  exact forwardReverseTwoSidedTrajMeasure_intForwardPrefix_law
    (π := π) (K := K) (Kr := Kr) n

/-- Select the first `l + 1` states of a mixed window that starts `m` steps
in the past. -/
def takeMixedPrefix (m l : ℕ) (w : Fin ((m + 1) + l) → α) : Fin (l + 1) → α :=
  fun i => w ⟨i.1, by omega⟩

theorem measurable_takeMixedPrefix (m l : ℕ) :
    Measurable (takeMixedPrefix (α := α) m l) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

theorem takeMixedPrefix_twoSided (m l : ℕ) (x : ℤ → α) :
    takeMixedPrefix m l (twoSidedWindow m l x) = intWindow (-(m : ℤ)) l x := by
  funext i
  change x ((i.1 : ℤ) - m) = x (-(m : ℤ) + i.1)
  congr 1
  omega

theorem takeMixedPrefix_forwardMixed (m l : ℕ) (x : ℕ → α) :
    takeMixedPrefix m l (forwardMixedWindow m l x) = natPrefix l x := by
  funext i
  rfl

/-- Every finite integer window of the forward/reverse path has the ordinary
stationary forward-prefix law. -/
theorem Kernel.ReversePairBalance.forwardReverseTwoSidedTrajMeasure_intWindow_law
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] [MeasurableEq α]
    (hbalance : Kernel.ReversePairBalance π K Kr)
    (hstationary : Kernel.Invariant K π) (a : ℤ) (l : ℕ) :
    (forwardReverseTwoSidedTrajMeasure π K Kr).map (intWindow a l) =
      (stationaryTrajMeasure π K).map (natPrefix l) := by
  by_cases hneg : a < 0
  · let m : ℕ := (-a).toNat
    have hmnonneg : 0 ≤ -a := by omega
    have hm : (m : ℤ) = -a := by
      dsimp [m]
      exact Int.toNat_of_nonneg hmnonneg
    have hleft :
        ((forwardReverseTwoSidedTrajMeasure π K Kr).map (twoSidedWindow m l)).map
            (takeMixedPrefix m l) =
          (forwardReverseTwoSidedTrajMeasure π K Kr).map (intWindow a l) := by
      rw [Measure.map_map (measurable_takeMixedPrefix m l) (measurable_twoSidedWindow m l)]
      congr 1
      funext x
      change takeMixedPrefix m l (twoSidedWindow m l x) = intWindow a l x
      calc
        takeMixedPrefix m l (twoSidedWindow m l x) = intWindow (-(m : ℤ)) l x :=
          takeMixedPrefix_twoSided m l x
        _ = intWindow a l x := by
          rw [hm]
          congr 1
          omega
    have hright :
        ((stationaryTrajMeasure π K).map (forwardMixedWindow m l)).map
            (takeMixedPrefix m l) =
          (stationaryTrajMeasure π K).map (natPrefix l) := by
      rw [Measure.map_map (measurable_takeMixedPrefix m l)
        (measurable_forwardMixedWindow m l)]
      congr 1
    calc
      (forwardReverseTwoSidedTrajMeasure π K Kr).map (intWindow a l) =
          ((forwardReverseTwoSidedTrajMeasure π K Kr).map (twoSidedWindow m l)).map
            (takeMixedPrefix m l) := by
              symm
              exact hleft
      _ = ((stationaryTrajMeasure π K).map (forwardMixedWindow m l)).map
            (takeMixedPrefix m l) := by
              rw [hbalance.forwardReverseTwoSidedTrajMeasure_mixedWindow_law
                hstationary m l]
      _ = (stationaryTrajMeasure π K).map (natPrefix l) := hright
  · have hnonneg : 0 ≤ a := by omega
    let s : ℕ := a.toNat
    have hs : (s : ℤ) = a := by
      dsimp [s]
      exact Int.toNat_of_nonneg hnonneg
    have hshift := hbalance.natPathShift_measurePreserving hstationary s
    have hfun : intWindow a l =
        natPrefix l ∘ natPathShift s ∘ intNonnegativePath (α := α) := by
      funext x i
      change x (a + i.1) = x ((s : ℤ) + i.1)
      rw [hs]
    calc
      (forwardReverseTwoSidedTrajMeasure π K Kr).map (intWindow a l) =
          (((forwardReverseTwoSidedTrajMeasure π K Kr).map
            (intNonnegativePath (α := α))).map (natPathShift s)).map (natPrefix l) := by
            rw [Measure.map_map (measurable_natPrefix l) (measurable_natPathShift s),
              Measure.map_map ((measurable_natPrefix l).comp (measurable_natPathShift s))
                measurable_intNonnegativePath]
            simpa only [Function.comp_assoc] using congrArg
              (fun f => (forwardReverseTwoSidedTrajMeasure π K Kr).map f) hfun
      _ = ((stationaryTrajMeasure π K).map (natPathShift s)).map (natPrefix l) := by
            rw [forwardReverseTwoSidedTrajMeasure_intNonnegativePath_law]
      _ = (stationaryTrajMeasure π K).map (natPrefix l) := by
            rw [hshift.map_eq]

/-- Reindex a consecutive finite window by its original integer interval. -/
def intWindowToIccRange (a b : ℤ) (hab : a ≤ b) :
    (Fin ((b - a).toNat + 1) → α) → (Finset.Icc a b → α) :=
  fun w j => w ⟨(j.1 - a).toNat, by
    have hjlo : a ≤ j.1 := (Finset.mem_Icc.mp j.2).1
    have hjhi : j.1 ≤ b := (Finset.mem_Icc.mp j.2).2
    omega⟩

theorem measurable_intWindowToIccRange (a b : ℤ) (hab : a ≤ b) :
    Measurable (intWindowToIccRange (α := α) a b hab) := by
  apply measurable_pi_lambda
  intro j
  exact measurable_pi_apply _

theorem intWindowToIccRange_comp_intWindow (a b : ℤ) (hab : a ≤ b) :
    intWindowToIccRange (α := α) a b hab ∘
        intWindow (α := α) a ((b - a).toNat) =
      (Finset.Icc a b).restrict := by
  funext x j
  simp only [Function.comp_apply, intWindowToIccRange, intWindow]
  have hjlo : a ≤ j.1 := (Finset.mem_Icc.mp j.2).1
  have hjdiff : 0 ≤ j.1 - a := sub_nonneg.mpr hjlo
  rw [Int.toNat_of_nonneg hjdiff]
  congr 1
  omega

theorem intWindow_intPathShift (k a : ℤ) (l : ℕ) :
    intWindow (α := α) a l ∘ intPathShift (α := α) k =
      intWindow (α := α) (k + a) l := by
  funext x i
  simp only [Function.comp_apply, intWindow, intPathShift_apply]
  congr 1
  omega

/-- A generic bridge from all finite chronological integer-window laws to
all contiguous integer-coordinate restrictions. -/
theorem map_Icc_restrict_eq_of_all_intWindow
    {μ ν : Measure (ℤ → α)}
    (hmass : μ Set.univ = ν Set.univ)
    (hwindow : ∀ a : ℤ, ∀ l : ℕ,
      μ.map (intWindow (α := α) a l) =
        ν.map (intWindow (α := α) a l)) :
    ∀ a b : ℤ,
      μ.map (Finset.Icc a b).restrict =
        ν.map (Finset.Icc a b).restrict := by
  intro a b
  by_cases hab : a ≤ b
  · let l : ℕ := (b - a).toNat
    let W : (Fin (l + 1) → α) → (Finset.Icc a b → α) :=
      intWindowToIccRange (α := α) a b hab
    have hW : Measurable W := by
      exact measurable_intWindowToIccRange a b hab
    have hw : μ.map (intWindow (α := α) a l) =
        ν.map (intWindow (α := α) a l) := hwindow a l
    have hcomp : W ∘ intWindow (α := α) a l =
        (Finset.Icc a b).restrict := by
      dsimp only [W, l]
      exact intWindowToIccRange_comp_intWindow a b hab
    calc
      μ.map (Finset.Icc a b).restrict =
          (μ.map (intWindow (α := α) a l)).map W := by
            rw [Measure.map_map hW (measurable_intWindow a l), hcomp]
      _ = (ν.map (intWindow (α := α) a l)).map W := by rw [hw]
      _ = ν.map (Finset.Icc a b).restrict := by
            rw [Measure.map_map hW (measurable_intWindow a l), hcomp]
  · have hempty : Finset.Icc a b = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hne
      obtain ⟨i, hi⟩ := hne
      exact hab ((Finset.mem_Icc.mp hi).1.trans (Finset.mem_Icc.mp hi).2)
    rw [hempty]
    exact map_empty_restrict_eq_of_univ hmass

/-- The preceding bridge specialized to integer relabeling. -/
theorem map_Icc_restrict_eq_after_intPathShift_of_all_intWindow
    {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ] (k : ℤ)
    (hwindow : ∀ a : ℤ, ∀ l : ℕ,
      μ.map (intWindow (α := α) a l) =
        μ.map (intWindow (α := α) (k + a) l)) :
    ∀ a b : ℤ,
      μ.map (Finset.Icc a b).restrict =
        (μ.map (intPathShift (α := α) k)).map (Finset.Icc a b).restrict := by
  apply map_Icc_restrict_eq_of_all_intWindow
  · rw [Measure.map_apply (measurable_intPathShift (α := α) k) MeasurableSet.univ]
    simp
  intro a l
  calc
    μ.map (intWindow (α := α) a l) =
        μ.map (intWindow (α := α) (k + a) l) := hwindow a l
    _ = (μ.map (intPathShift (α := α) k)).map
        (intWindow (α := α) a l) := by
          symm
          rw [Measure.map_map (measurable_intWindow a l)
            (measurable_intPathShift (α := α) k)]
          rw [intWindow_intPathShift]

/-- Full two-sided stationarity of the balanced forward/reverse trajectory.
This is the cylinder-extension theorem used by the selected-Palm bridge. -/
theorem Kernel.ReversePairBalance.forwardReverseTwoSidedTrajMeasure_intPathShift_measurePreserving
    {π : Measure α} [IsProbabilityMeasure π] {K Kr : Kernel α α}
    [IsMarkovKernel K] [IsMarkovKernel Kr] [MeasurableEq α]
    (hbalance : Kernel.ReversePairBalance π K Kr)
    (hstationary : Kernel.Invariant K π) (k : ℤ) :
    MeasurePreserving (intPathShift (α := α) k)
      (forwardReverseTwoSidedTrajMeasure π K Kr)
      (forwardReverseTwoSidedTrajMeasure π K Kr) := by
  have hT : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := hT
  have hsource : IsProbabilityMeasure (forwardReverseTwoSidedSourceMeasure π K Kr) := by
    unfold forwardReverseTwoSidedSourceMeasure
    infer_instance
  letI : IsProbabilityMeasure (forwardReverseTwoSidedSourceMeasure π K Kr) := hsource
  have hP : IsProbabilityMeasure (forwardReverseTwoSidedTrajMeasure π K Kr) := by
    unfold forwardReverseTwoSidedTrajMeasure
    exact Measure.isProbabilityMeasure_map measurable_spliceForwardReverse.aemeasurable
  letI : IsProbabilityMeasure (forwardReverseTwoSidedTrajMeasure π K Kr) := hP
  apply intPathShift_measurePreserving_of_all_Icc_restrict k
  apply map_Icc_restrict_eq_after_intPathShift_of_all_intWindow
  intro a l
  calc
    (forwardReverseTwoSidedTrajMeasure π K Kr).map (intWindow a l) =
        (stationaryTrajMeasure π K).map (natPrefix l) :=
          hbalance.forwardReverseTwoSidedTrajMeasure_intWindow_law hstationary a l
    _ = (forwardReverseTwoSidedTrajMeasure π K Kr).map (intWindow (k + a) l) :=
          (hbalance.forwardReverseTwoSidedTrajMeasure_intWindow_law hstationary (k + a) l).symm

end

end AppliedModelingLib.Probability.Queueing
