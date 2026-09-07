import AppliedModelingLib.Foundations.Math.FiniteCorrelation
import AppliedModelingLib.SocialChoice.Ranking.MallowsSequential
import KR21Monoculture.MallowsPairwise
import KR21Monoculture.Theorem1

open scoped BigOperators
open AppliedModelingLib

namespace KR21Monoculture

/--
Geometric product weight on binary-interleaving height vectors.

A binary interleaving with `a` low letters and `b` high letters can be encoded
by the nondecreasing tuple of counts of high letters before each low letter.
This product-space version is the FKG base measure before restricting to the
nondecreasing-height sublattice.
-/
noncomputable def binaryHeightProductWeight
    (a b : ℕ) (q : ℝ) (h : Fin a → Fin (b + 1)) : ℝ :=
  q ^ (∑ j : Fin a, (h j : ℕ))

theorem binaryHeightProductWeight_nonneg
    (a b : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (h : Fin a → Fin (b + 1)) :
    0 ≤ binaryHeightProductWeight a b q h := by
  unfold binaryHeightProductWeight
  exact pow_nonneg hq _

theorem binaryHeightProductWeight_logSupermodular
    (a b : ℕ) (q : ℝ) (h₁ h₂ : Fin a → Fin (b + 1)) :
    binaryHeightProductWeight a b q h₁ *
        binaryHeightProductWeight a b q h₂ =
      binaryHeightProductWeight a b q (h₁ ⊓ h₂) *
        binaryHeightProductWeight a b q (h₁ ⊔ h₂) := by
  classical
  unfold binaryHeightProductWeight
  let s₁ : ℕ := ∑ j : Fin a, (h₁ j : ℕ)
  let s₂ : ℕ := ∑ j : Fin a, (h₂ j : ℕ)
  let sInf : ℕ := ∑ j : Fin a, ((h₁ ⊓ h₂) j : ℕ)
  let sSup : ℕ := ∑ j : Fin a, ((h₁ ⊔ h₂) j : ℕ)
  have hsum : sInf + sSup = s₁ + s₂ := by
    simp [sInf, sSup, s₁, s₂, ← Finset.sum_add_distrib,
      add_comm]
  calc
    q ^ s₁ * q ^ s₂ = q ^ (s₁ + s₂) := by
      rw [pow_add]
    _ = q ^ (sInf + sSup) := by
      rw [hsum]
    _ = q ^ sInf * q ^ sSup := by
      rw [pow_add]

theorem binaryHeightProductWeight_positiveAssociation_antitone
    (a b : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (f g : (Fin a → Fin (b + 1)) → ℝ)
    (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g)
    (hf : Antitone f) (hg : Antitone g) :
    (∑ h, binaryHeightProductWeight a b q h * f h) *
        ∑ h, binaryHeightProductWeight a b q h * g h ≤
      (∑ h, binaryHeightProductWeight a b q h) *
        ∑ h, binaryHeightProductWeight a b q h * (f h * g h) := by
  classical
  exact
    finiteFkg_antitone_real
      (α := Fin a → Fin (b + 1))
      (μ := binaryHeightProductWeight a b q)
      (f := f) (g := g)
      (binaryHeightProductWeight_nonneg a b hq)
      hf₀ hg₀ hf hg
      (fun h₁ h₂ => by
        rw [binaryHeightProductWeight_logSupermodular a b q h₁ h₂])

/-- Height vectors that encode binary interleavings are nondecreasing. -/
def binaryHeightMonotone {a b : ℕ} (h : Fin a → Fin (b + 1)) : Prop :=
  Monotone h

theorem binaryHeightMonotone_inf {a b : ℕ}
    {h₁ h₂ : Fin a → Fin (b + 1)}
    (hh₁ : binaryHeightMonotone h₁)
    (hh₂ : binaryHeightMonotone h₂) :
    binaryHeightMonotone (h₁ ⊓ h₂) := by
  intro i j hij
  exact inf_le_inf (hh₁ hij) (hh₂ hij)

theorem binaryHeightMonotone_sup {a b : ℕ}
    {h₁ h₂ : Fin a → Fin (b + 1)}
    (hh₁ : binaryHeightMonotone h₁)
    (hh₂ : binaryHeightMonotone h₂) :
    binaryHeightMonotone (h₁ ⊔ h₂) := by
  intro i j hij
  exact sup_le_sup (hh₁ hij) (hh₂ hij)

/--
Geometric height weight supported on monotone height vectors, i.e. on actual
binary interleavings.
-/
noncomputable def binaryHeightInterleavingWeight
    (a b : ℕ) (q : ℝ) (h : Fin a → Fin (b + 1)) : ℝ :=
  by
    classical
    exact if binaryHeightMonotone h then binaryHeightProductWeight a b q h else 0

theorem binaryHeightInterleavingWeight_nonneg
    (a b : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (h : Fin a → Fin (b + 1)) :
    0 ≤ binaryHeightInterleavingWeight a b q h := by
  classical
  unfold binaryHeightInterleavingWeight
  by_cases hh : binaryHeightMonotone h
  · simpa [hh] using binaryHeightProductWeight_nonneg a b hq h
  · simp [hh]

noncomputable def binaryHeightMonotoneFinset
    (a b : ℕ) :
    Finset {h : Fin a → Fin (b + 1) // binaryHeightMonotone h} :=
  @Finset.univ
    {h : Fin a → Fin (b + 1) // binaryHeightMonotone h}
    (@Subtype.fintype (Fin a → Fin (b + 1))
      (fun h : Fin a → Fin (b + 1) => binaryHeightMonotone h)
      (Classical.decPred _)
      inferInstance)

theorem binaryHeightInterleavingWeight_sum_eq_subtypeFinset
    (a b : ℕ) (q : ℝ)
    (F : (Fin a → Fin (b + 1)) → ℝ) :
    (∑ h, binaryHeightInterleavingWeight a b q h * F h) =
      ∑ h ∈ binaryHeightMonotoneFinset a b,
        binaryHeightInterleavingWeight a b q h.1 * F h.1 := by
  classical
  let f : (Fin a → Fin (b + 1)) → ℝ :=
    fun h => binaryHeightInterleavingWeight a b q h * F h
  let S : Finset (Fin a → Fin (b + 1)) :=
    Finset.univ.filter
      (fun h : Fin a → Fin (b + 1) => binaryHeightMonotone h)
  have hfiltered :
      (∑ h, f h) = ∑ h ∈ S, f h := by
    calc
      (∑ h, f h) =
          ∑ h : Fin a → Fin (b + 1),
            (if binaryHeightMonotone h then f h else 0) := by
        refine Finset.sum_congr rfl ?_
        intro h _
        by_cases hh : binaryHeightMonotone h
        · simp [f, hh]
        · simp [f, binaryHeightInterleavingWeight, hh]
      _ = ∑ h ∈ S, f h := by
        simp [S, Finset.sum_filter]
  have hsub :
      (∑ h : {h : Fin a → Fin (b + 1) // binaryHeightMonotone h}, f h.1) =
        ∑ h ∈ S, f h := by
    let γ := {h : Fin a → Fin (b + 1) // binaryHeightMonotone h}
    have huniv :
        (Finset.univ : Finset γ) =
          (@Finset.univ γ
            (Subtype.fintype
              (p := fun h : Fin a → Fin (b + 1) => binaryHeightMonotone h))) := by
      ext x
      simp
    have hsub0 :
        (∑ h ∈
            (@Finset.univ γ
              (Subtype.fintype
                (p := fun h : Fin a → Fin (b + 1) => binaryHeightMonotone h))),
            f h.1) =
          ∑ h ∈ S, f h := by
      simpa [f, S, γ] using
        (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset (Fin a → Fin (b + 1))))
          (f := f)
          (p := fun h : Fin a → Fin (b + 1) => binaryHeightMonotone h))
    rw [huniv]
    exact hsub0
  simpa [f, binaryHeightMonotoneFinset] using hfiltered.trans hsub.symm

theorem binaryHeightInterleavingWeight_logSupermodular
    (a b : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (h₁ h₂ : Fin a → Fin (b + 1)) :
    binaryHeightInterleavingWeight a b q h₁ *
        binaryHeightInterleavingWeight a b q h₂ ≤
      binaryHeightInterleavingWeight a b q (h₁ ⊓ h₂) *
        binaryHeightInterleavingWeight a b q (h₁ ⊔ h₂) := by
  classical
  by_cases hh₁ : binaryHeightMonotone h₁
  · by_cases hh₂ : binaryHeightMonotone h₂
    · have hinf : binaryHeightMonotone (h₁ ⊓ h₂) :=
        binaryHeightMonotone_inf hh₁ hh₂
      have hsup : binaryHeightMonotone (h₁ ⊔ h₂) :=
        binaryHeightMonotone_sup hh₁ hh₂
      exact le_of_eq (by
        simpa [binaryHeightInterleavingWeight, hh₁, hh₂, hinf, hsup] using
          binaryHeightProductWeight_logSupermodular a b q h₁ h₂)
    · have hrhs :
          0 ≤
            binaryHeightInterleavingWeight a b q (h₁ ⊓ h₂) *
              binaryHeightInterleavingWeight a b q (h₁ ⊔ h₂) :=
        mul_nonneg
          (binaryHeightInterleavingWeight_nonneg a b hq (h₁ ⊓ h₂))
          (binaryHeightInterleavingWeight_nonneg a b hq (h₁ ⊔ h₂))
      simpa [binaryHeightInterleavingWeight, hh₂] using hrhs
  · have hrhs :
        0 ≤
          binaryHeightInterleavingWeight a b q (h₁ ⊓ h₂) *
            binaryHeightInterleavingWeight a b q (h₁ ⊔ h₂) :=
      mul_nonneg
        (binaryHeightInterleavingWeight_nonneg a b hq (h₁ ⊓ h₂))
        (binaryHeightInterleavingWeight_nonneg a b hq (h₁ ⊔ h₂))
    simpa [binaryHeightInterleavingWeight, hh₁] using hrhs

theorem binaryHeightInterleavingWeight_positiveAssociation_antitone
    (a b : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (f g : (Fin a → Fin (b + 1)) → ℝ)
    (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g)
    (hf : Antitone f) (hg : Antitone g) :
    (∑ h, binaryHeightInterleavingWeight a b q h * f h) *
        ∑ h, binaryHeightInterleavingWeight a b q h * g h ≤
      (∑ h, binaryHeightInterleavingWeight a b q h) *
        ∑ h, binaryHeightInterleavingWeight a b q h * (f h * g h) := by
  classical
  exact
    finiteFkg_antitone_real
      (α := Fin a → Fin (b + 1))
      (μ := binaryHeightInterleavingWeight a b q)
      (f := f) (g := g)
      (binaryHeightInterleavingWeight_nonneg a b hq)
      hf₀ hg₀ hf hg
      (binaryHeightInterleavingWeight_logSupermodular a b hq)

/-- Indicator that the first binary-interleaving letter is low. -/
noncomputable def binaryFirstLowIndicator
    (a b : ℕ) (h : Fin (a + 1) → Fin (b + 1)) : ℝ :=
  if h 0 = 0 then 1 else 0

theorem binaryFirstLowIndicator_nonneg
    (a b : ℕ) (h : Fin (a + 1) → Fin (b + 1)) :
    0 ≤ binaryFirstLowIndicator a b h := by
  classical
  unfold binaryFirstLowIndicator
  by_cases hh : h 0 = 0 <;> simp [hh]

theorem binaryFirstLowIndicator_antitone
    (a b : ℕ) :
    Antitone (binaryFirstLowIndicator a b) := by
  classical
  intro h₁ h₂ hle
  unfold binaryFirstLowIndicator
  by_cases hh₂ : h₂ 0 = 0
  · have hh₁ : h₁ 0 = 0 := by
      have hle0 : h₁ 0 ≤ h₂ 0 := hle 0
      have hval : (h₁ 0 : ℕ) ≤ 0 := by
        simpa [hh₂] using hle0
      exact Fin.ext (Nat.eq_zero_of_le_zero hval)
    simp [hh₁, hh₂]
  · simp [hh₂]
    by_cases hh₁ : h₁ 0 = 0 <;> simp [hh₁]

theorem binaryHeightInterleavingWeight_firstLow_positiveAssociation_antitone
    (a b : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (f : (Fin (a + 1) → Fin (b + 1)) → ℝ)
    (hf₀ : 0 ≤ f) (hf : Antitone f) :
    (∑ h, binaryHeightInterleavingWeight (a + 1) b q h * f h) *
        ∑ h, binaryHeightInterleavingWeight (a + 1) b q h *
          binaryFirstLowIndicator a b h ≤
      (∑ h, binaryHeightInterleavingWeight (a + 1) b q h) *
        ∑ h, binaryHeightInterleavingWeight (a + 1) b q h *
          (f h * binaryFirstLowIndicator a b h) := by
  classical
  exact
    binaryHeightInterleavingWeight_positiveAssociation_antitone
      (a + 1) b hq f (binaryFirstLowIndicator a b)
      hf₀ (binaryFirstLowIndicator_nonneg a b)
      hf (binaryFirstLowIndicator_antitone a b)

/-- Inversion count of a finite permutation in the natural order on `Fin m`. -/
noncomputable def finPermInversionCount (m : ℕ)
    (σ : Equiv.Perm (Fin m)) : ℕ :=
  ((Finset.univ : Finset (Fin m × Fin m)).filter
    (fun ij => ij.1 < ij.2 ∧ σ ij.2 < σ ij.1)).card

theorem finPermInversionCount_reindex
    {m : ℕ} {α : Type*} [Fintype α]
    (e : α ≃ Fin m) (σ : Equiv.Perm (Fin m)) :
    finPermInversionCount m σ =
      ((Finset.univ : Finset (α × α)).filter
        (fun xy => e xy.1 < e xy.2 ∧ σ (e xy.2) < σ (e xy.1))).card := by
  classical
  unfold finPermInversionCount
  refine Finset.card_bij
    (fun ij _ => (e.symm ij.1, e.symm ij.2)) ?hmem ?hinj ?hsurj
  · intro ij hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij ⊢
    simpa using hij
  · intro ij hij kl hkl heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij hkl
    apply Prod.ext
    · apply e.symm.injective
      exact (Prod.ext_iff.mp heq).1
    · apply e.symm.injective
      exact (Prod.ext_iff.mp heq).2
  · intro xy hxy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxy
    refine ⟨(e xy.1, e xy.2), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa using hxy
    · simp

theorem kendallTau_refl_eq_finPermInversionCount
    {n : ℕ} (π : Ranking n) :
    kendallTau (Equiv.refl (Candidate n)) π =
      finPermInversionCount (n + 2) π := by
  classical
  unfold kendallTau inversionFinset finPermInversionCount invertedPair rankOf
  refine Finset.card_bij
    (fun ab _ => (π.symm ab.2, π.symm ab.1)) ?hmem ?hinj ?hsurj
  · intro ab hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab ⊢
    constructor
    · simpa using hab.2
    · simpa using hab.1
  · intro ab hab cd hcd heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab hcd
    apply Prod.ext
    · apply π.symm.injective
      exact (Prod.ext_iff.mp heq).2
    · apply π.symm.injective
      exact (Prod.ext_iff.mp heq).1
  · intro ij hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
    refine ⟨(π ij.2, π ij.1), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · simpa using hij.2
      · simpa using hij.1
    · simp

noncomputable def prefixSplitInternalWeight
    (n : ℕ) (k : Candidate (n + 1)) (q : ℝ)
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val))) : ℝ :=
  q ^ finPermInversionCount (k.val + 1) lo *
    q ^ finPermInversionCount (n + 2 - k.val) hi

theorem prefixSplitInternalWeight_nonneg
    (n : ℕ) (k : Candidate (n + 1)) {q : ℝ} (hq : 0 ≤ q)
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val))) :
    0 ≤ prefixSplitInternalWeight n k q lo hi := by
  unfold prefixSplitInternalWeight
  exact mul_nonneg (pow_nonneg hq _) (pow_nonneg hq _)

/-- Position of the `i`-th low letter in the binary word encoded by a height vector. -/
def binaryHeightLowPosition {a b : ℕ}
    (h : Fin a → Fin (b + 1)) (i : Fin a) : Fin (a + b) :=
  ⟨i.val + (h i).val, by
    have hi : i.val < a := i.isLt
    have hh : (h i).val < b + 1 := (h i).isLt
    omega⟩

@[simp] theorem binaryHeightLowPosition_val {a b : ℕ}
    (h : Fin a → Fin (b + 1)) (i : Fin a) :
    (binaryHeightLowPosition h i : ℕ) = i.val + (h i).val := rfl

/-- Position of the `j`-th high letter in the binary word encoded by a height vector. -/
noncomputable def binaryHeightHighPosition {a b : ℕ}
    (h : Fin a → Fin (b + 1)) (j : Fin b) : Fin (a + b) :=
  ⟨j.val + ((Finset.univ : Finset (Fin a)).filter
      (fun i => (h i : ℕ) ≤ j.val)).card, by
    have hj : j.val < b := j.isLt
    have hcard :
        ((Finset.univ : Finset (Fin a)).filter
          (fun i => (h i : ℕ) ≤ j.val)).card ≤ a := by
      calc
        ((Finset.univ : Finset (Fin a)).filter
          (fun i => (h i : ℕ) ≤ j.val)).card
            ≤ (Finset.univ : Finset (Fin a)).card := Finset.card_filter_le _ _
        _ = a := by simp
    omega⟩

@[simp] theorem binaryHeightHighPosition_val {a b : ℕ}
    (h : Fin a → Fin (b + 1)) (j : Fin b) :
    (binaryHeightHighPosition h j : ℕ) =
      j.val + ((Finset.univ : Finset (Fin a)).filter
        (fun i => (h i : ℕ) ≤ j.val)).card := rfl

theorem binaryHeightLowPosition_strictMono {a b : ℕ}
    {h : Fin a → Fin (b + 1)} (hh : binaryHeightMonotone h) :
    StrictMono (binaryHeightLowPosition h) := by
  intro i j hij
  rw [Fin.lt_def]
  have hmono : (h i : ℕ) ≤ (h j : ℕ) := by
    exact hh (le_of_lt hij)
  have hijv : i.val < j.val := hij
  simp [binaryHeightLowPosition]
  omega

theorem binaryHeightHighPosition_strictMono {a b : ℕ}
    (h : Fin a → Fin (b + 1)) :
    StrictMono (binaryHeightHighPosition h : Fin b → Fin (a + b)) := by
  intro i j hij
  rw [Fin.lt_def]
  have hsubset :
      ((Finset.univ : Finset (Fin a)).filter
          (fun x => (h x : ℕ) ≤ i.val)) ⊆
        ((Finset.univ : Finset (Fin a)).filter
          (fun x => (h x : ℕ) ≤ j.val)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact le_trans hx (le_of_lt hij)
  have hcard := Finset.card_le_card hsubset
  simp [binaryHeightHighPosition]
  omega

/-- Position map for the low/high sum domain encoded by a binary height vector. -/
noncomputable def binaryHeightPositionMap {a b : ℕ}
    (h : Fin a → Fin (b + 1)) : (Fin a ⊕ Fin b) → Fin (a + b) :=
  Sum.elim (binaryHeightLowPosition h) (binaryHeightHighPosition h)

@[simp] theorem binaryHeightPositionMap_inl {a b : ℕ}
    (h : Fin a → Fin (b + 1)) (i : Fin a) :
    binaryHeightPositionMap h (Sum.inl i) = binaryHeightLowPosition h i := rfl

@[simp] theorem binaryHeightPositionMap_inr {a b : ℕ}
    (h : Fin a → Fin (b + 1)) (j : Fin b) :
    binaryHeightPositionMap h (Sum.inr j) = binaryHeightHighPosition h j := rfl

theorem binaryHeightLowPosition_lt_highPosition_of_height_le {a b : ℕ}
    {h : Fin a → Fin (b + 1)} (hh : binaryHeightMonotone h)
    {i : Fin a} {j : Fin b} (hle : (h i : ℕ) ≤ j.val) :
    binaryHeightLowPosition h i < binaryHeightHighPosition h j := by
  classical
  rw [Fin.lt_def]
  have hsubset :
      Finset.Iic i ⊆
        ((Finset.univ : Finset (Fin a)).filter
          (fun x => (h x : ℕ) ≤ j.val)) := by
    intro x hx
    simp only [Finset.mem_Iic, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact le_trans (hh hx) hle
  have hcard_ge :
      i.val + 1 ≤
        ((Finset.univ : Finset (Fin a)).filter
          (fun x => (h x : ℕ) ≤ j.val)).card := by
    have hcard := Finset.card_le_card hsubset
    simpa using hcard
  simp [binaryHeightLowPosition, binaryHeightHighPosition]
  omega

theorem binaryHeightHighPosition_lt_lowPosition_of_lt_height {a b : ℕ}
    {h : Fin a → Fin (b + 1)} (hh : binaryHeightMonotone h)
    {i : Fin a} {j : Fin b} (hlt : j.val < (h i : ℕ)) :
    binaryHeightHighPosition h j < binaryHeightLowPosition h i := by
  classical
  rw [Fin.lt_def]
  have hsubset :
      ((Finset.univ : Finset (Fin a)).filter
          (fun x => (h x : ℕ) ≤ j.val)) ⊆
        Finset.Iio i := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio] at hx ⊢
    by_contra hnot
    have hix : i ≤ x := le_of_not_gt hnot
    have hhi_le_hx : (h i : ℕ) ≤ (h x : ℕ) := hh hix
    exact not_lt_of_ge (le_trans hhi_le_hx hx) hlt
  have hcard_le :
      ((Finset.univ : Finset (Fin a)).filter
          (fun x => (h x : ℕ) ≤ j.val)).card ≤ i.val := by
    have hcard := Finset.card_le_card hsubset
    simpa using hcard
  simp [binaryHeightLowPosition, binaryHeightHighPosition]
  omega

theorem binaryHeightHighPosition_lt_lowPosition_iff {a b : ℕ}
    {h : Fin a → Fin (b + 1)} (hh : binaryHeightMonotone h)
    (i : Fin a) (j : Fin b) :
    binaryHeightHighPosition h j < binaryHeightLowPosition h i ↔
      j.val < (h i : ℕ) := by
  constructor
  · intro hlt
    by_contra hnot
    have hle : (h i : ℕ) ≤ j.val := Nat.le_of_not_gt hnot
    have hlow_lt_high :=
      binaryHeightLowPosition_lt_highPosition_of_height_le
        hh (i := i) (j := j) hle
    exact (lt_asymm hlt) hlow_lt_high
  · intro hlt
    exact binaryHeightHighPosition_lt_lowPosition_of_lt_height
      hh (i := i) (j := j) hlt

theorem binaryHeightPositionMap_injective_of_monotone {a b : ℕ}
    {h : Fin a → Fin (b + 1)} (hh : binaryHeightMonotone h) :
    Function.Injective (binaryHeightPositionMap h) := by
  intro x y hxy
  rcases x with i | j <;> rcases y with i' | j'
  · have hinj := (binaryHeightLowPosition_strictMono hh).injective
    exact congrArg Sum.inl (hinj hxy)
  · exfalso
    have hxy' : binaryHeightLowPosition h i = binaryHeightHighPosition h j' := by
      simpa [binaryHeightPositionMap] using hxy
    by_cases hle : (h i : ℕ) ≤ j'.val
    · have hlt :=
        binaryHeightLowPosition_lt_highPosition_of_height_le
          hh (i := i) (j := j') hle
      rw [hxy'] at hlt
      exact (lt_irrefl _ hlt)
    · have hlt_height : j'.val < (h i : ℕ) := Nat.lt_of_not_ge hle
      have hlt :=
        binaryHeightHighPosition_lt_lowPosition_of_lt_height
          hh (i := i) (j := j') hlt_height
      rw [hxy'] at hlt
      exact (lt_irrefl _ hlt)
  · exfalso
    have hxy' : binaryHeightHighPosition h j = binaryHeightLowPosition h i' := by
      simpa [binaryHeightPositionMap] using hxy
    by_cases hle : (h i' : ℕ) ≤ j.val
    · have hlt :=
        binaryHeightLowPosition_lt_highPosition_of_height_le
          hh (i := i') (j := j) hle
      rw [← hxy'] at hlt
      exact (lt_irrefl _ hlt)
    · have hlt_height : j.val < (h i' : ℕ) := Nat.lt_of_not_ge hle
      have hlt :=
        binaryHeightHighPosition_lt_lowPosition_of_lt_height
          hh (i := i') (j := j) hlt_height
      rw [hxy'] at hlt
      exact (lt_irrefl _ hlt)
  · have hinj := (binaryHeightHighPosition_strictMono h).injective
    exact congrArg Sum.inr (hinj hxy)

/-- Binary height vectors induce an equivalence between low/high labels and word positions. -/
noncomputable def binaryHeightPositionEquiv {a b : ℕ}
    (h : Fin a → Fin (b + 1)) (hh : binaryHeightMonotone h) :
    (Fin a ⊕ Fin b) ≃ Fin (a + b) :=
  Equiv.ofBijective (binaryHeightPositionMap h) <| by
    exact (Fintype.bijective_iff_injective_and_card
      (binaryHeightPositionMap h)).mpr
      ⟨binaryHeightPositionMap_injective_of_monotone hh, by simp⟩

@[simp] theorem binaryHeightPositionEquiv_apply_inl {a b : ℕ}
    (h : Fin a → Fin (b + 1)) (hh : binaryHeightMonotone h)
    (i : Fin a) :
    binaryHeightPositionEquiv h hh (Sum.inl i) =
      binaryHeightLowPosition h i := rfl

@[simp] theorem binaryHeightPositionEquiv_apply_inr {a b : ℕ}
    (h : Fin a → Fin (b + 1)) (hh : binaryHeightMonotone h)
    (j : Fin b) :
    binaryHeightPositionEquiv h hh (Sum.inr j) =
      binaryHeightHighPosition h j := rfl

/-- Lower one low letter's height by one. -/
def binaryHeightLowerAt {a b : ℕ}
    (h : Fin a → Fin (b + 1)) (i : Fin a)
    (hpos : 0 < (h i : ℕ)) : Fin a → Fin (b + 1) :=
  fun x =>
    if hx : x = i then
      ⟨(h i).val - 1, by
        have hi := (h i).isLt
        omega⟩
    else
      h x

@[simp] theorem binaryHeightLowerAt_self {a b : ℕ}
    (h : Fin a → Fin (b + 1)) (i : Fin a)
    (hpos : 0 < (h i : ℕ)) :
    binaryHeightLowerAt h i hpos i =
      ⟨(h i).val - 1, by
        have hi := (h i).isLt
        omega⟩ := by
  simp [binaryHeightLowerAt]

theorem binaryHeightLowerAt_of_ne {a b : ℕ}
    (h : Fin a → Fin (b + 1)) {i x : Fin a}
    (hpos : 0 < (h i : ℕ)) (hne : x ≠ i) :
    binaryHeightLowerAt h i hpos x = h x := by
  simp [binaryHeightLowerAt, hne]

@[simp] theorem binaryHeightLowerAt_self_val {a b : ℕ}
    (h : Fin a → Fin (b + 1)) (i : Fin a)
    (hpos : 0 < (h i : ℕ)) :
    (binaryHeightLowerAt h i hpos i : ℕ) = (h i : ℕ) - 1 := by
  simp [binaryHeightLowerAt]

theorem binaryHeightMonotone_lowerAt {a b : ℕ}
    {h : Fin a → Fin (b + 1)} {i : Fin a}
    (hh : binaryHeightMonotone h)
    (hpos : 0 < (h i : ℕ))
    (hleft : ∀ j : Fin a, j < i → (h j : ℕ) < (h i : ℕ)) :
    binaryHeightMonotone (binaryHeightLowerAt h i hpos) := by
  intro x y hxy
  by_cases hxi : x = i
  · subst x
    by_cases hyi : y = i
    · subst y
      exact le_rfl
    · have hiy : i < y := lt_of_le_of_ne hxy (fun h => hyi h.symm)
      have hmono : (h i : ℕ) ≤ (h y : ℕ) := hh (le_of_lt hiy)
      rw [Fin.le_iff_val_le_val]
      simp [binaryHeightLowerAt, hyi]
      omega
  · by_cases hyi : y = i
    · subst y
      have hxi_lt : x < i := lt_of_le_of_ne hxy hxi
      have hstrict : (h x : ℕ) < (h i : ℕ) := hleft x hxi_lt
      rw [Fin.le_iff_val_le_val]
      simp [binaryHeightLowerAt, hxi]
      omega
    · have hmono : h x ≤ h y := hh hxy
      simpa [binaryHeightLowerAt, hxi, hyi] using hmono

/-- Total cross-inversion height of a binary height vector. -/
noncomputable def binaryHeightSum {a b : ℕ}
    (h : Fin a → Fin (b + 1)) : ℕ :=
  ∑ i : Fin a, (h i : ℕ)

/-- Cross inversions encoded by a binary height vector: high letter before low letter. -/
noncomputable def binaryHeightCrossInversionFinset {a b : ℕ}
    (h : Fin a → Fin (b + 1)) : Finset (Fin a × Fin b) := by
  classical
  exact Finset.univ.filter (fun ij => ij.2.val < (h ij.1 : ℕ))

theorem binaryHeightCrossInversionFinset_card {a b : ℕ}
    (h : Fin a → Fin (b + 1)) :
    (binaryHeightCrossInversionFinset h).card = binaryHeightSum h := by
  classical
  unfold binaryHeightCrossInversionFinset binaryHeightSum
  rw [← Finset.univ_product_univ]
  rw [Finset.card_filter]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl ?_
  intro i _
  have hcard :
      ((Finset.univ : Finset (Fin b)).filter
        (fun j => j.val < (h i : ℕ))).card = (h i : ℕ) := by
    have hraw := Fin.card_filter_val_lt (n := b) (m := (h i : ℕ))
    have hmin : min b (h i : ℕ) = (h i : ℕ) := by
      have hle : (h i : ℕ) ≤ b := by
        have hi := (h i).isLt
        omega
      exact Nat.min_eq_right hle
    simpa [hmin] using hraw
  rw [← hcard]
  rw [Finset.card_filter]

theorem binaryHeightSum_lowerAt_lt {a b : ℕ}
    (h : Fin a → Fin (b + 1)) {i : Fin a}
    (hpos : 0 < (h i : ℕ)) :
    binaryHeightSum (binaryHeightLowerAt h i hpos) <
      binaryHeightSum h := by
  classical
  unfold binaryHeightSum
  refine Finset.sum_lt_sum ?hle ?hstrict
  · intro x _
    by_cases hxi : x = i
    · subst x
      simp [binaryHeightLowerAt]
    · simp [binaryHeightLowerAt_of_ne h hpos hxi]
  · exact ⟨i, Finset.mem_univ _, by
      simp [binaryHeightLowerAt]
      simpa using hpos⟩

theorem binaryHeightHighPosition_cross_val {a b : ℕ}
    {h : Fin a → Fin (b + 1)} (hh : binaryHeightMonotone h)
    {i : Fin a} (hpos : 0 < (h i : ℕ))
    (hleft : ∀ j : Fin a, j < i → (h j : ℕ) < (h i : ℕ)) :
    (binaryHeightHighPosition h
        (⟨(h i).val - 1, by
          have hi := (h i).isLt
          omega⟩ : Fin b) : ℕ) =
      i.val + (h i).val - 1 := by
  classical
  have hfilter :
      ((Finset.univ : Finset (Fin a)).filter
        (fun x => (h x : ℕ) ≤ (h i).val - 1)) =
        Finset.Iio i := by
    ext x
    constructor
    · intro hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_Iio]
      by_contra hnot
      have hix : i ≤ x := le_of_not_gt hnot
      have hmono : (h i : ℕ) ≤ (h x : ℕ) := hh hix
      omega
    · intro hx
      simp only [Finset.mem_Iio] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hstrict : (h x : ℕ) < (h i : ℕ) := hleft x hx
      omega
  simp [binaryHeightHighPosition, hfilter]
  omega

theorem binaryHeightHighPosition_lowerAt_cross_val {a b : ℕ}
    {h : Fin a → Fin (b + 1)} (hh : binaryHeightMonotone h)
    {i : Fin a} (hpos : 0 < (h i : ℕ))
    (hleft : ∀ j : Fin a, j < i → (h j : ℕ) < (h i : ℕ)) :
    (binaryHeightHighPosition (binaryHeightLowerAt h i hpos)
        (⟨(h i).val - 1, by
          have hi := (h i).isLt
          omega⟩ : Fin b) : ℕ) =
      i.val + (h i).val := by
  classical
  have hfilter :
      ((Finset.univ : Finset (Fin a)).filter
        (fun x => (binaryHeightLowerAt h i hpos x : ℕ) ≤ (h i).val - 1)) =
        Finset.Iic i := by
    ext x
    constructor
    · intro hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_Iic]
      by_contra hnot
      have hix : i < x := lt_of_not_ge hnot
      have hmono : (h i : ℕ) ≤ (h x : ℕ) := hh (le_of_lt hix)
      have hx_ne : x ≠ i := ne_of_gt hix
      rw [binaryHeightLowerAt_of_ne h hpos hx_ne] at hx
      omega
    · intro hx
      simp only [Finset.mem_Iic] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hxi : x = i
      · subst x
        simp [binaryHeightLowerAt]
      · have hxi_lt : x < i := lt_of_le_of_ne hx hxi
        have hstrict : (h x : ℕ) < (h i : ℕ) := hleft x hxi_lt
        rw [binaryHeightLowerAt_of_ne h hpos hxi]
        omega
  simp [binaryHeightHighPosition, hfilter]
  omega

theorem binaryHeightLowPosition_lowerAt_of_ne {a b : ℕ}
    (h : Fin a → Fin (b + 1)) {i x : Fin a}
    (hpos : 0 < (h i : ℕ)) (hne : x ≠ i) :
    binaryHeightLowPosition (binaryHeightLowerAt h i hpos) x =
      binaryHeightLowPosition h x := by
  ext
  simp [binaryHeightLowPosition, binaryHeightLowerAt_of_ne h hpos hne]

theorem binaryHeightLowPosition_lowerAt_self_val {a b : ℕ}
    (h : Fin a → Fin (b + 1)) (i : Fin a)
    (hpos : 0 < (h i : ℕ)) :
    (binaryHeightLowPosition (binaryHeightLowerAt h i hpos) i : ℕ) =
      i.val + (h i).val - 1 := by
  simp [binaryHeightLowPosition, binaryHeightLowerAt]
  omega

theorem binaryHeightHighPosition_lowerAt_of_ne_cross {a b : ℕ}
    (h : Fin a → Fin (b + 1)) {i : Fin a}
    (hpos : 0 < (h i : ℕ)) {j : Fin b}
    (hne : j.val ≠ (h i).val - 1) :
    binaryHeightHighPosition (binaryHeightLowerAt h i hpos) j =
      binaryHeightHighPosition h j := by
  classical
  ext
  have hfilter :
      ((Finset.univ : Finset (Fin a)).filter
        (fun x => (binaryHeightLowerAt h i hpos x : ℕ) ≤ j.val)) =
        ((Finset.univ : Finset (Fin a)).filter
          (fun x => (h x : ℕ) ≤ j.val)) := by
    ext x
    by_cases hxi : x = i
    · subst x
      simp [binaryHeightLowerAt]
      omega
    · simp [binaryHeightLowerAt_of_ne h hpos hxi]
  simp [binaryHeightHighPosition, hfilter]

/-- Candidate in the low side of a center-prefix split. -/
def prefixSplitCandidate
    (n : ℕ) (k : Candidate (n + 1))
    (i : Fin (k.val + 1)) : Candidate (n + 1) :=
  ⟨i.val, by
    have hi : i.val < k.val + 1 := i.isLt
    have hk : k.val < n + 3 := k.isLt
    omega⟩

@[simp] theorem prefixSplitCandidate_val
    (n : ℕ) (k : Candidate (n + 1))
    (i : Fin (k.val + 1)) :
    (prefixSplitCandidate n k i : ℕ) = i.val := rfl

theorem prefixSplitCandidate_le
    (n : ℕ) (k : Candidate (n + 1))
    (i : Fin (k.val + 1)) :
    prefixSplitCandidate n k i ≤ k := by
  exact Nat.le_of_lt_succ i.isLt

/-- Candidate in the high side of a center-prefix split. -/
def suffixSplitCandidate
    (n : ℕ) (k : Candidate (n + 1))
    (i : Fin (n + 2 - k.val)) : Candidate (n + 1) :=
  ⟨k.val + 1 + i.val, by
    have hk : k.val < n + 3 := k.isLt
    have hi : i.val < n + 2 - k.val := i.isLt
    omega⟩

@[simp] theorem suffixSplitCandidate_val
    (n : ℕ) (k : Candidate (n + 1))
    (i : Fin (n + 2 - k.val)) :
    (suffixSplitCandidate n k i : ℕ) = k.val + 1 + i.val := rfl

theorem k_lt_suffixSplitCandidate
    (n : ℕ) (k : Candidate (n + 1))
    (i : Fin (n + 2 - k.val)) :
    k < suffixSplitCandidate n k i := by
  change k.val < k.val + 1 + i.val
  omega

theorem prefixSplitCandidate_ne_suffixSplitCandidate
    (n : ℕ) (k : Candidate (n + 1))
    (i : Fin (k.val + 1)) (j : Fin (n + 2 - k.val)) :
    prefixSplitCandidate n k i ≠ suffixSplitCandidate n k j := by
  intro h
  have hle : prefixSplitCandidate n k i ≤ k :=
    prefixSplitCandidate_le n k i
  have hlt : k < prefixSplitCandidate n k i := by
    simpa [h] using k_lt_suffixSplitCandidate n k j
  exact not_lt_of_ge hle hlt

/-- Positions in a ranking occupied by candidates in the center prefix up to `k`. -/
noncomputable def prefixSplitLowPositionFinset
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) :
    Finset (Candidate (n + 1)) := by
  classical
  exact Finset.univ.filter (fun p : Candidate (n + 1) => π p ≤ k)

@[simp] theorem mem_prefixSplitLowPositionFinset
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (p : Candidate (n + 1)) :
    p ∈ prefixSplitLowPositionFinset n k π ↔ π p ≤ k := by
  classical
  simp [prefixSplitLowPositionFinset]

theorem image_prefixSplitLowPositionFinset
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) :
    (prefixSplitLowPositionFinset n k π).image π = Finset.Iic k := by
  classical
  ext c
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨p, hp, rfl⟩
    simpa using (mem_prefixSplitLowPositionFinset n k π p).mp hp
  · intro hc
    refine Finset.mem_image.mpr ?_
    refine ⟨π.symm c, ?_, by simp⟩
    exact (mem_prefixSplitLowPositionFinset n k π (π.symm c)).mpr (by
      simpa using hc)

@[simp] theorem card_prefixSplitLowPositionFinset
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) :
    (prefixSplitLowPositionFinset n k π).card = k.val + 1 := by
  classical
  calc
    (prefixSplitLowPositionFinset n k π).card =
        ((prefixSplitLowPositionFinset n k π).image π).card := by
          rw [Finset.card_image_of_injective _ π.injective]
    _ = (Finset.Iic k).card := by
          rw [image_prefixSplitLowPositionFinset]
    _ = k.val + 1 := by
          exact Fin.card_Iic k

/-- Positions in a ranking occupied by candidates strictly after the center prefix `k`. -/
noncomputable def prefixSplitHighPositionFinset
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) :
    Finset (Candidate (n + 1)) := by
  classical
  exact Finset.univ.filter (fun p : Candidate (n + 1) => k < π p)

@[simp] theorem mem_prefixSplitHighPositionFinset
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (p : Candidate (n + 1)) :
    p ∈ prefixSplitHighPositionFinset n k π ↔ k < π p := by
  classical
  simp [prefixSplitHighPositionFinset]

theorem image_prefixSplitHighPositionFinset
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) :
    (prefixSplitHighPositionFinset n k π).image π = Finset.Ioi k := by
  classical
  ext c
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨p, hp, rfl⟩
    simpa using (mem_prefixSplitHighPositionFinset n k π p).mp hp
  · intro hc
    refine Finset.mem_image.mpr ?_
    refine ⟨π.symm c, ?_, by simp⟩
    exact (mem_prefixSplitHighPositionFinset n k π (π.symm c)).mpr (by
      simpa using hc)

@[simp] theorem card_prefixSplitHighPositionFinset
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) :
    (prefixSplitHighPositionFinset n k π).card = n + 2 - k.val := by
  classical
  calc
    (prefixSplitHighPositionFinset n k π).card =
        ((prefixSplitHighPositionFinset n k π).image π).card := by
          rw [Finset.card_image_of_injective _ π.injective]
    _ = (Finset.Ioi k).card := by
          rw [image_prefixSplitHighPositionFinset]
    _ = n + 2 - k.val := by
          rw [Fin.card_Ioi]
          omega

/-- Increasing enumeration of positions occupied by center-prefix candidates. -/
noncomputable def prefixSplitLowPositionOrderIso
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) :
    Fin (k.val + 1) ≃o prefixSplitLowPositionFinset n k π :=
  (prefixSplitLowPositionFinset n k π).orderIsoOfFin
    (card_prefixSplitLowPositionFinset n k π)

/-- The `i`-th center-prefix position in the ranking. -/
noncomputable def prefixSplitLowPosition
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (i : Fin (k.val + 1)) : Candidate (n + 1) :=
  (prefixSplitLowPositionOrderIso n k π i).1

@[simp] theorem prefixSplitLowPosition_mem
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (i : Fin (k.val + 1)) :
    prefixSplitLowPosition n k π i ∈
      prefixSplitLowPositionFinset n k π :=
  (prefixSplitLowPositionOrderIso n k π i).2

theorem prefixSplitLowPosition_apply_le
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (i : Fin (k.val + 1)) :
    π (prefixSplitLowPosition n k π i) ≤ k := by
  exact (mem_prefixSplitLowPositionFinset n k π
    (prefixSplitLowPosition n k π i)).mp
    (prefixSplitLowPosition_mem n k π i)

theorem prefixSplitLowPosition_mono
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) :
    Monotone (prefixSplitLowPosition n k π) := by
  intro i j hij
  exact Subtype.coe_le_coe.mpr
    ((prefixSplitLowPositionOrderIso n k π).monotone hij)

theorem prefixSplitLowPosition_strictMono
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) :
    StrictMono (prefixSplitLowPosition n k π) := by
  intro i j hij
  exact Subtype.coe_lt_coe.mpr
    ((prefixSplitLowPositionOrderIso n k π).strictMono hij)

/-- Increasing enumeration of positions occupied by candidates after the center prefix. -/
noncomputable def prefixSplitHighPositionOrderIso
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) :
    Fin (n + 2 - k.val) ≃o prefixSplitHighPositionFinset n k π :=
  (prefixSplitHighPositionFinset n k π).orderIsoOfFin
    (card_prefixSplitHighPositionFinset n k π)

/-- The `j`-th strict-suffix position in the ranking. -/
noncomputable def prefixSplitHighPosition
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (j : Fin (n + 2 - k.val)) : Candidate (n + 1) :=
  (prefixSplitHighPositionOrderIso n k π j).1

@[simp] theorem prefixSplitHighPosition_mem
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (j : Fin (n + 2 - k.val)) :
    prefixSplitHighPosition n k π j ∈
      prefixSplitHighPositionFinset n k π :=
  (prefixSplitHighPositionOrderIso n k π j).2

theorem prefixSplitHighPosition_apply_gt
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (j : Fin (n + 2 - k.val)) :
    k < π (prefixSplitHighPosition n k π j) := by
  exact (mem_prefixSplitHighPositionFinset n k π
    (prefixSplitHighPosition n k π j)).mp
    (prefixSplitHighPosition_mem n k π j)

theorem prefixSplitHighPosition_mono
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) :
    Monotone (prefixSplitHighPosition n k π) := by
  intro i j hij
  exact Subtype.coe_le_coe.mpr
    ((prefixSplitHighPositionOrderIso n k π).monotone hij)

theorem prefixSplitHighPosition_strictMono
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) :
    StrictMono (prefixSplitHighPosition n k π) := by
  intro i j hij
  exact Subtype.coe_lt_coe.mpr
    ((prefixSplitHighPositionOrderIso n k π).strictMono hij)

/-- Internal order of the center-prefix candidates induced by their positions in `π`. -/
noncomputable def prefixSplitLowOrder
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) :
    Equiv.Perm (Fin (k.val + 1)) :=
  Equiv.ofBijective
    (fun i : Fin (k.val + 1) =>
      ⟨(π (prefixSplitLowPosition n k π i)).val, by
        have hle := prefixSplitLowPosition_apply_le n k π i
        have hleNat :
            (π (prefixSplitLowPosition n k π i)).val ≤ k.val := hle
        omega⟩)
    (by
      constructor
      · intro i j hij
        apply (prefixSplitLowPositionOrderIso n k π).injective
        apply Subtype.ext
        apply π.injective
        ext
        simpa using congrArg Fin.val hij
      · intro c
        let p : Candidate (n + 1) := π.symm (prefixSplitCandidate n k c)
        have hp : p ∈ prefixSplitLowPositionFinset n k π := by
          exact (mem_prefixSplitLowPositionFinset n k π p).mpr (by
            simp [p, prefixSplitCandidate_le n k c])
        let i : Fin (k.val + 1) :=
          (prefixSplitLowPositionOrderIso n k π).symm ⟨p, hp⟩
        refine ⟨i, ?_⟩
        apply Fin.ext
        simp [i, prefixSplitLowPosition, p])

@[simp] theorem prefixSplitLowOrder_apply_val
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (i : Fin (k.val + 1)) :
    (prefixSplitLowOrder n k π i : ℕ) =
      (π (prefixSplitLowPosition n k π i) : ℕ) := rfl

/-- Internal order of the strict-suffix candidates induced by their positions in `π`. -/
noncomputable def prefixSplitHighOrder
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) :
    Equiv.Perm (Fin (n + 2 - k.val)) :=
  Equiv.ofBijective
    (fun j : Fin (n + 2 - k.val) =>
      ⟨(π (prefixSplitHighPosition n k π j)).val - (k.val + 1), by
        have hgt := prefixSplitHighPosition_apply_gt n k π j
        have hgtNat :
            k.val < (π (prefixSplitHighPosition n k π j)).val := hgt
        have hπlt := (π (prefixSplitHighPosition n k π j)).isLt
        omega⟩)
    (by
      constructor
      · intro i j hij
        apply (prefixSplitHighPositionOrderIso n k π).injective
        apply Subtype.ext
        apply π.injective
        ext
        change
          (π (prefixSplitHighPosition n k π i)).val =
            (π (prefixSplitHighPosition n k π j)).val
        have hval :
            (π (prefixSplitHighPosition n k π i)).val - (k.val + 1) =
              (π (prefixSplitHighPosition n k π j)).val - (k.val + 1) := by
          exact congrArg Fin.val hij
        have hi_gt := prefixSplitHighPosition_apply_gt n k π i
        have hj_gt := prefixSplitHighPosition_apply_gt n k π j
        have hi_gtNat :
            k.val < (π (prefixSplitHighPosition n k π i)).val := hi_gt
        have hj_gtNat :
            k.val < (π (prefixSplitHighPosition n k π j)).val := hj_gt
        omega
      · intro c
        let full : Candidate (n + 1) := suffixSplitCandidate n k c
        let p : Candidate (n + 1) := π.symm full
        have hp : p ∈ prefixSplitHighPositionFinset n k π := by
          exact (mem_prefixSplitHighPositionFinset n k π p).mpr (by
            simp [p, full, k_lt_suffixSplitCandidate n k c])
        let j : Fin (n + 2 - k.val) :=
          (prefixSplitHighPositionOrderIso n k π).symm ⟨p, hp⟩
        refine ⟨j, ?_⟩
        apply Fin.ext
        simp [j, prefixSplitHighPosition, p, full])

@[simp] theorem prefixSplitHighOrder_apply_val
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (j : Fin (n + 2 - k.val)) :
    (prefixSplitHighOrder n k π j : ℕ) =
      (π (prefixSplitHighPosition n k π j) : ℕ) - (k.val + 1) := rfl

/-- Height vector induced by a ranking: high positions before each center-prefix position. -/
noncomputable def prefixSplitHeight
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) :
    Fin (k.val + 1) → Fin (n + 2 - k.val + 1) :=
  fun i =>
    ⟨((prefixSplitHighPositionFinset n k π).filter
        (fun p : Candidate (n + 1) => p < prefixSplitLowPosition n k π i)).card, by
      have hcard :
          ((prefixSplitHighPositionFinset n k π).filter
            (fun p : Candidate (n + 1) => p < prefixSplitLowPosition n k π i)).card ≤
            (prefixSplitHighPositionFinset n k π).card :=
        Finset.card_filter_le _ _
      rw [card_prefixSplitHighPositionFinset n k π] at hcard
      omega⟩

theorem prefixSplitHeight_mono
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) :
    binaryHeightMonotone (prefixSplitHeight n k π) := by
  intro i j hij
  rw [Fin.le_iff_val_le_val]
  simp [prefixSplitHeight]
  refine Finset.card_le_card ?_
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, lt_of_lt_of_le hp.2
    (prefixSplitLowPosition_mono n k π hij)⟩

theorem card_prefixSplitLowPositionFinset_filter_lt_lowPosition
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (i : Fin (k.val + 1)) :
    ((prefixSplitLowPositionFinset n k π).filter
        (fun p : Candidate (n + 1) => p < prefixSplitLowPosition n k π i)).card =
      i.val := by
  classical
  let e : Fin (k.val + 1) ↪ Candidate (n + 1) :=
    ⟨prefixSplitLowPosition n k π,
      (prefixSplitLowPosition_strictMono n k π).injective⟩
  have hfilter :
      (prefixSplitLowPositionFinset n k π).filter
          (fun p : Candidate (n + 1) => p < prefixSplitLowPosition n k π i) =
        (Finset.Iio i).map e := by
    ext p
    constructor
    · intro hp
      simp only [Finset.mem_filter] at hp
      let j : Fin (k.val + 1) :=
        (prefixSplitLowPositionOrderIso n k π).symm ⟨p, hp.1⟩
      have hj_lt : j < i := by
        have hlt_sub :
            prefixSplitLowPositionOrderIso n k π j <
              prefixSplitLowPositionOrderIso n k π i := by
          simpa [j] using
            (Subtype.coe_lt_coe.mp hp.2 :
              (⟨p, hp.1⟩ :
                prefixSplitLowPositionFinset n k π) <
                  prefixSplitLowPositionOrderIso n k π i)
        exact (prefixSplitLowPositionOrderIso n k π).lt_iff_lt.mp
          (by simpa [j] using hlt_sub)
      refine Finset.mem_map.mpr ?_
      refine ⟨j, Finset.mem_Iio.mpr hj_lt, ?_⟩
      ext
      simp [e, prefixSplitLowPosition, j]
    · intro hp
      rcases Finset.mem_map.mp hp with ⟨j, hj, rfl⟩
      have hj_lt : j < i := Finset.mem_Iio.mp hj
      simp only [Finset.mem_filter]
      exact ⟨prefixSplitLowPosition_mem n k π j,
        (prefixSplitLowPosition_strictMono n k π) hj_lt⟩
  rw [hfilter, Finset.card_map, Fin.card_Iio]

theorem prefixSplitLowPosition_val_eq_index_add_height
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (i : Fin (k.val + 1)) :
    (prefixSplitLowPosition n k π i : ℕ) =
      i.val + (prefixSplitHeight n k π i : ℕ) := by
  classical
  let p : Candidate (n + 1) := prefixSplitLowPosition n k π i
  have hlow_filter :
      (Finset.Iio p).filter (fun x : Candidate (n + 1) => π x ≤ k) =
        (prefixSplitLowPositionFinset n k π).filter
          (fun x : Candidate (n + 1) => x < p) := by
    ext x
    simp [p, prefixSplitLowPositionFinset, and_comm]
  have hhigh_filter :
      (Finset.Iio p).filter (fun x : Candidate (n + 1) => ¬π x ≤ k) =
        (prefixSplitHighPositionFinset n k π).filter
          (fun x : Candidate (n + 1) => x < p) := by
    ext x
    by_cases hle : π x ≤ k
    · have hnlt : ¬ k < π x := not_lt_of_ge hle
      simp [prefixSplitHighPositionFinset, hnlt]
    · have hlt : k < π x := lt_of_not_ge hle
      simp [prefixSplitHighPositionFinset, hlt, and_comm]
  have hpartition :
      ((Finset.Iio p).filter (fun x : Candidate (n + 1) => π x ≤ k)).card +
          ((Finset.Iio p).filter (fun x : Candidate (n + 1) => ¬π x ≤ k)).card =
        (Finset.Iio p).card :=
    Finset.card_filter_add_card_filter_not
      (s := Finset.Iio p) (p := fun x : Candidate (n + 1) => π x ≤ k)
  have hlow_card :
      ((prefixSplitLowPositionFinset n k π).filter
          (fun x : Candidate (n + 1) => x < p)).card = i.val := by
    simpa [p] using
      card_prefixSplitLowPositionFinset_filter_lt_lowPosition n k π i
  have hhigh_card :
      ((prefixSplitHighPositionFinset n k π).filter
          (fun x : Candidate (n + 1) => x < p)).card =
        (prefixSplitHeight n k π i : ℕ) := by
    rfl
  rw [hlow_filter, hhigh_filter, hlow_card, hhigh_card, Fin.card_Iio] at hpartition
  omega

theorem prefixSplitLowPosition_eq_of_mem_card
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    {p : Candidate (n + 1)} (hp : p ∈ prefixSplitLowPositionFinset n k π)
    (i : Fin (k.val + 1))
    (hcard : ((prefixSplitLowPositionFinset n k π).filter
        (fun x : Candidate (n + 1) => x < p)).card = i.val) :
    prefixSplitLowPosition n k π i = p := by
  let j : Fin (k.val + 1) :=
    (prefixSplitLowPositionOrderIso n k π).symm ⟨p, hp⟩
  have hpos : prefixSplitLowPosition n k π j = p := by
    ext
    simp [prefixSplitLowPosition, j]
  have hcard_j :
      ((prefixSplitLowPositionFinset n k π).filter
        (fun x : Candidate (n + 1) => x < p)).card = j.val := by
    simpa [hpos] using
      card_prefixSplitLowPositionFinset_filter_lt_lowPosition n k π j
  have hij : i = j := Fin.ext (by omega)
  rw [hij, hpos]

theorem card_prefixSplitHighPositionFinset_filter_lt_highPosition
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (j : Fin (n + 2 - k.val)) :
    ((prefixSplitHighPositionFinset n k π).filter
        (fun p : Candidate (n + 1) => p < prefixSplitHighPosition n k π j)).card =
      j.val := by
  classical
  let e : Fin (n + 2 - k.val) ↪ Candidate (n + 1) :=
    ⟨prefixSplitHighPosition n k π,
      (prefixSplitHighPosition_strictMono n k π).injective⟩
  have hfilter :
      (prefixSplitHighPositionFinset n k π).filter
          (fun p : Candidate (n + 1) => p < prefixSplitHighPosition n k π j) =
        (Finset.Iio j).map e := by
    ext p
    constructor
    · intro hp
      simp only [Finset.mem_filter] at hp
      let l : Fin (n + 2 - k.val) :=
        (prefixSplitHighPositionOrderIso n k π).symm ⟨p, hp.1⟩
      have hl_lt : l < j := by
        have hlt_sub :
            prefixSplitHighPositionOrderIso n k π l <
              prefixSplitHighPositionOrderIso n k π j := by
          simpa [l] using
            (Subtype.coe_lt_coe.mp hp.2 :
              (⟨p, hp.1⟩ :
                prefixSplitHighPositionFinset n k π) <
                  prefixSplitHighPositionOrderIso n k π j)
        exact (prefixSplitHighPositionOrderIso n k π).lt_iff_lt.mp
          (by simpa [l] using hlt_sub)
      refine Finset.mem_map.mpr ?_
      refine ⟨l, Finset.mem_Iio.mpr hl_lt, ?_⟩
      ext
      simp [e, prefixSplitHighPosition, l]
    · intro hp
      rcases Finset.mem_map.mp hp with ⟨l, hl, rfl⟩
      have hl_lt : l < j := Finset.mem_Iio.mp hl
      simp only [Finset.mem_filter]
      exact ⟨prefixSplitHighPosition_mem n k π l,
        (prefixSplitHighPosition_strictMono n k π) hl_lt⟩
  rw [hfilter, Finset.card_map, Fin.card_Iio]

theorem prefixSplitHighPosition_eq_of_mem_card
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    {p : Candidate (n + 1)} (hp : p ∈ prefixSplitHighPositionFinset n k π)
    (j : Fin (n + 2 - k.val))
    (hcard : ((prefixSplitHighPositionFinset n k π).filter
        (fun x : Candidate (n + 1) => x < p)).card = j.val) :
    prefixSplitHighPosition n k π j = p := by
  let l : Fin (n + 2 - k.val) :=
    (prefixSplitHighPositionOrderIso n k π).symm ⟨p, hp⟩
  have hpos : prefixSplitHighPosition n k π l = p := by
    ext
    simp [prefixSplitHighPosition, l]
  have hcard_l :
      ((prefixSplitHighPositionFinset n k π).filter
        (fun x : Candidate (n + 1) => x < p)).card = l.val := by
    simpa [hpos] using
      card_prefixSplitHighPositionFinset_filter_lt_highPosition n k π l
  have hjl : j = l := Fin.ext (by omega)
  rw [hjl, hpos]

theorem prefixSplitHighPosition_val_eq_heightLowCount_add_index
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (j : Fin (n + 2 - k.val)) :
    (prefixSplitHighPosition n k π j : ℕ) =
      ((prefixSplitLowPositionFinset n k π).filter
          (fun p : Candidate (n + 1) => p < prefixSplitHighPosition n k π j)).card +
        j.val := by
  classical
  let p : Candidate (n + 1) := prefixSplitHighPosition n k π j
  have hlow_filter :
      (Finset.Iio p).filter (fun x : Candidate (n + 1) => π x ≤ k) =
        (prefixSplitLowPositionFinset n k π).filter
          (fun x : Candidate (n + 1) => x < p) := by
    ext x
    simp [p, prefixSplitLowPositionFinset, and_comm]
  have hhigh_filter :
      (Finset.Iio p).filter (fun x : Candidate (n + 1) => ¬π x ≤ k) =
        (prefixSplitHighPositionFinset n k π).filter
          (fun x : Candidate (n + 1) => x < p) := by
    ext x
    by_cases hle : π x ≤ k
    · have hnlt : ¬ k < π x := not_lt_of_ge hle
      simp [prefixSplitHighPositionFinset, hnlt]
    · have hlt : k < π x := lt_of_not_ge hle
      simp [prefixSplitHighPositionFinset, hlt, and_comm]
  have hpartition :
      ((Finset.Iio p).filter (fun x : Candidate (n + 1) => π x ≤ k)).card +
          ((Finset.Iio p).filter (fun x : Candidate (n + 1) => ¬π x ≤ k)).card =
        (Finset.Iio p).card :=
    Finset.card_filter_add_card_filter_not
      (s := Finset.Iio p) (p := fun x : Candidate (n + 1) => π x ≤ k)
  have hhigh_card :
      ((prefixSplitHighPositionFinset n k π).filter
          (fun x : Candidate (n + 1) => x < p)).card = j.val := by
    simpa [p] using
      card_prefixSplitHighPositionFinset_filter_lt_highPosition n k π j
  rw [hlow_filter, hhigh_filter, hhigh_card, Fin.card_Iio] at hpartition
  exact hpartition.symm

theorem prefixSplitLowPosition_ne_highPosition
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (i : Fin (k.val + 1)) (j : Fin (n + 2 - k.val)) :
    prefixSplitLowPosition n k π i ≠ prefixSplitHighPosition n k π j := by
  intro h
  have hle := prefixSplitLowPosition_apply_le n k π i
  have hgt := prefixSplitHighPosition_apply_gt n k π j
  rw [h] at hle
  exact not_lt_of_ge hle hgt

theorem prefixSplitHeight_le_iff_lowPosition_lt_highPosition
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (i : Fin (k.val + 1)) (j : Fin (n + 2 - k.val)) :
    (prefixSplitHeight n k π i : ℕ) ≤ j.val ↔
      prefixSplitLowPosition n k π i < prefixSplitHighPosition n k π j := by
  classical
  constructor
  · intro hheight
    by_contra hnot
    have hhigh_lt_low :
        prefixSplitHighPosition n k π j < prefixSplitLowPosition n k π i := by
      have hle : prefixSplitHighPosition n k π j ≤
          prefixSplitLowPosition n k π i := le_of_not_gt hnot
      exact lt_of_le_of_ne hle
        (Ne.symm (prefixSplitLowPosition_ne_highPosition n k π i j))
    let e : Fin (n + 2 - k.val) ↪ Candidate (n + 1) :=
      ⟨prefixSplitHighPosition n k π,
        (prefixSplitHighPosition_strictMono n k π).injective⟩
    have hsubset :
        (Finset.Iic j).map e ⊆
          (prefixSplitHighPositionFinset n k π).filter
            (fun p : Candidate (n + 1) =>
              p < prefixSplitLowPosition n k π i) := by
      intro p hp
      rcases Finset.mem_map.mp hp with ⟨l, hl, rfl⟩
      have hl_le : l ≤ j := Finset.mem_Iic.mp hl
      have hpos_le :
          prefixSplitHighPosition n k π l ≤
            prefixSplitHighPosition n k π j :=
        prefixSplitHighPosition_mono n k π hl_le
      simp only [Finset.mem_filter]
      exact ⟨prefixSplitHighPosition_mem n k π l,
        lt_of_le_of_lt hpos_le hhigh_lt_low⟩
    have hcard := Finset.card_le_card hsubset
    have hmap_card :
        ((Finset.Iic j).map e).card = j.val + 1 := by
      rw [Finset.card_map, Fin.card_Iic]
    have hheight_ge :
        j.val + 1 ≤ (prefixSplitHeight n k π i : ℕ) := by
      simpa [hmap_card, prefixSplitHeight] using hcard
    omega
  · intro hlt
    have hsubset :
        (prefixSplitHighPositionFinset n k π).filter
            (fun p : Candidate (n + 1) =>
              p < prefixSplitLowPosition n k π i) ⊆
          (prefixSplitHighPositionFinset n k π).filter
            (fun p : Candidate (n + 1) =>
              p < prefixSplitHighPosition n k π j) := by
      intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, lt_trans hp.2 hlt⟩
    have hcard := Finset.card_le_card hsubset
    simpa [prefixSplitHeight,
      card_prefixSplitHighPositionFinset_filter_lt_highPosition n k π j] using hcard

theorem prefixSplitCandidate_prefixSplitLowOrder
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (i : Fin (k.val + 1)) :
    prefixSplitCandidate n k (prefixSplitLowOrder n k π i) =
      π (prefixSplitLowPosition n k π i) := by
  ext
  simp [prefixSplitCandidate]

theorem suffixSplitCandidate_prefixSplitHighOrder
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (j : Fin (n + 2 - k.val)) :
    suffixSplitCandidate n k (prefixSplitHighOrder n k π j) =
      π (prefixSplitHighPosition n k π j) := by
  ext
  have hgtNat :
      k.val < (π (prefixSplitHighPosition n k π j)).val :=
    prefixSplitHighPosition_apply_gt n k π j
  simp [suffixSplitCandidate]
  omega

/-- The candidate universe split into the center prefix up to `k` and its strict suffix. -/
noncomputable def splitCandidateSumEquiv
    (n : ℕ) (k : Candidate (n + 1)) :
    (Fin (k.val + 1) ⊕ Fin (n + 2 - k.val)) ≃ Candidate (n + 1) where
  toFun x := Sum.elim (prefixSplitCandidate n k) (suffixSplitCandidate n k) x
  invFun c :=
    if hc : (c : ℕ) ≤ k.val then
      Sum.inl ⟨c.val, by omega⟩
    else
      Sum.inr ⟨c.val - (k.val + 1), by
        have hc_lt : c.val < n + 3 := c.isLt
        have hk_lt : k.val < n + 3 := k.isLt
        omega⟩
  left_inv x := by
    classical
    rcases x with i | j
    · simp [prefixSplitCandidate, Nat.le_of_lt_succ i.isLt]
    · have hlt : k.val < k.val + 1 + j.val := by omega
      simp [suffixSplitCandidate, hlt]
  right_inv c := by
    classical
    by_cases hc : (c : ℕ) ≤ k.val
    · simp [hc, prefixSplitCandidate]
    · have hval :
          k.val + 1 + (c.val - (k.val + 1)) = c.val := by
        omega
      simp [hc, suffixSplitCandidate]
      ext
      exact hval

/-- Candidate split with fixed internal low-side and high-side orders. -/
noncomputable def splitCandidateOrderedSumEquiv
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val))) :
    (Fin (k.val + 1) ⊕ Fin (n + 2 - k.val)) ≃ Candidate (n + 1) :=
  (Equiv.sumCongr lo hi).trans (splitCandidateSumEquiv n k)

@[simp] theorem splitCandidateOrderedSumEquiv_apply_inl
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (i : Fin (k.val + 1)) :
    splitCandidateOrderedSumEquiv n k lo hi (Sum.inl i) =
      prefixSplitCandidate n k (lo i) := rfl

@[simp] theorem splitCandidateOrderedSumEquiv_apply_inr
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (j : Fin (n + 2 - k.val)) :
    splitCandidateOrderedSumEquiv n k lo hi (Sum.inr j) =
      suffixSplitCandidate n k (hi j) := rfl

theorem binaryHeightSplitSize
    (n : ℕ) (k : Candidate (n + 1)) :
    k.val + 1 + (n + 2 - k.val) = n + 3 := by
  have hk : k.val < n + 3 := k.isLt
  omega

/-- Ranking obtained by merging fixed low/high internal orders according to a binary height vector. -/
noncomputable def binaryHeightMergeRanking
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h) : Ranking (n + 1) :=
  (finCongr (binaryHeightSplitSize n k).symm).trans
    ((binaryHeightPositionEquiv h hh).symm.trans
      (splitCandidateOrderedSumEquiv n k lo hi))

/-- Word position, coerced to the ambient candidate-position type. -/
noncomputable def binaryHeightPositionCandidate
    (n : ℕ) (k : Candidate (n + 1))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h)
    (x : Fin (k.val + 1) ⊕ Fin (n + 2 - k.val)) :
    Candidate (n + 1) :=
  finCongr (binaryHeightSplitSize n k) (binaryHeightPositionEquiv h hh x)

/-- Binary height positions as an equivalence onto the ambient rank positions. -/
noncomputable def binaryHeightPositionCandidateEquiv
    (n : ℕ) (k : Candidate (n + 1))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h) :
    (Fin (k.val + 1) ⊕ Fin (n + 2 - k.val)) ≃ Candidate (n + 1) :=
  (binaryHeightPositionEquiv h hh).trans
    (finCongr (binaryHeightSplitSize n k))

@[simp] theorem binaryHeightPositionCandidateEquiv_apply
    (n : ℕ) (k : Candidate (n + 1))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h)
    (x : Fin (k.val + 1) ⊕ Fin (n + 2 - k.val)) :
    binaryHeightPositionCandidateEquiv n k h hh x =
      binaryHeightPositionCandidate n k h hh x := rfl

theorem binaryHeightPositionCandidate_inl_strictMono
    (n : ℕ) (k : Candidate (n + 1))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h) :
    StrictMono (fun i : Fin (k.val + 1) =>
      binaryHeightPositionCandidate n k h hh (Sum.inl i)) := by
  intro i j hij
  rw [Fin.lt_def]
  have hlt := binaryHeightLowPosition_strictMono hh hij
  simpa [binaryHeightPositionCandidate, binaryHeightLowPosition, Fin.lt_def] using hlt

theorem binaryHeightPositionCandidate_inr_strictMono
    (n : ℕ) (k : Candidate (n + 1))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h) :
    StrictMono (fun j : Fin (n + 2 - k.val) =>
      binaryHeightPositionCandidate n k h hh (Sum.inr j)) := by
  intro i j hij
  rw [Fin.lt_def]
  have hlt := binaryHeightHighPosition_strictMono h hij
  simpa [binaryHeightPositionCandidate, binaryHeightHighPosition, Fin.lt_def] using hlt

theorem binaryHeightPositionCandidate_inr_lt_inl_iff
    (n : ℕ) (k : Candidate (n + 1))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h)
    (i : Fin (k.val + 1)) (j : Fin (n + 2 - k.val)) :
    binaryHeightPositionCandidate n k h hh (Sum.inr j) <
        binaryHeightPositionCandidate n k h hh (Sum.inl i) ↔
      j.val < (h i : ℕ) := by
  rw [Fin.lt_def]
  simpa [binaryHeightPositionCandidate, binaryHeightLowPosition,
    binaryHeightHighPosition, Fin.lt_def] using
    (binaryHeightHighPosition_lt_lowPosition_iff hh i j)

@[simp] theorem binaryHeightMergeRanking_apply_position
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h)
    (x : Fin (k.val + 1) ⊕ Fin (n + 2 - k.val)) :
    binaryHeightMergeRanking n k lo hi h hh
        (binaryHeightPositionCandidate n k h hh x) =
      splitCandidateOrderedSumEquiv n k lo hi x := by
  simp [binaryHeightMergeRanking, binaryHeightPositionCandidate]

theorem binaryHeightPositionCandidate_prefixSplitHeight_inl
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (i : Fin (k.val + 1)) :
    binaryHeightPositionCandidate n k (prefixSplitHeight n k π)
        (prefixSplitHeight_mono n k π) (Sum.inl i) =
      prefixSplitLowPosition n k π i := by
  ext
  simp [binaryHeightPositionCandidate, binaryHeightLowPosition,
    prefixSplitLowPosition_val_eq_index_add_height]

theorem binaryHeightPositionCandidate_prefixSplitHeight_inr
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1))
    (j : Fin (n + 2 - k.val)) :
    binaryHeightPositionCandidate n k (prefixSplitHeight n k π)
        (prefixSplitHeight_mono n k π) (Sum.inr j) =
      prefixSplitHighPosition n k π j := by
  classical
  let e : Fin (k.val + 1) ↪ Candidate (n + 1) :=
    ⟨prefixSplitLowPosition n k π,
      (prefixSplitLowPosition_strictMono n k π).injective⟩
  have hmap :
      ((Finset.univ : Finset (Fin (k.val + 1))).filter
          (fun i => (prefixSplitHeight n k π i : ℕ) ≤ j.val)).map e =
        (prefixSplitLowPositionFinset n k π).filter
          (fun p : Candidate (n + 1) =>
            p < prefixSplitHighPosition n k π j) := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_map.mp hp with ⟨i, hi, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_filter]
      exact ⟨prefixSplitLowPosition_mem n k π i,
        (prefixSplitHeight_le_iff_lowPosition_lt_highPosition n k π i j).mp hi⟩
    · intro hp
      simp only [Finset.mem_filter] at hp
      let i : Fin (k.val + 1) :=
        (prefixSplitLowPositionOrderIso n k π).symm ⟨p, hp.1⟩
      have hi_pos : prefixSplitLowPosition n k π i = p := by
        ext
        simp [prefixSplitLowPosition, i]
      have hi_height :
          (prefixSplitHeight n k π i : ℕ) ≤ j.val := by
        exact (prefixSplitHeight_le_iff_lowPosition_lt_highPosition n k π i j).mpr
          (by simpa [hi_pos] using hp.2)
      refine Finset.mem_map.mpr ?_
      refine ⟨i, ?_, ?_⟩
      · simp [hi_height]
      · ext
        simp [e, hi_pos]
  ext
  have hcard :
      ((Finset.univ : Finset (Fin (k.val + 1))).filter
          (fun i => (prefixSplitHeight n k π i : ℕ) ≤ j.val)).card =
        ((prefixSplitLowPositionFinset n k π).filter
          (fun p : Candidate (n + 1) =>
            p < prefixSplitHighPosition n k π j)).card := by
    rw [← hmap, Finset.card_map]
  simp [binaryHeightPositionCandidate, binaryHeightHighPosition,
    prefixSplitHighPosition_val_eq_heightLowCount_add_index, hcard,
    add_comm]

@[simp] theorem binaryHeightMergeRanking_apply_lowPosition
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h)
    (i : Fin (k.val + 1)) :
    binaryHeightMergeRanking n k lo hi h hh
        (binaryHeightPositionCandidate n k h hh (Sum.inl i)) =
      prefixSplitCandidate n k (lo i) := by
  simp

@[simp] theorem binaryHeightMergeRanking_apply_highPosition
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h)
    (j : Fin (n + 2 - k.val)) :
    binaryHeightMergeRanking n k lo hi h hh
        (binaryHeightPositionCandidate n k h hh (Sum.inr j)) =
      suffixSplitCandidate n k (hi j) := by
  simp

theorem binaryHeightMergeRanking_prefixSplit
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) :
    binaryHeightMergeRanking n k
      (prefixSplitLowOrder n k π)
      (prefixSplitHighOrder n k π)
      (prefixSplitHeight n k π)
      (prefixSplitHeight_mono n k π) = π := by
  apply Equiv.ext
  intro p
  by_cases hle : π p ≤ k
  · have hp : p ∈ prefixSplitLowPositionFinset n k π := by
      exact (mem_prefixSplitLowPositionFinset n k π p).mpr hle
    let i : Fin (k.val + 1) :=
      (prefixSplitLowPositionOrderIso n k π).symm ⟨p, hp⟩
    have hpos : prefixSplitLowPosition n k π i = p := by
      ext
      simp [prefixSplitLowPosition, i]
    rw [← hpos,
      ← binaryHeightPositionCandidate_prefixSplitHeight_inl n k π i,
      binaryHeightMergeRanking_apply_lowPosition,
      prefixSplitCandidate_prefixSplitLowOrder,
      binaryHeightPositionCandidate_prefixSplitHeight_inl,
      hpos]
  · have hgt : k < π p := lt_of_not_ge hle
    have hp : p ∈ prefixSplitHighPositionFinset n k π := by
      exact (mem_prefixSplitHighPositionFinset n k π p).mpr hgt
    let j : Fin (n + 2 - k.val) :=
      (prefixSplitHighPositionOrderIso n k π).symm ⟨p, hp⟩
    have hpos : prefixSplitHighPosition n k π j = p := by
      ext
      simp [prefixSplitHighPosition, j]
    rw [← hpos,
      ← binaryHeightPositionCandidate_prefixSplitHeight_inr n k π j,
      binaryHeightMergeRanking_apply_highPosition,
      suffixSplitCandidate_prefixSplitHighOrder,
      binaryHeightPositionCandidate_prefixSplitHeight_inr,
      hpos]

theorem prefixSplitLowPosition_binaryHeightMergeRanking
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h)
    (i : Fin (k.val + 1)) :
    prefixSplitLowPosition n k (binaryHeightMergeRanking n k lo hi h hh) i =
      binaryHeightPositionCandidate n k h hh (Sum.inl i) := by
  classical
  let π : Ranking (n + 1) := binaryHeightMergeRanking n k lo hi h hh
  let p : Candidate (n + 1) :=
    binaryHeightPositionCandidate n k h hh (Sum.inl i)
  have hp : p ∈ prefixSplitLowPositionFinset n k π := by
    exact (mem_prefixSplitLowPositionFinset n k π p).mpr (by
      dsimp [π, p]
      rw [binaryHeightMergeRanking_apply_lowPosition]
      exact prefixSplitCandidate_le n k (lo i))
  let e : Fin (k.val + 1) ↪ Candidate (n + 1) :=
    ⟨fun t => binaryHeightPositionCandidate n k h hh (Sum.inl t),
      (binaryHeightPositionCandidate_inl_strictMono n k h hh).injective⟩
  have hfilter :
      (prefixSplitLowPositionFinset n k π).filter
          (fun x : Candidate (n + 1) => x < p) =
        (Finset.Iio i).map e := by
    ext x
    constructor
    · intro hxmem
      simp only [Finset.mem_filter] at hxmem
      have hle : π x ≤ k :=
        (mem_prefixSplitLowPositionFinset n k π x).mp hxmem.1
      let c : Fin (k.val + 1) :=
        ⟨(π x).val, by
          have hleNat : (π x).val ≤ k.val := hle
          omega⟩
      let t : Fin (k.val + 1) := lo.symm c
      have hπ : π (binaryHeightPositionCandidate n k h hh (Sum.inl t)) = π x := by
        dsimp [π]
        rw [binaryHeightMergeRanking_apply_lowPosition]
        have ht : lo t = c := by simp [t]
        rw [ht]
        exact Fin.ext rfl
      have hx : x = binaryHeightPositionCandidate n k h hh (Sum.inl t) := by
        exact (π.injective hπ).symm
      have ht_lt : t < i := by
        have hpos_lt :
            binaryHeightPositionCandidate n k h hh (Sum.inl t) <
              binaryHeightPositionCandidate n k h hh (Sum.inl i) := by
          simpa [hx, p] using hxmem.2
        exact (binaryHeightPositionCandidate_inl_strictMono n k h hh).lt_iff_lt.mp
          hpos_lt
      refine Finset.mem_map.mpr ?_
      exact ⟨t, Finset.mem_Iio.mpr ht_lt, hx.symm⟩
    · intro hxmem
      rcases Finset.mem_map.mp hxmem with ⟨t, htmem, rfl⟩
      have ht_lt : t < i := Finset.mem_Iio.mp htmem
      simp only [Finset.mem_filter]
      constructor
      · exact (mem_prefixSplitLowPositionFinset n k π _).mpr (by
          change binaryHeightMergeRanking n k lo hi h hh
              (binaryHeightPositionCandidate n k h hh (Sum.inl t)) ≤ k
          rw [binaryHeightMergeRanking_apply_lowPosition]
          exact prefixSplitCandidate_le n k (lo t))
      · exact (binaryHeightPositionCandidate_inl_strictMono n k h hh) ht_lt
  refine prefixSplitLowPosition_eq_of_mem_card n k π hp i ?_
  rw [hfilter, Finset.card_map, Fin.card_Iio]

theorem prefixSplitHighPosition_binaryHeightMergeRanking
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h)
    (j : Fin (n + 2 - k.val)) :
    prefixSplitHighPosition n k (binaryHeightMergeRanking n k lo hi h hh) j =
      binaryHeightPositionCandidate n k h hh (Sum.inr j) := by
  classical
  let π : Ranking (n + 1) := binaryHeightMergeRanking n k lo hi h hh
  let p : Candidate (n + 1) :=
    binaryHeightPositionCandidate n k h hh (Sum.inr j)
  have hp : p ∈ prefixSplitHighPositionFinset n k π := by
    exact (mem_prefixSplitHighPositionFinset n k π p).mpr (by
      dsimp [π, p]
      rw [binaryHeightMergeRanking_apply_highPosition]
      exact k_lt_suffixSplitCandidate n k (hi j))
  let e : Fin (n + 2 - k.val) ↪ Candidate (n + 1) :=
    ⟨fun t => binaryHeightPositionCandidate n k h hh (Sum.inr t),
      (binaryHeightPositionCandidate_inr_strictMono n k h hh).injective⟩
  have hfilter :
      (prefixSplitHighPositionFinset n k π).filter
          (fun x : Candidate (n + 1) => x < p) =
        (Finset.Iio j).map e := by
    ext x
    constructor
    · intro hxmem
      simp only [Finset.mem_filter] at hxmem
      have hgt : k < π x :=
        (mem_prefixSplitHighPositionFinset n k π x).mp hxmem.1
      let c : Fin (n + 2 - k.val) :=
        ⟨(π x).val - (k.val + 1), by
          have hgtNat : k.val < (π x).val := hgt
          have hxlt := (π x).isLt
          omega⟩
      let t : Fin (n + 2 - k.val) := hi.symm c
      have hπ : π (binaryHeightPositionCandidate n k h hh (Sum.inr t)) = π x := by
        dsimp [π]
        rw [binaryHeightMergeRanking_apply_highPosition]
        have ht : hi t = c := by simp [t]
        rw [ht]
        ext
        change k.val + 1 + ((π x).val - (k.val + 1)) = (π x).val
        have hgtNat : k.val < (π x).val := hgt
        omega
      have hx : x = binaryHeightPositionCandidate n k h hh (Sum.inr t) := by
        exact (π.injective hπ).symm
      have ht_lt : t < j := by
        have hpos_lt :
            binaryHeightPositionCandidate n k h hh (Sum.inr t) <
              binaryHeightPositionCandidate n k h hh (Sum.inr j) := by
          simpa [hx, p] using hxmem.2
        exact (binaryHeightPositionCandidate_inr_strictMono n k h hh).lt_iff_lt.mp
          hpos_lt
      refine Finset.mem_map.mpr ?_
      exact ⟨t, Finset.mem_Iio.mpr ht_lt, hx.symm⟩
    · intro hxmem
      rcases Finset.mem_map.mp hxmem with ⟨t, htmem, rfl⟩
      have ht_lt : t < j := Finset.mem_Iio.mp htmem
      simp only [Finset.mem_filter]
      constructor
      · exact (mem_prefixSplitHighPositionFinset n k π _).mpr (by
          change k < binaryHeightMergeRanking n k lo hi h hh
              (binaryHeightPositionCandidate n k h hh (Sum.inr t))
          rw [binaryHeightMergeRanking_apply_highPosition]
          exact k_lt_suffixSplitCandidate n k (hi t))
      · exact (binaryHeightPositionCandidate_inr_strictMono n k h hh) ht_lt
  refine prefixSplitHighPosition_eq_of_mem_card n k π hp j ?_
  rw [hfilter, Finset.card_map, Fin.card_Iio]

theorem prefixSplitLowOrder_binaryHeightMergeRanking
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h) :
    prefixSplitLowOrder n k (binaryHeightMergeRanking n k lo hi h hh) = lo := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  rw [prefixSplitLowOrder_apply_val]
  rw [prefixSplitLowPosition_binaryHeightMergeRanking]
  rw [binaryHeightMergeRanking_apply_lowPosition]
  simp [prefixSplitCandidate]

theorem prefixSplitHighOrder_binaryHeightMergeRanking
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h) :
    prefixSplitHighOrder n k (binaryHeightMergeRanking n k lo hi h hh) = hi := by
  apply Equiv.ext
  intro j
  apply Fin.ext
  rw [prefixSplitHighOrder_apply_val]
  rw [prefixSplitHighPosition_binaryHeightMergeRanking]
  rw [binaryHeightMergeRanking_apply_highPosition]
  simp [suffixSplitCandidate]

theorem prefixSplitHeight_binaryHeightMergeRanking
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h) :
    prefixSplitHeight n k (binaryHeightMergeRanking n k lo hi h hh) = h := by
  classical
  funext i
  apply Fin.ext
  let π : Ranking (n + 1) := binaryHeightMergeRanking n k lo hi h hh
  let lowp : Candidate (n + 1) :=
    binaryHeightPositionCandidate n k h hh (Sum.inl i)
  let e : Fin (n + 2 - k.val) ↪ Candidate (n + 1) :=
    ⟨fun t => binaryHeightPositionCandidate n k h hh (Sum.inr t),
      (binaryHeightPositionCandidate_inr_strictMono n k h hh).injective⟩
  have hlowpos : prefixSplitLowPosition n k π i = lowp := by
    simpa [π, lowp] using
      prefixSplitLowPosition_binaryHeightMergeRanking n k lo hi h hh i
  have hfilter :
      (prefixSplitHighPositionFinset n k π).filter
          (fun x : Candidate (n + 1) =>
            x < prefixSplitLowPosition n k π i) =
        ((Finset.univ : Finset (Fin (n + 2 - k.val))).filter
          (fun t => t.val < (h i : ℕ))).map e := by
    ext x
    constructor
    · intro hxmem
      simp only [Finset.mem_filter] at hxmem
      have hgt : k < π x :=
        (mem_prefixSplitHighPositionFinset n k π x).mp hxmem.1
      let c : Fin (n + 2 - k.val) :=
        ⟨(π x).val - (k.val + 1), by
          have hgtNat : k.val < (π x).val := hgt
          have hxlt := (π x).isLt
          omega⟩
      let t : Fin (n + 2 - k.val) := hi.symm c
      have hπ : π (binaryHeightPositionCandidate n k h hh (Sum.inr t)) = π x := by
        dsimp [π]
        rw [binaryHeightMergeRanking_apply_highPosition]
        have ht : hi t = c := by simp [t]
        rw [ht]
        ext
        change k.val + 1 + ((π x).val - (k.val + 1)) = (π x).val
        have hgtNat : k.val < (π x).val := hgt
        omega
      have hx : x = binaryHeightPositionCandidate n k h hh (Sum.inr t) := by
        exact (π.injective hπ).symm
      have ht_lt : t.val < (h i : ℕ) := by
        have hpos_lt :
            binaryHeightPositionCandidate n k h hh (Sum.inr t) <
              binaryHeightPositionCandidate n k h hh (Sum.inl i) := by
          simpa [hx, hlowpos, lowp] using hxmem.2
        exact (binaryHeightPositionCandidate_inr_lt_inl_iff n k h hh i t).mp
          hpos_lt
      refine Finset.mem_map.mpr ?_
      exact ⟨t, by simp [ht_lt], hx.symm⟩
    · intro hxmem
      rcases Finset.mem_map.mp hxmem with ⟨t, htmem, rfl⟩
      simp only [Finset.mem_filter] at htmem
      simp only [Finset.mem_filter]
      constructor
      · exact (mem_prefixSplitHighPositionFinset n k π _).mpr (by
          change k < binaryHeightMergeRanking n k lo hi h hh
              (binaryHeightPositionCandidate n k h hh (Sum.inr t))
          rw [binaryHeightMergeRanking_apply_highPosition]
          exact k_lt_suffixSplitCandidate n k (hi t))
      · rw [hlowpos]
        exact (binaryHeightPositionCandidate_inr_lt_inl_iff n k h hh i t).mpr
          htmem.2
  have hcard_high :
      ((Finset.univ : Finset (Fin (n + 2 - k.val))).filter
          (fun t => t.val < (h i : ℕ))).card = (h i : ℕ) := by
    have hcard :=
      Fin.card_filter_val_lt (n := n + 2 - k.val) (m := (h i : ℕ))
    have hmin : min (n + 2 - k.val) (h i : ℕ) = (h i : ℕ) := by
      have hle : (h i : ℕ) ≤ n + 2 - k.val := by
        have hi := (h i).isLt
        omega
      exact Nat.min_eq_right hle
    simpa [hmin] using hcard
  change ((prefixSplitHighPositionFinset n k π).filter
      (fun p : Candidate (n + 1) =>
        p < prefixSplitLowPosition n k π i)).card = (h i : ℕ)
  rw [hfilter, Finset.card_map, hcard_high]

theorem binaryHeightMergeRanking_low_low_inversion_iff
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h)
    (i j : Fin (k.val + 1)) :
    binaryHeightPositionCandidate n k h hh (Sum.inl i) <
          binaryHeightPositionCandidate n k h hh (Sum.inl j) ∧
        binaryHeightMergeRanking n k lo hi h hh
            (binaryHeightPositionCandidate n k h hh (Sum.inl j)) <
          binaryHeightMergeRanking n k lo hi h hh
            (binaryHeightPositionCandidate n k h hh (Sum.inl i)) ↔
      i < j ∧ lo j < lo i := by
  constructor
  · intro hp
    constructor
    · exact (binaryHeightPositionCandidate_inl_strictMono n k h hh).lt_iff_lt.mp hp.1
    · simpa [binaryHeightMergeRanking_apply_lowPosition, prefixSplitCandidate]
        using hp.2
  · intro hp
    constructor
    · exact (binaryHeightPositionCandidate_inl_strictMono n k h hh) hp.1
    · simpa [binaryHeightMergeRanking_apply_lowPosition, prefixSplitCandidate]
        using hp.2

theorem binaryHeightMergeRanking_high_high_inversion_iff
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h)
    (i j : Fin (n + 2 - k.val)) :
    binaryHeightPositionCandidate n k h hh (Sum.inr i) <
          binaryHeightPositionCandidate n k h hh (Sum.inr j) ∧
        binaryHeightMergeRanking n k lo hi h hh
            (binaryHeightPositionCandidate n k h hh (Sum.inr j)) <
          binaryHeightMergeRanking n k lo hi h hh
            (binaryHeightPositionCandidate n k h hh (Sum.inr i)) ↔
      i < j ∧ hi j < hi i := by
  constructor
  · intro hp
    constructor
    · exact (binaryHeightPositionCandidate_inr_strictMono n k h hh).lt_iff_lt.mp hp.1
    · have hlt := hp.2
      rw [binaryHeightMergeRanking_apply_highPosition,
        binaryHeightMergeRanking_apply_highPosition] at hlt
      change k.val + 1 + (hi j).val < k.val + 1 + (hi i).val at hlt
      rw [Fin.lt_def]
      omega
  · intro hp
    constructor
    · exact (binaryHeightPositionCandidate_inr_strictMono n k h hh) hp.1
    · rw [binaryHeightMergeRanking_apply_highPosition,
        binaryHeightMergeRanking_apply_highPosition]
      change k.val + 1 + (hi j).val < k.val + 1 + (hi i).val
      have hpNat : (hi j).val < (hi i).val := hp.2
      omega

theorem binaryHeightMergeRanking_high_low_inversion_iff
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h)
    (i : Fin (k.val + 1)) (j : Fin (n + 2 - k.val)) :
    binaryHeightPositionCandidate n k h hh (Sum.inr j) <
          binaryHeightPositionCandidate n k h hh (Sum.inl i) ∧
        binaryHeightMergeRanking n k lo hi h hh
            (binaryHeightPositionCandidate n k h hh (Sum.inl i)) <
          binaryHeightMergeRanking n k lo hi h hh
            (binaryHeightPositionCandidate n k h hh (Sum.inr j)) ↔
      j.val < (h i : ℕ) := by
  constructor
  · intro hp
    exact (binaryHeightPositionCandidate_inr_lt_inl_iff n k h hh i j).mp hp.1
  · intro hj
    constructor
    · exact (binaryHeightPositionCandidate_inr_lt_inl_iff n k h hh i j).mpr hj
    · rw [binaryHeightMergeRanking_apply_lowPosition,
        binaryHeightMergeRanking_apply_highPosition]
      exact lt_of_le_of_lt (prefixSplitCandidate_le n k (lo i))
        (k_lt_suffixSplitCandidate n k (hi j))

theorem not_binaryHeightMergeRanking_low_high_inversion
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h)
    (i : Fin (k.val + 1)) (j : Fin (n + 2 - k.val)) :
    ¬ binaryHeightMergeRanking n k lo hi h hh
            (binaryHeightPositionCandidate n k h hh (Sum.inr j)) <
          binaryHeightMergeRanking n k lo hi h hh
            (binaryHeightPositionCandidate n k h hh (Sum.inl i)) := by
  rw [binaryHeightMergeRanking_apply_lowPosition,
    binaryHeightMergeRanking_apply_highPosition]
  exact not_lt_of_ge (le_trans (prefixSplitCandidate_le n k (lo i))
    (le_of_lt (k_lt_suffixSplitCandidate n k (hi j))))

theorem binaryHeightMergeRanking_reindexedInversionCard
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h) :
    ((Finset.univ :
        Finset ((Fin (k.val + 1) ⊕ Fin (n + 2 - k.val)) ×
          (Fin (k.val + 1) ⊕ Fin (n + 2 - k.val)))).filter
      (fun xy =>
        binaryHeightPositionCandidateEquiv n k h hh xy.1 <
            binaryHeightPositionCandidateEquiv n k h hh xy.2 ∧
          binaryHeightMergeRanking n k lo hi h hh
              (binaryHeightPositionCandidateEquiv n k h hh xy.2) <
            binaryHeightMergeRanking n k lo hi h hh
              (binaryHeightPositionCandidateEquiv n k h hh xy.1))).card =
      (finPermInversionCount (k.val + 1) lo +
        finPermInversionCount (n + 2 - k.val) hi +
          binaryHeightSum h) := by
  classical
  let e := binaryHeightPositionCandidateEquiv n k h hh
  let σ := binaryHeightMergeRanking n k lo hi h hh
  let L : Finset (Fin (k.val + 1) × Fin (k.val + 1)) :=
    (Finset.univ.filter
      (fun ij : Fin (k.val + 1) × Fin (k.val + 1) =>
        ij.1 < ij.2 ∧ lo ij.2 < lo ij.1))
  let H : Finset (Fin (n + 2 - k.val) × Fin (n + 2 - k.val)) :=
    (Finset.univ.filter
      (fun ij : Fin (n + 2 - k.val) × Fin (n + 2 - k.val) =>
        ij.1 < ij.2 ∧ hi ij.2 < hi ij.1))
  let C : Finset (Fin (k.val + 1) × Fin (n + 2 - k.val)) :=
    binaryHeightCrossInversionFinset h
  let source :
      Finset ((Fin (k.val + 1) ⊕ Fin (n + 2 - k.val)) ×
        (Fin (k.val + 1) ⊕ Fin (n + 2 - k.val))) :=
    (Finset.univ.filter
      (fun xy =>
        e xy.1 < e xy.2 ∧ σ (e xy.2) < σ (e xy.1)))
  let target :
      Finset ((Fin (k.val + 1) × Fin (k.val + 1)) ⊕
        ((Fin (n + 2 - k.val) × Fin (n + 2 - k.val)) ⊕
          (Fin (k.val + 1) × Fin (n + 2 - k.val)))) :=
    L.disjSum (H.disjSum C)
  have hsplit : source.card = target.card := by
    refine Finset.card_bij'
      (i := fun xy hxy => ?forward)
      (j := fun y hy => ?backward)
      ?forward_mem ?backward_mem ?left_inv ?right_inv
    · rcases xy with ⟨x, y⟩
      rcases x with x | x <;> rcases y with y | y
      · exact Sum.inl (x, y)
      · have hp :
            e (Sum.inl x) < e (Sum.inr y) ∧
              σ (e (Sum.inr y)) < σ (e (Sum.inl x)) := by
          simpa [source] using (Finset.mem_filter.mp hxy).2
        exact False.elim
          ((not_binaryHeightMergeRanking_low_high_inversion
            n k lo hi h hh x y) (by simpa [e, σ] using hp.2))
      · exact Sum.inr (Sum.inr (y, x))
      · exact Sum.inr (Sum.inl (x, y))
    · rcases y with y | y
      · exact (Sum.inl y.1, Sum.inl y.2)
      · rcases y with y | y
        · exact (Sum.inr y.1, Sum.inr y.2)
        · exact (Sum.inr y.2, Sum.inl y.1)
    · intro xy hxy
      rcases xy with ⟨x, y⟩
      rcases x with x | x <;> rcases y with y | y
      · have hp :
            e (Sum.inl x) < e (Sum.inl y) ∧
              σ (e (Sum.inl y)) < σ (e (Sum.inl x)) := by
          simpa [source] using (Finset.mem_filter.mp hxy).2
        have hclass :=
          (binaryHeightMergeRanking_low_low_inversion_iff
            n k lo hi h hh x y).mp (by simpa [e, σ] using hp)
        simpa [target, L] using hclass
      · have hp :
            e (Sum.inl x) < e (Sum.inr y) ∧
              σ (e (Sum.inr y)) < σ (e (Sum.inl x)) := by
          simpa [source] using (Finset.mem_filter.mp hxy).2
        exact False.elim
          ((not_binaryHeightMergeRanking_low_high_inversion
            n k lo hi h hh x y) (by simpa [e, σ] using hp.2))
      · have hp :
            e (Sum.inr x) < e (Sum.inl y) ∧
              σ (e (Sum.inl y)) < σ (e (Sum.inr x)) := by
          simpa [source] using (Finset.mem_filter.mp hxy).2
        have hclass :=
          (binaryHeightMergeRanking_high_low_inversion_iff
            n k lo hi h hh y x).mp (by simpa [e, σ] using hp)
        simpa [target, C, binaryHeightCrossInversionFinset] using hclass
      · have hp :
            e (Sum.inr x) < e (Sum.inr y) ∧
              σ (e (Sum.inr y)) < σ (e (Sum.inr x)) := by
          simpa [source] using (Finset.mem_filter.mp hxy).2
        have hclass :=
          (binaryHeightMergeRanking_high_high_inversion_iff
            n k lo hi h hh x y).mp (by simpa [e, σ] using hp)
        simpa [target, H] using hclass
    · intro y hy
      rcases y with y | y
      · have hyL : y ∈ L := by
          simpa [target] using hy
        have hclass : y.1 < y.2 ∧ lo y.2 < lo y.1 := by
          simpa [L] using hyL
        have hp :=
          (binaryHeightMergeRanking_low_low_inversion_iff
            n k lo hi h hh y.1 y.2).mpr hclass
        simpa [source, e, σ] using hp
      · rcases y with y | y
        · have hyH : y ∈ H := by
            simpa [target] using hy
          have hclass : y.1 < y.2 ∧ hi y.2 < hi y.1 := by
            simpa [H] using hyH
          have hp :=
            (binaryHeightMergeRanking_high_high_inversion_iff
              n k lo hi h hh y.1 y.2).mpr hclass
          simpa [source, e, σ] using hp
        · have hyC : y ∈ C := by
            simpa [target] using hy
          have hclass : y.2.val < (h y.1 : ℕ) := by
            simpa [C, binaryHeightCrossInversionFinset] using hyC
          have hp :=
            (binaryHeightMergeRanking_high_low_inversion_iff
              n k lo hi h hh y.1 y.2).mpr hclass
          simpa [source, e, σ] using hp
    · intro xy hxy
      rcases xy with ⟨x, y⟩
      rcases x with x | x <;> rcases y with y | y
      · rfl
      · have hp :
            e (Sum.inl x) < e (Sum.inr y) ∧
              σ (e (Sum.inr y)) < σ (e (Sum.inl x)) := by
          simpa [source] using (Finset.mem_filter.mp hxy).2
        exact False.elim
          ((not_binaryHeightMergeRanking_low_high_inversion
            n k lo hi h hh x y) (by simpa [e, σ] using hp.2))
      · rfl
      · rfl
    · intro y hy
      rcases y with y | y
      · rfl
      · rcases y with y | y <;> rfl
  have htarget :
      target.card =
        finPermInversionCount (k.val + 1) lo +
          finPermInversionCount (n + 2 - k.val) hi +
            binaryHeightSum h := by
    simp [target, L, H, C, finPermInversionCount,
      binaryHeightCrossInversionFinset_card, Nat.add_assoc]
  simpa [source, e, σ, binaryHeightPositionCandidateEquiv,
    binaryHeightPositionCandidate, binaryHeightMergeRanking] using
      hsplit.trans htarget

theorem finPermInversionCount_binaryHeightMergeRanking
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h) :
    finPermInversionCount (n + 3)
        (binaryHeightMergeRanking n k lo hi h hh) =
      finPermInversionCount (k.val + 1) lo +
        finPermInversionCount (n + 2 - k.val) hi +
          binaryHeightSum h := by
  classical
  exact
    (finPermInversionCount_reindex
      (e := binaryHeightPositionCandidateEquiv n k h hh)
      (σ := binaryHeightMergeRanking n k lo hi h hh)).trans
      (binaryHeightMergeRanking_reindexedInversionCard n k lo hi h hh)

theorem kendallTau_refl_binaryHeightMergeRanking
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h) :
    kendallTau (Equiv.refl (Candidate (n + 1)))
        (binaryHeightMergeRanking n k lo hi h hh) =
      finPermInversionCount (k.val + 1) lo +
        finPermInversionCount (n + 2 - k.val) hi +
          binaryHeightSum h := by
  rw [kendallTau_refl_eq_finPermInversionCount]
  exact finPermInversionCount_binaryHeightMergeRanking n k lo hi h hh

/-- Canonical split data: low order, high order, and monotone interleaving height. -/
structure PrefixSplitTriple (n : ℕ) (k : Candidate (n + 1)) where
  lo : Equiv.Perm (Fin (k.val + 1))
  hi : Equiv.Perm (Fin (n + 2 - k.val))
  h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1)
  hh : binaryHeightMonotone h

noncomputable def prefixSplitTripleEquivProd
    (n : ℕ) (k : Candidate (n + 1)) :
    PrefixSplitTriple n k ≃
      Equiv.Perm (Fin (k.val + 1)) ×
        Equiv.Perm (Fin (n + 2 - k.val)) ×
          {h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1) //
            binaryHeightMonotone h} where
  toFun x := (x.lo, x.hi, ⟨x.h, x.hh⟩)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv x := by
    cases x
    rfl
  right_inv x := by
    rcases x with ⟨lo, hi, h, hh⟩
    rfl

noncomputable instance instFintypePrefixSplitTriple
    (n : ℕ) (k : Candidate (n + 1)) : Fintype (PrefixSplitTriple n k) :=
  Fintype.ofEquiv _ (prefixSplitTripleEquivProd n k).symm

/-- Full rankings are equivalent to their canonical prefix split data. -/
noncomputable def prefixSplitRankingEquiv
    (n : ℕ) (k : Candidate (n + 1)) :
    PrefixSplitTriple n k ≃ Ranking (n + 1) where
  toFun x :=
    binaryHeightMergeRanking n k x.lo x.hi x.h x.hh
  invFun π :=
    ⟨prefixSplitLowOrder n k π,
      prefixSplitHighOrder n k π,
      prefixSplitHeight n k π, prefixSplitHeight_mono n k π⟩
  left_inv x := by
    cases x
    simp [prefixSplitLowOrder_binaryHeightMergeRanking,
      prefixSplitHighOrder_binaryHeightMergeRanking,
      prefixSplitHeight_binaryHeightMergeRanking]
  right_inv π := by
    exact binaryHeightMergeRanking_prefixSplit n k π

@[simp] theorem rankOf_binaryHeightMergeRanking_prefix
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h)
    (i : Fin (k.val + 1)) :
    rankOf (binaryHeightMergeRanking n k lo hi h hh)
        (prefixSplitCandidate n k (lo i)) =
      binaryHeightPositionCandidate n k h hh (Sum.inl i) := by
  rw [rankOf, Equiv.symm_apply_eq]
  exact (binaryHeightMergeRanking_apply_lowPosition n k lo hi h hh i).symm

@[simp] theorem rankOf_binaryHeightMergeRanking_suffix
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h)
    (j : Fin (n + 2 - k.val)) :
    rankOf (binaryHeightMergeRanking n k lo hi h hh)
        (suffixSplitCandidate n k (hi j)) =
      binaryHeightPositionCandidate n k h hh (Sum.inr j) := by
  rw [rankOf, Equiv.symm_apply_eq]
  exact (binaryHeightMergeRanking_apply_highPosition n k lo hi h hh j).symm

theorem binaryHeightPositionCandidate_low_zero_of_first_height_zero
    (n : ℕ) (k : Candidate (n + 1))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h)
    (hzero : h 0 = 0) :
    binaryHeightPositionCandidate n k h hh (Sum.inl 0) =
      (0 : Candidate (n + 1)) := by
  ext
  simp [binaryHeightPositionCandidate, binaryHeightLowPosition, hzero]

theorem binaryHeightHighPosition_zero_of_first_height_pos {a b : ℕ}
    {h : Fin (a + 1) → Fin (b + 1)}
    (hh : binaryHeightMonotone h)
    (hpos : 0 < (h 0 : ℕ))
    (hb : 0 < b) :
    binaryHeightHighPosition h (⟨0, hb⟩ : Fin b) = 0 := by
  classical
  ext
  simp [binaryHeightHighPosition]
  intro i hi
  have h0i : (0 : Fin (a + 1)) ≤ i := Fin.zero_le i
  have hmono : (h 0 : ℕ) ≤ (h i : ℕ) := hh h0i
  have hival : (h i : ℕ) = 0 := by
    simpa [hi]
  omega

theorem binaryHeightPositionCandidate_high_zero_of_first_height_pos
    (n : ℕ) (k : Candidate (n + 1))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h)
    (hpos : 0 < (h 0 : ℕ))
    (hb : 0 < n + 2 - k.val) :
    binaryHeightPositionCandidate n k h hh (Sum.inr (⟨0, hb⟩ : Fin (n + 2 - k.val))) =
      (0 : Candidate (n + 1)) := by
  ext
  simp [binaryHeightPositionCandidate,
    binaryHeightHighPosition_zero_of_first_height_pos hh hpos hb]

/-- Indicator that the first choice lies in the center prefix ending at `k`. -/
noncomputable def firstChoicePrefixIndicator
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) : ℝ :=
  if firstChoice π ≤ k then 1 else 0

theorem firstChoicePrefixIndicator_eq_zero_or_one
    (n : ℕ) (k : Candidate (n + 1)) :
    ∀ π : Ranking (n + 1),
      firstChoicePrefixIndicator n k π = 0 ∨
        firstChoicePrefixIndicator n k π = 1 := by
  intro π
  classical
  unfold firstChoicePrefixIndicator
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem firstChoicePrefixIndicator_nonneg
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) :
    0 ≤ firstChoicePrefixIndicator n k π := by
  classical
  unfold firstChoicePrefixIndicator
  split <;> norm_num

theorem firstChoicePrefixIndicator_binaryHeightMergeRanking
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1))
    (hh : binaryHeightMonotone h) :
    firstChoicePrefixIndicator n k (binaryHeightMergeRanking n k lo hi h hh) =
      binaryFirstLowIndicator k.val (n + 2 - k.val) h := by
  classical
  unfold binaryFirstLowIndicator
  by_cases hzero : h 0 = 0
  · have hpos :=
      binaryHeightPositionCandidate_low_zero_of_first_height_zero n k h hh hzero
    have hfirst :
        firstChoice (binaryHeightMergeRanking n k lo hi h hh) =
          prefixSplitCandidate n k (lo 0) := by
      rw [firstChoice]
      rw [← hpos]
      exact binaryHeightMergeRanking_apply_lowPosition n k lo hi h hh 0
    have hle :
        firstChoice (binaryHeightMergeRanking n k lo hi h hh) ≤ k := by
      rw [hfirst]
      exact prefixSplitCandidate_le n k (lo 0)
    have hle0 :
        binaryHeightMergeRanking n k lo hi h hh 0 ≤ k := by
      simpa [firstChoice] using hle
    simp [firstChoicePrefixIndicator, firstChoice, hzero, hle0]
  · have hpos0 : 0 < (h 0 : ℕ) := by
      have hval_ne : (h 0 : ℕ) ≠ 0 := by
        intro hv
        apply hzero
        ext
        simpa using hv
      exact Nat.pos_of_ne_zero hval_ne
    have hb : 0 < n + 2 - k.val := by
      have hlt := (h 0).isLt
      omega
    let j0 : Fin (n + 2 - k.val) := ⟨0, hb⟩
    have hpos :
        binaryHeightPositionCandidate n k h hh (Sum.inr j0) =
          (0 : Candidate (n + 1)) := by
      simpa [j0] using
        binaryHeightPositionCandidate_high_zero_of_first_height_pos
          n k h hh hpos0 hb
    have hfirst :
        firstChoice (binaryHeightMergeRanking n k lo hi h hh) =
          suffixSplitCandidate n k (hi j0) := by
      rw [firstChoice]
      rw [← hpos]
      exact binaryHeightMergeRanking_apply_highPosition n k lo hi h hh j0
    have hnle :
        ¬ firstChoice (binaryHeightMergeRanking n k lo hi h hh) ≤ k := by
      rw [hfirst]
      exact not_le_of_gt (k_lt_suffixSplitCandidate n k (hi j0))
    have hnle0 :
        ¬ binaryHeightMergeRanking n k lo hi h hh 0 ≤ k := by
      simpa [firstChoice] using hnle
    simp [firstChoicePrefixIndicator, firstChoice, hzero, hnle0]

theorem firstChoicePrefixIndicator_le_one
    (n : ℕ) (k : Candidate (n + 1)) (π : Ranking (n + 1)) :
    firstChoicePrefixIndicator n k π ≤ 1 := by
  classical
  unfold firstChoicePrefixIndicator
  split <;> norm_num

/--
Total version of `binaryHeightMergeRanking`.

The binary FKG sums range over the full product lattice of height vectors; the
geometric interleaving weight is zero off monotone heights, so a harmless
default ranking is enough there.
-/
noncomputable def binaryHeightMergeRankingTotal
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1)) :
    Ranking (n + 1) :=
  by
    classical
    exact
      if hh : binaryHeightMonotone h then
        binaryHeightMergeRanking n k lo hi h hh
      else
        Equiv.refl (Candidate (n + 1))

theorem binaryHeightMergeRankingTotal_of_monotone
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    {h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1)}
    (hh : binaryHeightMonotone h) :
    binaryHeightMergeRankingTotal n k lo hi h =
      binaryHeightMergeRanking n k lo hi h hh := by
  simp [binaryHeightMergeRankingTotal, hh]

theorem firstChoicePrefixIndicator_binaryHeightMergeRankingTotal_of_monotone
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    {h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1)}
    (hh : binaryHeightMonotone h) :
    firstChoicePrefixIndicator n k (binaryHeightMergeRankingTotal n k lo hi h) =
      binaryFirstLowIndicator k.val (n + 2 - k.val) h := by
  rw [binaryHeightMergeRankingTotal_of_monotone n k lo hi hh]
  exact firstChoicePrefixIndicator_binaryHeightMergeRanking n k lo hi h hh

/-!
# Sequential Choice Interface for Theorem 4

Theorem 4 is a backward-induction statement about fixed-order hiring.  The
probabilistic input needed at each history is that the human/Mallows law gives
weakly (or strictly) higher expected value for the best remaining candidate than
the algorithmic law.  This file keeps that sequential-choice layer separate from
the Mallows finite-sum work proving such dominance facts.
-/

/--
The best candidate in a finite remaining set according to a ranking.

For the empty set this returns the first choice as a harmless default; all
sequential optimality predicates below only use feasible histories with a
nonempty remaining set.
-/
noncomputable def bestInSet {n : ℕ} (π : Ranking n)
    (remaining : Finset (Candidate n)) : Candidate n :=
  if h : remaining.Nonempty then
    π ((remaining.image (rankOf π)).min' (Finset.image_nonempty.mpr h))
  else
    firstChoice π

@[simp] theorem shared_bestInSet_eq {n : ℕ} (π : Ranking n)
    (remaining : Finset (Candidate n)) :
    AppliedModelingLib.SocialChoice.Ranking.bestInSet π remaining =
      bestInSet π remaining := rfl

/-- Characterization of `bestInSet` from a pointwise least rank in the set. -/
theorem bestInSet_eq_of_forall_rank_le {n : ℕ} (π : Ranking n)
    (remaining : Finset (Candidate n)) {c : Candidate n}
    (hc : c ∈ remaining)
    (hmin : ∀ d : Candidate n, d ∈ remaining → rankOf π c ≤ rankOf π d) :
    bestInSet π remaining = c := by
  simpa [bestInSet, rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using
    AppliedModelingLib.SocialChoice.Ranking.bestInSet_eq_of_forall_rank_le
      π remaining hc
      (fun d hd => by
        simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hmin d hd)

/-- The best element of a nonempty remaining set is itself remaining. -/
theorem bestInSet_mem {n : ℕ} (π : Ranking n)
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty) :
    bestInSet π remaining ∈ remaining := by
  simpa [bestInSet] using
    AppliedModelingLib.SocialChoice.Ranking.bestInSet_mem π hremaining

/-- The best element has weakly minimal rank among the remaining candidates. -/
theorem rankOf_bestInSet_le {n : ℕ} (π : Ranking n)
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty)
    {d : Candidate n} (hd : d ∈ remaining) :
    rankOf π (bestInSet π remaining) ≤ rankOf π d := by
  simpa [bestInSet, rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using
    AppliedModelingLib.SocialChoice.Ranking.rankOf_bestInSet_le π hremaining hd

@[simp] theorem rankOf_trans_center_symm {n : ℕ}
    (ρ π : Ranking n) (c : Candidate n) :
    rankOf (π.trans ρ.symm) (rankOf ρ c) = rankOf π c := by
  simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using
    AppliedModelingLib.SocialChoice.Ranking.rankOf_trans_center_symm ρ π c

/--
After relabeling candidates by center rank, the best remaining candidate is the
center rank of the original best remaining candidate.
-/
theorem bestInSet_trans_center_symm
    {n : ℕ} (ρ π : Ranking n) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) :
    bestInSet (π.trans ρ.symm) (remaining.image (rankOf ρ)) =
      rankOf ρ (bestInSet π remaining) := by
  simpa [bestInSet, AppliedModelingLib.SocialChoice.Ranking.bestInSet,
      rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using
    AppliedModelingLib.SocialChoice.Ranking.bestInSet_trans_center_symm
      ρ π hremaining

/-- Swapping the positions of two candidates in a ranking. -/
def swapCandidatePositions {n : ℕ} (π : Ranking n)
    (c d : Candidate n) : Ranking n := (Equiv.swap (rankOf π c) (rankOf π d)).trans π

@[simp] theorem shared_swapCandidatePositions_eq {n : ℕ}
    (π : Ranking n) (c d : Candidate n) :
    AppliedModelingLib.SocialChoice.Ranking.swapCandidatePositions π c d =
      swapCandidatePositions π c d := by
  unfold AppliedModelingLib.SocialChoice.Ranking.swapCandidatePositions
    swapCandidatePositions
  simp [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf]

@[simp] theorem rankOf_swapCandidatePositions_left {n : ℕ}
    (π : Ranking n) (c d : Candidate n) :
    rankOf (swapCandidatePositions π c d) c = rankOf π d := by
  simpa [swapCandidatePositions, rankOf,
      AppliedModelingLib.SocialChoice.Ranking.rankOf] using
    AppliedModelingLib.SocialChoice.Ranking.rankOf_swapCandidatePositions_left π c d

@[simp] theorem rankOf_swapCandidatePositions_right {n : ℕ}
    (π : Ranking n) (c d : Candidate n) :
    rankOf (swapCandidatePositions π c d) d = rankOf π c := by
  simpa [swapCandidatePositions, rankOf,
      AppliedModelingLib.SocialChoice.Ranking.rankOf] using
    AppliedModelingLib.SocialChoice.Ranking.rankOf_swapCandidatePositions_right π c d

theorem rankOf_swapCandidatePositions_of_ne {n : ℕ}
    (π : Ranking n) {c d e : Candidate n}
    (hec : e ≠ c) (hed : e ≠ d) :
    rankOf (swapCandidatePositions π c d) e = rankOf π e := by
  simpa [swapCandidatePositions, rankOf,
      AppliedModelingLib.SocialChoice.Ranking.rankOf] using
    AppliedModelingLib.SocialChoice.Ranking.rankOf_swapCandidatePositions_of_ne
      π hec hed

theorem swapCandidatePositions_comm {n : ℕ}
    (π : Ranking n) (c d : Candidate n) :
    swapCandidatePositions π c d = swapCandidatePositions π d c := by
  simpa [swapCandidatePositions] using
    AppliedModelingLib.SocialChoice.Ranking.swapCandidatePositions_comm π c d

theorem swapCandidatePositions_involutive {n : ℕ}
    (π : Ranking n) (c d : Candidate n) :
    swapCandidatePositions (swapCandidatePositions π c d) c d = π := by
  simpa [swapCandidatePositions] using
    AppliedModelingLib.SocialChoice.Ranking.swapCandidatePositions_involutive π c d

/-- Swapping two candidates' positions is an involutive equivalence on rankings. -/
def swapCandidatePositionsEquiv {n : ℕ} (c d : Candidate n) :
    Ranking n ≃ Ranking n where
  toFun π := swapCandidatePositions π c d
  invFun π := swapCandidatePositions π c d
  left_inv π := swapCandidatePositions_involutive π c d
  right_inv π := swapCandidatePositions_involutive π c d

/-- Rankings are equal when every candidate has the same position. -/
theorem ranking_ext_of_rankOf {n : ℕ} {π σ : Ranking n}
    (h : ∀ c : Candidate n, rankOf π c = rankOf σ c) :
    π = σ :=
    AppliedModelingLib.SocialChoice.Ranking.ranking_ext_of_rankOf
      (fun c => by
        simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using h c)

theorem apply_eq_of_rankOf {n : ℕ} (π : Ranking n)
    {x c : Candidate n} (h : rankOf π c = x) : π x = c :=
    AppliedModelingLib.SocialChoice.Ranking.apply_eq_of_rankOf π
      (by simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using h)

theorem eq_of_rankOf_eq {n : ℕ} (π : Ranking n)
    {c d : Candidate n} (h : rankOf π c = rankOf π d) : c = d :=
    AppliedModelingLib.SocialChoice.Ranking.eq_of_rankOf_eq π
      (by simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using h)

theorem rank_lt_adjacent_succ_iff_lt_castSucc_of_ne_castSucc
    {n : ℕ} (k : Fin (n + 1)) {r : Candidate n}
    (hr : r ≠ k.castSucc) :
    r < k.succ ↔ r < k.castSucc := by
  constructor
  · intro h
    rw [Fin.lt_def] at h ⊢
    have hrval : r.val ≠ k.val := by
      intro hval
      exact hr (Fin.ext hval)
    simp at h ⊢
    omega
  · exact fun h => lt_trans h k.castSucc_lt_succ

theorem adjacent_castSucc_lt_rank_iff_succ_lt_of_ne_succ
    {n : ℕ} (k : Fin (n + 1)) {r : Candidate n}
    (hr : r ≠ k.succ) :
    k.castSucc < r ↔ k.succ < r := by
  constructor
  · intro h
    rw [Fin.lt_def] at h ⊢
    have hrval : r.val ≠ k.val + 1 := by
      intro hval
      exact hr (Fin.ext (by simpa using hval))
    simp at h ⊢
    omega
  · exact fun h => lt_trans k.castSucc_lt_succ h

/--
If `d` is best in a remaining set containing both `c` and `d`, then swapping
the positions of `c` and `d` makes `c` best in that same remaining set.
-/
theorem bestInSet_swapCandidatePositions_of_bestInSet_eq
    {n : ℕ} (π : Ranking n) {remaining : Finset (Candidate n)}
    {c d : Candidate n} (hc : c ∈ remaining) (hd : d ∈ remaining)
    (hbest : bestInSet π remaining = d) :
    bestInSet (swapCandidatePositions π c d) remaining = c := by
  simpa [bestInSet, swapCandidatePositions] using
    AppliedModelingLib.SocialChoice.Ranking.bestInSet_swapCandidatePositions_of_bestInSet_eq
      π hc hd (by simpa [bestInSet] using hbest)

theorem bestInSet_swapCandidatePositions_eq_iff
    {n : ℕ} (π : Ranking n) {remaining : Finset (Candidate n)}
    {c d : Candidate n} (hc : c ∈ remaining) (hd : d ∈ remaining) :
    c = bestInSet (swapCandidatePositions π c d) remaining ↔
      d = bestInSet π remaining := by
  simpa [bestInSet, swapCandidatePositions] using
    AppliedModelingLib.SocialChoice.Ranking.bestInSet_swapCandidatePositions_eq_iff
      π hc hd

/--
If `d` is not the best remaining candidate and `d` precedes `c`, then moving
`c` into `d`'s position and `d` into `c`'s position leaves the best remaining
candidate unchanged.
-/
theorem bestInSet_swapCandidatePositions_of_not_best
    {n : ℕ} (π : Ranking n) {remaining : Finset (Candidate n)}
    {c d : Candidate n} (hc : c ∈ remaining) (hd : d ∈ remaining)
    (hpos : rankOf π d < rankOf π c)
    (hnot : d ≠ bestInSet π remaining) :
    bestInSet (swapCandidatePositions π c d) remaining =
      bestInSet π remaining := by
  simpa [bestInSet, swapCandidatePositions] using
    AppliedModelingLib.SocialChoice.Ranking.bestInSet_swapCandidatePositions_of_not_best
      π hc hd
      (by simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hpos)
      (by simpa [bestInSet] using hnot)

/--
Correcting an inverted center-ordered pair inside the remaining set weakly
improves the deterministic value of the best remaining candidate.
-/
theorem bestInSet_value_le_swapCandidatePositions
    {n : ℕ} (ρ π : Ranking n) {remaining : Finset (Candidate n)}
    {value : Candidate n → ℝ} {c d : Candidate n}
    (hvalue : WeaklyOrderedBy ρ value)
    (hcenter : rankOf ρ c < rankOf ρ d)
    (hc : c ∈ remaining) (hd : d ∈ remaining)
    (hpos : rankOf π d < rankOf π c) :
    value (bestInSet π remaining) ≤
      value (bestInSet (swapCandidatePositions π c d) remaining) := by
  have hvalue' :
      AppliedModelingLib.SocialChoice.Ranking.WeaklyOrderedBy ρ value := by
    intro a b hab
    exact hvalue (by
      simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hab)
  simpa [bestInSet, swapCandidatePositions] using
    AppliedModelingLib.SocialChoice.Ranking.bestInSet_value_le_swapCandidatePositions
      ρ π hvalue'
      (by simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hcenter)
      hc hd
      (by simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hpos)

theorem le_castSucc_of_le_succ_of_ne
    {n : ℕ} {k : Fin (n + 1)} {x : Fin (n + 2)}
    (hx : x ≤ k.succ) (hne : x ≠ k.succ) :
    x ≤ k.castSucc :=  AppliedModelingLib.SocialChoice.Ranking.le_castSucc_of_le_succ_of_ne hx hne

theorem succ_le_of_castSucc_le_of_ne
    {n : ℕ} {k : Fin (n + 1)} {x : Fin (n + 2)}
    (hx : k.castSucc ≤ x) (hne : x ≠ k.castSucc) :
    k.succ ≤ x :=  AppliedModelingLib.SocialChoice.Ranking.succ_le_of_castSucc_le_of_ne hx hne

/--
Correcting an adjacent inverted pair weakly improves the deterministic
best-in-set value.  Unlike arbitrary position swaps, this remains true for
proper remaining subsets: if only one of the adjacent candidates remains, their
swap does not change the relative order of remaining candidates.
-/
theorem bestInSet_value_le_adjacent_swapCandidatePositions
    {n : ℕ} (ρ π : Ranking n) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy ρ value)
    (k : Fin (n + 1))
    (hcenter :
      rankOf ρ (π k.succ) < rankOf ρ (π k.castSucc)) :
    value (bestInSet π remaining) ≤
      value
        (bestInSet
          (swapCandidatePositions π (π k.succ) (π k.castSucc))
          remaining) := by
  simpa [shared_bestInSet_eq, shared_swapCandidatePositions_eq] using
    AppliedModelingLib.SocialChoice.Ranking.bestInSet_value_le_adjacent_swapCandidatePositions
      ρ π hremaining
      (by
        intro c d hcd
        exact hvalue (by
          simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hcd))
      k
      (by simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hcenter)

/--
A payoff improves when an adjacent pair of candidates is swapped to correct an
inversion relative to the center ranking.
-/
def AdjacentSwapImproves {n : ℕ}
    (ρ : Ranking n) (F : Ranking n → ℝ) : Prop :=
  ∀ π : Ranking n, ∀ k : Fin (n + 1),
    rankOf ρ (π k.succ) < rankOf ρ (π k.castSucc) →
      F π ≤ F (swapCandidatePositions π (π k.succ) (π k.castSucc))

/-- One adjacent correction step in the weak order induced by a center ranking. -/
def AdjacentCorrection {n : ℕ} (ρ : Ranking n)
    (π σ : Ranking n) : Prop :=
  ∃ k : Fin (n + 1),
    rankOf ρ (π k.succ) < rankOf ρ (π k.castSucc) ∧
      σ = swapCandidatePositions π (π k.succ) (π k.castSucc)

/--
Weak-order reachability generated by adjacent inversion corrections.  The
orientation is from a noisier ranking to a weakly corrected ranking.
-/
def WeakBruhatLe {n : ℕ} (ρ : Ranking n)
    (π σ : Ranking n) : Prop := Relation.ReflTransGen (AdjacentCorrection ρ) π σ

theorem AdjacentSwapImproves.le_of_adjacentCorrection
    {n : ℕ} {ρ : Ranking n} {F : Ranking n → ℝ}
    (hF : AdjacentSwapImproves ρ F) {π σ : Ranking n}
    (hstep : AdjacentCorrection ρ π σ) :
    F π ≤ F σ := by
  simpa [AdjacentSwapImproves, AdjacentCorrection, shared_swapCandidatePositions_eq,
    rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using
    AppliedModelingLib.SocialChoice.Ranking.AdjacentSwapImproves.le_of_adjacentCorrection
      (ρ := ρ) (F := F)
      (by
        intro π k hcenter
        exact hF π k (by
          simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hcenter))
      (by
        rcases hstep with ⟨k, hcenter, hσ⟩
        exact ⟨k, by
          simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hcenter,
          by simpa [hσ, shared_swapCandidatePositions_eq]⟩)

theorem AdjacentSwapImproves.le_of_weakBruhatLe
    {n : ℕ} {ρ : Ranking n} {F : Ranking n → ℝ}
    (hF : AdjacentSwapImproves ρ F) {π σ : Ranking n}
    (hpath : WeakBruhatLe ρ π σ) :
    F π ≤ F σ := by
  induction hpath using Relation.ReflTransGen.trans_induction_on with
  | refl => exact le_rfl
  | single hstep => exact hF.le_of_adjacentCorrection hstep
  | trans _ _ hleft hright => exact le_trans hleft hright

theorem binaryHeightMergeRanking_adjacentCorrection_lowerAt
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    {h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1)}
    (hh : binaryHeightMonotone h)
    {i : Fin (k.val + 1)}
    (hpos : 0 < (h i : ℕ))
    (hleft :
      ∀ j : Fin (k.val + 1), j < i → (h j : ℕ) < (h i : ℕ)) :
    AdjacentCorrection (Equiv.refl (Candidate (n + 1)))
      (binaryHeightMergeRanking n k lo hi h hh)
      (binaryHeightMergeRanking n k lo hi
        (binaryHeightLowerAt h i hpos)
        (binaryHeightMonotone_lowerAt hh hpos hleft)) := by
  classical
  let h' : Fin (k.val + 1) → Fin (n + 2 - k.val + 1) :=
    binaryHeightLowerAt h i hpos
  let hh' : binaryHeightMonotone h' :=
    binaryHeightMonotone_lowerAt hh hpos hleft
  let j : Fin (n + 2 - k.val) := ⟨(h i).val - 1, by
    have hi_lt := (h i).isLt
    omega⟩
  let π₀ : Ranking (n + 1) := binaryHeightMergeRanking n k lo hi h hh
  let π₁ : Ranking (n + 1) := binaryHeightMergeRanking n k lo hi h' hh'
  let low : Candidate (n + 1) := prefixSplitCandidate n k (lo i)
  let high : Candidate (n + 1) := suffixSplitCandidate n k (hi j)
  have hlow_new_val :
      (binaryHeightPositionCandidate n k h' hh' (Sum.inl i) : ℕ) =
        i.val + (h i).val - 1 := by
    simpa [binaryHeightPositionCandidate, h'] using
      binaryHeightLowPosition_lowerAt_self_val h i hpos
  have hpos_high_val :
      (binaryHeightPositionCandidate n k h hh (Sum.inr j) : ℕ) =
        i.val + (h i).val - 1 := by
    simpa [binaryHeightPositionCandidate, j] using
      binaryHeightHighPosition_cross_val hh hpos hleft
  have hhigh_new_val :
      (binaryHeightPositionCandidate n k h' hh' (Sum.inr j) : ℕ) =
        i.val + (h i).val := by
    simpa [binaryHeightPositionCandidate, h', j] using
      binaryHeightHighPosition_lowerAt_cross_val hh hpos hleft
  have hpos_low_val :
      (binaryHeightPositionCandidate n k h hh (Sum.inl i) : ℕ) =
        i.val + (h i).val := by
    simp [binaryHeightPositionCandidate, binaryHeightLowPosition]
  have hlow_new_eq_high_old :
      binaryHeightPositionCandidate n k h' hh' (Sum.inl i) =
        binaryHeightPositionCandidate n k h hh (Sum.inr j) := by
    ext
    rw [hlow_new_val, hpos_high_val]
  have hhigh_new_eq_low_old :
      binaryHeightPositionCandidate n k h' hh' (Sum.inr j) =
        binaryHeightPositionCandidate n k h hh (Sum.inl i) := by
    ext
    rw [hhigh_new_val, hpos_low_val]
  have hpos_high_lt : (binaryHeightPositionCandidate n k h hh (Sum.inr j) : ℕ) < n + 2 := by
    have hlow_lt := (binaryHeightPositionCandidate n k h hh (Sum.inl i)).isLt
    rw [hpos_low_val] at hlow_lt
    rw [hpos_high_val]
    omega
  let p : Fin (n + 2) :=
    ⟨(binaryHeightPositionCandidate n k h hh (Sum.inr j) : ℕ), hpos_high_lt⟩
  have hp_cast :
      (p.castSucc : Candidate (n + 1)) =
        binaryHeightPositionCandidate n k h hh (Sum.inr j) := by
    ext
    rfl
  have hp_succ :
      (p.succ : Candidate (n + 1)) =
        binaryHeightPositionCandidate n k h hh (Sum.inl i) := by
    ext
    simp [p, hpos_high_val, hpos_low_val]
    omega
  have hlow_apply : π₀ p.succ = low := by
    simp [π₀, low, hp_succ]
  have hhigh_apply : π₀ p.castSucc = high := by
    simp [π₀, high, hp_cast]
  refine ⟨p, ?_, ?_⟩
  · rw [hlow_apply, hhigh_apply]
    simpa [rankOf] using
      lt_of_le_of_lt (prefixSplitCandidate_le n k (lo i))
        (k_lt_suffixSplitCandidate n k (hi j))
  · have hswap :
        swapCandidatePositions π₀ low high = π₁ := by
      apply ranking_ext_of_rankOf
      intro c
      rcases (splitCandidateOrderedSumEquiv n k lo hi).surjective c with ⟨x, rfl⟩
      rcases x with x | x
      · by_cases hxi : x = i
        · subst x
          simp [π₀, π₁, low, high, hlow_new_eq_high_old]
        · have hne_low :
              prefixSplitCandidate n k (lo x) ≠ low := by
            intro hEq
            apply hxi
            apply lo.injective
            ext
            simpa [low] using congrArg Fin.val hEq
          have hne_high :
              prefixSplitCandidate n k (lo x) ≠ high := by
            exact prefixSplitCandidate_ne_suffixSplitCandidate n k (lo x) (hi j)
          have hpos_same :
              binaryHeightPositionCandidate n k h' hh' (Sum.inl x) =
                binaryHeightPositionCandidate n k h hh (Sum.inl x) := by
            ext
            simp [binaryHeightPositionCandidate, h',
              binaryHeightLowPosition_lowerAt_of_ne h hpos hxi]
          simp only [splitCandidateOrderedSumEquiv_apply_inl]
          rw [rankOf_swapCandidatePositions_of_ne π₀ hne_low hne_high]
          simp [π₀, π₁, hpos_same]
      · by_cases hxj : x = j
        · subst x
          simp [π₀, π₁, low, high, hhigh_new_eq_low_old]
        · have hne_high :
              suffixSplitCandidate n k (hi x) ≠ high := by
            intro hEq
            apply hxj
            apply hi.injective
            ext
            simpa [high] using congrArg Fin.val hEq
          have hne_low :
              suffixSplitCandidate n k (hi x) ≠ low := by
            intro hEq
            exact prefixSplitCandidate_ne_suffixSplitCandidate n k (lo i) (hi x)
              hEq.symm
          have hx_cross : x.val ≠ (h i).val - 1 := by
            intro hval
            apply hxj
            ext
            simpa [j] using hval
          have hpos_same :
              binaryHeightPositionCandidate n k h' hh' (Sum.inr x) =
                binaryHeightPositionCandidate n k h hh (Sum.inr x) := by
            ext
            simp [binaryHeightPositionCandidate, h',
              binaryHeightHighPosition_lowerAt_of_ne_cross h hpos hx_cross]
          simp only [splitCandidateOrderedSumEquiv_apply_inr]
          rw [rankOf_swapCandidatePositions_of_ne π₀ hne_low hne_high]
          simp [π₀, π₁, hpos_same]
    rw [hlow_apply, hhigh_apply]
    exact hswap.symm

theorem binaryHeightMergeRanking_weakBruhatLe_of_le
    (n : ℕ) (k : Candidate (n + 1))
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    {h h₀ : Fin (k.val + 1) → Fin (n + 2 - k.val + 1)}
    (hh : binaryHeightMonotone h)
    (hh₀ : binaryHeightMonotone h₀)
    (hle : h ≤ h₀) :
    WeakBruhatLe (Equiv.refl (Candidate (n + 1)))
      (binaryHeightMergeRanking n k lo hi h₀ hh₀)
      (binaryHeightMergeRanking n k lo hi h hh) := by
  classical
  let P : ℕ → Prop := fun m =>
    ∀ h₀ : Fin (k.val + 1) → Fin (n + 2 - k.val + 1),
      ∀ hh₀ : binaryHeightMonotone h₀,
        binaryHeightSum h₀ = m →
          h ≤ h₀ →
            WeakBruhatLe (Equiv.refl (Candidate (n + 1)))
              (binaryHeightMergeRanking n k lo hi h₀ hh₀)
              (binaryHeightMergeRanking n k lo hi h hh)
  have hP : ∀ m, P m := by
    intro m
    exact Nat.strong_induction_on (p := P) m (by
      intro m ih h₀ hh₀ hsum hle₀
      by_cases heq : h₀ = h
      · subst h₀
        exact Relation.ReflTransGen.refl
      · have hexists : ∃ i : Fin (k.val + 1), h i < h₀ i := by
          by_contra hnone
          apply heq
          funext i
          have hle_i : h i ≤ h₀ i := hle₀ i
          have hnlt : ¬ h i < h₀ i := by
            intro hi
            exact hnone ⟨i, hi⟩
          exact le_antisymm (le_of_not_gt hnlt) hle_i
        let S : Finset (Fin (k.val + 1)) :=
          (Finset.univ : Finset (Fin (k.val + 1))).filter
            (fun i => h i < h₀ i)
        have hS_nonempty : S.Nonempty := by
          rcases hexists with ⟨i, hi⟩
          exact ⟨i, by simp [S, hi]⟩
        let i : Fin (k.val + 1) := S.min' hS_nonempty
        have hi_mem : i ∈ S := by
          simpa [i] using Finset.min'_mem S hS_nonempty
        have hi_excess : h i < h₀ i := by
          simpa [S] using hi_mem
        have hpos : 0 < (h₀ i : ℕ) := by
          rw [Fin.lt_def] at hi_excess
          omega
        have hleft :
            ∀ j : Fin (k.val + 1), j < i → (h₀ j : ℕ) < (h₀ i : ℕ) := by
          intro j hji
          have hj_not_mem : j ∉ S := by
            intro hj_mem
            have hmin_le : i ≤ j := by
              simpa [i] using Finset.min'_le S j hj_mem
            exact (not_le_of_gt hji) hmin_le
          have hj_not_excess : ¬ h j < h₀ j := by
            intro hj_excess
            exact hj_not_mem
              (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj_excess⟩)
          have h₀j_le_hj : h₀ j ≤ h j := le_of_not_gt hj_not_excess
          have hj_le_hi : h j ≤ h i := hh (le_of_lt hji)
          have h₀j_lt_h₀i : h₀ j < h₀ i :=
            lt_of_le_of_lt (le_trans h₀j_le_hj hj_le_hi) hi_excess
          exact h₀j_lt_h₀i
        let h₁ : Fin (k.val + 1) → Fin (n + 2 - k.val + 1) :=
          binaryHeightLowerAt h₀ i hpos
        have hh₁ : binaryHeightMonotone h₁ :=
          binaryHeightMonotone_lowerAt hh₀ hpos hleft
        have hle₁ : h ≤ h₁ := by
          intro x
          by_cases hxi : x = i
          · subst x
            rw [Fin.le_iff_val_le_val]
            simp [h₁]
            rw [Fin.lt_def] at hi_excess
            omega
          · simpa [h₁, binaryHeightLowerAt_of_ne h₀ hpos hxi] using hle₀ x
        have hsum_lt : binaryHeightSum h₁ < m := by
          rw [← hsum]
          exact binaryHeightSum_lowerAt_lt h₀ hpos
        have hstep :
            AdjacentCorrection (Equiv.refl (Candidate (n + 1)))
              (binaryHeightMergeRanking n k lo hi h₀ hh₀)
              (binaryHeightMergeRanking n k lo hi h₁ hh₁) := by
          simpa [h₁, hh₁] using
            binaryHeightMergeRanking_adjacentCorrection_lowerAt
              n k lo hi hh₀ hpos hleft
        exact Relation.ReflTransGen.head hstep
          (ih (binaryHeightSum h₁) hsum_lt h₁ hh₁ rfl hle₁))
  exact hP (binaryHeightSum h₀) h₀ hh₀ rfl hle

/--
Downward closure of a ranking event along a binary-height merge map.

The FKG argument runs on the full product lattice of height vectors, while the
ranking merge is only meaningful on monotone height vectors.  This wrapper
extends a 0/1 ranking event to the whole product lattice by downward closure
from supported monotone heights.
-/
noncomputable def binaryHeightDownClosedEvent {a b n : ℕ}
    (merge : (Fin a → Fin (b + 1)) → Ranking n)
    (F : Ranking n → ℝ) (h : Fin a → Fin (b + 1)) : ℝ :=
  by
    classical
    exact
      if ∃ h₀ : Fin a → Fin (b + 1),
          binaryHeightMonotone h₀ ∧ h ≤ h₀ ∧ F (merge h₀) = 1
      then 1 else 0

theorem binaryHeightDownClosedEvent_nonneg {a b n : ℕ}
    (merge : (Fin a → Fin (b + 1)) → Ranking n)
    (F : Ranking n → ℝ) (h : Fin a → Fin (b + 1)) :
    0 ≤ binaryHeightDownClosedEvent merge F h := by
  classical
  unfold binaryHeightDownClosedEvent
  by_cases hw :
      ∃ h₀ : Fin a → Fin (b + 1),
        binaryHeightMonotone h₀ ∧ h ≤ h₀ ∧ F (merge h₀) = 1
  · simp [hw]
  · simp [hw]

theorem binaryHeightDownClosedEvent_antitone {a b n : ℕ}
    (merge : (Fin a → Fin (b + 1)) → Ranking n)
    (F : Ranking n → ℝ) :
    Antitone (binaryHeightDownClosedEvent merge F) := by
  classical
  intro h₁ h₂ hle
  unfold binaryHeightDownClosedEvent
  by_cases h2 :
      ∃ h₀ : Fin a → Fin (b + 1),
        binaryHeightMonotone h₀ ∧ h₂ ≤ h₀ ∧ F (merge h₀) = 1
  · rcases h2 with ⟨h₀, hh₀, h₂_le, hF₀⟩
    have h1 :
        ∃ h₀ : Fin a → Fin (b + 1),
          binaryHeightMonotone h₀ ∧ h₁ ≤ h₀ ∧ F (merge h₀) = 1 :=
      ⟨h₀, hh₀, le_trans hle h₂_le, hF₀⟩
    by_cases h2' :
        ∃ h₀ : Fin a → Fin (b + 1),
          binaryHeightMonotone h₀ ∧ h₂ ≤ h₀ ∧ F (merge h₀) = 1 <;>
      simp [h1, h2']
  · by_cases h1 :
        ∃ h₀ : Fin a → Fin (b + 1),
          binaryHeightMonotone h₀ ∧ h₁ ≤ h₀ ∧ F (merge h₀) = 1 <;>
      simp [h1, h2]

theorem binaryHeightDownClosedEvent_eq_merge_of_monotone {a b n : ℕ}
    {ρ : Ranking n} {merge : (Fin a → Fin (b + 1)) → Ranking n}
    {F : Ranking n → ℝ}
    (hF01 : ∀ τ, F τ = 0 ∨ F τ = 1)
    (hF : AdjacentSwapImproves ρ F)
    (hmerge :
      ∀ {h h₀ : Fin a → Fin (b + 1)},
        binaryHeightMonotone h → binaryHeightMonotone h₀ → h ≤ h₀ →
          WeakBruhatLe ρ (merge h₀) (merge h))
    {h : Fin a → Fin (b + 1)}
    (hh : binaryHeightMonotone h) :
    binaryHeightDownClosedEvent merge F h = F (merge h) := by
  classical
  rcases hF01 (merge h) with hFh | hFh
  · have hno :
        ¬ ∃ h₀ : Fin a → Fin (b + 1),
          binaryHeightMonotone h₀ ∧ h ≤ h₀ ∧ F (merge h₀) = 1 := by
      intro hw
      rcases hw with ⟨h₀, hh₀, hle, hF₀⟩
      have hpath : WeakBruhatLe ρ (merge h₀) (merge h) :=
        hmerge hh hh₀ hle
      have hleF : F (merge h₀) ≤ F (merge h) :=
        hF.le_of_weakBruhatLe hpath
      rw [hF₀, hFh] at hleF
      norm_num at hleF
    simp [binaryHeightDownClosedEvent, hno, hFh]
  · have hw :
        ∃ h₀ : Fin a → Fin (b + 1),
          binaryHeightMonotone h₀ ∧ h ≤ h₀ ∧ F (merge h₀) = 1 :=
      ⟨h, hh, le_rfl, hFh⟩
    simp [binaryHeightDownClosedEvent, hw, hFh]

theorem binaryHeightInterleavingWeight_firstLow_positiveAssociation_merge
    (a b n : ℕ) {q : ℝ} (hq : 0 ≤ q)
    {ρ : Ranking n}
    (merge : (Fin (a + 1) → Fin (b + 1)) → Ranking n)
    (F : Ranking n → ℝ)
    (hF01 : ∀ τ, F τ = 0 ∨ F τ = 1)
    (hF : AdjacentSwapImproves ρ F)
    (hmerge :
      ∀ {h h₀ : Fin (a + 1) → Fin (b + 1)},
        binaryHeightMonotone h → binaryHeightMonotone h₀ → h ≤ h₀ →
          WeakBruhatLe ρ (merge h₀) (merge h)) :
    (∑ h, binaryHeightInterleavingWeight (a + 1) b q h * F (merge h)) *
        ∑ h, binaryHeightInterleavingWeight (a + 1) b q h *
          binaryFirstLowIndicator a b h ≤
      (∑ h, binaryHeightInterleavingWeight (a + 1) b q h) *
        ∑ h, binaryHeightInterleavingWeight (a + 1) b q h *
          (F (merge h) * binaryFirstLowIndicator a b h) := by
  classical
  let E : (Fin (a + 1) → Fin (b + 1)) → ℝ :=
    binaryHeightDownClosedEvent merge F
  have hcorr :=
    binaryHeightInterleavingWeight_firstLow_positiveAssociation_antitone
      a b hq E
      (binaryHeightDownClosedEvent_nonneg merge F)
      (binaryHeightDownClosedEvent_antitone merge F)
  have hsumE :
      (∑ h, binaryHeightInterleavingWeight (a + 1) b q h * E h) =
        ∑ h, binaryHeightInterleavingWeight (a + 1) b q h * F (merge h) := by
    refine Finset.sum_congr rfl ?_
    intro h _
    by_cases hh : binaryHeightMonotone h
    · have heq :
          E h = F (merge h) :=
        binaryHeightDownClosedEvent_eq_merge_of_monotone
          hF01 hF hmerge hh
      rw [heq]
    · unfold E binaryHeightDownClosedEvent binaryHeightInterleavingWeight
      simp [hh]
  have hsumEFirst :
      (∑ h, binaryHeightInterleavingWeight (a + 1) b q h *
          (E h * binaryFirstLowIndicator a b h)) =
        ∑ h, binaryHeightInterleavingWeight (a + 1) b q h *
          (F (merge h) * binaryFirstLowIndicator a b h) := by
    refine Finset.sum_congr rfl ?_
    intro h _
    by_cases hh : binaryHeightMonotone h
    · have heq :
          E h = F (merge h) :=
        binaryHeightDownClosedEvent_eq_merge_of_monotone
          hF01 hF hmerge hh
      rw [heq]
    · unfold E binaryHeightDownClosedEvent binaryHeightInterleavingWeight
      simp [hh]
  simpa [E, hsumE, hsumEFirst] using hcorr

theorem binaryHeightInterleavingWeight_firstChoicePrefix_positiveAssociation_mergeRanking
    (n : ℕ) (k : Candidate (n + 1)) {q : ℝ} (hq : 0 ≤ q)
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (F : Ranking (n + 1) → ℝ)
    (hF01 : ∀ τ, F τ = 0 ∨ F τ = 1)
    (hF : AdjacentSwapImproves (Equiv.refl (Candidate (n + 1))) F)
    (hmerge :
      ∀ {h h₀ : Fin (k.val + 1) → Fin (n + 2 - k.val + 1)},
        binaryHeightMonotone h → binaryHeightMonotone h₀ → h ≤ h₀ →
          WeakBruhatLe (Equiv.refl (Candidate (n + 1)))
            (binaryHeightMergeRankingTotal n k lo hi h₀)
            (binaryHeightMergeRankingTotal n k lo hi h)) :
    (∑ h, binaryHeightInterleavingWeight (k.val + 1) (n + 2 - k.val) q h *
        F (binaryHeightMergeRankingTotal n k lo hi h)) *
      ∑ h, binaryHeightInterleavingWeight (k.val + 1) (n + 2 - k.val) q h *
        firstChoicePrefixIndicator n k (binaryHeightMergeRankingTotal n k lo hi h)
      ≤
    (∑ h, binaryHeightInterleavingWeight (k.val + 1) (n + 2 - k.val) q h) *
      ∑ h, binaryHeightInterleavingWeight (k.val + 1) (n + 2 - k.val) q h *
        (F (binaryHeightMergeRankingTotal n k lo hi h) *
          firstChoicePrefixIndicator n k
            (binaryHeightMergeRankingTotal n k lo hi h)) := by
  classical
  have hcorr :=
    binaryHeightInterleavingWeight_firstLow_positiveAssociation_merge
      k.val (n + 2 - k.val) (n + 1) hq
      (ρ := Equiv.refl (Candidate (n + 1)))
      (merge := binaryHeightMergeRankingTotal n k lo hi)
      F hF01 hF hmerge
  have hfirst :
      (∑ h, binaryHeightInterleavingWeight (k.val + 1) (n + 2 - k.val) q h *
          firstChoicePrefixIndicator n k
            (binaryHeightMergeRankingTotal n k lo hi h)) =
        ∑ h, binaryHeightInterleavingWeight (k.val + 1) (n + 2 - k.val) q h *
          binaryFirstLowIndicator k.val (n + 2 - k.val) h := by
    refine Finset.sum_congr rfl ?_
    intro h _
    by_cases hh : binaryHeightMonotone h
    · rw [firstChoicePrefixIndicator_binaryHeightMergeRankingTotal_of_monotone
        n k lo hi hh]
    · simp [binaryHeightInterleavingWeight, hh]
  have hfirstF :
      (∑ h, binaryHeightInterleavingWeight (k.val + 1) (n + 2 - k.val) q h *
          (F (binaryHeightMergeRankingTotal n k lo hi h) *
            firstChoicePrefixIndicator n k
              (binaryHeightMergeRankingTotal n k lo hi h))) =
        ∑ h, binaryHeightInterleavingWeight (k.val + 1) (n + 2 - k.val) q h *
          (F (binaryHeightMergeRankingTotal n k lo hi h) *
            binaryFirstLowIndicator k.val (n + 2 - k.val) h) := by
    refine Finset.sum_congr rfl ?_
    intro h _
    by_cases hh : binaryHeightMonotone h
    · rw [firstChoicePrefixIndicator_binaryHeightMergeRankingTotal_of_monotone
        n k lo hi hh]
    · simp [binaryHeightInterleavingWeight, hh]
  simpa [hfirst, hfirstF] using hcorr

theorem binaryHeightInterleavingWeight_firstChoicePrefix_positiveAssociation_mergeRanking_of_adjacentSwapImproves
    (n : ℕ) (k : Candidate (n + 1)) {q : ℝ} (hq : 0 ≤ q)
    (lo : Equiv.Perm (Fin (k.val + 1)))
    (hi : Equiv.Perm (Fin (n + 2 - k.val)))
    (F : Ranking (n + 1) → ℝ)
    (hF01 : ∀ τ, F τ = 0 ∨ F τ = 1)
    (hF : AdjacentSwapImproves (Equiv.refl (Candidate (n + 1))) F) :
    (∑ h, binaryHeightInterleavingWeight (k.val + 1) (n + 2 - k.val) q h *
        F (binaryHeightMergeRankingTotal n k lo hi h)) *
      ∑ h, binaryHeightInterleavingWeight (k.val + 1) (n + 2 - k.val) q h *
        firstChoicePrefixIndicator n k (binaryHeightMergeRankingTotal n k lo hi h)
      ≤
    (∑ h, binaryHeightInterleavingWeight (k.val + 1) (n + 2 - k.val) q h) *
      ∑ h, binaryHeightInterleavingWeight (k.val + 1) (n + 2 - k.val) q h *
        (F (binaryHeightMergeRankingTotal n k lo hi h) *
          firstChoicePrefixIndicator n k
            (binaryHeightMergeRankingTotal n k lo hi h)) := by
  refine
    binaryHeightInterleavingWeight_firstChoicePrefix_positiveAssociation_mergeRanking
      n k hq lo hi F hF01 hF ?_
  intro h h₀ hh hh₀ hle
  rw [binaryHeightMergeRankingTotal_of_monotone n k lo hi hh₀,
    binaryHeightMergeRankingTotal_of_monotone n k lo hi hh]
  exact binaryHeightMergeRanking_weakBruhatLe_of_le
    n k lo hi hh hh₀ hle

theorem binaryHeightInterleavingWeight_firstLow_positiveAssociation_mergeRanking_averaged
    (n : ℕ) (k : Candidate (n + 1)) {q : ℝ} (hq : 0 ≤ q)
    (A : Equiv.Perm (Fin (k.val + 1)) ×
        Equiv.Perm (Fin (n + 2 - k.val)) → ℝ)
    (hA_nonneg : ∀ a, 0 ≤ A a)
    (F : Ranking (n + 1) → ℝ)
    (hF01 : ∀ τ, F τ = 0 ∨ F τ = 1)
    (hF : AdjacentSwapImproves (Equiv.refl (Candidate (n + 1))) F) :
    0 ≤
      (∑ a, A a *
          ∑ h, binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q h *
            (F (binaryHeightMergeRankingTotal n k a.1 a.2 h) *
              binaryFirstLowIndicator k.val (n + 2 - k.val) h)) *
        ((∑ a, A a) *
          ∑ h, binaryHeightInterleavingWeight
            (k.val + 1) (n + 2 - k.val) q h) -
      (∑ a, A a *
          ∑ h, binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q h *
            F (binaryHeightMergeRankingTotal n k a.1 a.2 h)) *
        ((∑ a, A a) *
          ∑ h, binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q h *
            binaryFirstLowIndicator k.val (n + 2 - k.val) h) := by
  classical
  refine
    weighted_average_covariance_nonneg_of_fiber_covariance
      (A := A)
      (W := binaryHeightInterleavingWeight
        (k.val + 1) (n + 2 - k.val) q)
      (F := fun a h => F (binaryHeightMergeRankingTotal n k a.1 a.2 h))
      (G := binaryFirstLowIndicator k.val (n + 2 - k.val))
      hA_nonneg ?_
  intro a
  exact
    binaryHeightInterleavingWeight_firstLow_positiveAssociation_merge
      k.val (n + 2 - k.val) (n + 1) hq
      (ρ := Equiv.refl (Candidate (n + 1)))
      (merge := binaryHeightMergeRankingTotal n k a.1 a.2)
      F hF01 hF
      (by
        intro h h₀ hh hh₀ hle
        rw [binaryHeightMergeRankingTotal_of_monotone n k a.1 a.2 hh₀,
          binaryHeightMergeRankingTotal_of_monotone n k a.1 a.2 hh]
        exact binaryHeightMergeRanking_weakBruhatLe_of_le
          n k a.1 a.2 hh hh₀ hle)

theorem binaryHeightInterleavingWeight_firstChoicePrefix_positiveAssociation_mergeRanking_averaged
    (n : ℕ) (k : Candidate (n + 1)) {q : ℝ} (hq : 0 ≤ q)
    (A : Equiv.Perm (Fin (k.val + 1)) ×
        Equiv.Perm (Fin (n + 2 - k.val)) → ℝ)
    (hA_nonneg : ∀ a, 0 ≤ A a)
    (F : Ranking (n + 1) → ℝ)
    (hF01 : ∀ τ, F τ = 0 ∨ F τ = 1)
    (hF : AdjacentSwapImproves (Equiv.refl (Candidate (n + 1))) F) :
    0 ≤
      (∑ a, A a *
          ∑ h, binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q h *
            (F (binaryHeightMergeRankingTotal n k a.1 a.2 h) *
              firstChoicePrefixIndicator n k
                (binaryHeightMergeRankingTotal n k a.1 a.2 h))) *
        ((∑ a, A a) *
          ∑ h, binaryHeightInterleavingWeight
            (k.val + 1) (n + 2 - k.val) q h) -
      (∑ a, A a *
          ∑ h, binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q h *
            F (binaryHeightMergeRankingTotal n k a.1 a.2 h)) *
        (∑ a, A a *
          ∑ h, binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q h *
            firstChoicePrefixIndicator n k
              (binaryHeightMergeRankingTotal n k a.1 a.2 h)) := by
  classical
  have hcorr :=
    binaryHeightInterleavingWeight_firstLow_positiveAssociation_mergeRanking_averaged
      n k hq A hA_nonneg F hF01 hF
  have hfirst :
      (∑ a, A a *
          ∑ h, binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q h *
            firstChoicePrefixIndicator n k
              (binaryHeightMergeRankingTotal n k a.1 a.2 h)) =
        ((∑ a, A a) *
          ∑ h, binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q h *
            binaryFirstLowIndicator k.val (n + 2 - k.val) h) := by
    calc
      (∑ a, A a *
          ∑ h, binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q h *
            firstChoicePrefixIndicator n k
              (binaryHeightMergeRankingTotal n k a.1 a.2 h)) =
          ∑ a, A a *
            ∑ h, binaryHeightInterleavingWeight
                (k.val + 1) (n + 2 - k.val) q h *
              binaryFirstLowIndicator k.val (n + 2 - k.val) h := by
        refine Finset.sum_congr rfl ?_
        intro a _
        congr 1
        refine Finset.sum_congr rfl ?_
        intro h _
        by_cases hh : binaryHeightMonotone h
        · rw [firstChoicePrefixIndicator_binaryHeightMergeRankingTotal_of_monotone
            n k a.1 a.2 hh]
        · simp [binaryHeightInterleavingWeight, hh]
      _ = ((∑ a, A a) *
          ∑ h, binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q h *
            binaryFirstLowIndicator k.val (n + 2 - k.val) h) := by
        rw [Finset.sum_mul]
  have hFfirst :
      (∑ a, A a *
          ∑ h, binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q h *
            (F (binaryHeightMergeRankingTotal n k a.1 a.2 h) *
              firstChoicePrefixIndicator n k
                (binaryHeightMergeRankingTotal n k a.1 a.2 h))) =
        ∑ a, A a *
          ∑ h, binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q h *
            (F (binaryHeightMergeRankingTotal n k a.1 a.2 h) *
              binaryFirstLowIndicator k.val (n + 2 - k.val) h) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    congr 1
    refine Finset.sum_congr rfl ?_
    intro h _
    by_cases hh : binaryHeightMonotone h
    · rw [firstChoicePrefixIndicator_binaryHeightMergeRankingTotal_of_monotone
        n k a.1 a.2 hh]
    · simp [binaryHeightInterleavingWeight, hh]
  simpa [hfirst, hFfirst] using hcorr

/-- The best-in-set payoff is monotone under adjacent inversion corrections. -/
theorem adjacentSwapImproves_bestInSet_value
    {n : ℕ} (ρ : Ranking n) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy ρ value) :
    AdjacentSwapImproves ρ
      (fun π : Ranking n => value (bestInSet π remaining)) := by
  intro π k hcenter
  simpa [shared_bestInSet_eq, shared_swapCandidatePositions_eq] using
    AppliedModelingLib.SocialChoice.Ranking.adjacentSwapImproves_bestInSet_value
      ρ hremaining
      (by
        intro c d hcd
        exact hvalue (by
          simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hcd))
      π k
      (by simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hcenter)

/--
For a fixed remaining set, a payoff is monotone under corrections of inverted
center-ordered pairs inside that remaining set.
-/
def SwapImprovesOn {n : ℕ} (remaining : Finset (Candidate n))
    (ρ : Ranking n) (F : Ranking n → ℝ) : Prop :=
  ∀ π : Ranking n, ∀ c d : Candidate n,
    c ∈ remaining → d ∈ remaining →
      rankOf ρ c < rankOf ρ d → rankOf π d < rankOf π c →
        F π ≤ F (swapCandidatePositions π c d)

/-- The deterministic best-in-set payoff is monotone under such corrections. -/
theorem swapImprovesOn_bestInSet_value
    {n : ℕ} (ρ : Ranking n) (remaining : Finset (Candidate n))
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy ρ value) :
    SwapImprovesOn remaining ρ
      (fun π : Ranking n => value (bestInSet π remaining)) := by
  intro π c d hc hd hcenter hpos
  simpa [shared_bestInSet_eq, shared_swapCandidatePositions_eq] using
    AppliedModelingLib.SocialChoice.Ranking.swapImprovesOn_bestInSet_value
      ρ remaining
      (by
        intro a b hab
        exact hvalue (by
          simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hab))
      π c d hc hd
      (by simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hcenter)
      (by simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hpos)

/--
Map an inversion of the ranking with `i` and `j` swapped back to an inversion
of the original ranking, in center coordinates.  The cases are the four ways an
inversion can involve one of the two swapped labels.
-/
def swapInversionMap {n : ℕ} (i j : Candidate n)
    (p : Candidate n × Candidate n) : Candidate n × Candidate n :=
  if p.2 = i then
    (p.1, j)
  else if p.1 = j then
    (i, p.2)
  else if p.1 = i ∧ j < p.2 then
    (j, p.2)
  else if p.2 = j ∧ p.1 < i then
    (p.1, i)
  else
    p

/-- Inverse decoder for `swapInversionMap` on its source inversion set. -/
def swapInversionMapInv {n : ℕ} (i j : Candidate n)
    (p : Candidate n × Candidate n) : Candidate n × Candidate n :=
  if p.2 = j ∧ p.1 < i then
    (p.1, i)
  else if p.1 = i ∧ j < p.2 then
    (j, p.2)
  else if p.1 = j then
    (i, p.2)
  else if p.2 = i then
    (p.1, j)
  else
    p

theorem swapInversionMapInv_left
    {n : ℕ} {i j : Candidate n} (hij : i < j)
    {p : Candidate n × Candidate n} (hp : p.1 < p.2) :
    swapInversionMapInv i j (swapInversionMap i j p) = p := by
  classical
  rcases p with ⟨a, b⟩
  dsimp at hp
  unfold swapInversionMap swapInversionMapInv
  by_cases hbi : b = i
  · subst b
    have hai : a < i := hp
    have haj : a < j := lt_trans hai hij
    simp [hai]
  · rw [if_neg hbi]
    by_cases haj_eq : a = j
    · subst a
      have hjb : j < b := hp
      have hbj : b ≠ j := ne_of_gt hjb
      simp [hjb, hbj]
    · rw [if_neg haj_eq]
      by_cases hai_jb : a = i ∧ j < b
      · rcases hai_jb with ⟨hai_eq, hjb⟩
        subst a
        have hbj : b ≠ j := ne_of_gt hjb
        have hji_not : ¬j < i := not_lt_of_gt hij
        simp [hjb, hbj, hji_not]
      · rw [if_neg hai_jb]
        by_cases hbj_ai : b = j ∧ a < i
        · rcases hbj_ai with ⟨hbj_eq, hai⟩
          subst b
          have hai_ne : a ≠ i := ne_of_lt hai
          have haj_ne : a ≠ j := ne_of_lt (lt_trans hai hij)
          simp [hai, hai_ne, haj_ne]
        · rw [if_neg hbj_ai]
          simp [hbi, haj_eq, hai_jb, hbj_ai]

/--
For an identity-center ranking, an inversion after swapping the positions of a
center-ordered inverted pair maps to an inversion of the original ranking.
-/
theorem swapInversionMap_mem_inversionFinset_refl
    {n : ℕ} (τ : Ranking n) {i j : Candidate n}
    (hij : i < j) (hpos : rankOf τ j < rankOf τ i)
    {p : Candidate n × Candidate n}
    (hp : p ∈ inversionFinset (Equiv.refl (Candidate n))
        (swapCandidatePositions τ i j)) :
    swapInversionMap i j p ∈
      inversionFinset (Equiv.refl (Candidate n)) τ := by
  classical
  rcases p with ⟨a, b⟩
  have hinv :
      invertedPair (Equiv.refl (Candidate n))
        (swapCandidatePositions τ i j) (a, b) := by
    simpa [inversionFinset] using hp
  have hab : a < b := by
    simpa [invertedPair, rankOf] using hinv.1
  have hrank :
      rankOf (swapCandidatePositions τ i j) b <
        rankOf (swapCandidatePositions τ i j) a := by
    simpa [invertedPair] using hinv.2
  unfold swapInversionMap
  by_cases hbi : b = i
  · rw [if_pos hbi]
    subst b
    have hai : a < i := hab
    have haj : a < j := lt_trans hai hij
    have ha_ne_i : a ≠ i := ne_of_lt hai
    have ha_ne_j : a ≠ j := ne_of_lt haj
    have hrank_a :
        rankOf (swapCandidatePositions τ i j) a = rankOf τ a :=
      rankOf_swapCandidatePositions_of_ne τ ha_ne_i ha_ne_j
    have hlt_rank : rankOf τ j < rankOf τ a := by
      simpa [hrank_a] using hrank
    have htarget :
        invertedPair (Equiv.refl (Candidate n)) τ (a, j) :=
      ⟨by simpa [rankOf] using haj, hlt_rank⟩
    simpa [inversionFinset] using htarget
  · rw [if_neg hbi]
    by_cases haj_eq : a = j
    · rw [if_pos haj_eq]
      subst a
      have hjb : j < b := hab
      have hb_ne_i : b ≠ i := by
        intro hb
        subst b
        exact (not_lt_of_gt hij) hjb
      have hb_ne_j : b ≠ j := ne_of_gt hjb
      have hrank_b :
          rankOf (swapCandidatePositions τ i j) b = rankOf τ b :=
        rankOf_swapCandidatePositions_of_ne τ hb_ne_i hb_ne_j
      have hlt_rank : rankOf τ b < rankOf τ i := by
        simpa [hrank_b] using hrank
      have htarget :
          invertedPair (Equiv.refl (Candidate n)) τ (i, b) :=
        ⟨by simpa [rankOf] using lt_trans hij hjb, hlt_rank⟩
      simpa [inversionFinset] using htarget
    · rw [if_neg haj_eq]
      by_cases hai_jb : a = i ∧ j < b
      · rw [if_pos hai_jb]
        rcases hai_jb with ⟨hai_eq, hjb⟩
        subst a
        have hb_ne_i : b ≠ i := by
          intro hb
          subst b
          exact (not_lt_of_gt hij) hjb
        have hb_ne_j : b ≠ j := ne_of_gt hjb
        have hrank_b :
            rankOf (swapCandidatePositions τ i j) b = rankOf τ b :=
          rankOf_swapCandidatePositions_of_ne τ hb_ne_i hb_ne_j
        have hlt_rank : rankOf τ b < rankOf τ j := by
          simpa [hrank_b] using hrank
        have htarget :
            invertedPair (Equiv.refl (Candidate n)) τ (j, b) :=
          ⟨by simpa [rankOf] using hjb, hlt_rank⟩
        simpa [inversionFinset] using htarget
      · rw [if_neg hai_jb]
        by_cases hbj_ai : b = j ∧ a < i
        · rw [if_pos hbj_ai]
          rcases hbj_ai with ⟨hbj_eq, hai⟩
          subst b
          have ha_ne_i : a ≠ i := ne_of_lt hai
          have ha_ne_j : a ≠ j := ne_of_lt (lt_trans hai hij)
          have hrank_a :
              rankOf (swapCandidatePositions τ i j) a = rankOf τ a :=
            rankOf_swapCandidatePositions_of_ne τ ha_ne_i ha_ne_j
          have hlt_rank : rankOf τ i < rankOf τ a := by
            simpa [hrank_a] using hrank
          have htarget :
              invertedPair (Equiv.refl (Candidate n)) τ (a, i) :=
            ⟨by simpa [rankOf] using hai, hlt_rank⟩
          simpa [inversionFinset] using htarget
        · rw [if_neg hbj_ai]
          by_cases hai : a = i
          · subst a
            have hib : i < b := hab
            have hnot_jb : ¬j < b := by
              intro hjb
              exact hai_jb ⟨rfl, hjb⟩
            have hb_le_j : b ≤ j := le_of_not_gt hnot_jb
            have hb_ne_j : b ≠ j := by
              intro hbj
              subst b
              have hbad : rankOf τ i < rankOf τ j := by
                simpa using hrank
              exact (not_lt_of_gt hpos) hbad
            have hb_ne_i : b ≠ i := hbi
            have hrank_b :
                rankOf (swapCandidatePositions τ i j) b = rankOf τ b :=
              rankOf_swapCandidatePositions_of_ne τ hb_ne_i hb_ne_j
            have hlt_rank_bj : rankOf τ b < rankOf τ j := by
              simpa [hrank_b] using hrank
            have hlt_rank : rankOf τ b < rankOf τ i :=
              lt_trans hlt_rank_bj hpos
            have htarget :
                invertedPair (Equiv.refl (Candidate n)) τ (i, b) :=
              ⟨by simpa [rankOf] using hib, hlt_rank⟩
            simpa [inversionFinset] using htarget
          · by_cases hbj : b = j
            · subst b
              have haj_lt : a < j := hab
              have hnot_ai : ¬a < i := by
                intro hai_lt
                exact hbj_ai ⟨rfl, hai_lt⟩
              have hi_le_a : i ≤ a := le_of_not_gt hnot_ai
              have ha_ne_i : a ≠ i := by
                intro hai_eq
                subst a
                have hbad : rankOf τ i < rankOf τ j := by
                  simpa using hrank
                exact (not_lt_of_gt hpos) hbad
              have ha_ne_j : a ≠ j := haj_eq
              have hrank_a :
                  rankOf (swapCandidatePositions τ i j) a = rankOf τ a :=
                rankOf_swapCandidatePositions_of_ne τ ha_ne_i ha_ne_j
              have hlt_rank_ia : rankOf τ i < rankOf τ a := by
                simpa [hrank_a] using hrank
              have hlt_rank : rankOf τ j < rankOf τ a :=
                lt_trans hpos hlt_rank_ia
              have htarget :
                  invertedPair (Equiv.refl (Candidate n)) τ (a, j) :=
                ⟨by simpa [rankOf] using haj_lt, hlt_rank⟩
              simpa [inversionFinset] using htarget
            · have ha_ne_i : a ≠ i := hai
              have ha_ne_j : a ≠ j := haj_eq
              have hb_ne_i : b ≠ i := hbi
              have hb_ne_j : b ≠ j := hbj
              have hrank_a :
                  rankOf (swapCandidatePositions τ i j) a = rankOf τ a :=
                rankOf_swapCandidatePositions_of_ne τ ha_ne_i ha_ne_j
              have hrank_b :
                  rankOf (swapCandidatePositions τ i j) b = rankOf τ b :=
                rankOf_swapCandidatePositions_of_ne τ hb_ne_i hb_ne_j
              have hlt_rank : rankOf τ b < rankOf τ a := by
                simpa [hrank_a, hrank_b] using hrank
              have htarget :
                  invertedPair (Equiv.refl (Candidate n)) τ (a, b) :=
                ⟨by simpa [rankOf] using hab, hlt_rank⟩
              simpa [inversionFinset] using htarget

/--
Swapping a center-ordered inverted pair in an identity-center ranking weakly
lowers Kendall tau.
-/
theorem kendallTau_refl_swapCandidatePositions_le
    {n : ℕ} (τ : Ranking n) {i j : Candidate n}
    (hij : i < j) (hpos : rankOf τ j < rankOf τ i) :
    kendallTau (Equiv.refl (Candidate n)) (swapCandidatePositions τ i j) ≤
      kendallTau (Equiv.refl (Candidate n)) τ := by
  classical
  unfold kendallTau
  refine Finset.card_le_card_of_injOn
    (swapInversionMap i j) ?hmaps ?hinj
  · intro p hp
    exact swapInversionMap_mem_inversionFinset_refl τ hij hpos hp
  · intro p hp q hq hpq
    have hp_inv :
        invertedPair (Equiv.refl (Candidate n))
          (swapCandidatePositions τ i j) p := by
      simpa [inversionFinset] using hp
    have hq_inv :
        invertedPair (Equiv.refl (Candidate n))
          (swapCandidatePositions τ i j) q := by
      simpa [inversionFinset] using hq
    have hp_order : p.1 < p.2 := by
      simpa [invertedPair, rankOf] using hp_inv.1
    have hq_order : q.1 < q.2 := by
      simpa [invertedPair, rankOf] using hq_inv.1
    have hp_left :
        swapInversionMapInv i j (swapInversionMap i j p) = p :=
      swapInversionMapInv_left hij hp_order
    have hq_left :
        swapInversionMapInv i j (swapInversionMap i j q) = q :=
      swapInversionMapInv_left hij hq_order
    rw [← hp_left, ← hq_left, hpq]

/--
Swapping a center-ordered inverted pair in an identity-center ranking strictly
lowers Kendall tau.
-/
theorem kendallTau_refl_swapCandidatePositions_lt
    {n : ℕ} (τ : Ranking n) {i j : Candidate n}
    (hij : i < j) (hpos : rankOf τ j < rankOf τ i) :
    kendallTau (Equiv.refl (Candidate n)) (swapCandidatePositions τ i j) <
      kendallTau (Equiv.refl (Candidate n)) τ := by
  classical
  let s : Finset (Candidate n × Candidate n) :=
    inversionFinset (Equiv.refl (Candidate n))
      (swapCandidatePositions τ i j)
  let t : Finset (Candidate n × Candidate n) :=
    inversionFinset (Equiv.refl (Candidate n)) τ
  let f : Candidate n × Candidate n → Candidate n × Candidate n :=
    swapInversionMap i j
  have hmaps : ∀ p ∈ s, f p ∈ t := by
    intro p hp
    exact swapInversionMap_mem_inversionFinset_refl τ hij hpos hp
  have hinj : Set.InjOn f s := by
    intro p hp q hq hpq
    have hp_inv :
        invertedPair (Equiv.refl (Candidate n))
          (swapCandidatePositions τ i j) p := by
      simpa [s, inversionFinset] using hp
    have hq_inv :
        invertedPair (Equiv.refl (Candidate n))
          (swapCandidatePositions τ i j) q := by
      simpa [s, inversionFinset] using hq
    have hp_order : p.1 < p.2 := by
      simpa [invertedPair, rankOf] using hp_inv.1
    have hq_order : q.1 < q.2 := by
      simpa [invertedPair, rankOf] using hq_inv.1
    have hp_left :
        swapInversionMapInv i j (swapInversionMap i j p) = p :=
      swapInversionMapInv_left hij hp_order
    have hq_left :
        swapInversionMapInv i j (swapInversionMap i j q) = q :=
      swapInversionMapInv_left hij hq_order
    dsimp [f] at hpq
    rw [← hp_left, ← hq_left, hpq]
  let im : Finset (Candidate n × Candidate n) := s.image f
  have him_subset : im ⊆ t := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨a, ha, rfl⟩
    exact hmaps a ha
  have hpair_mem : (i, j) ∈ t := by
    have hinv : invertedPair (Equiv.refl (Candidate n)) τ (i, j) :=
      ⟨by simpa [rankOf] using hij, hpos⟩
    simpa [t, inversionFinset] using hinv
  have hpair_not_mem_image : (i, j) ∉ im := by
    intro him
    rcases Finset.mem_image.mp him with ⟨p, hp, hpmap⟩
    have hp_inv :
        invertedPair (Equiv.refl (Candidate n))
          (swapCandidatePositions τ i j) p := by
      simpa [s, inversionFinset] using hp
    have hp_order : p.1 < p.2 := by
      simpa [invertedPair, rankOf] using hp_inv.1
    have hp_left :
        swapInversionMapInv i j (swapInversionMap i j p) = p :=
      swapInversionMapInv_left hij hp_order
    have hp_eq : p = (i, j) := by
      dsimp [f] at hpmap
      rw [hpmap] at hp_left
      simpa [swapInversionMapInv, hij.ne', (ne_of_lt hij).symm] using
        hp_left.symm
    have hinv_pair :
        invertedPair (Equiv.refl (Candidate n))
          (swapCandidatePositions τ i j) (i, j) := by
      simpa [hp_eq] using hp_inv
    have hbad : rankOf τ i < rankOf τ j := by
      simpa using hinv_pair.2
    exact (not_lt_of_gt hpos) hbad
  have him_ssub : im ⊂ t := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨him_subset, ?_⟩
    intro heq
    exact hpair_not_mem_image (by
      rw [heq]
      exact hpair_mem)
  have hcard_image : im.card = s.card := by
    simpa [im, f] using (Finset.card_image_of_injOn hinj)
  have hcard_lt : im.card < t.card := Finset.card_lt_card him_ssub
  unfold kendallTau
  simpa [s, t] using hcard_image.symm.trans_lt hcard_lt

/--
Swapping a center-ordered inverted pair weakly lowers Kendall tau for an
arbitrary center ranking.
-/
theorem kendallTau_swapCandidatePositions_le
    {n : ℕ} (ρ π : Ranking n) {c d : Candidate n}
    (hcenter : rankOf ρ c < rankOf ρ d)
    (hpos : rankOf π d < rankOf π c) :
    kendallTau ρ (swapCandidatePositions π c d) ≤ kendallTau ρ π := by
  classical
  let τ : Ranking n := π.trans ρ.symm
  let i : Candidate n := rankOf ρ c
  let j : Candidate n := rankOf ρ d
  have hij : i < j := by simpa [i, j] using hcenter
  have hc : ρ i = c := by simp [i, rankOf]
  have hd : ρ j = d := by simp [j, rankOf]
  have hposτ : rankOf τ j < rankOf τ i := by
    simpa [τ, i, j, hc, hd, rankOf] using hpos
  have hπ : τ.trans ρ = π := by
    ext x
    simp [τ]
  have hswap :
      swapCandidatePositions π c d =
        (swapCandidatePositions τ i j).trans ρ := by
    ext x
    simp [swapCandidatePositions, τ, i, j, rankOf]
  calc
    kendallTau ρ (swapCandidatePositions π c d)
        = kendallTau ρ ((swapCandidatePositions τ i j).trans ρ) := by
          rw [hswap]
    _ = kendallTau (Equiv.refl (Candidate n))
          (swapCandidatePositions τ i j) := by
          rw [kendallTau_center_trans]
    _ ≤ kendallTau (Equiv.refl (Candidate n)) τ :=
          kendallTau_refl_swapCandidatePositions_le τ hij hposτ
    _ = kendallTau ρ (τ.trans ρ) := by
          rw [kendallTau_center_trans]
    _ = kendallTau ρ π := by
          rw [hπ]

/--
The Mallows weight cross-ratio for the ranking obtained by correcting one
center-ordered inverted pair.
-/
theorem mallowsWeight_swapCandidatePositions_cross_nonneg
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (ρ π : Ranking n) {c d : Candidate n}
    (hcenter : rankOf ρ c < rankOf ρ d)
    (hpos : rankOf π d < rankOf π c) :
    0 ≤
      mallowsWeight qMore ρ (swapCandidatePositions π c d) *
          mallowsWeight qLess ρ π -
        mallowsWeight qMore ρ π *
          mallowsWeight qLess ρ (swapCandidatePositions π c d) := by
  unfold mallowsWeight
  have hle :
      kendallTau ρ (swapCandidatePositions π c d) ≤ kendallTau ρ π :=
    kendallTau_swapCandidatePositions_le ρ π hcenter hpos
  have h :=
    natPower_cross_nonneg_of_le
      (q₁ := qMore) (q₂ := qLess) hqMore_pos hq_lt hle
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

theorem rankOf_swapCandidatePositions_adjacent_lt_iff
    {n : ℕ} (π : Ranking n) (k : Fin (n + 1))
    (hcenter :
      rankOf (Equiv.refl (Candidate n)) (π k.succ) <
        rankOf (Equiv.refl (Candidate n)) (π k.castSucc))
    {x y : Candidate n} (hxy : x < y)
    (hnot : (x, y) ≠ (π k.succ, π k.castSucc)) :
    rankOf
        (swapCandidatePositions π (π k.succ) (π k.castSucc)) y <
          rankOf
            (swapCandidatePositions π (π k.succ) (π k.castSucc)) x ↔
      rankOf π y < rankOf π x := by
  classical
  let a : Candidate n := π k.succ
  let b : Candidate n := π k.castSucc
  have ha_rank : rankOf π a = k.succ := by
    simp [a, rankOf]
  have hb_rank : rankOf π b = k.castSucc := by
    simp [b, rankOf]
  have hab : a < b := by
    simpa [a, b, rankOf] using hcenter
  have hpair_not : (x, y) ≠ (a, b) := by
    simpa [a, b] using hnot
  by_cases hxa : x = a
  · subst x
    have hy_ne_a : y ≠ a := ne_of_gt hxy
    have hy_ne_b : y ≠ b := by
      intro hyb
      exact hpair_not (by ext <;> simp [hyb])
    have hyrank_ne_b : rankOf π y ≠ k.castSucc := by
      intro hy_rank
      exact hy_ne_b (eq_of_rankOf_eq π (by rw [hy_rank, hb_rank]))
    rw [rankOf_swapCandidatePositions_of_ne π hy_ne_a hy_ne_b,
      rankOf_swapCandidatePositions_left, ha_rank, hb_rank]
    exact
      (rank_lt_adjacent_succ_iff_lt_castSucc_of_ne_castSucc
        k hyrank_ne_b).symm
  · by_cases hya : y = a
    · subst y
      have hx_ne_a : x ≠ a := hxa
      have hx_ne_b : x ≠ b := by
        intro hxb
        subst x
        exact (not_lt_of_gt hab) hxy
      have hxrank_ne_a : rankOf π x ≠ k.succ := by
        intro hx_rank
        exact hx_ne_a (eq_of_rankOf_eq π (by rw [hx_rank, ha_rank]))
      rw [rankOf_swapCandidatePositions_left,
        rankOf_swapCandidatePositions_of_ne π hx_ne_a hx_ne_b,
        ha_rank, hb_rank]
      exact adjacent_castSucc_lt_rank_iff_succ_lt_of_ne_succ
        k hxrank_ne_a
    · by_cases hxb : x = b
      · subst x
        have hy_ne_a : y ≠ a := hya
        have hy_ne_b : y ≠ b := ne_of_gt hxy
        have hyrank_ne_b : rankOf π y ≠ k.castSucc := by
          intro hy_rank
          exact hy_ne_b (eq_of_rankOf_eq π (by rw [hy_rank, hb_rank]))
        rw [rankOf_swapCandidatePositions_of_ne π hy_ne_a hy_ne_b,
          rankOf_swapCandidatePositions_right, ha_rank, hb_rank]
        exact
          (rank_lt_adjacent_succ_iff_lt_castSucc_of_ne_castSucc
            k hyrank_ne_b)
      · by_cases hyb : y = b
        · subst y
          have hx_ne_a : x ≠ a := by
            intro hxa'
            subst x
            exact hpair_not rfl
          have hx_ne_b : x ≠ b := hxb
          have hxrank_ne_a : rankOf π x ≠ k.succ := by
            intro hx_rank
            exact hx_ne_a (eq_of_rankOf_eq π (by rw [hx_rank, ha_rank]))
          rw [rankOf_swapCandidatePositions_right,
            rankOf_swapCandidatePositions_of_ne π hx_ne_a hx_ne_b,
            ha_rank, hb_rank]
          exact
            (adjacent_castSucc_lt_rank_iff_succ_lt_of_ne_succ
              k hxrank_ne_a).symm
        · rw [rankOf_swapCandidatePositions_of_ne π hya hyb,
            rankOf_swapCandidatePositions_of_ne π hxa hxb]

theorem invertedPair_refl_swapCandidatePositions_adjacent_iff
    {n : ℕ} (π : Ranking n) (k : Fin (n + 1))
    (hcenter :
      rankOf (Equiv.refl (Candidate n)) (π k.succ) <
        rankOf (Equiv.refl (Candidate n)) (π k.castSucc))
    (ab : Candidate n × Candidate n) :
    invertedPair (Equiv.refl (Candidate n))
        (swapCandidatePositions π (π k.succ) (π k.castSucc)) ab ↔
      invertedPair (Equiv.refl (Candidate n)) π ab ∧
        ab ≠ (π k.succ, π k.castSucc) := by
  classical
  rcases ab with ⟨x, y⟩
  let a : Candidate n := π k.succ
  let b : Candidate n := π k.castSucc
  have hab : a < b := by
    simpa [a, b, rankOf] using hcenter
  constructor
  · intro hinv
    have hxy : x < y := by
      simpa [invertedPair, rankOf] using hinv.1
    have hnot : (x, y) ≠ (a, b) := by
      intro hpair
      have hpair' : (x, y) = (π k.succ, π k.castSucc) := by
        simpa [a, b] using hpair
      have hx_pair : x = π k.succ := (Prod.ext_iff.mp hpair').1
      have hy_pair : y = π k.castSucc := (Prod.ext_iff.mp hpair').2
      have hrank_bad :
          k.succ < k.castSucc := by
        have htmp :
            rankOf
                (swapCandidatePositions π (π k.succ) (π k.castSucc))
                (π k.castSucc) <
              rankOf
                (swapCandidatePositions π (π k.succ) (π k.castSucc))
                (π k.succ) := by
          simpa [hx_pair, hy_pair] using hinv.2
        rw [rankOf_swapCandidatePositions_right,
          rankOf_swapCandidatePositions_left] at htmp
        simpa [rankOf] using htmp
      exact (not_lt_of_gt k.castSucc_lt_succ) hrank_bad
    have hrank :=
      (rankOf_swapCandidatePositions_adjacent_lt_iff
        π k hcenter hxy (by simpa [a, b] using hnot)).mp hinv.2
    exact ⟨⟨by simpa [rankOf] using hxy, hrank⟩, by
      simpa [a, b] using hnot⟩
  · intro h
    rcases h with ⟨hinv, hnot⟩
    have hxy : x < y := by
      simpa [invertedPair, rankOf] using hinv.1
    have hrank :=
      (rankOf_swapCandidatePositions_adjacent_lt_iff
        π k hcenter hxy hnot).mpr hinv.2
    exact ⟨by simpa [rankOf] using hxy, hrank⟩

theorem inversionFinset_refl_swapCandidatePositions_adjacent
    {n : ℕ} (π : Ranking n) (k : Fin (n + 1))
    (hcenter :
      rankOf (Equiv.refl (Candidate n)) (π k.succ) <
        rankOf (Equiv.refl (Candidate n)) (π k.castSucc)) :
    inversionFinset (Equiv.refl (Candidate n))
        (swapCandidatePositions π (π k.succ) (π k.castSucc)) =
      (inversionFinset (Equiv.refl (Candidate n)) π).erase
        (π k.succ, π k.castSucc) := by
  classical
  ext ab
  simp [inversionFinset,
    invertedPair_refl_swapCandidatePositions_adjacent_iff π k hcenter ab,
    and_comm]

theorem kendallTau_refl_swapCandidatePositions_adjacent_add_one
    {n : ℕ} (π : Ranking n) (k : Fin (n + 1))
    (hcenter :
      rankOf (Equiv.refl (Candidate n)) (π k.succ) <
        rankOf (Equiv.refl (Candidate n)) (π k.castSucc)) :
    kendallTau (Equiv.refl (Candidate n)) π =
      kendallTau (Equiv.refl (Candidate n))
        (swapCandidatePositions π (π k.succ) (π k.castSucc)) + 1 := by
  classical
  let a : Candidate n := π k.succ
  let b : Candidate n := π k.castSucc
  have hpair_mem :
      (a, b) ∈ inversionFinset (Equiv.refl (Candidate n)) π := by
    have hinv : invertedPair (Equiv.refl (Candidate n)) π (a, b) := by
      constructor
      · simpa [a, b, rankOf] using hcenter
      · simp [a, b, rankOf]
    simpa [inversionFinset] using hinv
  have hset :=
    inversionFinset_refl_swapCandidatePositions_adjacent π k hcenter
  unfold kendallTau
  rw [hset]
  simpa [a, b] using (Finset.card_erase_add_one hpair_mem).symm

theorem AdjacentCorrection.kendallTau_le
    {n : ℕ} {π σ : Ranking n}
    (hstep : AdjacentCorrection (Equiv.refl (Candidate n)) π σ) :
    kendallTau (Equiv.refl (Candidate n)) σ ≤
      kendallTau (Equiv.refl (Candidate n)) π := by
  rcases hstep with ⟨k, hcenter, rfl⟩
  refine
    kendallTau_swapCandidatePositions_le
      (Equiv.refl (Candidate n)) π hcenter ?_
  simpa [rankOf] using k.castSucc_lt_succ

theorem AdjacentCorrection.kendallTau_lt
    {n : ℕ} {π σ : Ranking n}
    (hstep : AdjacentCorrection (Equiv.refl (Candidate n)) π σ) :
    kendallTau (Equiv.refl (Candidate n)) σ <
      kendallTau (Equiv.refl (Candidate n)) π := by
  rcases hstep with ⟨k, hcenter, rfl⟩
  refine kendallTau_refl_swapCandidatePositions_lt π ?_ ?_
  · simpa [rankOf] using hcenter
  · simpa [rankOf] using k.castSucc_lt_succ

theorem AdjacentCorrection.kendallTau_eq_add_one
    {n : ℕ} {π σ : Ranking n}
    (hstep : AdjacentCorrection (Equiv.refl (Candidate n)) π σ) :
    kendallTau (Equiv.refl (Candidate n)) π =
      kendallTau (Equiv.refl (Candidate n)) σ + 1 := by
  rcases hstep with ⟨k, hcenter, rfl⟩
  exact kendallTau_refl_swapCandidatePositions_adjacent_add_one π k hcenter

theorem ranking_eq_refl_of_no_adjacent_inversions
    {n : ℕ} {π : Ranking n}
    (hno :
      ∀ k : Fin (n + 1),
        ¬ rankOf (Equiv.refl (Candidate n)) (π k.succ) <
          rankOf (Equiv.refl (Candidate n)) (π k.castSucc)) :
    π = Equiv.refl (Candidate n) := by
  classical
  have hmono : StrictMono π := by
    rw [Fin.strictMono_iff_lt_succ]
    intro k
    have hle : π k.castSucc ≤ π k.succ :=
      le_of_not_gt (by simpa [rankOf] using hno k)
    have hne : π k.castSucc ≠ π k.succ := by
      intro hsame
      exact (ne_of_lt k.castSucc_lt_succ) (π.injective hsame)
    exact lt_of_le_of_ne hle hne
  let e : Candidate n ≃o Candidate n := {
    toEquiv := π
    map_rel_iff' := by
      intro i j
      exact hmono.le_iff_le }
  ext i
  simpa [e] using Fin.coe_orderIso_apply e i

theorem exists_adjacentCorrection_of_ne_refl
    {n : ℕ} {π : Ranking n}
    (hne : π ≠ Equiv.refl (Candidate n)) :
    ∃ σ : Ranking n,
      AdjacentCorrection (Equiv.refl (Candidate n)) π σ := by
  classical
  by_contra hnone
  have hno :
      ∀ k : Fin (n + 1),
        ¬ rankOf (Equiv.refl (Candidate n)) (π k.succ) <
          rankOf (Equiv.refl (Candidate n)) (π k.castSucc) := by
    intro k hcenter
    exact hnone
      ⟨swapCandidatePositions π (π k.succ) (π k.castSucc),
        ⟨k, hcenter, rfl⟩⟩
  exact hne (ranking_eq_refl_of_no_adjacent_inversions hno)

theorem exists_adjacentCorrection_of_kendallTau_pos
    {n : ℕ} {π : Ranking n}
    (hpos : 0 < kendallTau (Equiv.refl (Candidate n)) π) :
    ∃ σ : Ranking n,
      AdjacentCorrection (Equiv.refl (Candidate n)) π σ := by
  refine exists_adjacentCorrection_of_ne_refl ?_
  intro hπ
  rw [hπ, kendallTau_self] at hpos
  exact (Nat.lt_irrefl 0) hpos

theorem weakBruhatLe_refl_of_refl_center
    {n : ℕ} (π : Ranking n) :
    WeakBruhatLe (Equiv.refl (Candidate n)) π
      (Equiv.refl (Candidate n)) := by
  classical
  let P : ℕ → Prop := fun m =>
    ∀ τ : Ranking n,
      kendallTau (Equiv.refl (Candidate n)) τ = m →
        WeakBruhatLe (Equiv.refl (Candidate n)) τ
          (Equiv.refl (Candidate n))
  have hP : ∀ m, P m := by
    intro m
    exact Nat.strong_induction_on (p := P) m (by
      intro m ih τ hτ
      by_cases hτ_refl : τ = Equiv.refl (Candidate n)
      · subst τ
        exact Relation.ReflTransGen.refl
      · rcases exists_adjacentCorrection_of_ne_refl hτ_refl with ⟨σ, hstep⟩
        have hlt :
            kendallTau (Equiv.refl (Candidate n)) σ < m := by
          rw [← hτ]
          exact hstep.kendallTau_lt
        exact Relation.ReflTransGen.head hstep
          (ih (kendallTau (Equiv.refl (Candidate n)) σ) hlt σ rfl))
  exact hP (kendallTau (Equiv.refl (Candidate n)) π) π rfl

theorem exists_ranking_kendallTau_eq_of_le
    {n : ℕ} (π : Ranking n) {m : ℕ}
    (hm : m ≤ kendallTau (Equiv.refl (Candidate n)) π) :
    ∃ σ : Ranking n,
      kendallTau (Equiv.refl (Candidate n)) σ = m := by
  classical
  let P : ℕ → Prop := fun K =>
    ∀ τ : Ranking n,
      kendallTau (Equiv.refl (Candidate n)) τ = K →
        m ≤ K →
          ∃ σ : Ranking n,
            kendallTau (Equiv.refl (Candidate n)) σ = m
  have hP : ∀ K, P K := by
    intro K
    exact Nat.strong_induction_on (p := P) K (by
      intro K ih τ hτ hmK
      by_cases hmk : m = K
      · exact ⟨τ, by simpa [hmk] using hτ⟩
      · have hm_lt : m < K := lt_of_le_of_ne hmK hmk
        have hτ_pos :
            0 < kendallTau (Equiv.refl (Candidate n)) τ := by
          rw [hτ]
          omega
        rcases exists_adjacentCorrection_of_kendallTau_pos hτ_pos with
          ⟨σ, hstep⟩
        have hσ_lt :
            kendallTau (Equiv.refl (Candidate n)) σ < K := by
          rw [← hτ]
          exact hstep.kendallTau_lt
        have hmσ :
            m ≤ kendallTau (Equiv.refl (Candidate n)) σ := by
          have hdrop := hstep.kendallTau_eq_add_one
          rw [hτ] at hdrop
          omega
        exact
          ih (kendallTau (Equiv.refl (Candidate n)) σ)
            hσ_lt σ rfl hmσ)
  exact hP (kendallTau (Equiv.refl (Candidate n)) π) π rfl hm

theorem WeakBruhatLe.kendallTau_le
    {n : ℕ} {π σ : Ranking n}
    (hpath : WeakBruhatLe (Equiv.refl (Candidate n)) π σ) :
    kendallTau (Equiv.refl (Candidate n)) σ ≤
      kendallTau (Equiv.refl (Candidate n)) π := by
  induction hpath using Relation.ReflTransGen.trans_induction_on with
  | refl => exact le_rfl
  | single hstep => exact hstep.kendallTau_le
  | trans _ _ hleft hright => exact le_trans hright hleft

theorem WeakBruhatLe.kendallTau_lt_of_ne
    {n : ℕ} {π σ : Ranking n}
    (hpath : WeakBruhatLe (Equiv.refl (Candidate n)) π σ)
    (hne : π ≠ σ) :
    kendallTau (Equiv.refl (Candidate n)) σ <
      kendallTau (Equiv.refl (Candidate n)) π := by
  rcases Relation.ReflTransGen.cases_head hpath with hπσ | hhead
  · exact False.elim (hne hπσ)
  · rcases hhead with ⟨τ, hstep, htail⟩
    exact lt_of_le_of_lt
      (WeakBruhatLe.kendallTau_le (π := τ) (σ := σ) htail)
      hstep.kendallTau_lt

/-- Unnormalised identity-center Mallows payoff sum. -/
noncomputable def reflMallowsPayoffSum (n : ℕ) (q : ℝ)
    (F : Ranking n → ℝ) : ℝ :=
  ∑ τ : Ranking n,
    q ^ kendallTau (Equiv.refl (Candidate n)) τ * F τ

theorem reflMallowsPayoffSum_prefixSplit_raw
    (n : ℕ) (k : Candidate (n + 1)) (q : ℝ)
    (H : Ranking (n + 1) → ℝ) :
    reflMallowsPayoffSum (n + 1) q H =
      ∑ x : PrefixSplitTriple n k,
        q ^ kendallTau (Equiv.refl (Candidate (n + 1)))
          (prefixSplitRankingEquiv n k x) *
          H (prefixSplitRankingEquiv n k x) := by
  classical
  unfold reflMallowsPayoffSum
  simpa using
    (Equiv.sum_comp (prefixSplitRankingEquiv n k)
      (fun τ : Ranking (n + 1) =>
        q ^ kendallTau (Equiv.refl (Candidate (n + 1))) τ * H τ)).symm

theorem reflMallowsPayoffSum_prefixSplit_triple
    (n : ℕ) (k : Candidate (n + 1)) (q : ℝ)
    (H : Ranking (n + 1) → ℝ) :
    reflMallowsPayoffSum (n + 1) q H =
      ∑ x : PrefixSplitTriple n k,
        prefixSplitInternalWeight n k q x.lo x.hi *
          binaryHeightInterleavingWeight
            (k.val + 1) (n + 2 - k.val) q x.h *
            H (prefixSplitRankingEquiv n k x) := by
  classical
  rw [reflMallowsPayoffSum_prefixSplit_raw]
  refine Finset.sum_congr rfl ?_
  intro x _
  cases x with
  | mk lo hi h hh =>
      change
        q ^ kendallTau (Equiv.refl (Candidate (n + 1)))
              (binaryHeightMergeRanking n k lo hi h hh) *
            H (binaryHeightMergeRanking n k lo hi h hh) =
          prefixSplitInternalWeight n k q lo hi *
            binaryHeightInterleavingWeight (k.val + 1) (n + 2 - k.val) q h *
              H (binaryHeightMergeRanking n k lo hi h hh)
      rw [kendallTau_refl_binaryHeightMergeRanking]
      simp [prefixSplitInternalWeight,
        binaryHeightInterleavingWeight, hh, binaryHeightProductWeight,
        binaryHeightSum, pow_add]

theorem reflMallowsPayoffSum_prefixSplit
    (n : ℕ) (k : Candidate (n + 1)) (q : ℝ)
    (H : Ranking (n + 1) → ℝ) :
    reflMallowsPayoffSum (n + 1) q H =
      ∑ lo : Equiv.Perm (Fin (k.val + 1)),
        ∑ hi : Equiv.Perm (Fin (n + 2 - k.val)),
          prefixSplitInternalWeight n k q lo hi *
            ∑ h, binaryHeightInterleavingWeight
                (k.val + 1) (n + 2 - k.val) q h *
              H (binaryHeightMergeRankingTotal n k lo hi h) := by
  classical
  calc
    reflMallowsPayoffSum (n + 1) q H =
        ∑ x : PrefixSplitTriple n k,
          prefixSplitInternalWeight n k q x.lo x.hi *
            binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q x.h *
              H (prefixSplitRankingEquiv n k x) := by
      exact reflMallowsPayoffSum_prefixSplit_triple n k q H
    _ = ∑ lo : Equiv.Perm (Fin (k.val + 1)),
        ∑ hi : Equiv.Perm (Fin (n + 2 - k.val)),
          prefixSplitInternalWeight n k q lo hi *
            ∑ h, binaryHeightInterleavingWeight
                (k.val + 1) (n + 2 - k.val) q h *
              H (binaryHeightMergeRankingTotal n k lo hi h) := by
      let Φ : PrefixSplitTriple n k → ℝ := fun x =>
        prefixSplitInternalWeight n k q x.lo x.hi *
          binaryHeightInterleavingWeight (k.val + 1) (n + 2 - k.val) q x.h *
            H (prefixSplitRankingEquiv n k x)
      have hprod :
          (∑ x : PrefixSplitTriple n k, Φ x) =
            ∑ p :
              Equiv.Perm (Fin (k.val + 1)) ×
                Equiv.Perm (Fin (n + 2 - k.val)) ×
                  {h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1) //
                    binaryHeightMonotone h},
              Φ ((prefixSplitTripleEquivProd n k).symm p) := by
        simpa using
          (Equiv.sum_comp (prefixSplitTripleEquivProd n k).symm Φ).symm
      rw [show
          (∑ x : PrefixSplitTriple n k,
            prefixSplitInternalWeight n k q x.lo x.hi *
              binaryHeightInterleavingWeight
                (k.val + 1) (n + 2 - k.val) q x.h *
                H (prefixSplitRankingEquiv n k x)) =
            ∑ x : PrefixSplitTriple n k, Φ x by rfl]
      rw [hprod]
      rw [Fintype.sum_prod_type]
      simp only [Φ, prefixSplitTripleEquivProd]
      refine Finset.sum_congr rfl ?_
      intro lo _
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl ?_
      intro hi _
      simp [prefixSplitRankingEquiv]
      rw [show
          (∑ x : {h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1) //
              binaryHeightMonotone h},
            prefixSplitInternalWeight n k q lo hi *
                binaryHeightInterleavingWeight (k.val + 1) (n + 2 - k.val) q x.1 *
              H (binaryHeightMergeRanking n k lo hi x.1 x.2)) =
            ∑ x : {h : Fin (k.val + 1) → Fin (n + 2 - k.val + 1) //
              binaryHeightMonotone h},
              prefixSplitInternalWeight n k q lo hi *
                (binaryHeightInterleavingWeight (k.val + 1) (n + 2 - k.val) q x.1 *
                  H (binaryHeightMergeRanking n k lo hi x.1 x.2)) by
        refine Finset.sum_congr rfl ?_
        intro x _
        ring]
      rw [← Finset.mul_sum]
      congr 1
      symm
      rw [binaryHeightInterleavingWeight_sum_eq_subtypeFinset]
      refine Finset.sum_congr ?hset ?hterm
      · ext h
        simp [binaryHeightMonotoneFinset]
      · intro hs _
        have htotal :
            binaryHeightMergeRankingTotal n k lo hi hs.1 =
              binaryHeightMergeRanking n k lo hi hs.1 hs.2 := by
          exact binaryHeightMergeRankingTotal_of_monotone n k lo hi hs.2
        simp [binaryHeightInterleavingWeight, hs.2, binaryHeightProductWeight,
          htotal]

theorem reflMallowsPayoffSum_prefixSplit_pair
    (n : ℕ) (k : Candidate (n + 1)) (q : ℝ)
    (H : Ranking (n + 1) → ℝ) :
    reflMallowsPayoffSum (n + 1) q H =
      ∑ a : Equiv.Perm (Fin (k.val + 1)) ×
          Equiv.Perm (Fin (n + 2 - k.val)),
        prefixSplitInternalWeight n k q a.1 a.2 *
          ∑ h, binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q h *
            H (binaryHeightMergeRankingTotal n k a.1 a.2 h) := by
  calc
    reflMallowsPayoffSum (n + 1) q H =
        ∑ lo : Equiv.Perm (Fin (k.val + 1)),
          ∑ hi : Equiv.Perm (Fin (n + 2 - k.val)),
            prefixSplitInternalWeight n k q lo hi *
              ∑ h, binaryHeightInterleavingWeight
                  (k.val + 1) (n + 2 - k.val) q h *
                H (binaryHeightMergeRankingTotal n k lo hi h) := by
      exact reflMallowsPayoffSum_prefixSplit n k q H
    _ = ∑ a : Equiv.Perm (Fin (k.val + 1)) ×
          Equiv.Perm (Fin (n + 2 - k.val)),
        prefixSplitInternalWeight n k q a.1 a.2 *
          ∑ h, binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q h *
            H (binaryHeightMergeRankingTotal n k a.1 a.2 h) := by
      exact (Fintype.sum_prod_type
        (fun a : Equiv.Perm (Fin (k.val + 1)) ×
          Equiv.Perm (Fin (n + 2 - k.val)) =>
            prefixSplitInternalWeight n k q a.1 a.2 *
              ∑ h, binaryHeightInterleavingWeight
                  (k.val + 1) (n + 2 - k.val) q h *
                H (binaryHeightMergeRankingTotal n k a.1 a.2 h))).symm

theorem reflMallowsPayoffSum_const
    (n : ℕ) (q a : ℝ) :
    reflMallowsPayoffSum n q (fun _ : Ranking n => a) =
      mallowsPartition q (Equiv.refl (Candidate n)) * a := by
  classical
  unfold reflMallowsPayoffSum mallowsPartition mallowsWeight
  rw [Finset.sum_mul]

theorem mallowsPartition_refl_prefixSplit_pair
    (n : ℕ) (k : Candidate (n + 1)) (q : ℝ) :
    mallowsPartition q (Equiv.refl (Candidate (n + 1))) =
      ∑ a : Equiv.Perm (Fin (k.val + 1)) ×
          Equiv.Perm (Fin (n + 2 - k.val)),
        prefixSplitInternalWeight n k q a.1 a.2 *
          ∑ h, binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q h := by
  have hconst := reflMallowsPayoffSum_const (n + 1) q 1
  calc
    mallowsPartition q (Equiv.refl (Candidate (n + 1))) =
        reflMallowsPayoffSum (n + 1) q
          (fun _ : Ranking (n + 1) => (1 : ℝ)) := by
      simpa using hconst.symm
    _ = ∑ a : Equiv.Perm (Fin (k.val + 1)) ×
          Equiv.Perm (Fin (n + 2 - k.val)),
        prefixSplitInternalWeight n k q a.1 a.2 *
          ∑ h, binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q h := by
      rw [reflMallowsPayoffSum_prefixSplit_pair]
      refine Finset.sum_congr rfl ?_
      intro a _
      congr 1
      simp

theorem mallowsPartition_refl_prefixSplit_product
    (n : ℕ) (k : Candidate (n + 1)) (q : ℝ) :
    mallowsPartition q (Equiv.refl (Candidate (n + 1))) =
      (∑ a : Equiv.Perm (Fin (k.val + 1)) ×
          Equiv.Perm (Fin (n + 2 - k.val)),
        prefixSplitInternalWeight n k q a.1 a.2) *
          ∑ h, binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q h := by
  calc
    mallowsPartition q (Equiv.refl (Candidate (n + 1))) =
      ∑ a : Equiv.Perm (Fin (k.val + 1)) ×
          Equiv.Perm (Fin (n + 2 - k.val)),
        prefixSplitInternalWeight n k q a.1 a.2 *
          ∑ h, binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q h := by
      exact mallowsPartition_refl_prefixSplit_pair n k q
    _ = (∑ a : Equiv.Perm (Fin (k.val + 1)) ×
          Equiv.Perm (Fin (n + 2 - k.val)),
        prefixSplitInternalWeight n k q a.1 a.2) *
          ∑ h, binaryHeightInterleavingWeight
              (k.val + 1) (n + 2 - k.val) q h := by
      rw [Finset.sum_mul]

theorem reflMallowsPayoffSum_mul_const
    (n : ℕ) (q c : ℝ) (F : Ranking n → ℝ) :
    reflMallowsPayoffSum n q (fun τ => F τ * c) =
      reflMallowsPayoffSum n q F * c := by
  classical
  unfold reflMallowsPayoffSum
  calc
    (∑ τ : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate n)) τ * (F τ * c))
        =
      ∑ τ : Ranking n,
        (q ^ kendallTau (Equiv.refl (Candidate n)) τ * F τ) * c := by
        refine Finset.sum_congr rfl ?_
        intro τ _
        ring
    _ =
      (∑ τ : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate n)) τ * F τ) * c := by
        rw [Finset.sum_mul]

theorem reflMallowsPayoffSum_add
    (n : ℕ) (q : ℝ) (F G : Ranking n → ℝ) :
    reflMallowsPayoffSum n q (fun τ => F τ + G τ) =
      reflMallowsPayoffSum n q F + reflMallowsPayoffSum n q G := by
  classical
  unfold reflMallowsPayoffSum
  calc
    (∑ τ : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate n)) τ * (F τ + G τ))
        =
      ∑ τ : Ranking n,
        (q ^ kendallTau (Equiv.refl (Candidate n)) τ * F τ +
          q ^ kendallTau (Equiv.refl (Candidate n)) τ * G τ) := by
        refine Finset.sum_congr rfl ?_
        intro τ _
        ring
    _ =
      (∑ τ : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate n)) τ * F τ) +
        ∑ τ : Ranking n,
          q ^ kendallTau (Equiv.refl (Candidate n)) τ * G τ := by
        rw [Finset.sum_add_distrib]

theorem reflMallowsPayoffSum_finset_sum
    {α : Type*} (s : Finset α)
    (n : ℕ) (q : ℝ) (F : α → Ranking n → ℝ) :
    reflMallowsPayoffSum n q (fun τ => ∑ a ∈ s, F a τ) =
      ∑ a ∈ s, reflMallowsPayoffSum n q (F a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [reflMallowsPayoffSum_const]
  | insert a s has ih =>
      simp [has, reflMallowsPayoffSum_add, ih]

/-- Unnormalised covariance under identity-center Mallows weights. -/
noncomputable def reflMallowsCovariance
    (n : ℕ) (q : ℝ) (F G : Ranking n → ℝ) : ℝ :=
  reflMallowsPayoffSum n q (fun τ => F τ * G τ) *
      mallowsPartition q (Equiv.refl (Candidate n)) -
    reflMallowsPayoffSum n q F * reflMallowsPayoffSum n q G

theorem reflMallowsCovariance_pos_of_subset_not_total
    (n : ℕ) (q : ℝ) (F G : Ranking n → ℝ)
    (hFG : ∀ τ, F τ * G τ = G τ)
    (hGpos : 0 < reflMallowsPayoffSum n q G)
    (hF_lt :
      reflMallowsPayoffSum n q F <
        mallowsPartition q (Equiv.refl (Candidate n))) :
    0 < reflMallowsCovariance n q F G := by
  classical
  unfold reflMallowsCovariance
  have hFGsum :
      reflMallowsPayoffSum n q (fun τ => F τ * G τ) =
        reflMallowsPayoffSum n q G := by
    unfold reflMallowsPayoffSum
    refine Finset.sum_congr rfl ?_
    intro τ _
    change
      q ^ kendallTau (Equiv.refl (Candidate n)) τ * (F τ * G τ) =
        q ^ kendallTau (Equiv.refl (Candidate n)) τ * G τ
    rw [hFG τ]
  rw [hFGsum]
  have hfactor :
      reflMallowsPayoffSum n q G *
          mallowsPartition q (Equiv.refl (Candidate n)) -
        reflMallowsPayoffSum n q F * reflMallowsPayoffSum n q G =
      reflMallowsPayoffSum n q G *
        (mallowsPartition q (Equiv.refl (Candidate n)) -
          reflMallowsPayoffSum n q F) := by
    ring
  rw [hfactor]
  exact mul_pos hGpos (sub_pos.mpr hF_lt)

theorem reflMallowsCovariance_const_right
    (n : ℕ) (q c : ℝ) (F : Ranking n → ℝ) :
    reflMallowsCovariance n q F (fun _ => c) = 0 := by
  unfold reflMallowsCovariance
  rw [reflMallowsPayoffSum_mul_const, reflMallowsPayoffSum_const]
  ring

theorem reflMallowsCovariance_add_right
    (n : ℕ) (q : ℝ) (F G H : Ranking n → ℝ) :
    reflMallowsCovariance n q F (fun τ => G τ + H τ) =
      reflMallowsCovariance n q F G +
        reflMallowsCovariance n q F H := by
  unfold reflMallowsCovariance
  rw [reflMallowsPayoffSum_add]
  have hmul :
      reflMallowsPayoffSum n q (fun τ => F τ * (G τ + H τ)) =
        reflMallowsPayoffSum n q (fun τ => F τ * G τ) +
          reflMallowsPayoffSum n q (fun τ => F τ * H τ) := by
    simpa [mul_add] using
      reflMallowsPayoffSum_add n q
        (fun τ : Ranking n => F τ * G τ)
        (fun τ : Ranking n => F τ * H τ)
  rw [hmul]
  ring

theorem reflMallowsCovariance_mul_const_right
    (n : ℕ) (q c : ℝ) (F G : Ranking n → ℝ) :
    reflMallowsCovariance n q F (fun τ => c * G τ) =
      c * reflMallowsCovariance n q F G := by
  unfold reflMallowsCovariance
  have hmul :
      reflMallowsPayoffSum n q (fun τ => F τ * (c * G τ)) =
        c * reflMallowsPayoffSum n q (fun τ => F τ * G τ) := by
    calc
      reflMallowsPayoffSum n q (fun τ => F τ * (c * G τ))
          = reflMallowsPayoffSum n q (fun τ => (F τ * G τ) * c) := by
              congr
              ext τ
              ring
      _ = reflMallowsPayoffSum n q (fun τ => F τ * G τ) * c := by
              rw [reflMallowsPayoffSum_mul_const]
      _ = c * reflMallowsPayoffSum n q (fun τ => F τ * G τ) := by ring
  have hG :
      reflMallowsPayoffSum n q (fun τ => c * G τ) =
        c * reflMallowsPayoffSum n q G := by
    calc
      reflMallowsPayoffSum n q (fun τ => c * G τ)
          = reflMallowsPayoffSum n q (fun τ => G τ * c) := by
              congr
              ext τ
              ring
      _ = reflMallowsPayoffSum n q G * c := by
              rw [reflMallowsPayoffSum_mul_const]
      _ = c * reflMallowsPayoffSum n q G := by ring
  rw [hmul, hG]
  ring

theorem reflMallowsCovariance_finset_sum_right
    {α : Type*} (s : Finset α)
    (n : ℕ) (q : ℝ) (F : Ranking n → ℝ)
    (G : α → Ranking n → ℝ) :
    reflMallowsCovariance n q F (fun τ => ∑ a ∈ s, G a τ) =
      ∑ a ∈ s, reflMallowsCovariance n q F (G a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [reflMallowsCovariance_const_right]
  | insert a s has ih =>
      simp [has, reflMallowsCovariance_add_right, ih]

/-- Normalized identity-center Mallows expectation as a quotient of the
unnormalized payoff sum. -/
theorem pmfExp_mallowsPMF_refl_eq_reflMallowsPayoffSum_div
    (n : ℕ) {q : ℝ} (hq : 0 < q) (F : Ranking n → ℝ) :
    pmfExp (mallowsPMF q (Equiv.refl (Candidate n)) hq) F =
      reflMallowsPayoffSum n q F /
        mallowsPartition q (Equiv.refl (Candidate n)) := by
  classical
  unfold pmfExp reflMallowsPayoffSum
  calc
    (∑ π : Ranking n,
        ((mallowsPMF q (Equiv.refl (Candidate n)) hq) π).toReal * F π)
        =
      ∑ π : Ranking n,
        (q ^ kendallTau (Equiv.refl (Candidate n)) π /
            mallowsPartition q (Equiv.refl (Candidate n))) * F π := by
        refine Finset.sum_congr rfl ?_
        intro π _
        rw [mallowsPMF_apply_toReal]
        rfl
    _ =
      (∑ π : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate n)) π * F π) /
          mallowsPartition q (Equiv.refl (Candidate n)) := by
        calc
          (∑ π : Ranking n,
            (q ^ kendallTau (Equiv.refl (Candidate n)) π /
                mallowsPartition q (Equiv.refl (Candidate n))) * F π)
              =
            ∑ π : Ranking n,
              (q ^ kendallTau (Equiv.refl (Candidate n)) π * F π) /
                mallowsPartition q (Equiv.refl (Candidate n)) := by
              refine Finset.sum_congr (M := ℝ) rfl ?_
              intro π _
              ring
          _ =
            (∑ π : Ranking n,
              q ^ kendallTau (Equiv.refl (Candidate n)) π * F π) /
                mallowsPartition q (Equiv.refl (Candidate n)) := by
              rw [Finset.sum_div]

/--
First-order dominance of the normalized identity-center Mallows PMFs along the
weak Bruhat order.  This is a standard-order-theoretic version of the open
arbitrary-size stochastic dominance target.
-/
def ReflMallowsWeakBruhatFirstOrderLe
    (n : ℕ) (qMore qLess : ℝ)
    (hqMore : 0 < qMore) (hqLess : 0 < qLess) : Prop :=
  ∀ F : Ranking n → ℝ,
    (∀ π σ : Ranking n,
      WeakBruhatLe (Equiv.refl (Candidate n)) π σ → F π ≤ F σ) →
      pmfExp (mallowsPMF qLess (Equiv.refl (Candidate n)) hqLess) F ≤
        pmfExp (mallowsPMF qMore (Equiv.refl (Candidate n)) hqMore) F

/-- Left-coordinate expectation under a coupling of two rankings. -/
noncomputable def rankingPairLeftExp {n : ℕ}
    (γ : PMF (Ranking n × Ranking n)) (F : Ranking n → ℝ) : ℝ := ∑ z : Ranking n × Ranking n, (γ z).toReal * F z.1

/-- Right-coordinate expectation under a coupling of two rankings. -/
noncomputable def rankingPairRightExp {n : ℕ}
    (γ : PMF (Ranking n × Ranking n)) (F : Ranking n → ℝ) : ℝ := ∑ z : Ranking n × Ranking n, (γ z).toReal * F z.2

/--
Monotone-coupling certificate for the open arbitrary-size identity-center
Mallows dominance step.

The left marginal is the less accurate law and the right marginal is the more
accurate law.  The support condition says every coupled pair moves upward in
the weak Bruhat order generated by adjacent inversion corrections.
-/
structure ReflMallowsWeakBruhatCoupling
    (n : ℕ) (qMore qLess : ℝ)
    (hqMore : 0 < qMore) (hqLess : 0 < qLess) where
  joint : PMF (Ranking n × Ranking n)
  left_expectation : ∀ F : Ranking n → ℝ,
    pmfExp (mallowsPMF qLess (Equiv.refl (Candidate n)) hqLess) F =
      rankingPairLeftExp joint F
  right_expectation : ∀ F : Ranking n → ℝ,
    pmfExp (mallowsPMF qMore (Equiv.refl (Candidate n)) hqMore) F =
      rankingPairRightExp joint F
  ordered_support : ∀ z : Ranking n × Ranking n,
    0 < (joint z).toReal →
      WeakBruhatLe (Equiv.refl (Candidate n)) z.1 z.2

theorem ReflMallowsWeakBruhatCoupling.firstOrderLe
    {n : ℕ} {qMore qLess : ℝ}
    {hqMore : 0 < qMore} {hqLess : 0 < qLess}
    (C : ReflMallowsWeakBruhatCoupling n qMore qLess hqMore hqLess) :
    ReflMallowsWeakBruhatFirstOrderLe n qMore qLess hqMore hqLess := by
  intro F hmono
  rw [C.left_expectation F, C.right_expectation F]
  unfold rankingPairLeftExp rankingPairRightExp
  refine Finset.sum_le_sum ?_
  intro z _
  by_cases hzero : (C.joint z).toReal = 0
  · simp [hzero]
  · have hnonneg : 0 ≤ (C.joint z).toReal := ENNReal.toReal_nonneg
    have hpos : 0 < (C.joint z).toReal := by
      rcases lt_or_eq_of_le hnonneg with hpos | heq
      · exact hpos
      · exact False.elim (hzero heq.symm)
    exact mul_le_mul_of_nonneg_left
      (hmono z.1 z.2 (C.ordered_support z hpos)) hnonneg

/--
One-step insertion decomposition for identity-center Mallows payoff sums.
Peeling the best center candidate factors the Kendall exponent into its
insertion position plus the tail Kendall exponent.
-/
theorem reflMallowsPayoffSum_peelBest
    (n : ℕ) (q : ℝ) (F : Ranking (n + 1) → ℝ) :
    reflMallowsPayoffSum (n + 1) q F =
      ∑ p : Candidate (n + 1),
        q ^ (p : ℕ) *
          reflMallowsPayoffSum n q
            (fun σ : Ranking n =>
              F (rankingPeelBestOrderEquiv n (p, σ))) := by
  classical
  let e := rankingPeelBestOrderEquiv n
  unfold reflMallowsPayoffSum
  calc
    (∑ τ : Ranking (n + 1),
        q ^ kendallTau (Equiv.refl (Candidate (n + 1))) τ * F τ)
        =
      ∑ pe : Candidate (n + 1) × Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e pe) *
          F (e pe) := by
        simpa [e] using
          (Equiv.sum_comp e
            (fun τ : Ranking (n + 1) =>
              q ^ kendallTau (Equiv.refl (Candidate (n + 1))) τ *
                F τ)).symm
    _ =
      ∑ p : Candidate (n + 1), ∑ σ : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e (p, σ)) *
          F (e (p, σ)) := by
        simpa using
          (Finset.sum_product'
            (Finset.univ : Finset (Candidate (n + 1)))
            (Finset.univ : Finset (Ranking n))
            (fun p σ =>
              q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e (p, σ)) *
                F (e (p, σ))))
    _ =
      ∑ p : Candidate (n + 1), ∑ σ : Ranking n,
        q ^ (p : ℕ) *
          (q ^ kendallTau (Equiv.refl (Candidate n)) σ *
            F (e (p, σ))) := by
        refine Finset.sum_congr rfl ?_
        intro p _
        refine Finset.sum_congr rfl ?_
        intro σ _
        have hkend :
            kendallTau (Equiv.refl (Candidate (n + 1))) (e (p, σ)) =
              (p : ℕ) + kendallTau (Equiv.refl (Candidate n)) σ := by
          simpa [e] using kendallTau_rankingPeelBestOrderEquiv n p σ
        rw [hkend, pow_add]
        ring
    _ =
      ∑ p : Candidate (n + 1),
        q ^ (p : ℕ) *
          (∑ σ : Ranking n,
            q ^ kendallTau (Equiv.refl (Candidate n)) σ *
              F (e (p, σ))) := by
        refine Finset.sum_congr rfl ?_
        intro p _
        rw [Finset.mul_sum]

@[simp] theorem firstChoice_rankingPeelBestOrderEquiv_zero
    (n : ℕ) (σ : Ranking n) :
    firstChoice
        (rankingPeelBestOrderEquiv n ((0 : Candidate (n + 1)), σ)) =
      (0 : Candidate (n + 1)) := by
  have h :
      rankOf (rankingPeelBestOrderEquiv n ((0 : Candidate (n + 1)), σ))
          (0 : Candidate (n + 1)) =
        (0 : Candidate (n + 1)) := by
    simp
  exact ((rankOf_eq_zero_iff_eq_firstChoice
    (rankingPeelBestOrderEquiv n ((0 : Candidate (n + 1)), σ))
    (0 : Candidate (n + 1))).mp h).symm

@[simp] theorem rankingPeelBestOrderEquiv_zero_apply_zero
    (n : ℕ) (σ : Ranking n) :
    rankingPeelBestOrderEquiv n ((0 : Candidate (n + 1)), σ)
        (0 : Candidate (n + 1)) =
      (0 : Candidate (n + 1)) := by
  simpa [firstChoice] using firstChoice_rankingPeelBestOrderEquiv_zero n σ

/--
Decompose a ranking by its first-choice center rank and the order of the tail
after cycling that first choice to center rank `0` and peeling it off.
-/
noncomputable def rankingFirstChoiceOrderEquiv (n : ℕ) :
    Candidate (n + 1) × Ranking n ≃ Ranking (n + 1) :=
  Equiv.ofBijective
    (fun pe : Candidate (n + 1) × Ranking n =>
      (rankingPeelBestOrderEquiv n ((0 : Candidate (n + 1)), pe.2)).trans
        (Fin.cycleRange pe.1).symm)
    (by
      classical
      constructor
      · intro pe₁ pe₂ h
        rcases pe₁ with ⟨r₁, σ₁⟩
        rcases pe₂ with ⟨r₂, σ₂⟩
        have hfirst := congrArg firstChoice h
        have hr : r₁ = r₂ := by
          simpa using hfirst
        subst r₂
        have hcycle :
            (rankingPeelBestOrderEquiv n ((0 : Candidate (n + 1)), σ₁)) =
              rankingPeelBestOrderEquiv n ((0 : Candidate (n + 1)), σ₂) := by
          apply Equiv.ext
          intro x
          have hx := Equiv.ext_iff.mp h x
          exact (Fin.cycleRange r₁).symm.injective hx
        have hpe :
            ((0 : Candidate (n + 1)), σ₁) =
              ((0 : Candidate (n + 1)), σ₂) :=
          (rankingPeelBestOrderEquiv n).injective hcycle
        have hσ : σ₁ = σ₂ := (Prod.ext_iff.mp hpe).2
        subst σ₂
        rfl
      · intro τ
        let r : Candidate (n + 1) := firstChoice τ
        let β : Ranking (n + 1) := τ.trans (Fin.cycleRange r)
        let pe := (rankingPeelBestOrderEquiv n).symm β
        have hfirstβ : firstChoice β = (0 : Candidate (n + 1)) := by
          simp [β, r]
        have hp : pe.1 = (0 : Candidate (n + 1)) := by
          have hrankβ :
              rankOf β (0 : Candidate (n + 1)) =
                (0 : Candidate (n + 1)) :=
            (rankOf_eq_zero_iff_eq_firstChoice β
              (0 : Candidate (n + 1))).mpr hfirstβ.symm
          have hpe_apply :
              rankingPeelBestOrderEquiv n pe = β := by
            simpa [pe] using
              ((rankingPeelBestOrderEquiv n).apply_symm_apply β)
          have hpe_rank := congrArg
            (fun π : Ranking (n + 1) =>
              rankOf π (0 : Candidate (n + 1))) hpe_apply
          rcases pe with ⟨p, σ⟩
          simpa [hrankβ] using hpe_rank
        refine ⟨(r, pe.2), ?_⟩
        have hβ :
            rankingPeelBestOrderEquiv n
                ((0 : Candidate (n + 1)), pe.2) = β := by
          have hpair :
              ((0 : Candidate (n + 1)), pe.2) = pe := by
            apply Prod.ext
            · exact hp.symm
            · rfl
          rw [hpair]
          simpa [pe] using
            ((rankingPeelBestOrderEquiv n).apply_symm_apply β)
        change
          (rankingPeelBestOrderEquiv n
              ((0 : Candidate (n + 1)), pe.2)).trans
              (Fin.cycleRange r).symm = τ
        rw [hβ]
        ext x
        simp [β, r])

@[simp] theorem firstChoice_rankingFirstChoiceOrderEquiv
    (n : ℕ) (r : Candidate (n + 1)) (σ : Ranking n) :
    firstChoice (rankingFirstChoiceOrderEquiv n (r, σ)) = r := by
  classical
  change
    firstChoice
        ((rankingPeelBestOrderEquiv n ((0 : Candidate (n + 1)), σ)).trans
          (Fin.cycleRange r).symm) = r
  simp [firstChoice]

theorem kendallTau_rankingFirstChoiceOrderEquiv
    (n : ℕ) (r : Candidate (n + 1)) (σ : Ranking n) :
    kendallTau (Equiv.refl (Candidate (n + 1)))
        (rankingFirstChoiceOrderEquiv n (r, σ)) =
      (r : ℕ) + kendallTau (Equiv.refl (Candidate n)) σ := by
  classical
  let τ : Ranking (n + 1) := rankingFirstChoiceOrderEquiv n (r, σ)
  have hfirst : firstChoice τ = r := by
    simpa [τ] using firstChoice_rankingFirstChoiceOrderEquiv n r σ
  have hcycle_r :
      τ.trans (Fin.cycleRange r) =
        rankingPeelBestOrderEquiv n ((0 : Candidate (n + 1)), σ) := by
    have hτ :
        τ =
          (rankingPeelBestOrderEquiv n ((0 : Candidate (n + 1)), σ)).trans
            (Fin.cycleRange r).symm := by
      rfl
    rw [hτ]
    ext x
    simp
  calc
    kendallTau (Equiv.refl (Candidate (n + 1))) τ =
        (firstChoice τ : ℕ) +
          kendallTau (Equiv.refl (Candidate (n + 1)))
            (τ.trans (Fin.cycleRange (firstChoice τ))) :=
          kendallTau_eq_firstChoice_add_cycleRange τ
    _ = (r : ℕ) + kendallTau (Equiv.refl (Candidate n)) σ := by
          rw [hfirst, hcycle_r]
          simpa using
            kendallTau_rankingPeelBestOrderEquiv
              n (0 : Candidate (n + 1)) σ

/-- First-choice decomposition for identity-center Mallows payoff sums. -/
theorem reflMallowsPayoffSum_firstChoice
    (n : ℕ) (q : ℝ) (F : Ranking (n + 1) → ℝ) :
    reflMallowsPayoffSum (n + 1) q F =
      ∑ r : Candidate (n + 1),
        q ^ (r : ℕ) *
          reflMallowsPayoffSum n q
            (fun σ : Ranking n =>
              F (rankingFirstChoiceOrderEquiv n (r, σ))) := by
  classical
  let e := rankingFirstChoiceOrderEquiv n
  unfold reflMallowsPayoffSum
  calc
    (∑ τ : Ranking (n + 1),
        q ^ kendallTau (Equiv.refl (Candidate (n + 1))) τ * F τ)
        =
      ∑ pe : Candidate (n + 1) × Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e pe) *
          F (e pe) := by
        simpa [e] using
          (Equiv.sum_comp e
            (fun τ : Ranking (n + 1) =>
              q ^ kendallTau (Equiv.refl (Candidate (n + 1))) τ *
                F τ)).symm
    _ =
      ∑ r : Candidate (n + 1), ∑ σ : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e (r, σ)) *
          F (e (r, σ)) := by
        simpa using
          (Finset.sum_product'
            (Finset.univ : Finset (Candidate (n + 1)))
            (Finset.univ : Finset (Ranking n))
            (fun r σ =>
              q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e (r, σ)) *
                F (e (r, σ))))
    _ =
      ∑ r : Candidate (n + 1), ∑ σ : Ranking n,
        q ^ (r : ℕ) *
          (q ^ kendallTau (Equiv.refl (Candidate n)) σ *
            F (e (r, σ))) := by
        refine Finset.sum_congr rfl ?_
        intro r _
        refine Finset.sum_congr rfl ?_
        intro σ _
        have hkend :
            kendallTau (Equiv.refl (Candidate (n + 1))) (e (r, σ)) =
              (r : ℕ) + kendallTau (Equiv.refl (Candidate n)) σ := by
          simpa [e] using kendallTau_rankingFirstChoiceOrderEquiv n r σ
        rw [hkend, pow_add]
        ring
    _ =
      ∑ r : Candidate (n + 1),
        q ^ (r : ℕ) *
          (∑ σ : Ranking n,
            q ^ kendallTau (Equiv.refl (Candidate n)) σ *
              F (e (r, σ))) := by
        refine Finset.sum_congr rfl ?_
        intro r _
        rw [Finset.mul_sum]

/-- Tail candidates whose first-choice-deleted image remains available. -/
noncomputable def firstChoiceTailRemainingOf {n : ℕ}
    (r : Candidate (n + 1))
    (remaining : Finset (Candidate (n + 1))) : Finset (Candidate n) := by
  classical
  exact Finset.univ.filter (fun c : Candidate n => r.succAbove c ∈ remaining)

@[simp] theorem mem_firstChoiceTailRemainingOf {n : ℕ}
    {r : Candidate (n + 1)}
    {remaining : Finset (Candidate (n + 1))} {c : Candidate n} :
    c ∈ firstChoiceTailRemainingOf r remaining ↔ r.succAbove c ∈ remaining := by
  classical
  simp [firstChoiceTailRemainingOf]

theorem firstChoiceTailRemainingOf_nonempty_of_nonempty_of_first_not_mem
    {n : ℕ} {r : Candidate (n + 1)}
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (hr : r ∉ remaining) :
    (firstChoiceTailRemainingOf r remaining).Nonempty := by
  classical
  rcases hremaining with ⟨e, he⟩
  have her : e ≠ r := by
    intro h
    exact hr (by simpa [h] using he)
  rcases Fin.exists_succAbove_eq her with ⟨c, hc⟩
  exact ⟨c, by simpa [hc] using he⟩

theorem firstChoiceTailRemainingOf_castSucc_eq_succ_of_not_mem
    {n : ℕ} {remaining : Finset (Candidate (n + 1))}
    (k : Candidate n)
    (hcast : k.castSucc ∉ remaining) (hsucc : k.succ ∉ remaining) :
    firstChoiceTailRemainingOf k.castSucc remaining =
      firstChoiceTailRemainingOf k.succ remaining := by
  classical
  ext c
  by_cases hc : c = k
  · subst c
    have hleft : k.castSucc.succAbove k = k.succ :=
      Fin.succAbove_castSucc_self k
    have hright : k.succ.succAbove k = k.castSucc := by
      simpa using Fin.succAbove_pred_self k.succ (Fin.succ_ne_zero k)
    simp [firstChoiceTailRemainingOf, hleft, hright, hcast, hsucc]
  · have hsucc_ne_zero : k.succ ≠ (0 : Candidate (n + 1)) :=
      Fin.succ_ne_zero k
    have hsame :
        k.succ.succAbove c = k.castSucc.succAbove c := by
      by_cases hlt : c < k
      · have hsucc_above :
            k.succ.succAbove c = c.castSucc :=
          Fin.succAbove_succ_of_le k c (le_of_lt hlt)
        have hcast_above :
            k.castSucc.succAbove c = c.castSucc :=
          Fin.succAbove_castSucc_of_lt k c hlt
        rw [hsucc_above, hcast_above]
      · have hkc : k < c :=
          lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hc)
        have hsucc_above :
            k.succ.succAbove c = c.succ :=
          Fin.succAbove_succ_of_lt k c hkc
        have hcast_above :
            k.castSucc.succAbove c = c.succ :=
          Fin.succAbove_castSucc_of_le k c (le_of_lt hkc)
        rw [hsucc_above, hcast_above]
    simp [firstChoiceTailRemainingOf, hsame]

theorem rankOf_rankingFirstChoiceOrderEquiv_succAbove
    (n : ℕ) (r : Candidate (n + 1)) (σ : Ranking n)
    (c : Candidate n) :
    rankOf (rankingFirstChoiceOrderEquiv n (r, σ)) (r.succAbove c) =
      (rankOf σ c).succ := by
  classical
  let τ : Ranking (n + 1) := rankingFirstChoiceOrderEquiv n (r, σ)
  have hτ :
      τ =
        (rankingPeelBestOrderEquiv n ((0 : Candidate (n + 1)), σ)).trans
          (Fin.cycleRange r).symm := by
    rfl
  have hcycle :
      τ.trans (Fin.cycleRange r) =
        rankingPeelBestOrderEquiv n ((0 : Candidate (n + 1)), σ) := by
    rw [hτ]
    ext x
    simp
  have hrank := congrArg
    (fun π : Ranking (n + 1) =>
      rankOf π (Fin.cycleRange r (r.succAbove c))) hcycle
  simpa [τ, rankOf] using hrank

theorem rankOf_rankingFirstChoiceOrderEquiv_succAbove_lt_iff
    (n : ℕ) (r : Candidate (n + 1)) (σ : Ranking n)
    (c d : Candidate n) :
    rankOf (rankingFirstChoiceOrderEquiv n (r, σ)) (r.succAbove c) <
        rankOf (rankingFirstChoiceOrderEquiv n (r, σ)) (r.succAbove d) ↔
      rankOf σ c < rankOf σ d := by
  rw [rankOf_rankingFirstChoiceOrderEquiv_succAbove,
    rankOf_rankingFirstChoiceOrderEquiv_succAbove]
  exact Fin.succ_lt_succ_iff

/--
Fixing the first choice, swapping two tail candidates commutes with the
first-choice decomposition.
-/
theorem swapCandidatePositions_rankingFirstChoiceOrderEquiv_succAbove
    (n : ℕ) (r : Candidate (n + 1)) (σ : Ranking n)
    (c d : Candidate n) :
    swapCandidatePositions
        (rankingFirstChoiceOrderEquiv n (r, σ))
        (r.succAbove c) (r.succAbove d) =
      rankingFirstChoiceOrderEquiv n
        (r, swapCandidatePositions σ c d) := by
  classical
  apply ranking_ext_of_rankOf
  intro e
  by_cases her : e = r
  · subst e
    have hr_ne_c : r ≠ r.succAbove c := Fin.ne_succAbove r c
    have hr_ne_d : r ≠ r.succAbove d := Fin.ne_succAbove r d
    rw [rankOf_swapCandidatePositions_of_ne
      (rankingFirstChoiceOrderEquiv n (r, σ)) hr_ne_c hr_ne_d]
    have hleft :
        rankOf (rankingFirstChoiceOrderEquiv n (r, σ)) r = 0 :=
      (rankOf_eq_zero_iff_eq_firstChoice
        (rankingFirstChoiceOrderEquiv n (r, σ)) r).mpr
          (firstChoice_rankingFirstChoiceOrderEquiv n r σ).symm
    have hright :
        rankOf
            (rankingFirstChoiceOrderEquiv n
              (r, swapCandidatePositions σ c d)) r = 0 :=
      (rankOf_eq_zero_iff_eq_firstChoice
        (rankingFirstChoiceOrderEquiv n
          (r, swapCandidatePositions σ c d)) r).mpr
          (firstChoice_rankingFirstChoiceOrderEquiv n r
            (swapCandidatePositions σ c d)).symm
    rw [hleft, hright]
  · rcases Fin.exists_succAbove_eq her with ⟨a, ha⟩
    subst e
    by_cases hac : a = c
    · subst a
      rw [rankOf_swapCandidatePositions_left]
      rw [rankOf_rankingFirstChoiceOrderEquiv_succAbove,
        rankOf_rankingFirstChoiceOrderEquiv_succAbove,
        rankOf_swapCandidatePositions_left]
    · by_cases had : a = d
      · subst a
        rw [rankOf_swapCandidatePositions_right]
        rw [rankOf_rankingFirstChoiceOrderEquiv_succAbove,
          rankOf_rankingFirstChoiceOrderEquiv_succAbove,
          rankOf_swapCandidatePositions_right]
      · have ha_ne_c : r.succAbove a ≠ r.succAbove c := by
          intro h
          exact hac (r.succAbove_right_injective h)
        have ha_ne_d : r.succAbove a ≠ r.succAbove d := by
          intro h
          exact had (r.succAbove_right_injective h)
        rw [rankOf_swapCandidatePositions_of_ne
          (rankingFirstChoiceOrderEquiv n (r, σ)) ha_ne_c ha_ne_d]
        rw [rankOf_rankingFirstChoiceOrderEquiv_succAbove,
          rankOf_rankingFirstChoiceOrderEquiv_succAbove,
          rankOf_swapCandidatePositions_of_ne σ hac had]

theorem adjacentSwapImproves_firstChoice_tail
    {n : ℕ} {F : Ranking (n + 1) → ℝ}
    (hF : AdjacentSwapImproves (Equiv.refl (Candidate (n + 1))) F)
    (r : Candidate (n + 1)) :
    AdjacentSwapImproves (Equiv.refl (Candidate n))
      (fun σ : Ranking n => F (rankingFirstChoiceOrderEquiv n (r, σ))) := by
  classical
  intro σ k hcenter
  let τ : Ranking (n + 1) := rankingFirstChoiceOrderEquiv n (r, σ)
  let j : Fin (n + 2) := k.succ
  have hj_succ :
      τ j.succ = r.succAbove (σ k.succ) := by
    dsimp [τ, j]
    exact apply_eq_of_rankOf
      (rankingFirstChoiceOrderEquiv n (r, σ))
      (by
        rw [rankOf_rankingFirstChoiceOrderEquiv_succAbove]
        simp [rankOf])
  have hj_cast :
      τ j.castSucc = r.succAbove (σ k.castSucc) := by
    dsimp [τ, j]
    exact apply_eq_of_rankOf
      (rankingFirstChoiceOrderEquiv n (r, σ))
      (by
        rw [rankOf_rankingFirstChoiceOrderEquiv_succAbove]
        simp [rankOf])
  have hcenter_full :
      rankOf (Equiv.refl (Candidate (n + 1))) (τ j.succ) <
        rankOf (Equiv.refl (Candidate (n + 1))) (τ j.castSucc) := by
    rw [hj_succ, hj_cast]
    change r.succAbove (σ k.succ) < r.succAbove (σ k.castSucc)
    exact (Fin.succAbove_lt_succAbove_iff).mpr
      (by simpa [rankOf] using hcenter)
  have hstep := hF τ j hcenter_full
  rw [hj_succ, hj_cast] at hstep
  have hswap :
      swapCandidatePositions τ
          (r.succAbove (σ k.succ)) (r.succAbove (σ k.castSucc)) =
        rankingFirstChoiceOrderEquiv n
          (r, swapCandidatePositions σ (σ k.succ) (σ k.castSucc)) := by
    simpa [τ] using
      swapCandidatePositions_rankingFirstChoiceOrderEquiv_succAbove
        n r σ (σ k.succ) (σ k.castSucc)
  rw [hswap] at hstep
  simpa [τ] using hstep

@[simp] theorem rankOf_rankingFirstChoiceOrderEquiv_first
    (n : ℕ) (r : Candidate (n + 1)) (σ : Ranking n) :
    rankOf (rankingFirstChoiceOrderEquiv n (r, σ)) r = 0 :=
   (rankOf_eq_zero_iff_eq_firstChoice
    (rankingFirstChoiceOrderEquiv n (r, σ)) r).mpr
      (firstChoice_rankingFirstChoiceOrderEquiv n r σ).symm

/--
If the first-choice branch candidate remains available, it is the best
remaining candidate throughout that branch.
-/
theorem bestInSet_rankingFirstChoiceOrderEquiv_of_first_mem
    {n : ℕ} (r : Candidate (n + 1)) (σ : Ranking n)
    {remaining : Finset (Candidate (n + 1))}
    (hr : r ∈ remaining) :
    bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining = r := by
  classical
  refine bestInSet_eq_of_forall_rank_le
    (rankingFirstChoiceOrderEquiv n (r, σ)) remaining hr ?_
  intro e _he
  rw [rankOf_rankingFirstChoiceOrderEquiv_first]
  exact Fin.zero_le _

/--
If the first-choice branch candidate is not remaining, deleting it turns
`bestInSet` into the corresponding tail `bestInSet`.
-/
theorem bestInSet_rankingFirstChoiceOrderEquiv_of_first_not_mem
    {n : ℕ} (r : Candidate (n + 1)) (σ : Ranking n)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (hr : r ∉ remaining) :
    bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining =
      r.succAbove
        (bestInSet σ (firstChoiceTailRemainingOf r remaining)) := by
  classical
  have htail :
      (firstChoiceTailRemainingOf r remaining).Nonempty :=
    firstChoiceTailRemainingOf_nonempty_of_nonempty_of_first_not_mem
      hremaining hr
  refine bestInSet_eq_of_forall_rank_le
    (rankingFirstChoiceOrderEquiv n (r, σ)) remaining
    (c := r.succAbove
      (bestInSet σ (firstChoiceTailRemainingOf r remaining))) ?_ ?_
  · simpa using bestInSet_mem σ htail
  · intro e he
    have her : e ≠ r := by
      intro h
      exact hr (by simpa [h] using he)
    rcases Fin.exists_succAbove_eq her with ⟨a, ha⟩
    have ha_mem : a ∈ firstChoiceTailRemainingOf r remaining := by
      simpa [ha] using he
    rw [← ha]
    rw [rankOf_rankingFirstChoiceOrderEquiv_succAbove,
      rankOf_rankingFirstChoiceOrderEquiv_succAbove]
    exact Fin.succ_le_succ_iff.mpr
      (rankOf_bestInSet_le σ htail ha_mem)

theorem reflMallowsPayoffSum_firstChoice_branch_eq_of_first_mem
    {n : ℕ} (q : ℝ) (value : Candidate (n + 1) → ℝ)
    {remaining : Finset (Candidate (n + 1))}
    {r : Candidate (n + 1)} (hr : r ∈ remaining) :
    reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          value (bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining)) =
      reflMallowsPayoffSum n q (fun _ : Ranking n => value r) := by
  classical
  unfold reflMallowsPayoffSum
  refine Finset.sum_congr rfl ?_
  intro σ _
  change
    q ^ kendallTau (Equiv.refl (Candidate n)) σ *
        value (bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining) =
      q ^ kendallTau (Equiv.refl (Candidate n)) σ * value r
  rw [bestInSet_rankingFirstChoiceOrderEquiv_of_first_mem r σ hr]

theorem reflMallowsPayoffSum_firstChoice_branch_eq_of_first_not_mem
    {n : ℕ} (q : ℝ) (value : Candidate (n + 1) → ℝ)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {r : Candidate (n + 1)}
    (hr : r ∉ remaining) :
    reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          value (bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining)) =
      reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          value
            (r.succAbove
              (bestInSet σ (firstChoiceTailRemainingOf r remaining)))) := by
  classical
  unfold reflMallowsPayoffSum
  refine Finset.sum_congr rfl ?_
  intro σ _
  change
    q ^ kendallTau (Equiv.refl (Candidate n)) σ *
        value (bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining) =
      q ^ kendallTau (Equiv.refl (Candidate n)) σ *
        value
          (r.succAbove
            (bestInSet σ (firstChoiceTailRemainingOf r remaining)))
  rw [bestInSet_rankingFirstChoiceOrderEquiv_of_first_not_mem
    r σ hremaining hr]

/-- Identity-center unnormalised Mallows mass of the best-in-set fiber. -/
noncomputable def reflMallowsBestInSetWeight
    (n : ℕ) (q : ℝ) (remaining : Finset (Candidate n))
    (c : Candidate n) : ℝ :=
  reflMallowsPayoffSum n q
    (fun π : Ranking n =>
      if c = bestInSet π remaining then (1 : ℝ) else 0)

/-- Identity-center best-in-set fiber weights are nonnegative for `q >= 0`. -/
theorem reflMallowsBestInSetWeight_nonneg
    (n : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (remaining : Finset (Candidate n)) (c : Candidate n) :
    0 ≤ reflMallowsBestInSetWeight n q remaining c := by
  classical
  unfold reflMallowsBestInSetWeight reflMallowsPayoffSum
  refine Finset.sum_nonneg ?_
  intro π _
  exact mul_nonneg
    (pow_nonneg hq (kendallTau (Equiv.refl (Candidate n)) π))
    (by by_cases h : c = bestInSet π remaining <;> simp [h])

/-- A candidate outside a nonempty remaining set has zero identity-center fiber mass. -/
theorem reflMallowsBestInSetWeight_eq_zero_of_not_mem
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) {c : Candidate n} (hc : c ∉ remaining) :
    reflMallowsBestInSetWeight n q remaining c = 0 := by
  classical
  unfold reflMallowsBestInSetWeight reflMallowsPayoffSum
  apply Finset.sum_eq_zero
  intro π _
  have hnot : c ≠ bestInSet π remaining := by
    intro h
    exact hc (by simpa [h] using bestInSet_mem π hremaining)
  simp [hnot]

/-- First-choice branch of a best-in-set fiber when the first choice remains. -/
theorem reflMallowsBestInSetWeight_firstChoice_branch_eq_of_first_mem
    {n : ℕ} (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    {r c : Candidate (n + 1)} (hr : r ∈ remaining) :
    reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          if c = bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining then
            (1 : ℝ)
          else
            0) =
      mallowsPartition q (Equiv.refl (Candidate n)) *
        (if c = r then (1 : ℝ) else 0) := by
  classical
  calc
    reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          if c = bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining then
            (1 : ℝ)
          else
            0)
        =
      reflMallowsPayoffSum n q
        (fun _ : Ranking n => if c = r then (1 : ℝ) else 0) := by
        unfold reflMallowsPayoffSum
        refine Finset.sum_congr rfl ?_
        intro σ _
        change
          q ^ kendallTau (Equiv.refl (Candidate n)) σ *
              (if c = bestInSet
                  (rankingFirstChoiceOrderEquiv n (r, σ)) remaining then
                (1 : ℝ)
              else
                0) =
            q ^ kendallTau (Equiv.refl (Candidate n)) σ *
              (if c = r then (1 : ℝ) else 0)
        rw [bestInSet_rankingFirstChoiceOrderEquiv_of_first_mem r σ hr]
    _ =
      mallowsPartition q (Equiv.refl (Candidate n)) *
        (if c = r then (1 : ℝ) else 0) := by
        rw [reflMallowsPayoffSum_const]

/-- First-choice branch contributes zero to the deleted first-choice fiber. -/
theorem reflMallowsBestInSetWeight_firstChoice_branch_eq_zero_of_first_not_mem_self
    {n : ℕ} (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {r : Candidate (n + 1)}
    (hr : r ∉ remaining) :
    reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          if r = bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining then
            (1 : ℝ)
          else
            0) = 0 := by
  classical
  unfold reflMallowsPayoffSum
  apply Finset.sum_eq_zero
  intro σ _
  have hbest :
      bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining =
        r.succAbove
          (bestInSet σ (firstChoiceTailRemainingOf r remaining)) :=
    bestInSet_rankingFirstChoiceOrderEquiv_of_first_not_mem
      r σ hremaining hr
  have hnot :
      r ≠ bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining := by
    rw [hbest]
    exact Fin.ne_succAbove r
      (bestInSet σ (firstChoiceTailRemainingOf r remaining))
  simp [hnot]

/-- First-choice branch of a surviving tail candidate fiber. -/
theorem reflMallowsBestInSetWeight_firstChoice_branch_eq_of_first_not_mem_succAbove
    {n : ℕ} (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {r : Candidate (n + 1)}
    (hr : r ∉ remaining) (d : Candidate n) :
    reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          if r.succAbove d =
              bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining then
            (1 : ℝ)
          else
            0) =
      reflMallowsBestInSetWeight n q
        (firstChoiceTailRemainingOf r remaining) d := by
  classical
  unfold reflMallowsBestInSetWeight reflMallowsPayoffSum
  refine Finset.sum_congr rfl ?_
  intro σ _
  have hbest :
      bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining =
        r.succAbove
          (bestInSet σ (firstChoiceTailRemainingOf r remaining)) :=
    bestInSet_rankingFirstChoiceOrderEquiv_of_first_not_mem
      r σ hremaining hr
  change
    q ^ kendallTau (Equiv.refl (Candidate n)) σ *
        (if r.succAbove d =
            bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining then
          (1 : ℝ)
        else
          0) =
      q ^ kendallTau (Equiv.refl (Candidate n)) σ *
        (if d = bestInSet σ (firstChoiceTailRemainingOf r remaining) then
          (1 : ℝ)
        else
          0)
  rw [hbest]
  by_cases h : d = bestInSet σ (firstChoiceTailRemainingOf r remaining)
  · rw [if_pos (by rw [h]), if_pos h]
  · rw [if_neg (by
      intro hsucc
      exact h (r.succAbove_right_injective hsucc)), if_neg h]

/--
First-choice recursion for identity-center best-in-set fiber weights.

If the first-choice candidate `r` remains available, the branch contributes only
to the `r` fiber.  Otherwise the full fiber is the unique `succAbove` image of a
tail fiber after deleting `r`.
-/
theorem reflMallowsBestInSetWeight_firstChoice
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (c : Candidate (n + 1)) :
    reflMallowsBestInSetWeight (n + 1) q remaining c =
      ∑ r : Candidate (n + 1),
        q ^ (r : ℕ) *
          (if r ∈ remaining then
            mallowsPartition q (Equiv.refl (Candidate n)) *
              (if c = r then (1 : ℝ) else 0)
          else
            ∑ d : Candidate n,
              if c = r.succAbove d then
                reflMallowsBestInSetWeight n q
                  (firstChoiceTailRemainingOf r remaining) d
              else
                0) := by
  classical
  unfold reflMallowsBestInSetWeight
  rw [reflMallowsPayoffSum_firstChoice n q]
  refine Finset.sum_congr rfl ?_
  intro r _
  by_cases hr : r ∈ remaining
  · rw [if_pos hr]
    have hbranch :
        reflMallowsPayoffSum n q
            (fun σ : Ranking n =>
              if c = bestInSet
                  (rankingFirstChoiceOrderEquiv n (r, σ)) remaining then
                (1 : ℝ)
              else
                0) =
          mallowsPartition q (Equiv.refl (Candidate n)) *
            (if c = r then (1 : ℝ) else 0) := by
      calc
        reflMallowsPayoffSum n q
            (fun σ : Ranking n =>
              if c = bestInSet
                  (rankingFirstChoiceOrderEquiv n (r, σ)) remaining then
                (1 : ℝ)
              else
                0)
            =
          reflMallowsPayoffSum n q
            (fun _ : Ranking n => if c = r then (1 : ℝ) else 0) := by
            unfold reflMallowsPayoffSum
            refine Finset.sum_congr rfl ?_
            intro σ _
            change
              q ^ kendallTau (Equiv.refl (Candidate n)) σ *
                  (if c = bestInSet
                      (rankingFirstChoiceOrderEquiv n (r, σ)) remaining then
                    (1 : ℝ)
                  else
                    0) =
                q ^ kendallTau (Equiv.refl (Candidate n)) σ *
                  (if c = r then (1 : ℝ) else 0)
            rw [bestInSet_rankingFirstChoiceOrderEquiv_of_first_mem r σ hr]
        _ =
          mallowsPartition q (Equiv.refl (Candidate n)) *
            (if c = r then (1 : ℝ) else 0) := by
            rw [reflMallowsPayoffSum_const]
    rw [hbranch]
  · rw [if_neg hr]
    have htail :
        (firstChoiceTailRemainingOf r remaining).Nonempty :=
      firstChoiceTailRemainingOf_nonempty_of_nonempty_of_first_not_mem
        hremaining hr
    by_cases hcr : c = r
    · subst c
      have hbranch :
          reflMallowsPayoffSum n q
              (fun σ : Ranking n =>
                if r = bestInSet
                    (rankingFirstChoiceOrderEquiv n (r, σ)) remaining then
                  (1 : ℝ)
                else
                  0) = 0 := by
        unfold reflMallowsPayoffSum
        apply Finset.sum_eq_zero
        intro σ _
        have hbest :
            bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining =
              r.succAbove
                (bestInSet σ (firstChoiceTailRemainingOf r remaining)) :=
          bestInSet_rankingFirstChoiceOrderEquiv_of_first_not_mem
            r σ hremaining hr
        have hnot :
            r ≠ bestInSet
              (rankingFirstChoiceOrderEquiv n (r, σ)) remaining := by
          rw [hbest]
          exact Fin.ne_succAbove r
            (bestInSet σ (firstChoiceTailRemainingOf r remaining))
        simp [hnot]
      have hsum :
          (∑ d : Candidate n,
              if r = r.succAbove d then
                reflMallowsBestInSetWeight n q
                  (firstChoiceTailRemainingOf r remaining) d
              else
                0) = 0 := by
        apply Finset.sum_eq_zero
        intro d _
        have hnot : r ≠ r.succAbove d := Fin.ne_succAbove r d
        simp [hnot]
      have hsum_expanded :
          (∑ d : Candidate n,
              if r = r.succAbove d then
                reflMallowsPayoffSum n q
                  (fun π : Ranking n =>
                    if d = bestInSet π (firstChoiceTailRemainingOf r remaining) then
                      (1 : ℝ)
                    else
                      0)
              else
                0) = 0 := by
        simpa [reflMallowsBestInSetWeight] using hsum
      rw [hbranch, hsum_expanded]
    · rcases Fin.exists_succAbove_eq hcr with ⟨d0, hd0⟩
      subst c
      have hbranch :
          reflMallowsPayoffSum n q
              (fun σ : Ranking n =>
                if r.succAbove d0 = bestInSet
                    (rankingFirstChoiceOrderEquiv n (r, σ)) remaining then
                  (1 : ℝ)
                else
                  0) =
            reflMallowsBestInSetWeight n q
              (firstChoiceTailRemainingOf r remaining) d0 := by
        unfold reflMallowsBestInSetWeight reflMallowsPayoffSum
        refine Finset.sum_congr rfl ?_
        intro σ _
        have hbest :
            bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining =
              r.succAbove
                (bestInSet σ (firstChoiceTailRemainingOf r remaining)) :=
          bestInSet_rankingFirstChoiceOrderEquiv_of_first_not_mem
            r σ hremaining hr
        have hiff :
            r.succAbove d0 =
                bestInSet
                  (rankingFirstChoiceOrderEquiv n (r, σ)) remaining ↔
              d0 = bestInSet σ (firstChoiceTailRemainingOf r remaining) := by
          rw [hbest]
          constructor
          · intro h
            exact r.succAbove_right_injective h
          · intro h
            rw [h]
        change
          q ^ kendallTau (Equiv.refl (Candidate n)) σ *
              (if r.succAbove d0 =
                  bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining then
                (1 : ℝ)
              else
                0) =
            q ^ kendallTau (Equiv.refl (Candidate n)) σ *
              (if d0 = bestInSet σ (firstChoiceTailRemainingOf r remaining) then
                (1 : ℝ)
              else
                0)
        rw [hbest]
        by_cases h :
            d0 = bestInSet σ (firstChoiceTailRemainingOf r remaining)
        · rw [if_pos (by rw [h]), if_pos h]
        · rw [if_neg (by
            intro hsucc
            exact h (r.succAbove_right_injective hsucc)), if_neg h]
      have hsum :
          (∑ d : Candidate n,
              if r.succAbove d0 = r.succAbove d then
                reflMallowsBestInSetWeight n q
                  (firstChoiceTailRemainingOf r remaining) d
              else
                0) =
            reflMallowsBestInSetWeight n q
              (firstChoiceTailRemainingOf r remaining) d0 := by
        have hiff :
            ∀ d : Candidate n,
              (r.succAbove d0 = r.succAbove d) ↔ d0 = d := by
          intro d
          constructor
          · intro h
            exact r.succAbove_right_injective h
          · intro h
            rw [h]
        simpa [hiff] using
          (Finset.sum_ite_eq' Finset.univ d0
            (fun d : Candidate n =>
              reflMallowsBestInSetWeight n q
                (firstChoiceTailRemainingOf r remaining) d))
      have hsum_expanded :
          (∑ d : Candidate n,
              if r.succAbove d0 = r.succAbove d then
                reflMallowsPayoffSum n q
                  (fun π : Ranking n =>
                    if d = bestInSet π (firstChoiceTailRemainingOf r remaining) then
                      (1 : ℝ)
                    else
                      0)
              else
                0) =
            reflMallowsBestInSetWeight n q
              (firstChoiceTailRemainingOf r remaining) d0 := by
        simpa [reflMallowsBestInSetWeight] using hsum
      rw [hbranch, hsum_expanded]

theorem weaklyOrderedBy_succAbove
    {n : ℕ} {value : Candidate (n + 1) → ℝ}
    (hvalue : WeaklyOrderedBy (Equiv.refl (Candidate (n + 1))) value)
    (r : Candidate (n + 1)) :
    WeaklyOrderedBy (Equiv.refl (Candidate n))
      (fun c : Candidate n => value (r.succAbove c)) := by
  intro c d hcd
  have hlt : r.succAbove c < r.succAbove d :=
    (Fin.succAbove_lt_succAbove_iff).mpr (by simpa [rankOf] using hcd)
  exact hvalue (by simpa [rankOf] using hlt)

theorem weaklyOrderedBy_castSucc
    {n : ℕ} {value : Candidate (n + 1) → ℝ}
    (hvalue : WeaklyOrderedBy (Equiv.refl (Candidate (n + 1))) value) :
    WeaklyOrderedBy (Equiv.refl (Candidate n))
      (fun c : Candidate n => value c.castSucc) := by
  intro c d hcd
  have hlt : c.castSucc < d.castSucc :=
    Fin.castSucc_lt_castSucc_iff.mpr (by simpa [rankOf] using hcd)
  exact hvalue (by simpa [rankOf] using hlt)

theorem weaklyOrderedBy_succ
    {n : ℕ} {value : Candidate (n + 1) → ℝ}
    (hvalue : WeaklyOrderedBy (Equiv.refl (Candidate (n + 1))) value) :
    WeaklyOrderedBy (Equiv.refl (Candidate n))
      (fun c : Candidate n => value c.succ) := by
  intro c d hcd
  have hlt : c.succ < d.succ := by
    change (c : ℕ) + 1 < (d : ℕ) + 1
    exact Nat.succ_lt_succ (by exact hcd)
  exact hvalue (by simpa [rankOf] using hlt)

/--
Inserting the identity-center best candidate and swapping two tail candidates
commute.  This is the recursive compatibility needed by the Mallows insertion
decomposition.
-/
theorem swapCandidatePositions_rankingPeelBestOrderEquiv_succ
    (n : ℕ) (p : Candidate (n + 1)) (σ : Ranking n)
    (c d : Candidate n) :
    swapCandidatePositions
        (rankingPeelBestOrderEquiv n (p, σ)) c.succ d.succ =
      rankingPeelBestOrderEquiv n
        (p, swapCandidatePositions σ c d) := by
  classical
  apply ranking_ext_of_rankOf
  intro e
  cases e using Fin.cases with
  | zero =>
      have h0c : (0 : Candidate (n + 1)) ≠ c.succ := by
        intro h
        exact Fin.succ_ne_zero c h.symm
      have h0d : (0 : Candidate (n + 1)) ≠ d.succ := by
        intro h
        exact Fin.succ_ne_zero d h.symm
      rw [rankOf_swapCandidatePositions_of_ne
        (rankingPeelBestOrderEquiv n (p, σ)) h0c h0d]
      simp
  | succ a =>
      by_cases hac : a = c
      · subst a
        rw [rankOf_swapCandidatePositions_left]
        rw [rankOf_rankingPeelBestOrderEquiv_succ,
          rankOf_rankingPeelBestOrderEquiv_succ,
          rankOf_swapCandidatePositions_left]
      · by_cases had : a = d
        · subst a
          rw [rankOf_swapCandidatePositions_right]
          rw [rankOf_rankingPeelBestOrderEquiv_succ,
            rankOf_rankingPeelBestOrderEquiv_succ,
            rankOf_swapCandidatePositions_right]
        · have hsucc_c : a.succ ≠ c.succ := by
            intro h
            exact hac (Fin.succ_injective _ h)
          have hsucc_d : a.succ ≠ d.succ := by
            intro h
            exact had (Fin.succ_injective _ h)
          rw [rankOf_swapCandidatePositions_of_ne
            (rankingPeelBestOrderEquiv n (p, σ)) hsucc_c hsucc_d]
          rw [rankOf_rankingPeelBestOrderEquiv_succ,
            rankOf_rankingPeelBestOrderEquiv_succ,
            rankOf_swapCandidatePositions_of_ne σ hac had]

theorem succAbove_pred_castSucc_eq_of_ne
    {n : ℕ} (k : Candidate (n + 1)) (hk : k ≠ 0)
    {i : Candidate n} (hi : i ≠ k.pred hk) :
    k.succAbove i = (k.pred hk).castSucc.succAbove i := by
  let kp : Candidate n := k.pred hk
  have hk_eq : k = kp.succ := by
    dsimp [kp]
    exact (Fin.succ_pred k hk).symm
  by_cases hlt : i < kp
  · have hi_lt_k : i.castSucc < k := by
      rw [hk_eq]
      exact Fin.castSucc_lt_succ_iff.mpr (le_of_lt hlt)
    have hi_lt_prev : i.castSucc < kp.castSucc :=
      Fin.castSucc_lt_castSucc_iff.mpr hlt
    rw [Fin.succAbove_of_castSucc_lt k i hi_lt_k,
      Fin.succAbove_of_castSucc_lt kp.castSucc i hi_lt_prev]
  · have hkp_le_i : kp ≤ i := le_of_not_gt hlt
    have hkp_lt_i : kp < i :=
      lt_of_le_of_ne hkp_le_i (Ne.symm hi)
    have hk_le_i : k ≤ i.castSucc := by
      rw [hk_eq]
      exact Fin.succ_le_castSucc_iff.mpr hkp_lt_i
    have hprev_le_i : kp.castSucc ≤ i.castSucc :=
      Fin.castSucc_le_castSucc_iff.mpr hkp_le_i
    rw [Fin.succAbove_of_le_castSucc k i hk_le_i,
      Fin.succAbove_of_le_castSucc kp.castSucc i hprev_le_i]

/--
Moving the inserted identity-center best candidate up by one adjacent position
is exactly a correction swap with the candidate immediately above it.
-/
theorem rankingPeelBestOrderEquiv_adjacent_swap
    {n : ℕ} (k : Candidate (n + 1)) (hk : k ≠ 0)
    (σ : Ranking n) :
    let prev : Candidate (n + 1) := (k.pred hk).castSucc
    let τ : Ranking (n + 1) := rankingPeelBestOrderEquiv n (k, σ)
    swapCandidatePositions τ (0 : Candidate (n + 1)) (τ prev) =
      rankingPeelBestOrderEquiv n (prev, σ) := by
  classical
  intro prev τ
  apply ranking_ext_of_rankOf
  intro e
  have hprev_ne_k : prev ≠ k := by
    have hk_eq : k = (k.pred hk).succ :=
      (Fin.succ_pred k hk).symm
    rw [hk_eq]
    exact ne_of_lt (by
      dsimp [prev]
      exact (k.pred hk).castSucc_lt_succ)
  have hτprev_rank : rankOf τ (τ prev) = prev := by
    simp [rankOf]
  have hk_succAbove_pred : k.succAbove (k.pred hk) = prev := by
    simpa [prev] using Fin.succAbove_pred_self k hk
  have hprev_succAbove_pred : prev.succAbove (k.pred hk) = k := by
    simpa [prev] using Fin.succAbove_castSucc_self (k.pred hk)
  have hτprev_ne_zero : τ prev ≠ (0 : Candidate (n + 1)) := by
    intro h
    have hrank0 : rankOf τ (0 : Candidate (n + 1)) = k := by
      simp [τ]
    have hbad : prev = k := by
      have hkp : k = prev := by
        simpa [h, hrank0] using hτprev_rank
      exact hkp.symm
    exact hprev_ne_k hbad
  cases e using Fin.cases with
  | zero =>
      rw [rankOf_swapCandidatePositions_left]
      simpa [τ, prev] using hτprev_rank
  | succ a =>
      by_cases ha_rank : rankOf σ a = k.pred hk
      · have hcandidate : a.succ = τ prev := by
          have hrank_a :
              rankOf τ a.succ = prev := by
            rw [rankOf_rankingPeelBestOrderEquiv_succ, ha_rank]
            exact hk_succAbove_pred
          have hrank_eq :
              rankOf τ a.succ = rankOf τ (τ prev) := by
            rw [hrank_a, hτprev_rank]
          have happly := congrArg τ hrank_eq
          simpa [rankOf] using happly
        have hleft :
            rankOf (swapCandidatePositions τ (0 : Candidate (n + 1)) (τ prev))
                a.succ = k := by
          rw [hcandidate, rankOf_swapCandidatePositions_right]
          simp [τ]
        have hright :
            rankOf (rankingPeelBestOrderEquiv n (prev, σ)) a.succ = k := by
          rw [rankOf_rankingPeelBestOrderEquiv_succ, ha_rank]
          exact hprev_succAbove_pred
        rw [hleft, hright]
      · have ha_ne_candidate : a.succ ≠ τ prev := by
          intro h
          have hrank :
              rankOf τ a.succ = rankOf τ (τ prev) := by rw [h]
          rw [rankOf_rankingPeelBestOrderEquiv_succ, hτprev_rank] at hrank
          have hpos :
              k.succAbove (rankOf σ a) = k.succAbove (k.pred hk) := by
            simpa [prev] using hrank
          have hrank_eq : rankOf σ a = k.pred hk :=
            k.succAbove_right_injective hpos
          exact ha_rank hrank_eq
        have ha_ne_zero : a.succ ≠ (0 : Candidate (n + 1)) := by
          intro h
          exact Fin.succ_ne_zero a h
        rw [rankOf_swapCandidatePositions_of_ne τ ha_ne_zero ha_ne_candidate]
        rw [rankOf_rankingPeelBestOrderEquiv_succ,
          rankOf_rankingPeelBestOrderEquiv_succ]
        exact succAbove_pred_castSucc_eq_of_ne k hk
          (by
            intro hrank
            exact ha_rank hrank)

/--
For any payoff monotone under correcting remaining-set inversions, moving the
inserted identity-center best candidate up one position weakly improves payoff.
-/
theorem rankingPeelBestOrderEquiv_adjacent_swap_improves
    {n : ℕ} {F : Ranking (n + 1) → ℝ}
    (hF : SwapImprovesOn Finset.univ (Equiv.refl (Candidate (n + 1))) F)
    (k : Candidate (n + 1)) (hk : k ≠ 0) (σ : Ranking n) :
    F (rankingPeelBestOrderEquiv n (k, σ)) ≤
      F (rankingPeelBestOrderEquiv n ((k.pred hk).castSucc, σ)) := by
  classical
  let prev : Candidate (n + 1) := (k.pred hk).castSucc
  let τ : Ranking (n + 1) := rankingPeelBestOrderEquiv n (k, σ)
  have hprev_lt_k : prev < k := by
    simpa [prev] using (k.pred hk).castSucc_lt_succ
  have hτprev_rank : rankOf τ (τ prev) = prev := by
    simp [rankOf]
  have hτprev_ne_zero : τ prev ≠ (0 : Candidate (n + 1)) := by
    intro h
    have hrank0 : rankOf τ (0 : Candidate (n + 1)) = k := by
      simp [τ]
    have hkp : k = prev := by
      simpa [h, hrank0] using hτprev_rank
    exact (ne_of_lt hprev_lt_k) hkp.symm
  have hcenter :
      rankOf (Equiv.refl (Candidate (n + 1))) (0 : Candidate (n + 1)) <
        rankOf (Equiv.refl (Candidate (n + 1))) (τ prev) := by
    simpa [rankOf] using Fin.pos_of_ne_zero hτprev_ne_zero
  have hpos : rankOf τ (τ prev) < rankOf τ (0 : Candidate (n + 1)) := by
    have hzero : rankOf τ (0 : Candidate (n + 1)) = k := by
      simp [τ]
    rw [hτprev_rank, hzero]
    exact hprev_lt_k
  have hstep :=
    hF τ (0 : Candidate (n + 1)) (τ prev)
      (Finset.mem_univ _) (Finset.mem_univ _) hcenter hpos
  have hswap :
      swapCandidatePositions τ (0 : Candidate (n + 1)) (τ prev) =
        rankingPeelBestOrderEquiv n (prev, σ) := by
    simpa [τ, prev] using rankingPeelBestOrderEquiv_adjacent_swap k hk σ
  rw [hswap] at hstep
  simpa [τ, prev] using hstep

/--
Adjacent-swap version of
`rankingPeelBestOrderEquiv_adjacent_swap_improves`.  Moving the inserted
identity-center best candidate up by one slot is itself an adjacent inversion
correction, so the weaker weak-order monotonicity hypothesis is enough.
-/
theorem rankingPeelBestOrderEquiv_adjacent_swap_improves_of_adjacentSwapImproves
    {n : ℕ} {F : Ranking (n + 1) → ℝ}
    (hF : AdjacentSwapImproves (Equiv.refl (Candidate (n + 1))) F)
    (k : Candidate (n + 1)) (hk : k ≠ 0) (σ : Ranking n) :
    F (rankingPeelBestOrderEquiv n (k, σ)) ≤
      F (rankingPeelBestOrderEquiv n ((k.pred hk).castSucc, σ)) := by
  classical
  let prev : Candidate (n + 1) := (k.pred hk).castSucc
  let τ : Ranking (n + 1) := rankingPeelBestOrderEquiv n (k, σ)
  have hprev_lt_k : prev < k := by
    simpa [prev] using (k.pred hk).castSucc_lt_succ
  have hτprev_rank : rankOf τ (τ prev) = prev := by
    simp [rankOf]
  have hτprev_ne_zero : τ prev ≠ (0 : Candidate (n + 1)) := by
    intro h
    have hrank0 : rankOf τ (0 : Candidate (n + 1)) = k := by
      simp [τ]
    have hkp : k = prev := by
      simpa [h, hrank0] using hτprev_rank
    exact (ne_of_lt hprev_lt_k) hkp.symm
  have hzero_at :
      τ (k.pred hk).succ = (0 : Candidate (n + 1)) := by
    have hidx :
        (k.pred hk).succ = rankOf τ (0 : Candidate (n + 1)) := by
      rw [Fin.succ_pred k hk]
      simp [τ]
    rw [hidx]
    simp [rankOf]
  have hprev_at : τ (k.pred hk).castSucc = τ prev := by
    rfl
  have hcenter :
      rankOf (Equiv.refl (Candidate (n + 1)))
          (τ (k.pred hk).succ) <
        rankOf (Equiv.refl (Candidate (n + 1)))
          (τ (k.pred hk).castSucc) := by
    rw [hzero_at, hprev_at]
    simpa [rankOf] using Fin.pos_of_ne_zero hτprev_ne_zero
  have hstep := hF τ (k.pred hk) hcenter
  rw [hzero_at, hprev_at] at hstep
  have hswap :
      swapCandidatePositions τ (0 : Candidate (n + 1)) (τ prev) =
        rankingPeelBestOrderEquiv n (prev, σ) := by
    simpa [τ, prev] using rankingPeelBestOrderEquiv_adjacent_swap k hk σ
  rw [hswap] at hstep
  simpa [τ, prev] using hstep

/--
For such payoffs, the peel-best insertion payoff is antitone in the insertion
position: placing the center-best candidate earlier weakly improves payoff.
-/
theorem rankingPeelBestOrderEquiv_position_anti_of_swapImprovesOn
    {n : ℕ} {F : Ranking (n + 1) → ℝ}
    (hF : SwapImprovesOn Finset.univ (Equiv.refl (Candidate (n + 1))) F)
    (σ : Ranking n) {p r : Candidate (n + 1)} (hpr : p < r) :
    F (rankingPeelBestOrderEquiv n (r, σ)) ≤
      F (rankingPeelBestOrderEquiv n (p, σ)) := by
  classical
  have H :
      ∀ r : Candidate (n + 1), p ≤ r →
        F (rankingPeelBestOrderEquiv n (r, σ)) ≤
          F (rankingPeelBestOrderEquiv n (p, σ)) := by
    intro r
    induction r using Fin.strong_induction_on with
    | h r ih =>
        intro hpr_le
        by_cases hrp : r = p
        · subst r
          rfl
        · have hp_lt_r : p < r := lt_of_le_of_ne hpr_le (Ne.symm hrp)
          have hr_ne_zero : r ≠ (0 : Candidate (n + 1)) :=
            Fin.ne_of_gt (lt_of_le_of_lt (Fin.zero_le p) hp_lt_r)
          let prev : Candidate (n + 1) := (r.pred hr_ne_zero).castSucc
          have hprev_lt_r : prev < r := by
            simpa [prev] using (r.pred hr_ne_zero).castSucc_lt_succ
          have hp_le_prev : p ≤ prev := by
            rw [Fin.le_iff_val_le_val]
            have hp_lt_val : p.val < r.val :=
              hp_lt_r
            have hr_val_ne_zero : r.val ≠ 0 := by
              intro hval
              exact hr_ne_zero (Fin.ext hval)
            simp [prev, Fin.val_pred]
            omega
          have hstep :=
            rankingPeelBestOrderEquiv_adjacent_swap_improves
              (n := n) (F := F) hF r hr_ne_zero σ
          have htail := ih prev hprev_lt_r hp_le_prev
          exact le_trans hstep htail
  exact H r (le_of_lt hpr)

/--
Adjacent-swap analogue of
`rankingPeelBestOrderEquiv_position_anti_of_swapImprovesOn`.
-/
theorem rankingPeelBestOrderEquiv_position_anti_of_adjacentSwapImproves
    {n : ℕ} {F : Ranking (n + 1) → ℝ}
    (hF : AdjacentSwapImproves (Equiv.refl (Candidate (n + 1))) F)
    (σ : Ranking n) {p r : Candidate (n + 1)} (hpr : p < r) :
    F (rankingPeelBestOrderEquiv n (r, σ)) ≤
      F (rankingPeelBestOrderEquiv n (p, σ)) := by
  classical
  have H :
      ∀ r : Candidate (n + 1), p ≤ r →
        F (rankingPeelBestOrderEquiv n (r, σ)) ≤
          F (rankingPeelBestOrderEquiv n (p, σ)) := by
    intro r
    induction r using Fin.strong_induction_on with
    | h r ih =>
        intro hpr_le
        by_cases hrp : r = p
        · subst r
          rfl
        · have hp_lt_r : p < r := lt_of_le_of_ne hpr_le (Ne.symm hrp)
          have hr_ne_zero : r ≠ (0 : Candidate (n + 1)) :=
            Fin.ne_of_gt (lt_of_le_of_lt (Fin.zero_le p) hp_lt_r)
          let prev : Candidate (n + 1) := (r.pred hr_ne_zero).castSucc
          have hprev_lt_r : prev < r := by
            simpa [prev] using (r.pred hr_ne_zero).castSucc_lt_succ
          have hp_le_prev : p ≤ prev := by
            rw [Fin.le_iff_val_le_val]
            have hp_lt_val : p.val < r.val :=
              hp_lt_r
            have hr_val_ne_zero : r.val ≠ 0 := by
              intro hval
              exact hr_ne_zero (Fin.ext hval)
            simp [prev, Fin.val_pred]
            omega
          have hstep :=
            rankingPeelBestOrderEquiv_adjacent_swap_improves_of_adjacentSwapImproves
              (n := n) (F := F) hF r hr_ne_zero σ
          have htail := ih prev hprev_lt_r hp_le_prev
          exact le_trans hstep htail
  exact H r (le_of_lt hpr)

/--
The Mallows tail payoff sums in the peel-best decomposition are antitone in the
inserted position whenever the full payoff is monotone under adjacent inversion
corrections.
-/
theorem reflMallowsPayoffSum_peelBest_position_anti_of_adjacentSwapImproves
    {n : ℕ} {q : ℝ} (hq_nonneg : 0 ≤ q)
    {F : Ranking (n + 1) → ℝ}
    (hF : AdjacentSwapImproves (Equiv.refl (Candidate (n + 1))) F)
    {p r : Candidate (n + 1)} (hpr : p < r) :
    reflMallowsPayoffSum n q
        (fun σ : Ranking n => F (rankingPeelBestOrderEquiv n (r, σ))) ≤
      reflMallowsPayoffSum n q
        (fun σ : Ranking n => F (rankingPeelBestOrderEquiv n (p, σ))) := by
  classical
  unfold reflMallowsPayoffSum
  refine Finset.sum_le_sum ?_
  intro σ _
  have hweight :
      0 ≤ q ^ kendallTau (Equiv.refl (Candidate n)) σ :=
    pow_nonneg hq_nonneg _
  have hpoint :
      F (rankingPeelBestOrderEquiv n (r, σ)) ≤
        F (rankingPeelBestOrderEquiv n (p, σ)) :=
    rankingPeelBestOrderEquiv_position_anti_of_adjacentSwapImproves
      hF σ hpr
  exact mul_le_mul_of_nonneg_left hpoint hweight

/-- Tail candidates whose successor belongs to a full remaining set. -/
noncomputable def tailRemainingOf {n : ℕ}
    (remaining : Finset (Candidate (n + 1))) : Finset (Candidate n) := by
  classical
  exact Finset.univ.filter (fun c : Candidate n => c.succ ∈ remaining)

@[simp] theorem mem_tailRemainingOf {n : ℕ}
    {remaining : Finset (Candidate (n + 1))} {c : Candidate n} :
    c ∈ tailRemainingOf remaining ↔ c.succ ∈ remaining := by
  classical
  simp [tailRemainingOf]

theorem tailRemainingOf_nonempty_of_nonempty_of_zero_not_mem
    {n : ℕ} {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hzero : (0 : Candidate (n + 1)) ∉ remaining) :
    (tailRemainingOf remaining).Nonempty := by
  classical
  rcases hremaining with ⟨e, he⟩
  cases e using Fin.cases with
  | zero =>
      exact False.elim (hzero he)
  | succ a =>
      exact ⟨a, by simpa using he⟩

theorem tailRemainingOf_nonempty_of_zero_mem_of_one_lt_card
    {n : ℕ} {remaining : Finset (Candidate (n + 1))}
    (hzero : (0 : Candidate (n + 1)) ∈ remaining)
    (hcard : 1 < remaining.card) :
    (tailRemainingOf remaining).Nonempty := by
  classical
  by_contra htail
  have htail_not :
      ∀ c : Candidate n, c ∉ tailRemainingOf remaining := by
    intro c hc
    exact htail ⟨c, hc⟩
  have hcard_le_one : remaining.card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    cases a using Fin.cases with
    | zero =>
        cases b using Fin.cases with
        | zero =>
            rfl
        | succ btail =>
            exact False.elim (htail_not btail (by simpa using hb))
    | succ atail =>
      exact False.elim (htail_not atail (by simpa using ha))
  omega

theorem tailRemainingOf_card_eq_of_zero_not_mem
    {n : ℕ} {remaining : Finset (Candidate (n + 1))}
    (hzero : (0 : Candidate (n + 1)) ∉ remaining) :
    (tailRemainingOf remaining).card = remaining.card := by
  classical
  refine Finset.card_bij
    (fun c _ => c.succ) ?hmem ?hinj ?hsurj
  · intro c hc
    simpa using hc
  · intro a ha b hb hsucc
    exact Fin.succ_injective _ hsucc
  · intro e he
    cases e using Fin.cases with
    | zero =>
        exact False.elim (hzero he)
    | succ a =>
        exact ⟨a, by simpa using he, rfl⟩

/--
If the center-best candidate `0` is not remaining, inserting it at any position
does not change the best remaining tail candidate.
-/
theorem bestInSet_rankingPeelBestOrderEquiv_of_zero_not_mem
    {n : ℕ} (p : Candidate (n + 1)) (σ : Ranking n)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hzero : (0 : Candidate (n + 1)) ∉ remaining) :
    bestInSet (rankingPeelBestOrderEquiv n (p, σ)) remaining =
      (bestInSet σ (tailRemainingOf remaining)).succ := by
  classical
  have htail :
      (tailRemainingOf remaining).Nonempty :=
    tailRemainingOf_nonempty_of_nonempty_of_zero_not_mem hremaining hzero
  refine bestInSet_eq_of_forall_rank_le
    (rankingPeelBestOrderEquiv n (p, σ)) remaining
    (c := (bestInSet σ (tailRemainingOf remaining)).succ) ?_ ?_
  · simpa using bestInSet_mem σ htail
  · intro e he
    cases e using Fin.cases with
    | zero =>
        exact False.elim (hzero he)
    | succ a =>
        have ha : a ∈ tailRemainingOf remaining := by
          simpa using he
        by_contra hnot
        have hlt_full :
            rankOf (rankingPeelBestOrderEquiv n (p, σ)) a.succ <
              rankOf (rankingPeelBestOrderEquiv n (p, σ))
                (bestInSet σ (tailRemainingOf remaining)).succ :=
          lt_of_not_ge hnot
        have hlt_tail :
            rankOf σ a <
              rankOf σ (bestInSet σ (tailRemainingOf remaining)) :=
          (rankOf_rankingPeelBestOrderEquiv_succ_lt_iff
            n p σ a (bestInSet σ (tailRemainingOf remaining))).mp hlt_full
        exact (not_lt_of_ge (rankOf_bestInSet_le σ htail ha)) hlt_tail

/--
If `0` remains and the tail best remaining candidate appears before the inserted
`0`, then that tail candidate is the full best remaining candidate.
-/
theorem bestInSet_rankingPeelBestOrderEquiv_of_zero_mem_tail_before
    {n : ℕ} (p : Candidate (n + 1)) (σ : Ranking n)
    {remaining : Finset (Candidate (n + 1))}
    (hzero : (0 : Candidate (n + 1)) ∈ remaining)
    (htail : (tailRemainingOf remaining).Nonempty)
    (hbefore :
      (rankOf σ (bestInSet σ (tailRemainingOf remaining))).castSucc < p) :
    bestInSet (rankingPeelBestOrderEquiv n (p, σ)) remaining =
      (bestInSet σ (tailRemainingOf remaining)).succ := by
  classical
  let b : Candidate n := bestInSet σ (tailRemainingOf remaining)
  refine bestInSet_eq_of_forall_rank_le
    (rankingPeelBestOrderEquiv n (p, σ)) remaining
    (c := b.succ) ?_ ?_
  · simpa [b] using bestInSet_mem σ htail
  · intro e he
    cases e using Fin.cases with
    | zero =>
        rw [rankOf_rankingPeelBestOrderEquiv_succ,
          rankOf_rankingPeelBestOrderEquiv_zero]
        rw [Fin.succAbove_of_castSucc_lt]
        · exact le_of_lt hbefore
        · simpa [b] using hbefore
    | succ a =>
        have ha : a ∈ tailRemainingOf remaining := by
          simpa using he
        by_contra hnot
        have hlt_full :
            rankOf (rankingPeelBestOrderEquiv n (p, σ)) a.succ <
              rankOf (rankingPeelBestOrderEquiv n (p, σ)) b.succ :=
          lt_of_not_ge hnot
        have hlt_tail : rankOf σ a < rankOf σ b :=
          (rankOf_rankingPeelBestOrderEquiv_succ_lt_iff
            n p σ a b).mp hlt_full
        exact (not_lt_of_ge (rankOf_bestInSet_le σ htail ha)) hlt_tail

/--
If `0` remains and the tail best remaining candidate does not appear before the
inserted `0`, then the inserted `0` is the full best remaining candidate.
-/
theorem bestInSet_rankingPeelBestOrderEquiv_of_zero_mem_tail_not_before
    {n : ℕ} (p : Candidate (n + 1)) (σ : Ranking n)
    {remaining : Finset (Candidate (n + 1))}
    (hzero : (0 : Candidate (n + 1)) ∈ remaining)
    (htail : (tailRemainingOf remaining).Nonempty)
    (hnot_before :
      ¬ (rankOf σ (bestInSet σ (tailRemainingOf remaining))).castSucc < p) :
    bestInSet (rankingPeelBestOrderEquiv n (p, σ)) remaining =
      (0 : Candidate (n + 1)) := by
  classical
  let b : Candidate n := bestInSet σ (tailRemainingOf remaining)
  refine bestInSet_eq_of_forall_rank_le
    (rankingPeelBestOrderEquiv n (p, σ)) remaining hzero ?_
  intro e he
  cases e using Fin.cases with
  | zero =>
      simp
  | succ a =>
      have ha : a ∈ tailRemainingOf remaining := by
        simpa using he
      have hb_le_a : rankOf σ b ≤ rankOf σ a :=
        rankOf_bestInSet_le σ htail ha
      have hp_le_b : p ≤ (rankOf σ b).castSucc :=
        le_of_not_gt (by simpa [b] using hnot_before)
      have hp_le_a : p ≤ (rankOf σ a).castSucc :=
        le_trans hp_le_b (Fin.castSucc_le_castSucc_iff.mpr hb_le_a)
      rw [rankOf_rankingPeelBestOrderEquiv_zero,
        rankOf_rankingPeelBestOrderEquiv_succ]
      exact le_of_lt ((Fin.lt_succAbove_iff_le_castSucc p (rankOf σ a)).mpr
        hp_le_a)

/-- In the no-`0` branch, the tail payoff sum is independent of insertion position. -/
theorem reflMallowsPayoffSum_peelBest_position_eq_of_zero_not_mem
    {n : ℕ} (q : ℝ) (value : Candidate (n + 1) → ℝ)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hzero : (0 : Candidate (n + 1)) ∉ remaining)
    (p r : Candidate (n + 1)) :
    reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          value (bestInSet (rankingPeelBestOrderEquiv n (p, σ)) remaining)) =
      reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          value (bestInSet (rankingPeelBestOrderEquiv n (r, σ)) remaining)) := by
  classical
  unfold reflMallowsPayoffSum
  refine Finset.sum_congr rfl ?_
  intro σ _
  change
    q ^ kendallTau (Equiv.refl (Candidate n)) σ *
        value (bestInSet (rankingPeelBestOrderEquiv n (p, σ)) remaining) =
      q ^ kendallTau (Equiv.refl (Candidate n)) σ *
        value (bestInSet (rankingPeelBestOrderEquiv n (r, σ)) remaining)
  rw [bestInSet_rankingPeelBestOrderEquiv_of_zero_not_mem
      p σ hremaining hzero,
    bestInSet_rankingPeelBestOrderEquiv_of_zero_not_mem
      r σ hremaining hzero]

theorem reflMallowsPayoffSum_peelBest_position_anti_of_zero_not_mem
    {n : ℕ} (q : ℝ) (value : Candidate (n + 1) → ℝ)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hzero : (0 : Candidate (n + 1)) ∉ remaining)
    {p r : Candidate (n + 1)} (_hpr : p < r) :
    reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          value (bestInSet (rankingPeelBestOrderEquiv n (r, σ)) remaining)) ≤
      reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          value (bestInSet (rankingPeelBestOrderEquiv n (p, σ)) remaining)) :=
   le_of_eq
    (reflMallowsPayoffSum_peelBest_position_eq_of_zero_not_mem
      q value hremaining hzero p r).symm

theorem le_succAbove_of_lt_of_le_succAbove
    {n : ℕ} {p r : Fin (n + 1)} {x : Fin n}
    (hpr : p < r) (hr : r ≤ r.succAbove x) :
    p ≤ p.succAbove x := by
  have hrlt : r < r.succAbove x :=
    lt_of_le_of_ne hr (Fin.ne_succAbove r x)
  have hrx : r ≤ x.castSucc :=
    (Fin.lt_succAbove_iff_le_castSucc r x).mp hrlt
  have hpx : p ≤ x.castSucc := le_trans (le_of_lt hpr) hrx
  exact le_of_lt ((Fin.lt_succAbove_iff_le_castSucc p x).mpr hpx)

/--
If the center-best candidate `0` remains, inserting it earlier weakly improves
the deterministic best-in-set value.
-/
theorem bestInSet_value_rankingPeelBestOrderEquiv_anti_position_of_zero_mem
    {n : ℕ} {value : Candidate (n + 1) → ℝ}
    (hvalue : WeaklyOrderedBy (Equiv.refl (Candidate (n + 1))) value)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hzero : (0 : Candidate (n + 1)) ∈ remaining)
    (σ : Ranking n) {p r : Candidate (n + 1)} (hpr : p < r) :
    value (bestInSet (rankingPeelBestOrderEquiv n (r, σ)) remaining) ≤
      value (bestInSet (rankingPeelBestOrderEquiv n (p, σ)) remaining) := by
  classical
  let πp : Ranking (n + 1) := rankingPeelBestOrderEquiv n (p, σ)
  let πr : Ranking (n + 1) := rankingPeelBestOrderEquiv n (r, σ)
  cases hbest_r : bestInSet πr remaining using Fin.cases with
  | zero =>
      have hbest_p_zero : bestInSet πp remaining = (0 : Candidate (n + 1)) := by
        refine bestInSet_eq_of_forall_rank_le πp remaining hzero ?_
        intro e he
        cases e using Fin.cases with
        | zero =>
            simp [πp]
        | succ a =>
            have hr_le :
                rankOf πr (0 : Candidate (n + 1)) ≤
                  rankOf πr a.succ := by
              simpa [hbest_r] using
                rankOf_bestInSet_le πr hremaining he
            rw [rankOf_rankingPeelBestOrderEquiv_zero,
              rankOf_rankingPeelBestOrderEquiv_succ] at hr_le ⊢
            exact le_succAbove_of_lt_of_le_succAbove hpr hr_le
      simp [πp, hbest_p_zero]
  | succ btail =>
      have hbtail_mem : btail.succ ∈ remaining := by
        simpa [hbest_r] using bestInSet_mem πr hremaining
      have hbtail_min :
          ∀ a : Candidate n, a.succ ∈ remaining →
            rankOf σ btail ≤ rankOf σ a := by
        intro a ha
        by_contra hnot
        have hlt_tail : rankOf σ a < rankOf σ btail :=
          lt_of_not_ge hnot
        have hlt_full :
            rankOf πr a.succ < rankOf πr btail.succ := by
          simpa [πr] using
            (rankOf_rankingPeelBestOrderEquiv_succ_lt_iff
              n r σ a btail).mpr hlt_tail
        have hb_le :
            rankOf πr btail.succ ≤ rankOf πr a.succ := by
          simpa [hbest_r] using
            rankOf_bestInSet_le πr hremaining ha
        exact (not_lt_of_ge hb_le) hlt_full
      cases hbest_p : bestInSet πp remaining using Fin.cases with
      | zero =>
          have hcenter :
              rankOf (Equiv.refl (Candidate (n + 1))) (0 : Candidate (n + 1)) <
                rankOf (Equiv.refl (Candidate (n + 1))) btail.succ := by
            change (0 : ℕ) < (btail : ℕ) + 1
            omega
          simpa [πr, πp, hbest_r, hbest_p] using hvalue hcenter
      | succ a =>
          have ha_mem : a.succ ∈ remaining := by
            simpa [hbest_p] using bestInSet_mem πp hremaining
          have ha_le_btail : rankOf σ a ≤ rankOf σ btail := by
            by_contra hnot
            have hlt_tail : rankOf σ btail < rankOf σ a :=
              lt_of_not_ge hnot
            have hlt_full :
                rankOf πp btail.succ < rankOf πp a.succ := by
              simpa [πp] using
                (rankOf_rankingPeelBestOrderEquiv_succ_lt_iff
                  n p σ btail a).mpr hlt_tail
            have ha_best_le :
                rankOf πp a.succ ≤ rankOf πp btail.succ := by
              simpa [hbest_p] using
                rankOf_bestInSet_le πp hremaining hbtail_mem
            exact (not_lt_of_ge ha_best_le) hlt_full
          have hbtail_le_a : rankOf σ btail ≤ rankOf σ a :=
            hbtail_min a ha_mem
          have hrank : rankOf σ a = rankOf σ btail :=
            le_antisymm ha_le_btail hbtail_le_a
          have ha_eq : a = btail := by
            have hσ := congrArg σ hrank
            simpa [rankOf] using hσ
          simp [ha_eq]

/--
The less-accurate tail payoff sums used in the peel-best induction step are
antitone in the insertion position for the best-in-set payoff.
-/
theorem reflMallowsPayoffSum_peelBest_position_anti_bestInSet
    {n : ℕ} {q : ℝ} (hq_nonneg : 0 ≤ q)
    {value : Candidate (n + 1) → ℝ}
    (hvalue : WeaklyOrderedBy (Equiv.refl (Candidate (n + 1))) value)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    {p r : Candidate (n + 1)} (hpr : p < r) :
    reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          value (bestInSet (rankingPeelBestOrderEquiv n (r, σ)) remaining)) ≤
      reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          value (bestInSet (rankingPeelBestOrderEquiv n (p, σ)) remaining)) := by
  classical
  by_cases hzero : (0 : Candidate (n + 1)) ∈ remaining
  · unfold reflMallowsPayoffSum
    refine Finset.sum_le_sum ?_
    intro σ _
    have hweight :
        0 ≤ q ^ kendallTau (Equiv.refl (Candidate n)) σ :=
      pow_nonneg hq_nonneg _
    have hpoint :
        value (bestInSet (rankingPeelBestOrderEquiv n (r, σ)) remaining) ≤
          value (bestInSet (rankingPeelBestOrderEquiv n (p, σ)) remaining) :=
      bestInSet_value_rankingPeelBestOrderEquiv_anti_position_of_zero_mem
        hvalue hremaining hzero σ hpr
    exact mul_le_mul_of_nonneg_left hpoint hweight
  · exact
      reflMallowsPayoffSum_peelBest_position_anti_of_zero_not_mem
        q value hremaining hzero hpr

/--
If the center-best candidate is still available and another candidate remains,
moving the center-best insertion from rank `0` to rank `1` strictly lowers the
less-accurate branch payoff for a strictly center-ordered value vector.
-/
theorem reflMallowsPayoffSum_peelBest_position_strict_bestInSet_zero_one
    {n : ℕ} {q : ℝ} (hq_pos : 0 < q)
    {value : Candidate (n + 1) → ℝ}
    (hvalue : StrictlyOrderedBy (Equiv.refl (Candidate (n + 1))) value)
    {remaining : Finset (Candidate (n + 1))}
    (hzero : (0 : Candidate (n + 1)) ∈ remaining)
    (hcard : 1 < remaining.card) :
    reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          value (bestInSet (rankingPeelBestOrderEquiv n
            ((1 : Candidate (n + 1)), σ)) remaining)) <
      reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          value (bestInSet (rankingPeelBestOrderEquiv n
            ((0 : Candidate (n + 1)), σ)) remaining)) := by
  classical
  have htail :
      (tailRemainingOf remaining).Nonempty :=
    tailRemainingOf_nonempty_of_zero_mem_of_one_lt_card hzero hcard
  let b : Candidate n := bestInSet (Equiv.refl (Candidate n))
    (tailRemainingOf remaining)
  let σ0 : Ranking n := Equiv.swap (0 : Candidate n) b
  have hb_mem : b ∈ tailRemainingOf remaining := by
    simpa [b] using bestInSet_mem (Equiv.refl (Candidate n)) htail
  have hb_rank : rankOf σ0 b = (0 : Candidate n) := by
    simp [σ0, rankOf]
  have hb_best : bestInSet σ0 (tailRemainingOf remaining) = b := by
    refine bestInSet_eq_of_forall_rank_le σ0 (tailRemainingOf remaining)
      hb_mem ?_
    intro d hd
    rw [hb_rank]
    exact Fin.zero_le _
  have hzero_branch :
      ∀ σ : Ranking n,
        bestInSet
            (rankingPeelBestOrderEquiv n
              ((0 : Candidate (n + 1)), σ)) remaining =
          (0 : Candidate (n + 1)) := by
    intro σ
    refine bestInSet_rankingPeelBestOrderEquiv_of_zero_mem_tail_not_before
      (0 : Candidate (n + 1)) σ hzero htail ?_
    exact not_lt_of_ge (Fin.zero_le _)
  unfold reflMallowsPayoffSum
  refine Finset.sum_lt_sum ?hle ?hstrict
  · intro σ _
    have hweight :
        0 ≤ q ^ kendallTau (Equiv.refl (Candidate n)) σ :=
      pow_nonneg (le_of_lt hq_pos) _
    have hpoint :
        value (bestInSet (rankingPeelBestOrderEquiv n
            ((1 : Candidate (n + 1)), σ)) remaining) ≤
          value (bestInSet (rankingPeelBestOrderEquiv n
            ((0 : Candidate (n + 1)), σ)) remaining) :=
      bestInSet_value_rankingPeelBestOrderEquiv_anti_position_of_zero_mem
        (weaklyOrderedBy_of_strictlyOrderedBy hvalue) ⟨0, hzero⟩
        hzero σ (by norm_num)
    exact mul_le_mul_of_nonneg_left hpoint hweight
  · refine ⟨σ0, Finset.mem_univ _, ?_⟩
    have hweight :
        0 < q ^ kendallTau (Equiv.refl (Candidate n)) σ0 :=
      pow_pos hq_pos _
    have hone_branch :
        bestInSet
            (rankingPeelBestOrderEquiv n
              ((1 : Candidate (n + 1)), σ0)) remaining =
          b.succ := by
      have hraw :=
        bestInSet_rankingPeelBestOrderEquiv_of_zero_mem_tail_before
          (1 : Candidate (n + 1)) σ0 hzero htail ?_
      · simpa [hb_best] using hraw
      · rw [hb_best, hb_rank]
        norm_num
    have hstrict_value : value b.succ < value (0 : Candidate (n + 1)) := by
      have hcenter :
          rankOf (Equiv.refl (Candidate (n + 1)))
              (0 : Candidate (n + 1)) <
            rankOf (Equiv.refl (Candidate (n + 1))) b.succ := by
        change (0 : ℕ) < (b : ℕ) + 1
        omega
      simpa [rankOf] using hvalue hcenter
    have hzero0 := hzero_branch σ0
    simpa [hone_branch, hzero0] using
      mul_lt_mul_of_pos_left hstrict_value hweight

theorem reflMallowsPayoffSum_peelBest_position_strict_bestInSet
    {n : ℕ} {q : ℝ} (hq_pos : 0 < q)
    {value : Candidate (n + 1) → ℝ}
    (hvalue : StrictlyOrderedBy (Equiv.refl (Candidate (n + 1))) value)
    {remaining : Finset (Candidate (n + 1))}
    (hzero : (0 : Candidate (n + 1)) ∈ remaining)
    (hcard : 1 < remaining.card) :
    ∃ p r : Candidate (n + 1), p < r ∧
      reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          value (bestInSet (rankingPeelBestOrderEquiv n (r, σ)) remaining)) <
      reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          value (bestInSet (rankingPeelBestOrderEquiv n (p, σ)) remaining)) := by
  refine ⟨0, 1, by norm_num, ?_⟩
  exact
    reflMallowsPayoffSum_peelBest_position_strict_bestInSet_zero_one
      hq_pos hvalue hzero hcard

/--
Swap-improvement on a full remaining set descends through the best-candidate
insertion decomposition to swap-improvement on the tail candidates.
-/
theorem swapImprovesOn_peelBest_succ
    {n : ℕ} {remainingTail : Finset (Candidate n)}
    {remainingFull : Finset (Candidate (n + 1))}
    {F : Ranking (n + 1) → ℝ}
    (hmem : ∀ c : Candidate n, c ∈ remainingTail → c.succ ∈ remainingFull)
    (hF :
      SwapImprovesOn remainingFull (Equiv.refl (Candidate (n + 1))) F)
    (p : Candidate (n + 1)) :
    SwapImprovesOn remainingTail (Equiv.refl (Candidate n))
      (fun σ : Ranking n => F (rankingPeelBestOrderEquiv n (p, σ))) := by
  intro σ c d hc hd hcenter hpos
  have hcenter_full :
      rankOf (Equiv.refl (Candidate (n + 1))) c.succ <
        rankOf (Equiv.refl (Candidate (n + 1))) d.succ := by
    have hcd : c < d := by
      simpa [rankOf] using hcenter
    change (c : ℕ) + 1 < (d : ℕ) + 1
    exact Nat.succ_lt_succ hcd
  have hpos_full :
      rankOf (rankingPeelBestOrderEquiv n (p, σ)) d.succ <
        rankOf (rankingPeelBestOrderEquiv n (p, σ)) c.succ := by
    simpa using
      (rankOf_rankingPeelBestOrderEquiv_succ_lt_iff
        n p σ d c).mpr hpos
  have h :=
    hF (rankingPeelBestOrderEquiv n (p, σ)) c.succ d.succ
      (hmem c hc) (hmem d hd) hcenter_full hpos_full
  simpa [swapCandidatePositions_rankingPeelBestOrderEquiv_succ] using h

/-- One-step insertion decomposition for the identity-center partition. -/
theorem mallowsPartition_refl_peelBest
    (n : ℕ) (q : ℝ) :
    mallowsPartition q (Equiv.refl (Candidate (n + 1))) =
      candidateRankPowerSum (n + 1) q *
        mallowsPartition q (Equiv.refl (Candidate n)) := by
  classical
  have h :=
    reflMallowsPayoffSum_peelBest n q
      (fun _ : Ranking (n + 1) => (1 : ℝ))
  unfold reflMallowsPayoffSum at h
  unfold mallowsPartition mallowsWeight candidateRankPowerSum
  calc
    (∑ τ : Ranking (n + 1),
        q ^ kendallTau (Equiv.refl (Candidate (n + 1))) τ)
        =
      ∑ p : Candidate (n + 1),
        q ^ (p : ℕ) *
          (∑ σ : Ranking n,
            q ^ kendallTau (Equiv.refl (Candidate n)) σ) := by
        simpa [Finset.mul_sum] using h
    _ =
      (∑ p : Candidate (n + 1), q ^ (p : ℕ)) *
        (∑ σ : Ranking n,
          q ^ kendallTau (Equiv.refl (Candidate n)) σ) := by
        rw [Finset.sum_mul]

/--
One-step worst-candidate insertion decomposition for identity-center Mallows
payoff sums.
-/
theorem reflMallowsPayoffSum_peelWorst
    (n : ℕ) (q : ℝ) (F : Ranking (n + 1) → ℝ) :
    reflMallowsPayoffSum (n + 1) q F =
      ∑ p : Candidate (n + 1),
        q ^ (n + 2 - (p : ℕ)) *
          reflMallowsPayoffSum n q
            (fun σ : Ranking n =>
              F (rankingPeelWorstOrderEquiv n (p, σ))) := by
  classical
  let e := rankingPeelWorstOrderEquiv n
  unfold reflMallowsPayoffSum
  calc
    (∑ τ : Ranking (n + 1),
        q ^ kendallTau (Equiv.refl (Candidate (n + 1))) τ * F τ)
        =
      ∑ pe : Candidate (n + 1) × Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e pe) *
          F (e pe) := by
        simpa [e] using
          (Equiv.sum_comp e
            (fun τ : Ranking (n + 1) =>
              q ^ kendallTau (Equiv.refl (Candidate (n + 1))) τ *
                F τ)).symm
    _ =
      ∑ p : Candidate (n + 1), ∑ σ : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e (p, σ)) *
          F (e (p, σ)) := by
        simpa using
          (Finset.sum_product'
            (Finset.univ : Finset (Candidate (n + 1)))
            (Finset.univ : Finset (Ranking n))
            (fun p σ =>
              q ^ kendallTau (Equiv.refl (Candidate (n + 1))) (e (p, σ)) *
                F (e (p, σ))))
    _ =
      ∑ p : Candidate (n + 1), ∑ σ : Ranking n,
        q ^ (n + 2 - (p : ℕ)) *
          (q ^ kendallTau (Equiv.refl (Candidate n)) σ *
            F (e (p, σ))) := by
        refine Finset.sum_congr rfl ?_
        intro p _
        refine Finset.sum_congr rfl ?_
        intro σ _
        have hkend :
            kendallTau (Equiv.refl (Candidate (n + 1))) (e (p, σ)) =
              (n + 2 - (p : ℕ)) +
                kendallTau (Equiv.refl (Candidate n)) σ := by
          simpa [e] using kendallTau_rankingPeelWorstOrderEquiv n p σ
        rw [hkend, pow_add]
        ring
    _ =
      ∑ p : Candidate (n + 1),
        q ^ (n + 2 - (p : ℕ)) *
          (∑ σ : Ranking n,
            q ^ kendallTau (Equiv.refl (Candidate n)) σ *
              F (e (p, σ))) := by
        refine Finset.sum_congr rfl ?_
        intro p _
        rw [Finset.mul_sum]

/-- One-step worst-candidate insertion decomposition for the identity-center partition. -/
theorem mallowsPartition_refl_peelWorst
    (n : ℕ) (q : ℝ) :
    mallowsPartition q (Equiv.refl (Candidate (n + 1))) =
      candidateRankReversePowerSum (n + 1) q *
        mallowsPartition q (Equiv.refl (Candidate n)) := by
  classical
  have h :=
    reflMallowsPayoffSum_peelWorst n q
      (fun _ : Ranking (n + 1) => (1 : ℝ))
  unfold reflMallowsPayoffSum at h
  unfold mallowsPartition mallowsWeight candidateRankReversePowerSum
  calc
    (∑ τ : Ranking (n + 1),
        q ^ kendallTau (Equiv.refl (Candidate (n + 1))) τ)
        =
      ∑ p : Candidate (n + 1),
        q ^ (n + 2 - (p : ℕ)) *
          (∑ σ : Ranking n,
            q ^ kendallTau (Equiv.refl (Candidate n)) σ) := by
        simpa [Finset.mul_sum] using h
    _ =
      (∑ p : Candidate (n + 1), q ^ (n + 2 - (p : ℕ))) *
        (∑ σ : Ranking n,
          q ^ kendallTau (Equiv.refl (Candidate n)) σ) := by
        rw [Finset.sum_mul]

/-- Initial candidates whose cast into the larger identity-center set remains available. -/
noncomputable def initRemainingOf {n : ℕ}
    (remaining : Finset (Candidate (n + 1))) : Finset (Candidate n) := by
  classical
  exact Finset.univ.filter (fun c : Candidate n => c.castSucc ∈ remaining)

@[simp] theorem mem_initRemainingOf {n : ℕ}
    {remaining : Finset (Candidate (n + 1))} {c : Candidate n} :
    c ∈ initRemainingOf remaining ↔ c.castSucc ∈ remaining := by
  classical
  simp [initRemainingOf]

theorem initRemainingOf_nonempty_of_nonempty_of_last_not_mem
    {n : ℕ} {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hlast : reflLastCandidate (n + 1) ∉ remaining) :
    (initRemainingOf remaining).Nonempty := by
  classical
  rcases hremaining with ⟨e, he⟩
  have he_last : e ≠ reflLastCandidate (n + 1) := by
    intro h
    exact hlast (by simpa [h] using he)
  rcases Fin.eq_castSucc_of_ne_last
      (x := e) (by simpa [reflLastCandidate] using he_last) with ⟨c, hc⟩
  exact ⟨c, by simpa [hc] using he⟩

/--
If the center-worst candidate is not remaining, inserting it at any position
does not change the best remaining initial candidate.
-/
theorem bestInSet_rankingPeelWorstOrderEquiv_of_last_not_mem
    {n : ℕ} (p : Candidate (n + 1)) (σ : Ranking n)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hlast : reflLastCandidate (n + 1) ∉ remaining) :
    bestInSet (rankingPeelWorstOrderEquiv n (p, σ)) remaining =
      (bestInSet σ (initRemainingOf remaining)).castSucc := by
  classical
  have hinit :
      (initRemainingOf remaining).Nonempty :=
    initRemainingOf_nonempty_of_nonempty_of_last_not_mem hremaining hlast
  refine bestInSet_eq_of_forall_rank_le
    (rankingPeelWorstOrderEquiv n (p, σ)) remaining
    (c := (bestInSet σ (initRemainingOf remaining)).castSucc) ?_ ?_
  · simpa using bestInSet_mem σ hinit
  · intro e he
    have he_last : e ≠ reflLastCandidate (n + 1) := by
      intro h
      exact hlast (by simpa [h] using he)
    rcases Fin.eq_castSucc_of_ne_last
        (x := e) (by simpa [reflLastCandidate] using he_last) with ⟨a, ha⟩
    have ha_mem : a ∈ initRemainingOf remaining := by
      simpa [ha] using he
    rw [← ha]
    by_contra hnot
    have hlt_full :
        rankOf (rankingPeelWorstOrderEquiv n (p, σ)) a.castSucc <
          rankOf (rankingPeelWorstOrderEquiv n (p, σ))
            (bestInSet σ (initRemainingOf remaining)).castSucc :=
      lt_of_not_ge hnot
    have hlt_init :
        rankOf σ a <
          rankOf σ (bestInSet σ (initRemainingOf remaining)) :=
      (rankOf_rankingPeelWorstOrderEquiv_castSucc_lt_iff
        n p σ a (bestInSet σ (initRemainingOf remaining))).mp hlt_full
    exact (not_lt_of_ge (rankOf_bestInSet_le σ hinit ha_mem)) hlt_init

/--
If the center-worst candidate remains and the initial best remaining candidate
appears before the inserted worst candidate, then that initial candidate is the
full best remaining candidate.
-/
theorem bestInSet_rankingPeelWorstOrderEquiv_of_last_mem_tail_before
    {n : ℕ} (p : Candidate (n + 1)) (σ : Ranking n)
    {remaining : Finset (Candidate (n + 1))}
    (hlast : reflLastCandidate (n + 1) ∈ remaining)
    (hinit : (initRemainingOf remaining).Nonempty)
    (hbefore :
      (rankOf σ (bestInSet σ (initRemainingOf remaining))).castSucc < p) :
    bestInSet (rankingPeelWorstOrderEquiv n (p, σ)) remaining =
      (bestInSet σ (initRemainingOf remaining)).castSucc := by
  classical
  let b : Candidate n := bestInSet σ (initRemainingOf remaining)
  refine bestInSet_eq_of_forall_rank_le
    (rankingPeelWorstOrderEquiv n (p, σ)) remaining
    (c := b.castSucc) ?_ ?_
  · simpa [b] using bestInSet_mem σ hinit
  · intro e he
    by_cases he_last : e = reflLastCandidate (n + 1)
    · subst e
      rw [rankOf_rankingPeelWorstOrderEquiv_castSucc,
        rankOf_rankingPeelWorstOrderEquiv_last]
      exact le_of_lt
        ((Fin.succAbove_lt_iff_castSucc_lt p (rankOf σ b)).mpr
          (by simpa [b] using hbefore))
    · rcases Fin.eq_castSucc_of_ne_last
        (x := e) (by simpa [reflLastCandidate] using he_last)
        with ⟨a, ha⟩
      subst e
      have ha_mem : a ∈ initRemainingOf remaining :=
        (mem_initRemainingOf (remaining := remaining)
          (c := a)).mpr he
      have hb_le_a : rankOf σ b ≤ rankOf σ a :=
        rankOf_bestInSet_le σ hinit ha_mem
      rw [rankOf_rankingPeelWorstOrderEquiv_castSucc,
        rankOf_rankingPeelWorstOrderEquiv_castSucc]
      exact (Fin.succAbove_le_succAbove_iff).mpr hb_le_a

/--
If the center-worst candidate remains and no initial remaining candidate
appears before it, then the inserted worst candidate is the full best remaining
candidate.
-/
theorem bestInSet_rankingPeelWorstOrderEquiv_of_last_mem_tail_not_before
    {n : ℕ} (p : Candidate (n + 1)) (σ : Ranking n)
    {remaining : Finset (Candidate (n + 1))}
    (hlast : reflLastCandidate (n + 1) ∈ remaining)
    (hinit : (initRemainingOf remaining).Nonempty)
    (hnot_before :
      ¬ (rankOf σ (bestInSet σ (initRemainingOf remaining))).castSucc < p) :
    bestInSet (rankingPeelWorstOrderEquiv n (p, σ)) remaining =
      reflLastCandidate (n + 1) := by
  classical
  let b : Candidate n := bestInSet σ (initRemainingOf remaining)
  refine bestInSet_eq_of_forall_rank_le
    (rankingPeelWorstOrderEquiv n (p, σ)) remaining hlast ?_
  intro e he
  by_cases he_last : e = reflLastCandidate (n + 1)
  · subst e
    simp
  · rcases Fin.eq_castSucc_of_ne_last
      (x := e) (by simpa [reflLastCandidate] using he_last)
      with ⟨a, ha⟩
    subst e
    have ha_mem : a ∈ initRemainingOf remaining :=
      (mem_initRemainingOf (remaining := remaining)
        (c := a)).mpr he
    have hb_le_a : rankOf σ b ≤ rankOf σ a :=
      rankOf_bestInSet_le σ hinit ha_mem
    have hp_le_b : p ≤ (rankOf σ b).castSucc :=
      le_of_not_gt (by simpa [b] using hnot_before)
    have hp_le_a : p ≤ (rankOf σ a).castSucc :=
      le_trans hp_le_b (Fin.castSucc_le_castSucc_iff.mpr hb_le_a)
    rw [rankOf_rankingPeelWorstOrderEquiv_last,
      rankOf_rankingPeelWorstOrderEquiv_castSucc]
    exact le_of_lt ((Fin.lt_succAbove_iff_le_castSucc p (rankOf σ a)).mpr
      hp_le_a)

/-- If the center-worst candidate is the only remaining candidate, it is best. -/
theorem bestInSet_rankingPeelWorstOrderEquiv_of_last_mem_init_empty
    {n : ℕ} (p : Candidate (n + 1)) (σ : Ranking n)
    {remaining : Finset (Candidate (n + 1))}
    (hlast : reflLastCandidate (n + 1) ∈ remaining)
    (hinit : ¬ (initRemainingOf remaining).Nonempty) :
    bestInSet (rankingPeelWorstOrderEquiv n (p, σ)) remaining =
      reflLastCandidate (n + 1) := by
  classical
  refine bestInSet_eq_of_forall_rank_le
    (rankingPeelWorstOrderEquiv n (p, σ)) remaining hlast ?_
  intro e he
  by_cases he_last : e = reflLastCandidate (n + 1)
  · subst e
    simp
  · rcases Fin.eq_castSucc_of_ne_last
      (x := e) (by simpa [reflLastCandidate] using he_last)
      with ⟨a, ha⟩
    have ha_mem : a ∈ initRemainingOf remaining :=
      (mem_initRemainingOf (remaining := remaining)
        (c := a)).mpr (by simpa [ha] using he)
    exact False.elim (hinit ⟨a, ha_mem⟩)

/--
Deleting a center-worst candidate that is not remaining reduces the
identity-center best-in-set Mallows cross comparison to the initial-candidate
comparison.
-/
theorem reflMallowsPayoffSum_cross_bestInSet_of_last_not_mem
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {value : Candidate (n + 1) → ℝ}
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hlast : reflLastCandidate (n + 1) ∉ remaining)
    (hinit :
      0 ≤
        mallowsPartition qLess (Equiv.refl (Candidate n)) *
            reflMallowsPayoffSum n qMore
              (fun σ : Ranking n =>
                value ((bestInSet σ (initRemainingOf remaining)).castSucc)) -
          mallowsPartition qMore (Equiv.refl (Candidate n)) *
            reflMallowsPayoffSum n qLess
              (fun σ : Ranking n =>
                value ((bestInSet σ (initRemainingOf remaining)).castSucc))) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qMore
            (fun τ : Ranking (n + 1) =>
              value (bestInSet τ remaining)) -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qLess
            (fun τ : Ranking (n + 1) =>
              value (bestInSet τ remaining)) := by
  classical
  let initF : Ranking n → ℝ := fun σ =>
    value ((bestInSet σ (initRemainingOf remaining)).castSucc)
  let PMore : ℝ := candidateRankReversePowerSum (n + 1) qMore
  let PLess : ℝ := candidateRankReversePowerSum (n + 1) qLess
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let SMore : ℝ := reflMallowsPayoffSum n qMore initF
  let SLess : ℝ := reflMallowsPayoffSum n qLess initF
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hbranch :
      ∀ q : ℝ, ∀ p : Candidate (n + 1),
        reflMallowsPayoffSum n q
            (fun σ : Ranking n =>
              value
                (bestInSet (rankingPeelWorstOrderEquiv n (p, σ)) remaining)) =
          reflMallowsPayoffSum n q initF := by
    intro q p
    unfold reflMallowsPayoffSum initF
    refine Finset.sum_congr rfl ?_
    intro σ _
    change
      q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          value (bestInSet (rankingPeelWorstOrderEquiv n (p, σ)) remaining) =
        q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          value ((bestInSet σ (initRemainingOf remaining)).castSucc)
    rw [bestInSet_rankingPeelWorstOrderEquiv_of_last_not_mem
      p σ hremaining hlast]
  have hsum :
      ∀ q : ℝ,
        reflMallowsPayoffSum (n + 1) q
            (fun τ : Ranking (n + 1) =>
              value (bestInSet τ remaining)) =
          candidateRankReversePowerSum (n + 1) q *
            reflMallowsPayoffSum n q initF := by
    intro q
    rw [reflMallowsPayoffSum_peelWorst n q
      (fun τ : Ranking (n + 1) => value (bestInSet τ remaining))]
    simp_rw [hbranch q]
    change
      (∑ p : Candidate (n + 1),
        q ^ (n + 2 - (p : ℕ)) * reflMallowsPayoffSum n q initF) =
        candidateRankReversePowerSum (n + 1) q *
          reflMallowsPayoffSum n q initF
    rw [← Finset.sum_mul]
    rfl
  have hPMore_nonneg : 0 ≤ PMore :=
    le_of_lt (candidateRankReversePowerSum_pos (n + 1) hqMore_pos)
  have hPLess_nonneg : 0 ≤ PLess :=
    le_of_lt (candidateRankReversePowerSum_pos (n + 1) hqLess_pos)
  rw [mallowsPartition_refl_peelWorst n qLess,
    mallowsPartition_refl_peelWorst n qMore,
    hsum qMore, hsum qLess]
  change
    0 ≤
      (PLess * ZLess) * (PMore * SMore) -
        (PMore * ZMore) * (PLess * SLess)
  have hfactor :
      (PLess * ZLess) * (PMore * SMore) -
          (PMore * ZMore) * (PLess * SLess) =
        PLess * PMore * (ZLess * SMore - ZMore * SLess) := by
    ring
  rw [hfactor]
  exact mul_nonneg (mul_nonneg hPLess_nonneg hPMore_nonneg)
    (by simpa [ZLess, ZMore, SMore, SLess, initF] using hinit)

/--
Deleting a center-best candidate that is not remaining reduces the
identity-center best-in-set Mallows cross comparison to the tail comparison.
-/
theorem reflMallowsPayoffSum_cross_bestInSet_of_zero_not_mem
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {value : Candidate (n + 1) → ℝ}
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hzero : (0 : Candidate (n + 1)) ∉ remaining)
    (htail :
      0 ≤
        mallowsPartition qLess (Equiv.refl (Candidate n)) *
            reflMallowsPayoffSum n qMore
              (fun σ : Ranking n =>
                value ((bestInSet σ (tailRemainingOf remaining)).succ)) -
          mallowsPartition qMore (Equiv.refl (Candidate n)) *
            reflMallowsPayoffSum n qLess
              (fun σ : Ranking n =>
                value ((bestInSet σ (tailRemainingOf remaining)).succ))) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qMore
            (fun τ : Ranking (n + 1) =>
              value (bestInSet τ remaining)) -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qLess
            (fun τ : Ranking (n + 1) =>
              value (bestInSet τ remaining)) := by
  classical
  let tailF : Ranking n → ℝ := fun σ =>
    value ((bestInSet σ (tailRemainingOf remaining)).succ)
  let PMore : ℝ := candidateRankPowerSum (n + 1) qMore
  let PLess : ℝ := candidateRankPowerSum (n + 1) qLess
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let SMore : ℝ := reflMallowsPayoffSum n qMore tailF
  let SLess : ℝ := reflMallowsPayoffSum n qLess tailF
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hbranch :
      ∀ q : ℝ, ∀ p : Candidate (n + 1),
        reflMallowsPayoffSum n q
            (fun σ : Ranking n =>
              value
                (bestInSet (rankingPeelBestOrderEquiv n (p, σ)) remaining)) =
          reflMallowsPayoffSum n q tailF := by
    intro q p
    unfold reflMallowsPayoffSum tailF
    refine Finset.sum_congr rfl ?_
    intro σ _
    change
      q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          value (bestInSet (rankingPeelBestOrderEquiv n (p, σ)) remaining) =
        q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          value ((bestInSet σ (tailRemainingOf remaining)).succ)
    rw [bestInSet_rankingPeelBestOrderEquiv_of_zero_not_mem
      p σ hremaining hzero]
  have hsum :
      ∀ q : ℝ,
        reflMallowsPayoffSum (n + 1) q
            (fun τ : Ranking (n + 1) =>
              value (bestInSet τ remaining)) =
          candidateRankPowerSum (n + 1) q *
            reflMallowsPayoffSum n q tailF := by
    intro q
    rw [reflMallowsPayoffSum_peelBest n q
      (fun τ : Ranking (n + 1) => value (bestInSet τ remaining))]
    simp_rw [hbranch q]
    change
      (∑ p : Candidate (n + 1),
        q ^ (p : ℕ) * reflMallowsPayoffSum n q tailF) =
        candidateRankPowerSum (n + 1) q *
          reflMallowsPayoffSum n q tailF
    rw [← Finset.sum_mul]
    rfl
  have hPMore_nonneg : 0 ≤ PMore :=
    le_of_lt (candidateRankPowerSum_pos (n + 1) hqMore_pos)
  have hPLess_nonneg : 0 ≤ PLess :=
    le_of_lt (candidateRankPowerSum_pos (n + 1) hqLess_pos)
  rw [mallowsPartition_refl_peelBest n qLess,
    mallowsPartition_refl_peelBest n qMore,
    hsum qMore, hsum qLess]
  change
    0 ≤
      (PLess * ZLess) * (PMore * SMore) -
        (PMore * ZMore) * (PLess * SLess)
  have hfactor :
      (PLess * ZLess) * (PMore * SMore) -
          (PMore * ZMore) * (PLess * SLess) =
        PLess * PMore * (ZLess * SMore - ZMore * SLess) := by
    ring
  rw [hfactor]
  exact mul_nonneg (mul_nonneg hPLess_nonneg hPMore_nonneg)
    (by simpa [ZLess, ZMore, SMore, SLess, tailF] using htail)

/--
Strict version of deleting an unavailable center-best candidate: the full
cross comparison is a positive insertion-position factor times the tail cross.
-/
theorem reflMallowsPayoffSum_cross_bestInSet_pos_of_zero_not_mem
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {value : Candidate (n + 1) → ℝ}
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hzero : (0 : Candidate (n + 1)) ∉ remaining)
    (htail :
      0 <
        mallowsPartition qLess (Equiv.refl (Candidate n)) *
            reflMallowsPayoffSum n qMore
              (fun σ : Ranking n =>
                value ((bestInSet σ (tailRemainingOf remaining)).succ)) -
          mallowsPartition qMore (Equiv.refl (Candidate n)) *
            reflMallowsPayoffSum n qLess
              (fun σ : Ranking n =>
                value ((bestInSet σ (tailRemainingOf remaining)).succ))) :
    0 <
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qMore
            (fun τ : Ranking (n + 1) =>
              value (bestInSet τ remaining)) -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qLess
            (fun τ : Ranking (n + 1) =>
              value (bestInSet τ remaining)) := by
  classical
  let tailF : Ranking n → ℝ := fun σ =>
    value ((bestInSet σ (tailRemainingOf remaining)).succ)
  let PMore : ℝ := candidateRankPowerSum (n + 1) qMore
  let PLess : ℝ := candidateRankPowerSum (n + 1) qLess
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let SMore : ℝ := reflMallowsPayoffSum n qMore tailF
  let SLess : ℝ := reflMallowsPayoffSum n qLess tailF
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hbranch :
      ∀ q : ℝ, ∀ p : Candidate (n + 1),
        reflMallowsPayoffSum n q
            (fun σ : Ranking n =>
              value
                (bestInSet (rankingPeelBestOrderEquiv n (p, σ)) remaining)) =
          reflMallowsPayoffSum n q tailF := by
    intro q p
    unfold reflMallowsPayoffSum tailF
    refine Finset.sum_congr rfl ?_
    intro σ _
    change
      q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          value (bestInSet (rankingPeelBestOrderEquiv n (p, σ)) remaining) =
        q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          value ((bestInSet σ (tailRemainingOf remaining)).succ)
    rw [bestInSet_rankingPeelBestOrderEquiv_of_zero_not_mem
      p σ hremaining hzero]
  have hsum :
      ∀ q : ℝ,
        reflMallowsPayoffSum (n + 1) q
            (fun τ : Ranking (n + 1) =>
              value (bestInSet τ remaining)) =
          candidateRankPowerSum (n + 1) q *
            reflMallowsPayoffSum n q tailF := by
    intro q
    rw [reflMallowsPayoffSum_peelBest n q
      (fun τ : Ranking (n + 1) => value (bestInSet τ remaining))]
    simp_rw [hbranch q]
    change
      (∑ p : Candidate (n + 1),
        q ^ (p : ℕ) * reflMallowsPayoffSum n q tailF) =
        candidateRankPowerSum (n + 1) q *
          reflMallowsPayoffSum n q tailF
    rw [← Finset.sum_mul]
    rfl
  have hPMore_pos : 0 < PMore :=
    candidateRankPowerSum_pos (n + 1) hqMore_pos
  have hPLess_pos : 0 < PLess :=
    candidateRankPowerSum_pos (n + 1) hqLess_pos
  rw [mallowsPartition_refl_peelBest n qLess,
    mallowsPartition_refl_peelBest n qMore,
    hsum qMore, hsum qLess]
  change
    0 <
      (PLess * ZLess) * (PMore * SMore) -
        (PMore * ZMore) * (PLess * SLess)
  have hfactor :
      (PLess * ZLess) * (PMore * SMore) -
          (PMore * ZMore) * (PLess * SLess) =
        PLess * PMore * (ZLess * SMore - ZMore * SLess) := by
    ring
  rw [hfactor]
  exact mul_pos (mul_pos hPLess_pos hPMore_pos)
    (by simpa [ZLess, ZMore, SMore, SLess, tailF] using htail)

/--
If the identity-center best candidate is not remaining, every best-in-set fiber
is a common insertion-position scale times the corresponding tail fiber.
-/
theorem reflMallowsBestInSetWeight_eq_tail_of_zero_not_mem
    {n : ℕ} (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hzero : (0 : Candidate (n + 1)) ∉ remaining)
    (c : Candidate n) :
    reflMallowsBestInSetWeight (n + 1) q remaining c.succ =
      candidateRankPowerSum (n + 1) q *
        reflMallowsBestInSetWeight n q (tailRemainingOf remaining) c := by
  classical
  have hbranch :
      ∀ p : Candidate (n + 1),
        reflMallowsPayoffSum n q
            (fun σ : Ranking n =>
              if c.succ =
                  bestInSet (rankingPeelBestOrderEquiv n (p, σ))
                    remaining then
                (1 : ℝ)
              else
                0) =
          reflMallowsBestInSetWeight n q (tailRemainingOf remaining) c := by
    intro p
    unfold reflMallowsBestInSetWeight reflMallowsPayoffSum
    refine Finset.sum_congr rfl ?_
    intro σ _
    change
      q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          (if c.succ =
              bestInSet (rankingPeelBestOrderEquiv n (p, σ)) remaining then
            (1 : ℝ)
          else
            0) =
        q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          (if c = bestInSet σ (tailRemainingOf remaining) then
            (1 : ℝ)
          else
            0)
    rw [bestInSet_rankingPeelBestOrderEquiv_of_zero_not_mem
      p σ hremaining hzero]
    by_cases h : c = bestInSet σ (tailRemainingOf remaining)
    · rw [if_pos (by rw [h]), if_pos h]
    · rw [if_neg (by
        intro hsucc
        exact h (Fin.succ_injective _ hsucc)), if_neg h]
  unfold reflMallowsBestInSetWeight
  rw [reflMallowsPayoffSum_peelBest n q
    (fun τ : Ranking (n + 1) =>
      if c.succ = bestInSet τ remaining then (1 : ℝ) else 0)]
  simp_rw [hbranch]
  change
    (∑ p : Candidate (n + 1),
        q ^ (p : ℕ) *
          reflMallowsBestInSetWeight n q (tailRemainingOf remaining) c) =
      candidateRankPowerSum (n + 1) q *
        reflMallowsBestInSetWeight n q (tailRemainingOf remaining) c
  rw [← Finset.sum_mul]
  rfl

/--
If the identity-center worst candidate is not remaining, every best-in-set fiber
is a common insertion-position scale times the corresponding initial fiber.
-/
theorem reflMallowsBestInSetWeight_eq_init_of_last_not_mem
    {n : ℕ} (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hlast : reflLastCandidate (n + 1) ∉ remaining)
    (c : Candidate n) :
    reflMallowsBestInSetWeight (n + 1) q remaining c.castSucc =
      candidateRankReversePowerSum (n + 1) q *
        reflMallowsBestInSetWeight n q (initRemainingOf remaining) c := by
  classical
  have hbranch :
      ∀ p : Candidate (n + 1),
        reflMallowsPayoffSum n q
            (fun σ : Ranking n =>
              if c.castSucc =
                  bestInSet (rankingPeelWorstOrderEquiv n (p, σ))
                    remaining then
                (1 : ℝ)
              else
                0) =
          reflMallowsBestInSetWeight n q (initRemainingOf remaining) c := by
    intro p
    unfold reflMallowsBestInSetWeight reflMallowsPayoffSum
    refine Finset.sum_congr rfl ?_
    intro σ _
    change
      q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          (if c.castSucc =
              bestInSet (rankingPeelWorstOrderEquiv n (p, σ)) remaining then
            (1 : ℝ)
          else
            0) =
        q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          (if c = bestInSet σ (initRemainingOf remaining) then
            (1 : ℝ)
          else
            0)
    rw [bestInSet_rankingPeelWorstOrderEquiv_of_last_not_mem
      p σ hremaining hlast]
    by_cases h : c = bestInSet σ (initRemainingOf remaining)
    · rw [if_pos (by rw [h]), if_pos h]
    · rw [if_neg (by
        intro hcast
        exact h (Fin.castSucc_injective _ hcast)), if_neg h]
  unfold reflMallowsBestInSetWeight
  rw [reflMallowsPayoffSum_peelWorst n q
    (fun τ : Ranking (n + 1) =>
      if c.castSucc = bestInSet τ remaining then (1 : ℝ) else 0)]
  simp_rw [hbranch]
  change
    (∑ p : Candidate (n + 1),
        q ^ (n + 2 - (p : ℕ)) *
          reflMallowsBestInSetWeight n q (initRemainingOf remaining) c) =
      candidateRankReversePowerSum (n + 1) q *
        reflMallowsBestInSetWeight n q (initRemainingOf remaining) c
  rw [← Finset.sum_mul]
  rfl

/-- A remaining set is an interval in the identity-center order. -/
def CenterConvex {n : ℕ} (remaining : Finset (Candidate n)) : Prop :=
  ∀ a b c : Candidate n,
    a ∈ remaining → c ∈ remaining → a ≤ b → b ≤ c → b ∈ remaining

theorem centerConvex_eq_univ_of_zero_last_mem
    {n : ℕ} {remaining : Finset (Candidate n)}
    (hconv : CenterConvex remaining)
    (hzero : (0 : Candidate n) ∈ remaining)
    (hlast : reflLastCandidate n ∈ remaining) :
    remaining = Finset.univ := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro b
  exact hconv (0 : Candidate n) b (reflLastCandidate n)
    hzero hlast (Fin.zero_le b)
    (by
      change (b : ℕ) ≤ n + 1
      exact Nat.le_of_lt_succ b.isLt)

theorem centerConvex_tailRemainingOf
    {n : ℕ} {remaining : Finset (Candidate (n + 1))}
    (hconv : CenterConvex remaining) :
    CenterConvex (tailRemainingOf remaining) := by
  intro a b c ha hc hab hbc
  have ha_full : a.succ ∈ remaining := by simpa using ha
  have hc_full : c.succ ∈ remaining := by simpa using hc
  have hab_full : a.succ ≤ b.succ := by
    change (a : ℕ) + 1 ≤ (b : ℕ) + 1
    exact Nat.succ_le_succ (by exact hab)
  have hbc_full : b.succ ≤ c.succ := by
    change (b : ℕ) + 1 ≤ (c : ℕ) + 1
    exact Nat.succ_le_succ (by exact hbc)
  simpa using hconv a.succ b.succ c.succ
    ha_full hc_full hab_full hbc_full

theorem centerConvex_initRemainingOf
    {n : ℕ} {remaining : Finset (Candidate (n + 1))}
    (hconv : CenterConvex remaining) :
    CenterConvex (initRemainingOf remaining) := by
  intro a b c ha hc hab hbc
  have ha_full : a.castSucc ∈ remaining := by simpa using ha
  have hc_full : c.castSucc ∈ remaining := by simpa using hc
  have hab_full : a.castSucc ≤ b.castSucc := by
    change (a : ℕ) ≤ (b : ℕ)
    exact hab
  have hbc_full : b.castSucc ≤ c.castSucc := by
    change (b : ℕ) ≤ (c : ℕ)
    exact hbc
  simpa using hconv a.castSucc b.castSucc c.castSucc
    ha_full hc_full hab_full hbc_full

/--
Indicator that the best available candidate lies in the identity-center prefix
ending at adjacent threshold `k`.

This is the finite first-hit event needed to strengthen the paper's Lemma-8
pairwise sentence into a theorem about arbitrary remaining sets.
-/
noncomputable def bestInSetPrefixIndicator {n : ℕ}
    (remaining : Finset (Candidate n)) (k : Fin (n + 1))
    (τ : Ranking n) : ℝ := if bestInSet τ remaining ≤ k.castSucc then 1 else 0

/-- Indicator value of the identity-center prefix ending at `k.castSucc`. -/
noncomputable def centerPrefixValue {n : ℕ} (k : Fin (n + 1))
    (c : Candidate n) : ℝ := if c ≤ k.castSucc then 1 else 0

theorem weaklyOrderedBy_centerPrefixValue {n : ℕ} (k : Fin (n + 1)) :
    WeaklyOrderedBy (Equiv.refl (Candidate n)) (centerPrefixValue k) := by
  intro c d hcd
  unfold centerPrefixValue
  by_cases hd : d ≤ k.castSucc
  · have hc : c ≤ k.castSucc :=
      le_trans (le_of_lt (by simpa [rankOf] using hcd)) hd
    simp [hc, hd]
  · by_cases hc : c ≤ k.castSucc
    · simp [hc, hd]
    · simp [hc, hd]

theorem bestInSetPrefixIndicator_eq_centerPrefixValue
    {n : ℕ} (remaining : Finset (Candidate n)) (k : Fin (n + 1))
    (τ : Ranking n) :
    bestInSetPrefixIndicator remaining k τ =
      centerPrefixValue k (bestInSet τ remaining) := by
  rfl

theorem adjacentSwapImproves_bestInSetPrefixIndicator
    {n : ℕ} {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) (k : Fin (n + 1)) :
    AdjacentSwapImproves (Equiv.refl (Candidate n))
      (bestInSetPrefixIndicator remaining k) := by
  simpa [bestInSetPrefixIndicator, centerPrefixValue] using
    adjacentSwapImproves_bestInSet_value
      (Equiv.refl (Candidate n)) hremaining
      (weaklyOrderedBy_centerPrefixValue k)

theorem prefix_gap_sum_castSucc_step
    {n : ℕ} (value : Candidate n → ℝ) (i : Fin (n + 1)) :
    (∑ k : Fin (n + 1),
        if (i.castSucc : Candidate n) ≤ k.castSucc then
          value k.castSucc - value k.succ
        else
          0) =
      (value i.castSucc - value i.succ) +
        ∑ k : Fin (n + 1),
          if (i.succ : Candidate n) ≤ k.castSucc then
            value k.castSucc - value k.succ
          else
            0 := by
  classical
  rw [Fin.sum_univ_succAbove
      (fun k : Fin (n + 1) =>
        if (i.castSucc : Candidate n) ≤ k.castSucc then
          value k.castSucc - value k.succ
        else
          0) i]
  rw [Fin.sum_univ_succAbove
      (fun k : Fin (n + 1) =>
        if (i.succ : Candidate n) ≤ k.castSucc then
          value k.castSucc - value k.succ
        else
          0) i]
  have hterm_right :
      (if (i.succ : Candidate n) ≤ i.castSucc then
          value i.castSucc - value i.succ
        else
          0) = 0 := by
    rw [if_neg]
    exact not_le_of_gt i.castSucc_lt_succ
  rw [if_pos (le_rfl : (i.castSucc : Candidate n) ≤ i.castSucc),
    hterm_right]
  rw [zero_add]
  have hsum_eq :
      (∑ j : Fin n,
        (if (i.castSucc : Candidate n) ≤ (i.succAbove j).castSucc then
          value (i.succAbove j).castSucc - value (i.succAbove j).succ
        else
          0 : ℝ)) =
        ∑ j : Fin n,
          (if (i.succ : Candidate n) ≤ (i.succAbove j).castSucc then
            value (i.succAbove j).castSucc - value (i.succAbove j).succ
          else
            0 : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    have hiff :
        (i.castSucc : Candidate n) ≤ (i.succAbove j).castSucc ↔
          (i.succ : Candidate n) ≤ (i.succAbove j).castSucc := by
      rw [Fin.castSucc_le_castSucc_iff, Fin.succ_le_castSucc_iff]
      constructor
      · intro hle
        exact lt_of_le_of_ne hle (Fin.ne_succAbove i j)
      · intro hlt
        exact le_of_lt hlt
    by_cases hle : (i.castSucc : Candidate n) ≤ (i.succAbove j).castSucc
    · rw [if_pos hle, if_pos (hiff.mp hle)]
    · rw [if_neg hle, if_neg (by
        intro h
        exact hle (hiff.mpr h))]
  rw [hsum_eq]

/--
Discrete layer-cake identity for a center-ordered finite value profile.

The value of candidate `c` is the worst candidate's value plus adjacent value
gaps over all center prefixes containing `c`.
-/
theorem value_eq_last_add_prefix_gaps
    {n : ℕ} (value : Candidate n → ℝ) (c : Candidate n) :
    value c =
      value (reflLastCandidate n) +
        ∑ k : Fin (n + 1),
          if c ≤ k.castSucc then
            value k.castSucc - value k.succ
          else
            0 := by
  classical
  induction c using Fin.reverseInduction with
  | last =>
      have hsum :
          (∑ k : Fin (n + 1),
            if (Fin.last (n + 1) : Candidate n) ≤ k.castSucc then
              value k.castSucc - value k.succ
            else
              0) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        rw [if_neg]
        exact not_le_of_gt k.castSucc_lt_last
      rw [hsum]
      rw [add_zero]
      apply congrArg value
      ext
      simp [reflLastCandidate]
  | cast i ih =>
      rw [prefix_gap_sum_castSucc_step value i]
      calc
        value i.castSucc =
            value i.succ + (value i.castSucc - value i.succ) := by ring
        _ =
            (value (reflLastCandidate n) +
                ∑ k : Fin (n + 1),
                  if i.succ ≤ k.castSucc then
                    value k.castSucc - value k.succ
                  else
                    0) + (value i.castSucc - value i.succ) := by
              rw [ih]
        _ =
            value (reflLastCandidate n) +
              (value i.castSucc - value i.succ +
                ∑ k : Fin (n + 1),
                  if i.succ ≤ k.castSucc then
                    value k.castSucc - value k.succ
                  else
                    0) := by ring

/--
Layer-cake identity for a single geometric rank power.

For `0 ≤ r ≤ 1`, the adjacent gaps below are nonnegative; the identity itself
is purely algebraic and does not need side conditions.
-/
theorem rankPower_eq_last_add_prefix_gaps
    (n : ℕ) (r : ℝ) (c : Candidate n) :
    r ^ (c : ℕ) =
      r ^ (n + 1) +
        ∑ k : Fin (n + 1),
          if c ≤ k.castSucc then
            r ^ (k : ℕ) - r ^ ((k : ℕ) + 1)
          else
            0 := by
  simpa [reflLastCandidate] using
    (value_eq_last_add_prefix_gaps
      (n := n) (value := fun c : Candidate n => r ^ (c : ℕ)) c)

theorem firstChoice_rankPower_eq_const_add_prefixIndicators
    (n : ℕ) (r : ℝ) (π : Ranking (n + 1)) :
    r ^ ((firstChoice π : Candidate (n + 1)) : ℕ) =
      r ^ (n + 2) +
        ∑ k : Fin (n + 2),
          (r ^ (k : ℕ) - r ^ ((k : ℕ) + 1)) *
            firstChoicePrefixIndicator n k.castSucc π := by
  classical
  rw [rankPower_eq_last_add_prefix_gaps (n + 1) r (firstChoice π)]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k _
  unfold firstChoicePrefixIndicator
  split <;> ring

theorem rankPower_prefix_gap_nonneg
    {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_le_one : r ≤ 1)
    {m : ℕ} (k : Fin m) :
    0 ≤ r ^ (k : ℕ) - r ^ ((k : ℕ) + 1) := by
  have hp : 0 ≤ r ^ (k : ℕ) := pow_nonneg hr_nonneg _
  have hle : r ^ ((k : ℕ) + 1) ≤ r ^ (k : ℕ) := by
    rw [pow_succ]
    exact mul_le_of_le_one_right hp hr_le_one
  exact sub_nonneg.mpr hle

theorem reflMallowsCovariance_firstChoiceGeom_nonneg_of_prefix
    (n : ℕ) (q r : ℝ) (hr_nonneg : 0 ≤ r) (hr_le_one : r ≤ 1)
    (F : Ranking (n + 1) → ℝ)
    (hprefix :
      ∀ k : Fin (n + 2),
        0 ≤
          reflMallowsCovariance (n + 1) q F
            (fun π : Ranking (n + 1) =>
              firstChoicePrefixIndicator n k.castSucc π)) :
    0 ≤
      reflMallowsCovariance (n + 1) q F
        (fun π : Ranking (n + 1) =>
          r ^ ((firstChoice π : Candidate (n + 1)) : ℕ)) := by
  classical
  let G : Ranking (n + 1) → ℝ := fun π =>
    r ^ (n + 2) +
      ∑ k : Fin (n + 2),
        (r ^ (k : ℕ) - r ^ ((k : ℕ) + 1)) *
          firstChoicePrefixIndicator n k.castSucc π
  have hG :
      (fun π : Ranking (n + 1) =>
          r ^ ((firstChoice π : Candidate (n + 1)) : ℕ)) = G := by
    funext π
    exact firstChoice_rankPower_eq_const_add_prefixIndicators n r π
  rw [hG]
  unfold G
  rw [reflMallowsCovariance_add_right,
    reflMallowsCovariance_const_right, zero_add]
  rw [reflMallowsCovariance_finset_sum_right Finset.univ]
  refine Finset.sum_nonneg ?_
  intro k _
  rw [reflMallowsCovariance_mul_const_right]
  exact mul_nonneg
    (rankPower_prefix_gap_nonneg hr_nonneg hr_le_one k)
    (hprefix k)

theorem reflMallowsCovariance_firstChoiceGeom_pos_of_prefix
    (n : ℕ) (q r : ℝ) (hr_nonneg : 0 ≤ r) (hr_le_one : r ≤ 1)
    (F : Ranking (n + 1) → ℝ)
    (hprefix_nonneg :
      ∀ k : Fin (n + 2),
        0 ≤
          reflMallowsCovariance (n + 1) q F
            (fun π : Ranking (n + 1) =>
              firstChoicePrefixIndicator n k.castSucc π))
    (k₀ : Fin (n + 2))
    (hgap_pos : 0 < r ^ (k₀ : ℕ) - r ^ ((k₀ : ℕ) + 1))
    (hprefix_pos :
      0 <
        reflMallowsCovariance (n + 1) q F
          (fun π : Ranking (n + 1) =>
            firstChoicePrefixIndicator n k₀.castSucc π)) :
    0 <
      reflMallowsCovariance (n + 1) q F
        (fun π : Ranking (n + 1) =>
          r ^ ((firstChoice π : Candidate (n + 1)) : ℕ)) := by
  classical
  let G : Ranking (n + 1) → ℝ := fun π =>
    r ^ (n + 2) +
      ∑ k : Fin (n + 2),
        (r ^ (k : ℕ) - r ^ ((k : ℕ) + 1)) *
          firstChoicePrefixIndicator n k.castSucc π
  have hG :
      (fun π : Ranking (n + 1) =>
          r ^ ((firstChoice π : Candidate (n + 1)) : ℕ)) = G := by
    funext π
    exact firstChoice_rankPower_eq_const_add_prefixIndicators n r π
  rw [hG]
  unfold G
  rw [reflMallowsCovariance_add_right,
    reflMallowsCovariance_const_right, zero_add]
  rw [reflMallowsCovariance_finset_sum_right Finset.univ]
  refine Finset.sum_pos' ?nonneg ?pos
  · intro k _
    rw [reflMallowsCovariance_mul_const_right]
    exact mul_nonneg
      (rankPower_prefix_gap_nonneg hr_nonneg hr_le_one k)
      (hprefix_nonneg k)
  · refine ⟨k₀, Finset.mem_univ _, ?_⟩
    rw [reflMallowsCovariance_mul_const_right]
    exact mul_pos hgap_pos hprefix_pos

/-- Unnormalised Mallows mass of the prefix first-hit event. -/
noncomputable def reflMallowsBestInSetPrefixSum
    (n : ℕ) (q : ℝ) (remaining : Finset (Candidate n))
    (k : Fin (n + 1)) : ℝ :=
  reflMallowsPayoffSum n q
    (fun τ : Ranking n => bestInSetPrefixIndicator remaining k τ)

/--
Layer-cake expansion of the unnormalised identity-center Mallows best-in-set
payoff.
-/
theorem reflMallowsPayoffSum_bestInSet_eq_last_add_prefix
    (n : ℕ) (q : ℝ) (value : Candidate n → ℝ)
    (remaining : Finset (Candidate n)) :
    reflMallowsPayoffSum n q
        (fun τ : Ranking n => value (bestInSet τ remaining)) =
      mallowsPartition q (Equiv.refl (Candidate n)) *
          value (reflLastCandidate n) +
        ∑ k : Fin (n + 1),
          (value k.castSucc - value k.succ) *
            reflMallowsBestInSetPrefixSum n q remaining k := by
  classical
  unfold reflMallowsPayoffSum reflMallowsBestInSetPrefixSum
    bestInSetPrefixIndicator
  calc
    (∑ τ : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate n)) τ *
          value (bestInSet τ remaining))
        =
      ∑ τ : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate n)) τ *
          (value (reflLastCandidate n) +
            ∑ k : Fin (n + 1),
              if bestInSet τ remaining ≤ k.castSucc then
                value k.castSucc - value k.succ
              else
                0) := by
          refine Finset.sum_congr rfl ?_
          intro τ _
          rw [value_eq_last_add_prefix_gaps value (bestInSet τ remaining)]
    _ =
      (∑ τ : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate n)) τ *
          value (reflLastCandidate n)) +
        ∑ τ : Ranking n,
          q ^ kendallTau (Equiv.refl (Candidate n)) τ *
            (∑ k : Fin (n + 1),
              if bestInSet τ remaining ≤ k.castSucc then
                value k.castSucc - value k.succ
              else
                0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro τ _
          ring
    _ =
      mallowsPartition q (Equiv.refl (Candidate n)) *
          value (reflLastCandidate n) +
        ∑ τ : Ranking n,
          q ^ kendallTau (Equiv.refl (Candidate n)) τ *
            (∑ k : Fin (n + 1),
              if bestInSet τ remaining ≤ k.castSucc then
                value k.castSucc - value k.succ
              else
                0) := by
          congr 1
          unfold mallowsPartition mallowsWeight
          rw [Finset.sum_mul]
    _ =
      mallowsPartition q (Equiv.refl (Candidate n)) *
          value (reflLastCandidate n) +
        ∑ k : Fin (n + 1),
          (value k.castSucc - value k.succ) *
            (∑ τ : Ranking n,
              q ^ kendallTau (Equiv.refl (Candidate n)) τ *
                if bestInSet τ remaining ≤ k.castSucc then 1 else 0) := by
          congr 1
          calc
            (∑ τ : Ranking n,
              q ^ kendallTau (Equiv.refl (Candidate n)) τ *
                (∑ k : Fin (n + 1),
                  if bestInSet τ remaining ≤ k.castSucc then
                    value k.castSucc - value k.succ
                  else
                    0))
                =
              ∑ τ : Ranking n, ∑ k : Fin (n + 1),
                q ^ kendallTau (Equiv.refl (Candidate n)) τ *
                  (if bestInSet τ remaining ≤ k.castSucc then
                    value k.castSucc - value k.succ
                  else
                    0) := by
                refine Finset.sum_congr rfl ?_
                intro τ _
                rw [Finset.mul_sum]
            _ =
              ∑ k : Fin (n + 1), ∑ τ : Ranking n,
                q ^ kendallTau (Equiv.refl (Candidate n)) τ *
                  (if bestInSet τ remaining ≤ k.castSucc then
                    value k.castSucc - value k.succ
                  else
                    0) := by
                rw [Finset.sum_comm]
            _ =
              ∑ k : Fin (n + 1),
                (value k.castSucc - value k.succ) *
                  (∑ τ : Ranking n,
                    q ^ kendallTau (Equiv.refl (Candidate n)) τ *
                      if bestInSet τ remaining ≤ k.castSucc then 1 else 0) := by
                refine Finset.sum_congr rfl ?_
                intro k _
                calc
                  (∑ τ : Ranking n,
                    q ^ kendallTau (Equiv.refl (Candidate n)) τ *
                      (if bestInSet τ remaining ≤ k.castSucc then
                        value k.castSucc - value k.succ
                      else
                        0))
                      =
                    ∑ τ : Ranking n,
                      (value k.castSucc - value k.succ) *
                        (q ^ kendallTau (Equiv.refl (Candidate n)) τ *
                          if bestInSet τ remaining ≤ k.castSucc then 1 else 0) := by
                      refine Finset.sum_congr rfl ?_
                      intro τ _
                      by_cases hprefix : bestInSet τ remaining ≤ k.castSucc
                      · simp [hprefix]
                        ring
                      · simp [hprefix]
                  _ =
                    (value k.castSucc - value k.succ) *
                      (∑ τ : Ranking n,
                        q ^ kendallTau (Equiv.refl (Candidate n)) τ *
                          if bestInSet τ remaining ≤ k.castSucc then 1 else 0) := by
                      rw [Finset.mul_sum]

/--
Prefix first-hit dominance is sufficient for arbitrary remaining-set expected
utility dominance.  This is the layer-cake bridge for the open non-convex part
of Theorem 4.
-/
theorem reflMallowsPayoffSum_cross_bestInSet_of_prefix
    (n : ℕ) {qMore qLess : ℝ}
    {value : Candidate n → ℝ}
    (hvalue : WeaklyOrderedBy (Equiv.refl (Candidate n)) value)
    (remaining : Finset (Candidate n))
    (hprefix :
      ∀ k : Fin (n + 1),
        0 ≤
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixSum n qMore remaining k -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixSum n qLess remaining k) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate n)) *
          reflMallowsPayoffSum n qMore
            (fun τ : Ranking n => value (bestInSet τ remaining)) -
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          reflMallowsPayoffSum n qLess
            (fun τ : Ranking n => value (bestInSet τ remaining)) := by
  classical
  rw [reflMallowsPayoffSum_bestInSet_eq_last_add_prefix,
    reflMallowsPayoffSum_bestInSet_eq_last_add_prefix]
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let worst : ℝ := value (reflLastCandidate n)
  let gap : Fin (n + 1) → ℝ := fun k => value k.castSucc - value k.succ
  let PMore : Fin (n + 1) → ℝ := fun k =>
    reflMallowsBestInSetPrefixSum n qMore remaining k
  let PLess : Fin (n + 1) → ℝ := fun k =>
    reflMallowsBestInSetPrefixSum n qLess remaining k
  change
    0 ≤
      ZLess * (ZMore * worst + ∑ k : Fin (n + 1), gap k * PMore k) -
        ZMore * (ZLess * worst + ∑ k : Fin (n + 1), gap k * PLess k)
  have hdecomp :
      ZLess * (ZMore * worst + ∑ k : Fin (n + 1), gap k * PMore k) -
          ZMore * (ZLess * worst + ∑ k : Fin (n + 1), gap k * PLess k)
        =
      ∑ k : Fin (n + 1), gap k * (ZLess * PMore k - ZMore * PLess k) := by
    have hcancel :
        ZLess * (ZMore * worst) - ZMore * (ZLess * worst) = 0 := by
      ring
    calc
      ZLess * (ZMore * worst + ∑ k : Fin (n + 1), gap k * PMore k) -
          ZMore * (ZLess * worst + ∑ k : Fin (n + 1), gap k * PLess k)
          =
        (ZLess * (ZMore * worst) - ZMore * (ZLess * worst)) +
          (ZLess * (∑ k : Fin (n + 1), gap k * PMore k) -
            ZMore * (∑ k : Fin (n + 1), gap k * PLess k)) := by
          ring
      _ =
        ZLess * (∑ k : Fin (n + 1), gap k * PMore k) -
          ZMore * (∑ k : Fin (n + 1), gap k * PLess k) := by
          rw [hcancel, zero_add]
      _ =
        ∑ k : Fin (n + 1), gap k * (ZLess * PMore k - ZMore * PLess k) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro k _
          ring
  rw [hdecomp]
  apply Finset.sum_nonneg
  intro k _
  have hgap : 0 ≤ gap k :=
    sub_nonneg.mpr (hvalue (by
      change (k.castSucc : Candidate n) < k.succ
      exact k.castSucc_lt_succ))
  exact mul_nonneg hgap (by simpa [ZLess, ZMore, PMore, PLess] using hprefix k)

/--
Strict layer-cake bridge for arbitrary remaining sets.

If every center-prefix first-hit comparison is weakly positive and at least one
prefix comparison is strictly positive, then a strictly center-ordered value
vector gives a strict cleared payoff comparison.
-/
theorem reflMallowsPayoffSum_cross_bestInSet_pos_of_prefix
    (n : ℕ) {qMore qLess : ℝ}
    {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy (Equiv.refl (Candidate n)) value)
    (remaining : Finset (Candidate n))
    (hprefix_nonneg :
      ∀ k : Fin (n + 1),
        0 ≤
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixSum n qMore remaining k -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixSum n qLess remaining k)
    (hprefix_pos :
      ∃ k : Fin (n + 1),
        0 <
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixSum n qMore remaining k -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixSum n qLess remaining k) :
    0 <
      mallowsPartition qLess (Equiv.refl (Candidate n)) *
          reflMallowsPayoffSum n qMore
            (fun τ : Ranking n => value (bestInSet τ remaining)) -
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          reflMallowsPayoffSum n qLess
            (fun τ : Ranking n => value (bestInSet τ remaining)) := by
  classical
  rw [reflMallowsPayoffSum_bestInSet_eq_last_add_prefix,
    reflMallowsPayoffSum_bestInSet_eq_last_add_prefix]
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let worst : ℝ := value (reflLastCandidate n)
  let gap : Fin (n + 1) → ℝ := fun k => value k.castSucc - value k.succ
  let PMore : Fin (n + 1) → ℝ := fun k =>
    reflMallowsBestInSetPrefixSum n qMore remaining k
  let PLess : Fin (n + 1) → ℝ := fun k =>
    reflMallowsBestInSetPrefixSum n qLess remaining k
  change
    0 <
      ZLess * (ZMore * worst + ∑ k : Fin (n + 1), gap k * PMore k) -
        ZMore * (ZLess * worst + ∑ k : Fin (n + 1), gap k * PLess k)
  have hdecomp :
      ZLess * (ZMore * worst + ∑ k : Fin (n + 1), gap k * PMore k) -
          ZMore * (ZLess * worst + ∑ k : Fin (n + 1), gap k * PLess k)
        =
      ∑ k : Fin (n + 1), gap k * (ZLess * PMore k - ZMore * PLess k) := by
    have hcancel :
        ZLess * (ZMore * worst) - ZMore * (ZLess * worst) = 0 := by
      ring
    calc
      ZLess * (ZMore * worst + ∑ k : Fin (n + 1), gap k * PMore k) -
          ZMore * (ZLess * worst + ∑ k : Fin (n + 1), gap k * PLess k)
          =
        (ZLess * (ZMore * worst) - ZMore * (ZLess * worst)) +
          (ZLess * (∑ k : Fin (n + 1), gap k * PMore k) -
            ZMore * (∑ k : Fin (n + 1), gap k * PLess k)) := by
          ring
      _ =
        ZLess * (∑ k : Fin (n + 1), gap k * PMore k) -
          ZMore * (∑ k : Fin (n + 1), gap k * PLess k) := by
          rw [hcancel, zero_add]
      _ =
        ∑ k : Fin (n + 1), gap k * (ZLess * PMore k - ZMore * PLess k) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro k _
          ring
  rw [hdecomp]
  refine Finset.sum_pos' ?nonneg ?pos
  · intro k _
    have hgap : 0 ≤ gap k :=
      le_of_lt (sub_pos.mpr (hvalue (by
        change (k.castSucc : Candidate n) < k.succ
        exact k.castSucc_lt_succ)))
    exact mul_nonneg hgap
      (by simpa [ZLess, ZMore, PMore, PLess] using hprefix_nonneg k)
  · rcases hprefix_pos with ⟨k, hk⟩
    refine ⟨k, Finset.mem_univ _, ?_⟩
    have hgap : 0 < gap k :=
      sub_pos.mpr (hvalue (by
        change (k.castSucc : Candidate n) < k.succ
        exact k.castSucc_lt_succ))
    exact mul_pos hgap (by simpa [ZLess, ZMore, PMore, PLess] using hk)

/--
Reverse layer-cake extraction: a strict best-in-set payoff cross, together with
weak prefix-cross nonnegativity, forces at least one prefix-cross inequality to
be strict.
-/
theorem exists_prefix_pos_of_payoff_cross_pos
    (n : ℕ) {qMore qLess : ℝ}
    {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy (Equiv.refl (Candidate n)) value)
    (remaining : Finset (Candidate n))
    (hprefix_nonneg :
      ∀ k : Fin (n + 1),
        0 ≤
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixSum n qMore remaining k -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixSum n qLess remaining k)
    (hcross :
      0 <
        mallowsPartition qLess (Equiv.refl (Candidate n)) *
            reflMallowsPayoffSum n qMore
              (fun τ : Ranking n => value (bestInSet τ remaining)) -
          mallowsPartition qMore (Equiv.refl (Candidate n)) *
            reflMallowsPayoffSum n qLess
              (fun τ : Ranking n => value (bestInSet τ remaining))) :
    ∃ k : Fin (n + 1),
      0 <
        mallowsPartition qLess (Equiv.refl (Candidate n)) *
            reflMallowsBestInSetPrefixSum n qMore remaining k -
          mallowsPartition qMore (Equiv.refl (Candidate n)) *
            reflMallowsBestInSetPrefixSum n qLess remaining k := by
  classical
  by_contra hnone
  push Not at hnone
  have hprefix_zero :
      ∀ k : Fin (n + 1),
        mallowsPartition qLess (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixSum n qMore remaining k -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixSum n qLess remaining k = 0 := by
    intro k
    exact le_antisymm (hnone k) (hprefix_nonneg k)
  rw [reflMallowsPayoffSum_bestInSet_eq_last_add_prefix,
    reflMallowsPayoffSum_bestInSet_eq_last_add_prefix] at hcross
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let worst : ℝ := value (reflLastCandidate n)
  let gap : Fin (n + 1) → ℝ := fun k => value k.castSucc - value k.succ
  let PMore : Fin (n + 1) → ℝ := fun k =>
    reflMallowsBestInSetPrefixSum n qMore remaining k
  let PLess : Fin (n + 1) → ℝ := fun k =>
    reflMallowsBestInSetPrefixSum n qLess remaining k
  change
    0 <
      ZLess * (ZMore * worst + ∑ k : Fin (n + 1), gap k * PMore k) -
        ZMore * (ZLess * worst + ∑ k : Fin (n + 1), gap k * PLess k) at hcross
  have hdecomp :
      ZLess * (ZMore * worst + ∑ k : Fin (n + 1), gap k * PMore k) -
          ZMore * (ZLess * worst + ∑ k : Fin (n + 1), gap k * PLess k)
        =
      ∑ k : Fin (n + 1), gap k * (ZLess * PMore k - ZMore * PLess k) := by
    have hcancel :
        ZLess * (ZMore * worst) - ZMore * (ZLess * worst) = 0 := by
      ring
    calc
      ZLess * (ZMore * worst + ∑ k : Fin (n + 1), gap k * PMore k) -
          ZMore * (ZLess * worst + ∑ k : Fin (n + 1), gap k * PLess k)
          =
        (ZLess * (ZMore * worst) - ZMore * (ZLess * worst)) +
          (ZLess * (∑ k : Fin (n + 1), gap k * PMore k) -
            ZMore * (∑ k : Fin (n + 1), gap k * PLess k)) := by
          ring
      _ =
        ZLess * (∑ k : Fin (n + 1), gap k * PMore k) -
          ZMore * (∑ k : Fin (n + 1), gap k * PLess k) := by
          rw [hcancel, zero_add]
      _ =
        ∑ k : Fin (n + 1), gap k * (ZLess * PMore k - ZMore * PLess k) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro k _
          ring
  rw [hdecomp] at hcross
  have hsum_zero :
      (∑ k : Fin (n + 1), gap k * (ZLess * PMore k - ZMore * PLess k)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro k _
    have hk : ZLess * PMore k - ZMore * PLess k = 0 := by
      simpa [ZLess, ZMore, PMore, PLess] using hprefix_zero k
    rw [hk, mul_zero]
  rw [hsum_zero] at hcross
  exact (lt_irrefl (0 : ℝ)) hcross

/--
Generic adjacent-swap stochastic dominance interface for identity-center Mallows
laws.  Closing this interface would lift the pointwise adjacent-correction
property of prefix first-hit events to the full non-convex Theorem 4 bridge.
-/
def ReflMallowsAdjacentStochasticDominance
    (n : ℕ) (qMore qLess : ℝ) : Prop :=
  ∀ F : Ranking n → ℝ,
    AdjacentSwapImproves (Equiv.refl (Candidate n)) F →
      0 ≤
        mallowsPartition qLess (Equiv.refl (Candidate n)) *
            reflMallowsPayoffSum n qMore F -
          mallowsPartition qMore (Equiv.refl (Candidate n)) *
            reflMallowsPayoffSum n qLess F

theorem reflMallowsAdjacentStochasticDominance_of_weakBruhatFirstOrderLe
    {n : ℕ} {qMore qLess : ℝ}
    (hqMore : 0 < qMore) (hqLess : 0 < qLess)
    (hdom :
      ReflMallowsWeakBruhatFirstOrderLe n qMore qLess hqMore hqLess) :
    ReflMallowsAdjacentStochasticDominance n qMore qLess := by
  classical
  intro F hF
  have hnormalized :
      pmfExp (mallowsPMF qLess (Equiv.refl (Candidate n)) hqLess) F ≤
        pmfExp (mallowsPMF qMore (Equiv.refl (Candidate n)) hqMore) F :=
    hdom F (fun π σ hπσ => hF.le_of_weakBruhatLe hπσ)
  rw [pmfExp_mallowsPMF_refl_eq_reflMallowsPayoffSum_div n hqLess F,
    pmfExp_mallowsPMF_refl_eq_reflMallowsPayoffSum_div n hqMore F] at hnormalized
  let SMore : ℝ := reflMallowsPayoffSum n qMore F
  let SLess : ℝ := reflMallowsPayoffSum n qLess F
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  have hZMore_pos : 0 < ZMore := by
    simpa [ZMore] using
      (mallowsPartition_pos (hq := hqMore) (Equiv.refl (Candidate n)))
  have hZLess_pos : 0 < ZLess := by
    simpa [ZLess] using
      (mallowsPartition_pos (hq := hqLess) (Equiv.refl (Candidate n)))
  have hcross : SLess * ZMore ≤ SMore * ZLess := by
    have hmul :=
      mul_le_mul_of_nonneg_right hnormalized
        (le_of_lt (mul_pos hZLess_pos hZMore_pos))
    calc
      SLess * ZMore =
          SLess / ZLess * (ZLess * ZMore) := by
            field_simp [ne_of_gt hZLess_pos]
      _ ≤ SMore / ZMore * (ZLess * ZMore) := hmul
      _ = SMore * ZLess := by
            field_simp [ne_of_gt hZMore_pos]
  change 0 ≤ ZLess * SMore - ZMore * SLess
  linarith

theorem reflMallowsAdjacentStochasticDominance_of_weakBruhatCoupling
    {n : ℕ} {qMore qLess : ℝ}
    {hqMore : 0 < qMore} {hqLess : 0 < qLess}
    (C : ReflMallowsWeakBruhatCoupling n qMore qLess hqMore hqLess) :
    ReflMallowsAdjacentStochasticDominance n qMore qLess :=
  reflMallowsAdjacentStochasticDominance_of_weakBruhatFirstOrderLe
    hqMore hqLess C.firstOrderLe

theorem reflMallowsWeakBruhatFirstOrderLe_of_adjacentStochasticDominance
    {n : ℕ} {qMore qLess : ℝ}
    (hqMore : 0 < qMore) (hqLess : 0 < qLess)
    (hadj : ReflMallowsAdjacentStochasticDominance n qMore qLess) :
    ReflMallowsWeakBruhatFirstOrderLe n qMore qLess hqMore hqLess := by
  classical
  intro F hmono
  have hF :
      AdjacentSwapImproves (Equiv.refl (Candidate n)) F := by
    intro π k hcenter
    exact hmono π
      (swapCandidatePositions π (π k.succ) (π k.castSucc))
      (Relation.ReflTransGen.single ⟨k, hcenter, rfl⟩)
  have hcross := hadj F hF
  rw [pmfExp_mallowsPMF_refl_eq_reflMallowsPayoffSum_div n hqLess F,
    pmfExp_mallowsPMF_refl_eq_reflMallowsPayoffSum_div n hqMore F]
  refine AppliedModelingLib.PositiveDenominator.div_le_div_of_cross_mul_le
    (mallowsPartition_pos (hq := hqLess) (Equiv.refl (Candidate n)))
    (mallowsPartition_pos (hq := hqMore) (Equiv.refl (Candidate n))) ?_
  nlinarith [hcross]

theorem reflMallowsBestInSetPrefixSum_cross_of_adjacentStochasticDominance
    {n : ℕ} {qMore qLess : ℝ}
    (hadj : ReflMallowsAdjacentStochasticDominance n qMore qLess)
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty)
    (k : Fin (n + 1)) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixSum n qMore remaining k -
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixSum n qLess remaining k :=
   hadj
    (bestInSetPrefixIndicator remaining k)
    (adjacentSwapImproves_bestInSetPrefixIndicator hremaining k)

/--
A loose finite rank-index bound for Kendall layers.  The true maximum Kendall
rank is smaller, but the square bound is easy to discharge from the inversion
finset being a subset of the full candidate-pair universe.  Empty extra layers
are harmless in the cross-product layer theorem below.
-/
def kendallTauLayerIndexBound (n : ℕ) : ℕ := (n + 2) * (n + 2)

theorem kendallTau_le_layerIndexBound
    {n : ℕ} (ρ π : Ranking n) :
    kendallTau ρ π ≤ kendallTauLayerIndexBound n := by
  classical
  unfold kendallTau kendallTauLayerIndexBound
  simpa [Candidate, Fintype.card_prod] using
    (Finset.card_le_univ (inversionFinset ρ π))

/-- Kendall rank as an element of the loose finite layer-index type. -/
noncomputable def reflKendallTauLayerIndex
    {n : ℕ} (π : Ranking n) :
    Candidate (kendallTauLayerIndexBound n) :=
  ⟨kendallTau (Equiv.refl (Candidate n)) π, by
    have hle :
        kendallTau (Equiv.refl (Candidate n)) π ≤
          kendallTauLayerIndexBound n :=
      kendallTau_le_layerIndexBound (Equiv.refl (Candidate n)) π
    omega⟩

/-- Rankings in a fixed identity-center Kendall layer. -/
noncomputable def reflKendallTauLayer
    (n : ℕ) (r : Candidate (kendallTauLayerIndexBound n)) :
    Finset (Ranking n) := Finset.univ.filter (fun π : Ranking n => reflKendallTauLayerIndex π = r)

/-- The cardinality of a fixed identity-center Kendall layer, as a real. -/
noncomputable def reflKendallTauLayerCount
    (n : ℕ) (r : Candidate (kendallTauLayerIndexBound n)) : ℝ := ((reflKendallTauLayer n r).card : ℝ)

/-- The unweighted payoff sum over a fixed identity-center Kendall layer. -/
noncomputable def reflKendallTauLayerPayoffSum
    (n : ℕ) (F : Ranking n → ℝ)
    (r : Candidate (kendallTauLayerIndexBound n)) : ℝ := ∑ π ∈ reflKendallTauLayer n r, F π

theorem reflKendallTauLayerIndex_val
    {n : ℕ} (π : Ranking n) :
    (reflKendallTauLayerIndex π : ℕ) =
      kendallTau (Equiv.refl (Candidate n)) π := rfl

theorem reflKendallTauLayerCount_pos_iff_nonempty
    (n : ℕ) (r : Candidate (kendallTauLayerIndexBound n)) :
    0 < reflKendallTauLayerCount n r ↔
      (reflKendallTauLayer n r).Nonempty := by
  constructor
  · intro h
    have hcard : 0 < (reflKendallTauLayer n r).card := by
      rw [reflKendallTauLayerCount] at h
      exact_mod_cast h
    exact Finset.card_pos.mp hcard
  · intro h
    rw [reflKendallTauLayerCount]
    exact_mod_cast (Finset.card_pos.mpr h)

theorem reflKendallTauLayerPayoffSum_eq_zero_of_count_eq_zero
    (n : ℕ) (F : Ranking n → ℝ)
    (r : Candidate (kendallTauLayerIndexBound n))
    (hcount : reflKendallTauLayerCount n r = 0) :
    reflKendallTauLayerPayoffSum n F r = 0 := by
  have hcard : (reflKendallTauLayer n r).card = 0 := by
    rw [reflKendallTauLayerCount] at hcount
    exact_mod_cast hcount
  have hempty : reflKendallTauLayer n r = ∅ := Finset.card_eq_zero.mp hcard
  simp [reflKendallTauLayerPayoffSum, hempty]

theorem reflKendallTauLayer_nonempty_of_le_of_nonempty
    {n : ℕ} {i j : Candidate (kendallTauLayerIndexBound n)}
    (hij : i ≤ j) (hj : (reflKendallTauLayer n j).Nonempty) :
    (reflKendallTauLayer n i).Nonempty := by
  classical
  rcases hj with ⟨π, hπ⟩
  have hidx : reflKendallTauLayerIndex π = j := by
    simpa [reflKendallTauLayer] using (Finset.mem_filter.mp hπ).2
  have htau :
      kendallTau (Equiv.refl (Candidate n)) π = (j : ℕ) := by
    have hval := congrArg Fin.val hidx
    simpa [reflKendallTauLayerIndex] using hval
  have hle_tau :
      (i : ℕ) ≤ kendallTau (Equiv.refl (Candidate n)) π := by
    rw [htau]
    exact hij
  rcases exists_ranking_kendallTau_eq_of_le π hle_tau with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  simp [reflKendallTauLayer]
  apply Fin.ext
  change kendallTau (Equiv.refl (Candidate n)) σ = (i : ℕ)
  exact hσ

theorem reflKendallTauLayerCount_pos_of_le_of_pos
    {n : ℕ} {i j : Candidate (kendallTauLayerIndexBound n)}
    (hij : i ≤ j) (hj : 0 < reflKendallTauLayerCount n j) :
    0 < reflKendallTauLayerCount n i := by
  rw [reflKendallTauLayerCount_pos_iff_nonempty] at hj ⊢
  exact reflKendallTauLayer_nonempty_of_le_of_nonempty hij hj

theorem reflKendallTauLayerPayoffSum_peelBest_raw
    (n : ℕ) (F : Ranking (n + 1) → ℝ)
    (r : Candidate (kendallTauLayerIndexBound (n + 1))) :
    reflKendallTauLayerPayoffSum (n + 1) F r =
      ∑ p : Candidate (n + 1), ∑ σ : Ranking n,
        if (p : ℕ) + kendallTau (Equiv.refl (Candidate n)) σ = (r : ℕ) then
          F (rankingPeelBestOrderEquiv n (p, σ))
        else
          0 := by
  classical
  let e := rankingPeelBestOrderEquiv n
  have hfilter :
      reflKendallTauLayerPayoffSum (n + 1) F r =
        ∑ τ : Ranking (n + 1),
          if reflKendallTauLayerIndex τ = r then F τ else 0 := by
    simp [reflKendallTauLayerPayoffSum, reflKendallTauLayer, Finset.sum_filter]
  rw [hfilter]
  calc
    (∑ τ : Ranking (n + 1),
        if reflKendallTauLayerIndex τ = r then F τ else 0)
        =
      ∑ pe : Candidate (n + 1) × Ranking n,
        if reflKendallTauLayerIndex (e pe) = r then F (e pe) else 0 := by
        simpa [e] using
          (Equiv.sum_comp e
            (fun τ : Ranking (n + 1) =>
              if reflKendallTauLayerIndex τ = r then F τ else 0)).symm
    _ =
      ∑ p : Candidate (n + 1), ∑ σ : Ranking n,
        if reflKendallTauLayerIndex (e (p, σ)) = r then
          F (e (p, σ))
        else
          0 := by
        simpa using
          (Finset.sum_product'
            (Finset.univ : Finset (Candidate (n + 1)))
            (Finset.univ : Finset (Ranking n))
            (fun p σ =>
              if reflKendallTauLayerIndex (e (p, σ)) = r then
                F (e (p, σ))
              else
                0))
    _ =
      ∑ p : Candidate (n + 1), ∑ σ : Ranking n,
        if (p : ℕ) + kendallTau (Equiv.refl (Candidate n)) σ = (r : ℕ) then
          F (rankingPeelBestOrderEquiv n (p, σ))
        else
          0 := by
        refine Finset.sum_congr rfl ?_
        intro p _
        refine Finset.sum_congr rfl ?_
        intro σ _
        have hidx :
            reflKendallTauLayerIndex (e (p, σ)) = r ↔
              (p : ℕ) + kendallTau (Equiv.refl (Candidate n)) σ = (r : ℕ) := by
          constructor
          · intro h
            have hval := congrArg Fin.val h
            simpa [e, reflKendallTauLayerIndex,
              kendallTau_rankingPeelBestOrderEquiv] using hval
          · intro h
            apply Fin.ext
            simpa [e, reflKendallTauLayerIndex,
              kendallTau_rankingPeelBestOrderEquiv] using h
        by_cases h :
            (p : ℕ) + kendallTau (Equiv.refl (Candidate n)) σ = (r : ℕ)
        · rw [if_pos (hidx.mpr h), if_pos h]
        · rw [if_neg (fun hidx_eq => h (hidx.mp hidx_eq)), if_neg h]

theorem reflKendallTauLayerCount_peelBest_raw
    (n : ℕ) (r : Candidate (kendallTauLayerIndexBound (n + 1))) :
    reflKendallTauLayerCount (n + 1) r =
      ∑ p : Candidate (n + 1), ∑ σ : Ranking n,
        if (p : ℕ) + kendallTau (Equiv.refl (Candidate n)) σ = (r : ℕ) then
          (1 : ℝ)
        else
          0 := by
  have h :=
    reflKendallTauLayerPayoffSum_peelBest_raw
      n (fun _ : Ranking (n + 1) => (1 : ℝ)) r
  rw [← h]
  simp [reflKendallTauLayerPayoffSum, reflKendallTauLayerCount]

theorem mallowsPartition_refl_eq_kendallLayerSum
    (n : ℕ) (q : ℝ) :
    mallowsPartition q (Equiv.refl (Candidate n)) =
      ∑ r : Candidate (kendallTauLayerIndexBound n),
        reflKendallTauLayerCount n r * q ^ (r : ℕ) := by
  classical
  unfold mallowsPartition mallowsWeight
  let idx : Ranking n → Candidate (kendallTauLayerIndexBound n) :=
    reflKendallTauLayerIndex
  have hfiber :
      (∑ r : Candidate (kendallTauLayerIndexBound n),
          ∑ π ∈ (Finset.univ.filter fun π : Ranking n => idx π = r),
            q ^ kendallTau (Equiv.refl (Candidate n)) π)
        =
      ∑ π : Ranking n, q ^ kendallTau (Equiv.refl (Candidate n)) π := by
    simpa [idx] using
      (Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset (Ranking n)))
        (t := (Finset.univ :
          Finset (Candidate (kendallTauLayerIndexBound n))))
        (g := idx)
        (by intro π hπ; simp)
        (fun π : Ranking n =>
          q ^ kendallTau (Equiv.refl (Candidate n)) π))
  rw [← hfiber]
  refine Finset.sum_congr rfl ?_
  intro r _
  have hconst :
      ∀ π ∈ (Finset.univ.filter fun π : Ranking n => idx π = r),
        q ^ kendallTau (Equiv.refl (Candidate n)) π = q ^ (r : ℕ) := by
    intro π hπ
    have hidx : idx π = r := (Finset.mem_filter.mp hπ).2
    have hval := congrArg Fin.val hidx
    rw [show kendallTau (Equiv.refl (Candidate n)) π = (r : ℕ) by
      simpa [idx, reflKendallTauLayerIndex] using hval]
  calc
    (∑ π ∈ (Finset.univ.filter fun π : Ranking n => idx π = r),
        q ^ kendallTau (Equiv.refl (Candidate n)) π)
        =
      ∑ π ∈ (Finset.univ.filter fun π : Ranking n => idx π = r),
        q ^ (r : ℕ) :=
          Finset.sum_congr rfl hconst
    _ =
      reflKendallTauLayerCount n r * q ^ (r : ℕ) := by
          simp [reflKendallTauLayerCount, reflKendallTauLayer, idx]

theorem reflMallowsPayoffSum_eq_kendallLayerSum
    (n : ℕ) (q : ℝ) (F : Ranking n → ℝ) :
    reflMallowsPayoffSum n q F =
      ∑ r : Candidate (kendallTauLayerIndexBound n),
        q ^ (r : ℕ) * reflKendallTauLayerPayoffSum n F r := by
  classical
  unfold reflMallowsPayoffSum
  let idx : Ranking n → Candidate (kendallTauLayerIndexBound n) :=
    reflKendallTauLayerIndex
  have hfiber :
      (∑ r : Candidate (kendallTauLayerIndexBound n),
          ∑ π ∈ (Finset.univ.filter fun π : Ranking n => idx π = r),
            q ^ kendallTau (Equiv.refl (Candidate n)) π * F π)
        =
      ∑ π : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate n)) π * F π := by
    simpa [idx] using
      (Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset (Ranking n)))
        (t := (Finset.univ :
          Finset (Candidate (kendallTauLayerIndexBound n))))
        (g := idx)
        (by intro π hπ; simp)
        (fun π : Ranking n =>
          q ^ kendallTau (Equiv.refl (Candidate n)) π * F π))
  rw [← hfiber]
  refine Finset.sum_congr rfl ?_
  intro r _
  have hconst :
      ∀ π ∈ (Finset.univ.filter fun π : Ranking n => idx π = r),
        q ^ kendallTau (Equiv.refl (Candidate n)) π * F π =
          q ^ (r : ℕ) * F π := by
    intro π hπ
    have hidx : idx π = r := (Finset.mem_filter.mp hπ).2
    have hval := congrArg Fin.val hidx
    rw [show kendallTau (Equiv.refl (Candidate n)) π = (r : ℕ) by
      simpa [idx, reflKendallTauLayerIndex] using hval]
  calc
    (∑ π ∈ (Finset.univ.filter fun π : Ranking n => idx π = r),
        q ^ kendallTau (Equiv.refl (Candidate n)) π * F π)
        =
      ∑ π ∈ (Finset.univ.filter fun π : Ranking n => idx π = r),
        q ^ (r : ℕ) * F π :=
          Finset.sum_congr rfl hconst
    _ =
      q ^ (r : ℕ) * reflKendallTauLayerPayoffSum n F r := by
          rw [← Finset.mul_sum]
          simp [reflKendallTauLayerPayoffSum, reflKendallTauLayer, idx]

/--
Rank-layer average antitonicity, stated without division.  For every adjacent
correction-improving payoff, lower Kendall layers have weakly larger average
payoff than higher layers after clearing by the layer cardinalities.
-/
def ReflKendallLayerAverageAnti (n : ℕ) : Prop :=
  ∀ F : Ranking n → ℝ,
    AdjacentSwapImproves (Equiv.refl (Candidate n)) F →
      ∀ i j : Candidate (kendallTauLayerIndexBound n), i < j →
        0 ≤
          reflKendallTauLayerCount n j *
              reflKendallTauLayerPayoffSum n F i -
            reflKendallTauLayerCount n i *
              reflKendallTauLayerPayoffSum n F j

/--
Adjacent rank-layer average antitonicity.  This is the local version of
`ReflKendallLayerAverageAnti`: it asks only for consecutive Kendall layers.
-/
def ReflKendallAdjacentLayerAverageAnti (n : ℕ) : Prop :=
  ∀ F : Ranking n → ℝ,
    AdjacentSwapImproves (Equiv.refl (Candidate n)) F →
      ∀ i j : Candidate (kendallTauLayerIndexBound n),
        (j : ℕ) = (i : ℕ) + 1 →
          0 ≤
            reflKendallTauLayerCount n j *
                reflKendallTauLayerPayoffSum n F i -
              reflKendallTauLayerCount n i *
                reflKendallTauLayerPayoffSum n F j

/--
Consecutive Kendall-layer average antitonicity implies the all-pairs layer
condition.  The proof uses the fact that identity-center Kendall layers have no
internal gaps: once a higher layer is nonempty, every lower layer is nonempty.
-/
theorem reflKendallLayerAverageAnti_of_adjacent
    {n : ℕ}
    (hadj : ReflKendallAdjacentLayerAverageAnti n) :
    ReflKendallLayerAverageAnti n := by
  classical
  intro F hF i j hij
  let m := kendallTauLayerIndexBound n
  let C : Candidate m → ℝ := reflKendallTauLayerCount n
  let S : Candidate m → ℝ := reflKendallTauLayerPayoffSum n F
  change 0 ≤ C j * S i - C i * S j
  have hC_nonneg : ∀ r : Candidate m, 0 ≤ C r := by
    intro r
    dsimp [C, reflKendallTauLayerCount]
    positivity
  have hadjC :
      ∀ a b : Candidate m, (b : ℕ) = (a : ℕ) + 1 →
        0 ≤ C b * S a - C a * S b := by
    intro a b hsucc
    dsimp [C, S]
    exact hadj F hF a b hsucc
  by_cases hjzero : C j = 0
  · have hSj : S j = 0 := by
      dsimp [S]
      exact reflKendallTauLayerPayoffSum_eq_zero_of_count_eq_zero
        n F j (by simpa [C] using hjzero)
    simp [hjzero, hSj]
  · have hjpos : 0 < C j := lt_of_le_of_ne (hC_nonneg j) (Ne.symm hjzero)
    have hchain :
        ∀ b : ℕ, ∀ hb : b < m + 2, 0 < C ⟨b, hb⟩ →
          ∀ a : ℕ, ∀ ha : a < m + 2, a < b →
            0 ≤ C ⟨b, hb⟩ * S ⟨a, ha⟩ -
              C ⟨a, ha⟩ * S ⟨b, hb⟩ := by
      intro b
      induction b using Nat.strong_induction_on with
      | h b ih =>
          intro hb hbpos a ha hab
          by_cases hsucc : b = a + 1
          · exact hadjC ⟨a, ha⟩ ⟨b, hb⟩ hsucc
          · have hbpos_nat : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le a) hab
            let k := b - 1
            have hk_lt_b : k < b := Nat.pred_lt (Nat.ne_of_gt hbpos_nat)
            have hk_succ : k + 1 = b := Nat.succ_pred_eq_of_pos hbpos_nat
            have hk_lt_m : k < m + 2 := lt_trans hk_lt_b hb
            have ha_lt_k : a < k := by
              have : a + 1 < b := by omega
              omega
            have hkpos : 0 < C ⟨k, hk_lt_m⟩ := by
              dsimp [C]
              exact reflKendallTauLayerCount_pos_of_le_of_pos
                (n := n) (i := ⟨k, hk_lt_m⟩) (j := ⟨b, hb⟩)
                (by exact_mod_cast Nat.le_of_lt hk_lt_b)
                (by simpa [C] using hbpos)
            have hleft :
                0 ≤ C ⟨k, hk_lt_m⟩ * S ⟨a, ha⟩ -
                  C ⟨a, ha⟩ * S ⟨k, hk_lt_m⟩ :=
              ih k hk_lt_b hk_lt_m hkpos a ha ha_lt_k
            have hright :
                0 ≤ C ⟨b, hb⟩ * S ⟨k, hk_lt_m⟩ -
                  C ⟨k, hk_lt_m⟩ * S ⟨b, hb⟩ :=
              hadjC ⟨k, hk_lt_m⟩ ⟨b, hb⟩ hk_succ.symm
            have hsum :
                0 ≤
                  C ⟨b, hb⟩ *
                      (C ⟨k, hk_lt_m⟩ * S ⟨a, ha⟩ -
                        C ⟨a, ha⟩ * S ⟨k, hk_lt_m⟩) +
                    C ⟨a, ha⟩ *
                      (C ⟨b, hb⟩ * S ⟨k, hk_lt_m⟩ -
                        C ⟨k, hk_lt_m⟩ * S ⟨b, hb⟩) :=
              add_nonneg
                (mul_nonneg (hC_nonneg ⟨b, hb⟩) hleft)
                (mul_nonneg (hC_nonneg ⟨a, ha⟩) hright)
            have hmul :
                0 ≤
                  C ⟨k, hk_lt_m⟩ *
                    (C ⟨b, hb⟩ * S ⟨a, ha⟩ -
                      C ⟨a, ha⟩ * S ⟨b, hb⟩) := by
              convert hsum using 1
              ring
            have hmul' :
                0 ≤
                  (C ⟨b, hb⟩ * S ⟨a, ha⟩ -
                    C ⟨a, ha⟩ * S ⟨b, hb⟩) * C ⟨k, hk_lt_m⟩ := by
              simpa [mul_comm] using hmul
            exact nonneg_of_mul_nonneg_left hmul' hkpos
    exact hchain j.val j.isLt hjpos i.val i.isLt (by exact hij)

/--
Single-payoff version of the adjacent-layer chaining algebra.  If a fixed
payoff has the cleared average inequality between every consecutive nonempty
identity-center Kendall layer, then it has the inequality between every
lower/higher layer pair.
-/
theorem reflKendallTauLayerPair_cross_nonneg_of_adjacent
    {n : ℕ} (F : Ranking n → ℝ)
    (hadj :
      ∀ i j : Candidate (kendallTauLayerIndexBound n),
        (j : ℕ) = (i : ℕ) + 1 →
          0 ≤
            reflKendallTauLayerCount n j *
                reflKendallTauLayerPayoffSum n F i -
              reflKendallTauLayerCount n i *
                reflKendallTauLayerPayoffSum n F j) :
    ∀ i j : Candidate (kendallTauLayerIndexBound n), i < j →
      0 ≤
        reflKendallTauLayerCount n j *
            reflKendallTauLayerPayoffSum n F i -
          reflKendallTauLayerCount n i *
            reflKendallTauLayerPayoffSum n F j := by
  classical
  intro i j hij
  let m := kendallTauLayerIndexBound n
  let C : Candidate m → ℝ := reflKendallTauLayerCount n
  let S : Candidate m → ℝ := reflKendallTauLayerPayoffSum n F
  change 0 ≤ C j * S i - C i * S j
  have hC_nonneg : ∀ r : Candidate m, 0 ≤ C r := by
    intro r
    dsimp [C, reflKendallTauLayerCount]
    positivity
  have hadjC :
      ∀ a b : Candidate m, (b : ℕ) = (a : ℕ) + 1 →
        0 ≤ C b * S a - C a * S b := by
    intro a b hsucc
    dsimp [C, S]
    exact hadj a b hsucc
  by_cases hjzero : C j = 0
  · have hSj : S j = 0 := by
      dsimp [S]
      exact reflKendallTauLayerPayoffSum_eq_zero_of_count_eq_zero
        n F j (by simpa [C] using hjzero)
    simp [hjzero, hSj]
  · have hjpos : 0 < C j := lt_of_le_of_ne (hC_nonneg j) (Ne.symm hjzero)
    have hchain :
        ∀ b : ℕ, ∀ hb : b < m + 2, 0 < C ⟨b, hb⟩ →
          ∀ a : ℕ, ∀ ha : a < m + 2, a < b →
            0 ≤ C ⟨b, hb⟩ * S ⟨a, ha⟩ -
              C ⟨a, ha⟩ * S ⟨b, hb⟩ := by
      intro b
      induction b using Nat.strong_induction_on with
      | h b ih =>
          intro hb hbpos a ha hab
          by_cases hsucc : b = a + 1
          · exact hadjC ⟨a, ha⟩ ⟨b, hb⟩ hsucc
          · have hbpos_nat : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le a) hab
            let k := b - 1
            have hk_lt_b : k < b := Nat.pred_lt (Nat.ne_of_gt hbpos_nat)
            have hk_succ : k + 1 = b := Nat.succ_pred_eq_of_pos hbpos_nat
            have hk_lt_m : k < m + 2 := lt_trans hk_lt_b hb
            have ha_lt_k : a < k := by
              have : a + 1 < b := by omega
              omega
            have hkpos : 0 < C ⟨k, hk_lt_m⟩ := by
              dsimp [C]
              exact reflKendallTauLayerCount_pos_of_le_of_pos
                (n := n) (i := ⟨k, hk_lt_m⟩) (j := ⟨b, hb⟩)
                (by exact_mod_cast Nat.le_of_lt hk_lt_b)
                (by simpa [C] using hbpos)
            have hleft :
                0 ≤ C ⟨k, hk_lt_m⟩ * S ⟨a, ha⟩ -
                  C ⟨a, ha⟩ * S ⟨k, hk_lt_m⟩ :=
              ih k hk_lt_b hk_lt_m hkpos a ha ha_lt_k
            have hright :
                0 ≤ C ⟨b, hb⟩ * S ⟨k, hk_lt_m⟩ -
                  C ⟨k, hk_lt_m⟩ * S ⟨b, hb⟩ :=
              hadjC ⟨k, hk_lt_m⟩ ⟨b, hb⟩ hk_succ.symm
            have hsum :
                0 ≤
                  C ⟨b, hb⟩ *
                      (C ⟨k, hk_lt_m⟩ * S ⟨a, ha⟩ -
                        C ⟨a, ha⟩ * S ⟨k, hk_lt_m⟩) +
                    C ⟨a, ha⟩ *
                      (C ⟨b, hb⟩ * S ⟨k, hk_lt_m⟩ -
                        C ⟨k, hk_lt_m⟩ * S ⟨b, hb⟩) :=
              add_nonneg
                (mul_nonneg (hC_nonneg ⟨b, hb⟩) hleft)
                (mul_nonneg (hC_nonneg ⟨a, ha⟩) hright)
            have hmul :
                0 ≤
                  C ⟨k, hk_lt_m⟩ *
                    (C ⟨b, hb⟩ * S ⟨a, ha⟩ -
                      C ⟨a, ha⟩ * S ⟨b, hb⟩) := by
              convert hsum using 1
              ring
            have hmul' :
                0 ≤
                  (C ⟨b, hb⟩ * S ⟨a, ha⟩ -
                    C ⟨a, ha⟩ * S ⟨b, hb⟩) * C ⟨k, hk_lt_m⟩ := by
              simpa [mul_comm] using hmul
            exact nonneg_of_mul_nonneg_left hmul' hkpos
    exact hchain j.val j.isLt hjpos i.val i.isLt (by exact hij)

/--
Finite layer-sum comparison from pairwise rank-layer cross-products.  This is
the same weighted-average algebra used for Lemma 4, but with cleared layer sums
instead of explicit averages so that empty Kendall layers cause no side cases.
-/
theorem candidateLayerWeightedSum_cross_nonneg_of_pairwise
    (m : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {C S : Candidate m → ℝ}
    (hlayer :
      ∀ i j : Candidate m, i < j → 0 ≤ C j * S i - C i * S j) :
    0 ≤
      (∑ j : Candidate m, C j * qLess ^ (j : ℕ)) *
          (∑ i : Candidate m, qMore ^ (i : ℕ) * S i) -
        (∑ j : Candidate m, C j * qMore ^ (j : ℕ)) *
          (∑ i : Candidate m, qLess ^ (i : ℕ) * S i) := by
  classical
  let t : Candidate m → Candidate m → ℝ := fun i j =>
    (C i * qLess ^ (i : ℕ)) * (qMore ^ (j : ℕ) * S j) -
      (C i * qMore ^ (i : ℕ)) * (qLess ^ (j : ℕ) * S j)
  have hdouble :
      (∑ j : Candidate m, C j * qLess ^ (j : ℕ)) *
          (∑ i : Candidate m, qMore ^ (i : ℕ) * S i) -
        (∑ j : Candidate m, C j * qMore ^ (j : ℕ)) *
          (∑ i : Candidate m, qLess ^ (i : ℕ) * S i)
        =
      ∑ i : Candidate m, ∑ j : Candidate m, t i j := by
    calc
      (∑ j : Candidate m, C j * qLess ^ (j : ℕ)) *
            (∑ i : Candidate m, qMore ^ (i : ℕ) * S i) -
          (∑ j : Candidate m, C j * qMore ^ (j : ℕ)) *
            (∑ i : Candidate m, qLess ^ (i : ℕ) * S i)
          =
        (∑ i : Candidate m, ∑ j : Candidate m,
            (C i * qLess ^ (i : ℕ)) * (qMore ^ (j : ℕ) * S j)) -
          (∑ i : Candidate m, ∑ j : Candidate m,
            (C i * qMore ^ (i : ℕ)) * (qLess ^ (j : ℕ) * S j)) := by
            rw [Finset.sum_mul, Finset.sum_mul]
            simp_rw [Finset.mul_sum]
      _ = ∑ i : Candidate m, ∑ j : Candidate m, t i j := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [← Finset.sum_sub_distrib]
  rw [hdouble]
  rw [MallowsSpec.pair_sum_eq_ordered_swap_sum
    (Equiv.refl (Candidate m)) t
    (by intro i; simp [t]; ring)]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  by_cases hij_rank :
      rankOf (Equiv.refl (Candidate m)) i <
        rankOf (Equiv.refl (Candidate m)) j
  · have hij : i < j := by
      simpa [rankOf] using hij_rank
    have hpow :
        0 ≤ qMore ^ (i : ℕ) * qLess ^ (j : ℕ) -
          qMore ^ (j : ℕ) * qLess ^ (i : ℕ) :=
      sub_nonneg.mpr (le_of_lt (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          rankPower_mul_lt_mul_rankPower hqMore_pos hq_lt hij))
    have heq :
        t i j + t j i =
          (qMore ^ (i : ℕ) * qLess ^ (j : ℕ) -
              qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
            (C j * S i - C i * S j) := by
      simp [t]
      ring
    rw [if_pos hij_rank, heq]
    exact mul_nonneg hpow (hlayer i j hij)
  · simp [hij_rank]

/--
Rank-layer average antitonicity is sufficient for the open arbitrary-size
identity-center adjacent stochastic dominance theorem.
-/
theorem reflMallowsAdjacentStochasticDominance_of_kendallLayerAverageAnti
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    (hlayers : ReflKendallLayerAverageAnti n) :
    ReflMallowsAdjacentStochasticDominance n qMore qLess := by
  classical
  intro F hF
  have h :=
    candidateLayerWeightedSum_cross_nonneg_of_pairwise
      (kendallTauLayerIndexBound n)
      (qMore := qMore) (qLess := qLess)
      hqMore_pos hq_lt
      (C := reflKendallTauLayerCount n)
      (S := reflKendallTauLayerPayoffSum n F)
      (hlayers F hF)
  rw [mallowsPartition_refl_eq_kendallLayerSum,
    mallowsPartition_refl_eq_kendallLayerSum,
    reflMallowsPayoffSum_eq_kendallLayerSum,
    reflMallowsPayoffSum_eq_kendallLayerSum]
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/--
The same stochastic-dominance bridge can be invoked from the local consecutive
layer condition, using `reflKendallLayerAverageAnti_of_adjacent` to chain
adjacent layers into all lower/higher layer pairs.
-/
theorem reflMallowsAdjacentStochasticDominance_of_adjacent_kendallLayerAverageAnti
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    (hlayers : ReflKendallAdjacentLayerAverageAnti n) :
    ReflMallowsAdjacentStochasticDominance n qMore qLess :=
  reflMallowsAdjacentStochasticDominance_of_kendallLayerAverageAnti
    hqMore_pos hq_lt
    (reflKendallLayerAverageAnti_of_adjacent hlayers)

/--
Prefix cut after deleting a first-choice candidate.  If the deleted center rank
lies before the cut, the cut shifts down by one; otherwise it is unchanged.
-/
def deleteFirstChoicePrefixCut {n : ℕ}
    (r : Candidate (n + 1)) (cut : ℕ) : ℕ := if (r : ℕ) < cut then cut - 1 else cut

theorem succAbove_val_lt_deleteFirstChoicePrefixCut_iff
    {n : ℕ} (r : Candidate (n + 1)) (c : Candidate n) (cut : ℕ) :
    ((r.succAbove c : Candidate (n + 1)) : ℕ) < cut ↔
      (c : ℕ) < deleteFirstChoicePrefixCut r cut := by
  simpa [deleteFirstChoicePrefixCut,
    AppliedModelingLib.SocialChoice.Ranking.deleteFirstChoicePrefixCut] using
    AppliedModelingLib.SocialChoice.Ranking.succAbove_val_lt_deleteFirstChoicePrefixCut_iff
      r c cut

/--
Cut-form first-hit indicator.  This generalizes
`bestInSetPrefixIndicator`: `cut = 0` is the empty prefix and cuts beyond the
candidate universe are the full prefix.
-/
noncomputable def bestInSetPrefixCutIndicator {n : ℕ}
    (remaining : Finset (Candidate n)) (cut : ℕ)
    (τ : Ranking n) : ℝ := if ((bestInSet τ remaining : Candidate n) : ℕ) < cut then 1 else 0

theorem bestInSetPrefixCutIndicator_nonneg {n : ℕ}
    (remaining : Finset (Candidate n)) (cut : ℕ) (τ : Ranking n) :
    0 ≤ bestInSetPrefixCutIndicator remaining cut τ := by
  simpa [bestInSetPrefixCutIndicator,
    AppliedModelingLib.SocialChoice.Ranking.bestInSetPrefixCutIndicator,
    shared_bestInSet_eq] using
    AppliedModelingLib.SocialChoice.Ranking.bestInSetPrefixCutIndicator_nonneg
      remaining cut τ

theorem bestInSetPrefixCutIndicator_le_one {n : ℕ}
    (remaining : Finset (Candidate n)) (cut : ℕ) (τ : Ranking n) :
    bestInSetPrefixCutIndicator remaining cut τ ≤ 1 := by
  simpa [bestInSetPrefixCutIndicator,
    AppliedModelingLib.SocialChoice.Ranking.bestInSetPrefixCutIndicator,
    shared_bestInSet_eq] using
    AppliedModelingLib.SocialChoice.Ranking.bestInSetPrefixCutIndicator_le_one
      remaining cut τ

theorem bestInSetPrefixCutIndicator_eq_zero_or_one {n : ℕ}
    (remaining : Finset (Candidate n)) (cut : ℕ) (τ : Ranking n) :
    bestInSetPrefixCutIndicator remaining cut τ = 0 ∨
      bestInSetPrefixCutIndicator remaining cut τ = 1 := by
  classical
  unfold bestInSetPrefixCutIndicator
  by_cases h : ((bestInSet τ remaining : Candidate n) : ℕ) < cut
  · simp [h]
  · simp [h]

theorem bestInSetPrefixCutIndicator_eq_of_adjacent_cut_not_mem
    {n : ℕ} {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) {k : Candidate n}
    (hk : k ∉ remaining) (τ : Ranking n) :
    bestInSetPrefixCutIndicator remaining (k : ℕ) τ =
      bestInSetPrefixCutIndicator remaining ((k : ℕ) + 1) τ := by
  simpa [bestInSetPrefixCutIndicator,
    AppliedModelingLib.SocialChoice.Ranking.bestInSetPrefixCutIndicator,
    shared_bestInSet_eq] using
    AppliedModelingLib.SocialChoice.Ranking.bestInSetPrefixCutIndicator_eq_of_adjacent_cut_not_mem
      hremaining hk τ

/-- Cut-form prefix value in identity-center coordinates. -/
noncomputable def centerPrefixCutValue {n : ℕ} (cut : ℕ)
    (c : Candidate n) : ℝ := if (c : ℕ) < cut then 1 else 0

theorem weaklyOrderedBy_centerPrefixCutValue {n : ℕ} (cut : ℕ) :
    WeaklyOrderedBy (Equiv.refl (Candidate n)) (centerPrefixCutValue cut) := by
  intro c d hcd
  have hle :=
    AppliedModelingLib.SocialChoice.Ranking.weaklyOrderedBy_centerPrefixCutValue
      (n := n) (cut := cut) (a := c) (b := d)
      (by simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hcd)
  simpa [centerPrefixCutValue,
    AppliedModelingLib.SocialChoice.Ranking.centerPrefixCutValue] using hle

theorem bestInSetPrefixCutIndicator_eq_centerPrefixCutValue
    {n : ℕ} (remaining : Finset (Candidate n)) (cut : ℕ)
    (τ : Ranking n) :
    bestInSetPrefixCutIndicator remaining cut τ =
      centerPrefixCutValue cut (bestInSet τ remaining) := by
  simpa [bestInSetPrefixCutIndicator, centerPrefixCutValue,
    AppliedModelingLib.SocialChoice.Ranking.bestInSetPrefixCutIndicator,
    AppliedModelingLib.SocialChoice.Ranking.centerPrefixCutValue,
    shared_bestInSet_eq] using
    AppliedModelingLib.SocialChoice.Ranking.bestInSetPrefixCutIndicator_eq_centerPrefixCutValue
      remaining cut τ

theorem adjacentSwapImproves_bestInSetPrefixCutIndicator
    {n : ℕ} {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) (cut : ℕ) :
    AdjacentSwapImproves (Equiv.refl (Candidate n))
      (bestInSetPrefixCutIndicator remaining cut) := by
  intro π k hcenter
  simpa [bestInSetPrefixCutIndicator,
    AppliedModelingLib.SocialChoice.Ranking.bestInSetPrefixCutIndicator,
    shared_bestInSet_eq, shared_swapCandidatePositions_eq] using
    AppliedModelingLib.SocialChoice.Ranking.adjacentSwapImproves_bestInSetPrefixCutIndicator
      (remaining := remaining) hremaining cut π k
      (by simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hcenter)

/--
Tail event produced by peeling the center-best candidate `0` when `0` remains.
If the tail best remaining candidate appears before the inserted `0`, use the
tail prefix event; otherwise the inserted `0` is the first remaining candidate.
-/
noncomputable def bestInSetPrefixCutBeforeInsertIndicator {n : ℕ}
    (remaining : Finset (Candidate n)) (cut : ℕ)
    (p : Candidate (n + 1)) (σ : Ranking n) : ℝ :=
  if hremaining : remaining.Nonempty then
    if (rankOf σ (bestInSet σ remaining)).castSucc < p then
      bestInSetPrefixCutIndicator remaining cut σ
    else
      1
  else
    1

/-- Unified peel-best branch value for the cut-form prefix first-hit event. -/
noncomputable def bestInSetPrefixCutPeelBestIndicator {n : ℕ}
    (remaining : Finset (Candidate (n + 1))) (cut : ℕ)
    (p : Candidate (n + 1)) (σ : Ranking n) : ℝ :=
  if (0 : Candidate (n + 1)) ∈ remaining then
    if cut = 0 then
      0
    else
      bestInSetPrefixCutBeforeInsertIndicator
        (tailRemainingOf remaining) (cut - 1) p σ
  else
    bestInSetPrefixCutIndicator
      (tailRemainingOf remaining) (cut - 1) σ

theorem bestInSetPrefixCutIndicator_rankingPeelBestOrderEquiv_of_zero_mem
    {n : ℕ} {remaining : Finset (Candidate (n + 1))}
    (hzero : (0 : Candidate (n + 1)) ∈ remaining)
    {cut : ℕ} (hcut : 0 < cut)
    (p : Candidate (n + 1)) (σ : Ranking n) :
    bestInSetPrefixCutIndicator remaining cut
        (rankingPeelBestOrderEquiv n (p, σ)) =
      bestInSetPrefixCutBeforeInsertIndicator
        (tailRemainingOf remaining) (cut - 1) p σ := by
  classical
  let tail : Finset (Candidate n) := tailRemainingOf remaining
  by_cases htail : tail.Nonempty
  · by_cases hbefore :
        (rankOf σ (bestInSet σ tail)).castSucc < p
    · have hbest :=
        bestInSet_rankingPeelBestOrderEquiv_of_zero_mem_tail_before
          (n := n) (p := p) (σ := σ) (remaining := remaining)
          hzero (by simpa [tail] using htail) (by simpa [tail] using hbefore)
      unfold bestInSetPrefixCutIndicator
      rw [hbest]
      unfold bestInSetPrefixCutBeforeInsertIndicator
      rw [dif_pos htail, if_pos hbefore]
      unfold bestInSetPrefixCutIndicator
      have hiff :
          (((bestInSet σ tail).succ : Candidate (n + 1)) : ℕ) < cut ↔
            ((bestInSet σ tail : Candidate n) : ℕ) < cut - 1 := by
        change (bestInSet σ tail).val + 1 < cut ↔
          (bestInSet σ tail).val < cut - 1
        omega
      by_cases hb : ((bestInSet σ tail : Candidate n) : ℕ) < cut - 1
      · rw [if_pos (hiff.mpr hb), if_pos hb]
      · rw [if_neg (fun h => hb (hiff.mp h)), if_neg hb]
    · have hbest :=
        bestInSet_rankingPeelBestOrderEquiv_of_zero_mem_tail_not_before
          (n := n) (p := p) (σ := σ) (remaining := remaining)
          hzero (by simpa [tail] using htail) (by simpa [tail] using hbefore)
      unfold bestInSetPrefixCutIndicator
      rw [hbest, if_pos (by simpa using hcut)]
      unfold bestInSetPrefixCutBeforeInsertIndicator
      rw [dif_pos htail, if_neg hbefore]
  · have hbest :
        bestInSet (rankingPeelBestOrderEquiv n (p, σ)) remaining =
          (0 : Candidate (n + 1)) := by
      refine bestInSet_eq_of_forall_rank_le
        (rankingPeelBestOrderEquiv n (p, σ)) remaining hzero ?_
      intro e he
      cases e using Fin.cases with
      | zero =>
          simp
      | succ a =>
          have ha : a ∈ tail := by
            simpa [tail] using he
          exact False.elim (htail ⟨a, ha⟩)
    unfold bestInSetPrefixCutIndicator
    rw [hbest, if_pos (by simpa using hcut)]
    unfold bestInSetPrefixCutBeforeInsertIndicator
    rw [dif_neg htail]

theorem bestInSetPrefixCutIndicator_rankingPeelBestOrderEquiv_of_zero_not_mem
    {n : ℕ} {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hzero : (0 : Candidate (n + 1)) ∉ remaining)
    (cut : ℕ) (p : Candidate (n + 1)) (σ : Ranking n) :
    bestInSetPrefixCutIndicator remaining cut
        (rankingPeelBestOrderEquiv n (p, σ)) =
      bestInSetPrefixCutIndicator
        (tailRemainingOf remaining) (cut - 1) σ := by
  classical
  have hbest :=
    bestInSet_rankingPeelBestOrderEquiv_of_zero_not_mem
      (n := n) p σ hremaining hzero
  unfold bestInSetPrefixCutIndicator
  rw [hbest]
  have hiff :
      ((((bestInSet σ (tailRemainingOf remaining)).succ) :
          Candidate (n + 1)) : ℕ) < cut ↔
        (((bestInSet σ (tailRemainingOf remaining)) :
          Candidate n) : ℕ) < cut - 1 := by
    change (bestInSet σ (tailRemainingOf remaining)).val + 1 < cut ↔
      (bestInSet σ (tailRemainingOf remaining)).val < cut - 1
    omega
  by_cases htail_cut :
      (((bestInSet σ (tailRemainingOf remaining)) :
        Candidate n) : ℕ) < cut - 1
  · rw [if_pos (hiff.mpr htail_cut), if_pos htail_cut]
  · rw [if_neg (fun h => htail_cut (hiff.mp h)), if_neg htail_cut]

theorem bestInSetPrefixCutIndicator_rankingPeelBestOrderEquiv
    {n : ℕ} {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (cut : ℕ) (p : Candidate (n + 1)) (σ : Ranking n) :
    bestInSetPrefixCutIndicator remaining cut
        (rankingPeelBestOrderEquiv n (p, σ)) =
      bestInSetPrefixCutPeelBestIndicator remaining cut p σ := by
  classical
  unfold bestInSetPrefixCutPeelBestIndicator
  by_cases hzero : (0 : Candidate (n + 1)) ∈ remaining
  · rw [if_pos hzero]
    by_cases hcut0 : cut = 0
    · rw [if_pos hcut0]
      unfold bestInSetPrefixCutIndicator
      simp [hcut0]
    · rw [if_neg hcut0]
      exact
        bestInSetPrefixCutIndicator_rankingPeelBestOrderEquiv_of_zero_mem
          (n := n) (remaining := remaining) hzero
          (cut := cut) (Nat.pos_of_ne_zero hcut0) p σ
  · rw [if_neg hzero]
    exact
      bestInSetPrefixCutIndicator_rankingPeelBestOrderEquiv_of_zero_not_mem
        (n := n) (remaining := remaining) hremaining hzero cut p σ

theorem reflKendallTauLayerPayoffSum_prefix_peelBest_raw
    (n : ℕ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ)
    (r : Candidate (kendallTauLayerIndexBound (n + 1))) :
    reflKendallTauLayerPayoffSum (n + 1)
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ) r =
      ∑ p : Candidate (n + 1), ∑ σ : Ranking n,
        if (p : ℕ) + kendallTau (Equiv.refl (Candidate n)) σ = (r : ℕ) then
          bestInSetPrefixCutPeelBestIndicator remaining cut p σ
        else
          0 := by
  classical
  rw [reflKendallTauLayerPayoffSum_peelBest_raw]
  refine Finset.sum_congr rfl ?_
  intro p _
  refine Finset.sum_congr rfl ?_
  intro σ _
  by_cases h :
      (p : ℕ) + kendallTau (Equiv.refl (Candidate n)) σ = (r : ℕ)
  · rw [if_pos h, if_pos h]
    exact bestInSetPrefixCutIndicator_rankingPeelBestOrderEquiv
      hremaining cut p σ
  · rw [if_neg h, if_neg h]

theorem bestInSetPrefixCutPeelBestIndicator_anti_position
    {n : ℕ} {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ) (σ : Ranking n)
    {p r : Candidate (n + 1)} (hpr : p < r) :
    bestInSetPrefixCutPeelBestIndicator remaining cut r σ ≤
      bestInSetPrefixCutPeelBestIndicator remaining cut p σ := by
  classical
  let F : Ranking (n + 1) → ℝ := fun τ =>
    bestInSetPrefixCutIndicator remaining cut τ
  have hF : AdjacentSwapImproves (Equiv.refl (Candidate (n + 1))) F :=
    adjacentSwapImproves_bestInSetPrefixCutIndicator hremaining cut
  have hpoint :
      F (rankingPeelBestOrderEquiv n (r, σ)) ≤
        F (rankingPeelBestOrderEquiv n (p, σ)) :=
    rankingPeelBestOrderEquiv_position_anti_of_adjacentSwapImproves
      (n := n) (F := F) hF σ hpr
  simpa [F,
    bestInSetPrefixCutIndicator_rankingPeelBestOrderEquiv hremaining cut r σ,
    bestInSetPrefixCutIndicator_rankingPeelBestOrderEquiv hremaining cut p σ]
    using hpoint

theorem bestInSetPrefixCutPeelBestIndicator_of_zero_not_mem
    {n : ℕ} {remaining : Finset (Candidate (n + 1))}
    (hzero : (0 : Candidate (n + 1)) ∉ remaining)
    (cut : ℕ) (p : Candidate (n + 1)) (σ : Ranking n) :
    bestInSetPrefixCutPeelBestIndicator remaining cut p σ =
      bestInSetPrefixCutIndicator
        (tailRemainingOf remaining) (cut - 1) σ := by
  unfold bestInSetPrefixCutPeelBestIndicator
  rw [if_neg hzero]

theorem bestInSetPrefixIndicator_eq_cut
    {n : ℕ} (remaining : Finset (Candidate n)) (k : Fin (n + 1))
    (τ : Ranking n) :
    bestInSetPrefixIndicator remaining k τ =
      bestInSetPrefixCutIndicator remaining (k.val + 1) τ := by
  unfold bestInSetPrefixIndicator bestInSetPrefixCutIndicator
  have hiff :
      bestInSet τ remaining ≤ k.castSucc ↔
        ((bestInSet τ remaining : Candidate n) : ℕ) < k.val + 1 := by
    rw [Fin.le_iff_val_le_val]
    change ((bestInSet τ remaining : Candidate n).val ≤ k.val) ↔
      ((bestInSet τ remaining : Candidate n).val < k.val + 1)
    omega
  by_cases h : bestInSet τ remaining ≤ k.castSucc
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (by
      intro hcut
      exact h (hiff.mpr hcut))]

/-- Unnormalised Mallows mass of the cut-form prefix first-hit event. -/
noncomputable def reflMallowsBestInSetPrefixCutSum
    (n : ℕ) (q : ℝ) (remaining : Finset (Candidate n))
    (cut : ℕ) : ℝ :=
  reflMallowsPayoffSum n q
    (fun τ : Ranking n => bestInSetPrefixCutIndicator remaining cut τ)

theorem reflMallowsBestInSetPrefixCutSum_nonneg
    (n : ℕ) {q : ℝ} (hq_nonneg : 0 ≤ q)
    (remaining : Finset (Candidate n)) (cut : ℕ) :
    0 ≤ reflMallowsBestInSetPrefixCutSum n q remaining cut := by
  classical
  unfold reflMallowsBestInSetPrefixCutSum reflMallowsPayoffSum
  exact Finset.sum_nonneg (by
    intro τ _
    exact mul_nonneg
      (pow_nonneg hq_nonneg _)
      (bestInSetPrefixCutIndicator_nonneg remaining cut τ))

theorem reflMallowsBestInSetPrefixCutSum_le_partition
    (n : ℕ) {q : ℝ} (hq_nonneg : 0 ≤ q)
    (remaining : Finset (Candidate n)) (cut : ℕ) :
    reflMallowsBestInSetPrefixCutSum n q remaining cut ≤
      mallowsPartition q (Equiv.refl (Candidate n)) := by
  classical
  unfold reflMallowsBestInSetPrefixCutSum reflMallowsPayoffSum
    mallowsPartition mallowsWeight
  refine Finset.sum_le_sum ?_
  intro τ _
  have hweight : 0 ≤ q ^ kendallTau (Equiv.refl (Candidate n)) τ :=
    pow_nonneg hq_nonneg _
  have hindicator := bestInSetPrefixCutIndicator_le_one remaining cut τ
  calc
    q ^ kendallTau (Equiv.refl (Candidate n)) τ *
        bestInSetPrefixCutIndicator remaining cut τ
        ≤ q ^ kendallTau (Equiv.refl (Candidate n)) τ * 1 :=
          mul_le_mul_of_nonneg_left hindicator hweight
    _ = q ^ kendallTau (Equiv.refl (Candidate n)) τ := by ring

theorem reflMallowsBestInSetPrefixCutSum_eq_sum_bestInSetWeight
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) (cut : ℕ) :
    reflMallowsBestInSetPrefixCutSum n q remaining cut =
      ∑ c : Candidate n,
        if ((c : Candidate n) : ℕ) < cut then
          reflMallowsBestInSetWeight n q remaining c
        else
          0 := by
  classical
  unfold reflMallowsBestInSetPrefixCutSum reflMallowsBestInSetWeight
    reflMallowsPayoffSum
  calc
    (∑ τ : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate n)) τ *
          bestInSetPrefixCutIndicator remaining cut τ)
        =
      ∑ τ : Ranking n, ∑ c : Candidate n,
        if c = bestInSet τ remaining then
          q ^ kendallTau (Equiv.refl (Candidate n)) τ *
            bestInSetPrefixCutIndicator remaining cut τ
        else
          0 := by
        refine Finset.sum_congr rfl ?_
        intro τ _
        simpa using
          (Finset.sum_ite_eq' Finset.univ (bestInSet τ remaining)
            (fun _ : Candidate n =>
              q ^ kendallTau (Equiv.refl (Candidate n)) τ *
                bestInSetPrefixCutIndicator remaining cut τ)).symm
    _ =
      ∑ c : Candidate n, ∑ τ : Ranking n,
        if c = bestInSet τ remaining then
          q ^ kendallTau (Equiv.refl (Candidate n)) τ *
            bestInSetPrefixCutIndicator remaining cut τ
        else
          0 := by
        rw [Finset.sum_comm]
    _ =
      ∑ c : Candidate n,
        if ((c : Candidate n) : ℕ) < cut then
          ∑ τ : Ranking n,
            q ^ kendallTau (Equiv.refl (Candidate n)) τ *
              (if c = bestInSet τ remaining then (1 : ℝ) else 0)
        else
          0 := by
        refine Finset.sum_congr rfl ?_
        intro c _
        by_cases hc_cut : ((c : Candidate n) : ℕ) < cut
        · rw [if_pos hc_cut]
          refine Finset.sum_congr rfl ?_
          intro τ _
          by_cases hbest : c = bestInSet τ remaining
          · rw [if_pos hbest, if_pos hbest]
            unfold bestInSetPrefixCutIndicator
            have hbest_cut :
                ((bestInSet τ remaining : Candidate n) : ℕ) < cut := by
              simpa [hbest] using hc_cut
            simp [hbest_cut]
          · simp [hbest]
        · rw [if_neg hc_cut]
          apply Finset.sum_eq_zero
          intro τ _
          by_cases hbest : c = bestInSet τ remaining
          · rw [if_pos hbest]
            unfold bestInSetPrefixCutIndicator
            have hbest_not_cut :
                ¬ ((bestInSet τ remaining : Candidate n) : ℕ) < cut := by
              simpa [hbest] using hc_cut
            simp [hbest_not_cut]
          · simp [hbest]

theorem reflMallowsBestInSetPrefixCutSum_eq_of_adjacent_cut_not_mem
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) {k : Candidate n}
    (hk : k ∉ remaining) :
    reflMallowsBestInSetPrefixCutSum n q remaining (k : ℕ) =
      reflMallowsBestInSetPrefixCutSum n q remaining ((k : ℕ) + 1) := by
  classical
  unfold reflMallowsBestInSetPrefixCutSum reflMallowsPayoffSum
  refine Finset.sum_congr rfl ?_
  intro τ _
  have hind :
      bestInSetPrefixCutIndicator remaining (k : ℕ) τ =
        bestInSetPrefixCutIndicator remaining ((k : ℕ) + 1) τ :=
    bestInSetPrefixCutIndicator_eq_of_adjacent_cut_not_mem
      hremaining hk τ
  simpa using congrArg
    (fun x : ℝ => q ^ kendallTau (Equiv.refl (Candidate n)) τ * x) hind

theorem reflMallowsBestInSetPrefixCutSum_peelBest
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ) :
    reflMallowsBestInSetPrefixCutSum (n + 1) q remaining cut =
      ∑ p : Candidate (n + 1),
        q ^ (p : ℕ) *
          reflMallowsPayoffSum n q
            (fun σ : Ranking n =>
              bestInSetPrefixCutPeelBestIndicator remaining cut p σ) := by
  classical
  unfold reflMallowsBestInSetPrefixCutSum
  rw [reflMallowsPayoffSum_peelBest n q]
  refine Finset.sum_congr rfl ?_
  intro p _
  congr 1
  unfold reflMallowsPayoffSum
  refine Finset.sum_congr rfl ?_
  intro σ _
  change
    q ^ kendallTau (Equiv.refl (Candidate n)) σ *
        bestInSetPrefixCutIndicator remaining cut
          (rankingPeelBestOrderEquiv n (p, σ)) =
      q ^ kendallTau (Equiv.refl (Candidate n)) σ *
        bestInSetPrefixCutPeelBestIndicator remaining cut p σ
  rw [bestInSetPrefixCutIndicator_rankingPeelBestOrderEquiv
    hremaining cut p σ]

theorem reflMallowsPayoffSum_prefix_peelBest_branch_eq
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ)
    (p : Candidate (n + 1)) :
    reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          bestInSetPrefixCutIndicator remaining cut
            (rankingPeelBestOrderEquiv n (p, σ))) =
      reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          bestInSetPrefixCutPeelBestIndicator remaining cut p σ) := by
  classical
  unfold reflMallowsPayoffSum
  refine Finset.sum_congr rfl ?_
  intro σ _
  change
    q ^ kendallTau (Equiv.refl (Candidate n)) σ *
        bestInSetPrefixCutIndicator remaining cut
          (rankingPeelBestOrderEquiv n (p, σ)) =
      q ^ kendallTau (Equiv.refl (Candidate n)) σ *
        bestInSetPrefixCutPeelBestIndicator remaining cut p σ
  rw [bestInSetPrefixCutIndicator_rankingPeelBestOrderEquiv
    hremaining cut p σ]

theorem reflMallowsBestInSetPrefixCutSum_cross_of_adjacentStochasticDominance
    {n : ℕ} {qMore qLess : ℝ}
    (hadj : ReflMallowsAdjacentStochasticDominance n qMore qLess)
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty)
    (cut : ℕ) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixCutSum n qMore remaining cut -
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixCutSum n qLess remaining cut :=
   hadj
    (bestInSetPrefixCutIndicator remaining cut)
    (adjacentSwapImproves_bestInSetPrefixCutIndicator hremaining cut)

/--
Prefix-event Kendall-layer average antitonicity, stated without division.

Unlike `ReflKendallLayerAverageAnti`, this only asks for the first-hit prefix
events that actually feed the remaining-set utility layer-cake proof for
Theorem 4.
-/
def ReflKendallPrefixLayerAverageAnti (n : ℕ) : Prop :=
  ∀ remaining : Finset (Candidate n), remaining.Nonempty → ∀ cut : ℕ,
    ∀ i j : Candidate (kendallTauLayerIndexBound n), i < j →
      0 ≤
        reflKendallTauLayerCount n j *
            reflKendallTauLayerPayoffSum n
              (fun τ : Ranking n =>
                bestInSetPrefixCutIndicator remaining cut τ) i -
          reflKendallTauLayerCount n i *
            reflKendallTauLayerPayoffSum n
              (fun τ : Ranking n =>
                bestInSetPrefixCutIndicator remaining cut τ) j

/--
Adjacent version of `ReflKendallPrefixLayerAverageAnti`: it is enough to check
consecutive Kendall layers for each prefix first-hit event.
-/
def ReflKendallAdjacentPrefixLayerAverageAnti (n : ℕ) : Prop :=
  ∀ remaining : Finset (Candidate n), remaining.Nonempty → ∀ cut : ℕ,
    ∀ i j : Candidate (kendallTauLayerIndexBound n),
      (j : ℕ) = (i : ℕ) + 1 →
        0 ≤
          reflKendallTauLayerCount n j *
              reflKendallTauLayerPayoffSum n
                (fun τ : Ranking n =>
                  bestInSetPrefixCutIndicator remaining cut τ) i -
            reflKendallTauLayerCount n i *
              reflKendallTauLayerPayoffSum n
                (fun τ : Ranking n =>
                  bestInSetPrefixCutIndicator remaining cut τ) j

theorem reflKendallPrefixLayerAverageAnti_of_adjacent
    {n : ℕ}
    (hlayers : ReflKendallAdjacentPrefixLayerAverageAnti n) :
    ReflKendallPrefixLayerAverageAnti n := by
  intro remaining hremaining cut i j hij
  exact
    reflKendallTauLayerPair_cross_nonneg_of_adjacent
      (n := n)
      (F := fun τ : Ranking n =>
        bestInSetPrefixCutIndicator remaining cut τ)
      (by
        intro a b hsucc
        exact hlayers remaining hremaining cut a b hsucc)
      i j hij

theorem reflMallowsBestInSetPrefixCutSum_cross_of_kendallPrefixLayerAverageAnti
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    (hlayers : ReflKendallPrefixLayerAverageAnti n)
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty)
    (cut : ℕ) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixCutSum n qMore remaining cut -
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixCutSum n qLess remaining cut := by
  classical
  let F : Ranking n → ℝ := fun τ =>
    bestInSetPrefixCutIndicator remaining cut τ
  have h :=
    candidateLayerWeightedSum_cross_nonneg_of_pairwise
      (kendallTauLayerIndexBound n)
      (qMore := qMore) (qLess := qLess)
      hqMore_pos hq_lt
      (C := reflKendallTauLayerCount n)
      (S := reflKendallTauLayerPayoffSum n F)
      (by
        intro i j hij
        simpa [F] using hlayers remaining hremaining cut i j hij)
  change
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate n)) *
          reflMallowsPayoffSum n qMore F -
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          reflMallowsPayoffSum n qLess F
  rw [mallowsPartition_refl_eq_kendallLayerSum,
    mallowsPartition_refl_eq_kendallLayerSum,
    reflMallowsPayoffSum_eq_kendallLayerSum,
    reflMallowsPayoffSum_eq_kendallLayerSum]
  simpa [reflMallowsBestInSetPrefixCutSum, F, mul_comm, mul_left_comm,
    mul_assoc] using h

theorem reflMallowsBestInSetPrefixCutSum_cross_of_adjacent_kendallPrefixLayerAverageAnti
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    (hlayers : ReflKendallAdjacentPrefixLayerAverageAnti n)
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty)
    (cut : ℕ) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixCutSum n qMore remaining cut -
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixCutSum n qLess remaining cut :=
  reflMallowsBestInSetPrefixCutSum_cross_of_kendallPrefixLayerAverageAnti
    hqMore_pos hq_lt
    (reflKendallPrefixLayerAverageAnti_of_adjacent hlayers)
    hremaining cut

theorem bestInSetPrefixCutIndicator_eq_one_of_forall_remaining_lt
    {n : ℕ} {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    (hcut : ∀ c : Candidate n, c ∈ remaining → (c : ℕ) < cut)
    (τ : Ranking n) :
    bestInSetPrefixCutIndicator remaining cut τ = 1 := by
  unfold bestInSetPrefixCutIndicator
  rw [if_pos]
  exact hcut (bestInSet τ remaining) (bestInSet_mem τ hremaining)

theorem bestInSetPrefixCutIndicator_eq_zero_of_forall_remaining_ge
    {n : ℕ} {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    (hcut : ∀ c : Candidate n, c ∈ remaining → cut ≤ (c : ℕ))
    (τ : Ranking n) :
    bestInSetPrefixCutIndicator remaining cut τ = 0 := by
  unfold bestInSetPrefixCutIndicator
  rw [if_neg]
  exact not_lt_of_ge
    (hcut (bestInSet τ remaining) (bestInSet_mem τ hremaining))

theorem reflKendallTauLayerPayoffSum_prefix_eq_count_of_forall_remaining_lt
    (n : ℕ) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    (hcut : ∀ c : Candidate n, c ∈ remaining → (c : ℕ) < cut)
    (r : Candidate (kendallTauLayerIndexBound n)) :
    reflKendallTauLayerPayoffSum n
        (fun τ : Ranking n => bestInSetPrefixCutIndicator remaining cut τ) r =
      reflKendallTauLayerCount n r := by
  classical
  rw [reflKendallTauLayerPayoffSum, reflKendallTauLayerCount]
  simp [bestInSetPrefixCutIndicator_eq_one_of_forall_remaining_lt
    hremaining hcut]

theorem reflKendallTauLayerPayoffSum_prefix_eq_zero_of_forall_remaining_ge
    (n : ℕ) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    (hcut : ∀ c : Candidate n, c ∈ remaining → cut ≤ (c : ℕ))
    (r : Candidate (kendallTauLayerIndexBound n)) :
    reflKendallTauLayerPayoffSum n
        (fun τ : Ranking n => bestInSetPrefixCutIndicator remaining cut τ) r =
      0 := by
  classical
  rw [reflKendallTauLayerPayoffSum]
  simp [bestInSetPrefixCutIndicator_eq_zero_of_forall_remaining_ge
    hremaining hcut]

theorem reflKendallAdjacentPrefixLayer_cross_of_forall_remaining_lt
    (n : ℕ) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    (hcut : ∀ c : Candidate n, c ∈ remaining → (c : ℕ) < cut)
    (i j : Candidate (kendallTauLayerIndexBound n)) :
    0 ≤
      reflKendallTauLayerCount n j *
          reflKendallTauLayerPayoffSum n
            (fun τ : Ranking n =>
              bestInSetPrefixCutIndicator remaining cut τ) i -
        reflKendallTauLayerCount n i *
          reflKendallTauLayerPayoffSum n
            (fun τ : Ranking n =>
              bestInSetPrefixCutIndicator remaining cut τ) j := by
  rw [reflKendallTauLayerPayoffSum_prefix_eq_count_of_forall_remaining_lt
      n hremaining hcut i,
    reflKendallTauLayerPayoffSum_prefix_eq_count_of_forall_remaining_lt
      n hremaining hcut j]
  ring_nf
  exact le_rfl

theorem reflKendallAdjacentPrefixLayer_cross_of_forall_remaining_ge
    (n : ℕ) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    (hcut : ∀ c : Candidate n, c ∈ remaining → cut ≤ (c : ℕ))
    (i j : Candidate (kendallTauLayerIndexBound n)) :
    0 ≤
      reflKendallTauLayerCount n j *
          reflKendallTauLayerPayoffSum n
            (fun τ : Ranking n =>
              bestInSetPrefixCutIndicator remaining cut τ) i -
        reflKendallTauLayerCount n i *
          reflKendallTauLayerPayoffSum n
            (fun τ : Ranking n =>
              bestInSetPrefixCutIndicator remaining cut τ) j := by
  rw [reflKendallTauLayerPayoffSum_prefix_eq_zero_of_forall_remaining_ge
      n hremaining hcut i,
    reflKendallTauLayerPayoffSum_prefix_eq_zero_of_forall_remaining_ge
      n hremaining hcut j]
  ring_nf
  exact le_rfl

theorem reflMallowsBestInSetPrefixCutSum_eq_partition_of_forall_remaining_lt
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    (hcut : ∀ c : Candidate n, c ∈ remaining → (c : ℕ) < cut) :
    reflMallowsBestInSetPrefixCutSum n q remaining cut =
      mallowsPartition q (Equiv.refl (Candidate n)) := by
  unfold reflMallowsBestInSetPrefixCutSum
  calc
    reflMallowsPayoffSum n q
        (fun τ : Ranking n => bestInSetPrefixCutIndicator remaining cut τ)
        =
      reflMallowsPayoffSum n q (fun _ : Ranking n => (1 : ℝ)) := by
        unfold reflMallowsPayoffSum
        refine Finset.sum_congr rfl ?_
        intro τ _
        change
          q ^ kendallTau (Equiv.refl (Candidate n)) τ *
              bestInSetPrefixCutIndicator remaining cut τ =
            q ^ kendallTau (Equiv.refl (Candidate n)) τ * (1 : ℝ)
        rw [bestInSetPrefixCutIndicator_eq_one_of_forall_remaining_lt
          hremaining hcut τ]
    _ = mallowsPartition q (Equiv.refl (Candidate n)) := by
        rw [reflMallowsPayoffSum_const]
        ring

theorem reflMallowsBestInSetPrefixCutSum_eq_zero_of_forall_remaining_ge
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    (hcut : ∀ c : Candidate n, c ∈ remaining → cut ≤ (c : ℕ)) :
    reflMallowsBestInSetPrefixCutSum n q remaining cut = 0 := by
  unfold reflMallowsBestInSetPrefixCutSum reflMallowsPayoffSum
  apply Finset.sum_eq_zero
  intro τ _
  change
    q ^ kendallTau (Equiv.refl (Candidate n)) τ *
        bestInSetPrefixCutIndicator remaining cut τ = 0
  rw [bestInSetPrefixCutIndicator_eq_zero_of_forall_remaining_ge
    hremaining hcut τ]
  ring

theorem reflMallowsBestInSetPrefixCutSum_cross_of_forall_remaining_lt
    (n : ℕ) (qMore qLess : ℝ) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    (hcut : ∀ c : Candidate n, c ∈ remaining → (c : ℕ) < cut) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixCutSum n qMore remaining cut -
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixCutSum n qLess remaining cut := by
  rw [reflMallowsBestInSetPrefixCutSum_eq_partition_of_forall_remaining_lt
      n qMore hremaining hcut,
    reflMallowsBestInSetPrefixCutSum_eq_partition_of_forall_remaining_lt
      n qLess hremaining hcut]
  ring_nf
  exact le_rfl

theorem reflMallowsBestInSetPrefixCutSum_cross_of_forall_remaining_ge
    (n : ℕ) (qMore qLess : ℝ) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    (hcut : ∀ c : Candidate n, c ∈ remaining → cut ≤ (c : ℕ)) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixCutSum n qMore remaining cut -
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixCutSum n qLess remaining cut := by
  rw [reflMallowsBestInSetPrefixCutSum_eq_zero_of_forall_remaining_ge
      n qMore hremaining hcut,
    reflMallowsBestInSetPrefixCutSum_eq_zero_of_forall_remaining_ge
      n qLess hremaining hcut]
  ring_nf
  exact le_rfl

theorem reflMallowsBestInSetPrefixSum_eq_cut
    (n : ℕ) (q : ℝ) (remaining : Finset (Candidate n))
    (k : Fin (n + 1)) :
    reflMallowsBestInSetPrefixSum n q remaining k =
      reflMallowsBestInSetPrefixCutSum n q remaining (k.val + 1) := by
  unfold reflMallowsBestInSetPrefixSum reflMallowsBestInSetPrefixCutSum
  refine Finset.sum_congr rfl ?_
  intro τ _
  change
    q ^ kendallTau (Equiv.refl (Candidate n)) τ *
        bestInSetPrefixIndicator remaining k τ =
      q ^ kendallTau (Equiv.refl (Candidate n)) τ *
        bestInSetPrefixCutIndicator remaining (k.val + 1) τ
  rw [bestInSetPrefixIndicator_eq_cut]

theorem reflMallowsBestInSetPrefixSum_cross_of_kendallPrefixLayerAverageAnti
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    (hlayers : ReflKendallPrefixLayerAverageAnti n)
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty)
    (k : Fin (n + 1)) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixSum n qMore remaining k -
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixSum n qLess remaining k := by
  rw [reflMallowsBestInSetPrefixSum_eq_cut,
    reflMallowsBestInSetPrefixSum_eq_cut]
  exact
    reflMallowsBestInSetPrefixCutSum_cross_of_kendallPrefixLayerAverageAnti
      hqMore_pos hq_lt hlayers hremaining (k.val + 1)

theorem bestInSetPrefixCutIndicator_rankingFirstChoiceOrderEquiv
    {n : ℕ} {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ)
    (r : Candidate (n + 1)) (σ : Ranking n) :
    bestInSetPrefixCutIndicator remaining cut
        (rankingFirstChoiceOrderEquiv n (r, σ)) =
      if r ∈ remaining then
        if (r : ℕ) < cut then 1 else 0
      else
        bestInSetPrefixCutIndicator
          (firstChoiceTailRemainingOf r remaining)
          (deleteFirstChoicePrefixCut r cut) σ := by
  classical
  unfold bestInSetPrefixCutIndicator
  by_cases hr : r ∈ remaining
  · rw [bestInSet_rankingFirstChoiceOrderEquiv_of_first_mem r σ hr]
    simp [hr]
  · rw [bestInSet_rankingFirstChoiceOrderEquiv_of_first_not_mem
      r σ hremaining hr]
    rw [if_neg hr]
    have hiff :=
      succAbove_val_lt_deleteFirstChoicePrefixCut_iff r
        (bestInSet σ (firstChoiceTailRemainingOf r remaining)) cut
    by_cases hcut :
        ((r.succAbove
          (bestInSet σ (firstChoiceTailRemainingOf r remaining)) :
            Candidate (n + 1)) : ℕ) < cut
    · rw [if_pos hcut, if_pos (hiff.mp hcut)]
    · rw [if_neg hcut, if_neg (by
        intro htail
        exact hcut (hiff.mpr htail))]

theorem exists_ne_zero_mem_of_zero_mem_of_one_lt_card
    {n : ℕ} {remaining : Finset (Candidate n)}
    (hzero : (0 : Candidate n) ∈ remaining)
    (hcard : 1 < remaining.card) :
    ∃ b : Candidate n, b ∈ remaining ∧ b ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hcard_le_one : remaining.card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    rw [hnone a ha, hnone b hb]
  omega

theorem reflMallowsPayoffSum_firstChoicePrefix_zero_pos
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) :
    0 <
      reflMallowsPayoffSum (n + 1) q
        (fun π : Ranking (n + 1) =>
          firstChoicePrefixIndicator n (0 : Candidate (n + 1)) π) := by
  classical
  unfold reflMallowsPayoffSum
  refine Finset.sum_pos' ?nonneg ?pos
  · intro π _
    exact mul_nonneg
      (pow_nonneg hq_pos.le _)
      (firstChoicePrefixIndicator_nonneg n (0 : Candidate (n + 1)) π)
  · refine ⟨Equiv.refl (Candidate (n + 1)), Finset.mem_univ _, ?_⟩
    simp [firstChoicePrefixIndicator, firstChoice]

theorem reflMallowsBestInSetPrefixCutSum_one_lt_partition_of_zero_mem_card_gt_one
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q)
    {remaining : Finset (Candidate (n + 1))}
    (hzero : (0 : Candidate (n + 1)) ∈ remaining)
    (hcard : 1 < remaining.card) :
    reflMallowsBestInSetPrefixCutSum (n + 1) q remaining 1 <
      mallowsPartition q (Equiv.refl (Candidate (n + 1))) := by
  classical
  rcases exists_ne_zero_mem_of_zero_mem_of_one_lt_card hzero hcard with
    ⟨b, hb_mem, hb_ne_zero⟩
  unfold reflMallowsBestInSetPrefixCutSum reflMallowsPayoffSum
    mallowsPartition mallowsWeight
  let σ0 : Ranking n := Equiv.refl (Candidate n)
  let π0 : Ranking (n + 1) := rankingFirstChoiceOrderEquiv n (b, σ0)
  refine Finset.sum_lt_sum ?hle ?hstrict
  · intro π _
    have hweight : 0 ≤ q ^ kendallTau (Equiv.refl (Candidate (n + 1))) π :=
      pow_nonneg hq_pos.le _
    have hindicator := bestInSetPrefixCutIndicator_le_one remaining 1 π
    calc
      q ^ kendallTau (Equiv.refl (Candidate (n + 1))) π *
          (fun τ => bestInSetPrefixCutIndicator remaining 1 τ) π
          ≤ q ^ kendallTau (Equiv.refl (Candidate (n + 1))) π * 1 :=
            mul_le_mul_of_nonneg_left hindicator hweight
      _ = q ^ kendallTau (Equiv.refl (Candidate (n + 1))) π := by ring
  · refine ⟨π0, Finset.mem_univ _, ?_⟩
    have hb_not_lt_one : ¬ ((b : Candidate (n + 1)) : ℕ) < 1 := by
      intro hb_lt
      have hb_zero : b = 0 := by
        exact Fin.ext (Nat.lt_one_iff.mp hb_lt)
      exact hb_ne_zero hb_zero
    have hindicator :
        bestInSetPrefixCutIndicator remaining 1 π0 = 0 := by
      simpa [π0, σ0, hb_mem, hb_not_lt_one] using
        bestInSetPrefixCutIndicator_rankingFirstChoiceOrderEquiv
          (n := n) (remaining := remaining)
          ⟨0, hzero⟩ 1 b σ0
    have hweight_pos :
        0 < q ^ kendallTau (Equiv.refl (Candidate (n + 1))) π0 :=
      pow_pos hq_pos _
    change
      q ^ kendallTau (Equiv.refl (Candidate (n + 1))) π0 *
          bestInSetPrefixCutIndicator remaining 1 π0 <
        q ^ kendallTau (Equiv.refl (Candidate (n + 1))) π0
    rw [hindicator]
    simpa using hweight_pos

theorem bestInSetPrefixCutBeforeInsertIndicator_rankingFirstChoiceOrderEquiv
    {n : ℕ} {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ)
    (p : Candidate (n + 2)) (r : Candidate (n + 1)) (σ : Ranking n) :
    bestInSetPrefixCutBeforeInsertIndicator remaining cut p
        (rankingFirstChoiceOrderEquiv n (r, σ)) =
      if hp : p = 0 then
        1
      else if r ∈ remaining then
        if (r : ℕ) < cut then 1 else 0
      else
        bestInSetPrefixCutBeforeInsertIndicator
          (firstChoiceTailRemainingOf r remaining)
          (deleteFirstChoicePrefixCut r cut)
          (p.pred hp) σ := by
  classical
  unfold bestInSetPrefixCutBeforeInsertIndicator
  rw [dif_pos hremaining]
  by_cases hp : p = 0
  · rw [dif_pos hp]
    subst p
    have hnot :
        ¬(rankOf (rankingFirstChoiceOrderEquiv n (r, σ))
            (bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining)).castSucc
          < (0 : Candidate (n + 2)) :=
      Fin.not_lt_zero _
    rw [if_neg hnot]
  · rw [dif_neg hp]
    by_cases hr : r ∈ remaining
    · rw [if_pos hr]
      have hbest :
          bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining = r :=
        bestInSet_rankingFirstChoiceOrderEquiv_of_first_mem r σ hr
      rw [hbest]
      have hbefore :
          (rankOf (rankingFirstChoiceOrderEquiv n (r, σ)) r).castSucc < p := by
        rw [rankOf_rankingFirstChoiceOrderEquiv_first]
        exact Fin.pos_iff_ne_zero.mpr hp
      rw [if_pos hbefore]
      unfold bestInSetPrefixCutIndicator
      rw [hbest]
    · rw [if_neg hr]
      have htail :
          (firstChoiceTailRemainingOf r remaining).Nonempty :=
        firstChoiceTailRemainingOf_nonempty_of_nonempty_of_first_not_mem
          hremaining hr
      have hbest :
          bestInSet (rankingFirstChoiceOrderEquiv n (r, σ)) remaining =
            r.succAbove
              (bestInSet σ (firstChoiceTailRemainingOf r remaining)) :=
        bestInSet_rankingFirstChoiceOrderEquiv_of_first_not_mem
          r σ hremaining hr
      rw [hbest]
      rw [dif_pos htail]
      have hbefore_iff :
          ((rankOf (rankingFirstChoiceOrderEquiv n (r, σ))
              (r.succAbove
                (bestInSet σ (firstChoiceTailRemainingOf r remaining)))).castSucc
              < p) ↔
            (rankOf σ (bestInSet σ (firstChoiceTailRemainingOf r remaining))).castSucc
              < p.pred hp := by
        rw [rankOf_rankingFirstChoiceOrderEquiv_succAbove]
        rw [Fin.lt_def, Fin.lt_def]
        simp [Fin.val_pred]
        omega
      by_cases hbefore_full :
          (rankOf (rankingFirstChoiceOrderEquiv n (r, σ))
            (r.succAbove
              (bestInSet σ (firstChoiceTailRemainingOf r remaining)))).castSucc
            < p
      · have hbefore :
            (rankOf σ
              (bestInSet σ (firstChoiceTailRemainingOf r remaining))).castSucc
              < p.pred hp :=
          hbefore_iff.mp hbefore_full
        rw [if_pos hbefore_full, if_pos hbefore]
        simpa [hr] using
          bestInSetPrefixCutIndicator_rankingFirstChoiceOrderEquiv
            hremaining cut r σ
      · have hbefore :
            ¬ (rankOf σ
              (bestInSet σ (firstChoiceTailRemainingOf r remaining))).castSucc
                < p.pred hp := by
          intro htail_before
          exact hbefore_full (hbefore_iff.mpr htail_before)
        rw [if_neg hbefore_full, if_neg hbefore]

/-- Unnormalised Mallows mass of the before-insert prefix event. -/
noncomputable def reflMallowsBestInSetPrefixCutBeforeInsertSum
    (n : ℕ) (q : ℝ) (remaining : Finset (Candidate n))
    (cut : ℕ) (p : Candidate (n + 1)) : ℝ :=
  reflMallowsPayoffSum n q
    (fun σ : Ranking n =>
      bestInSetPrefixCutBeforeInsertIndicator remaining cut p σ)

/--
First-choice recursion for the before-insert cut-form first-hit mass.  This
keeps the `0`-insert branch explicit, which is the branch produced by peeling
the center-best candidate in the arbitrary remaining-set proof.
-/
theorem reflMallowsBestInSetPrefixCutBeforeInsertSum_firstChoice
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ)
    (p : Candidate (n + 2)) :
    reflMallowsBestInSetPrefixCutBeforeInsertSum
        (n + 1) q remaining cut p =
      ∑ r : Candidate (n + 1),
        q ^ (r : ℕ) *
          (if hp : p = 0 then
            mallowsPartition q (Equiv.refl (Candidate n))
          else if r ∈ remaining then
            mallowsPartition q (Equiv.refl (Candidate n)) *
              (if (r : ℕ) < cut then (1 : ℝ) else 0)
          else
            reflMallowsBestInSetPrefixCutBeforeInsertSum n q
              (firstChoiceTailRemainingOf r remaining)
              (deleteFirstChoicePrefixCut r cut)
              (p.pred hp)) := by
  classical
  unfold reflMallowsBestInSetPrefixCutBeforeInsertSum
  rw [reflMallowsPayoffSum_firstChoice n q]
  refine Finset.sum_congr rfl ?_
  intro r _
  by_cases hp : p = 0
  · rw [dif_pos hp]
    have hbranch :
        reflMallowsPayoffSum n q
            (fun σ : Ranking n =>
              bestInSetPrefixCutBeforeInsertIndicator remaining cut p
                (rankingFirstChoiceOrderEquiv n (r, σ))) =
          reflMallowsPayoffSum n q
            (fun _ : Ranking n => (1 : ℝ)) := by
      unfold reflMallowsPayoffSum
      refine Finset.sum_congr rfl ?_
      intro σ _
      change
        q ^ kendallTau (Equiv.refl (Candidate n)) σ *
            bestInSetPrefixCutBeforeInsertIndicator remaining cut p
              (rankingFirstChoiceOrderEquiv n (r, σ)) =
          q ^ kendallTau (Equiv.refl (Candidate n)) σ * (1 : ℝ)
      rw [bestInSetPrefixCutBeforeInsertIndicator_rankingFirstChoiceOrderEquiv
        hremaining cut p r σ]
      simp [hp]
    rw [hbranch, reflMallowsPayoffSum_const]
    simp
  · rw [dif_neg hp]
    by_cases hr : r ∈ remaining
    · rw [if_pos hr]
      have hbranch :
          reflMallowsPayoffSum n q
              (fun σ : Ranking n =>
                bestInSetPrefixCutBeforeInsertIndicator remaining cut p
                  (rankingFirstChoiceOrderEquiv n (r, σ))) =
            reflMallowsPayoffSum n q
              (fun _ : Ranking n =>
                if (r : ℕ) < cut then (1 : ℝ) else 0) := by
        unfold reflMallowsPayoffSum
        refine Finset.sum_congr rfl ?_
        intro σ _
        change
          q ^ kendallTau (Equiv.refl (Candidate n)) σ *
              bestInSetPrefixCutBeforeInsertIndicator remaining cut p
                (rankingFirstChoiceOrderEquiv n (r, σ)) =
            q ^ kendallTau (Equiv.refl (Candidate n)) σ *
              (if (r : ℕ) < cut then (1 : ℝ) else 0)
        rw [bestInSetPrefixCutBeforeInsertIndicator_rankingFirstChoiceOrderEquiv
          hremaining cut p r σ]
        simp [hp, hr]
      rw [hbranch, reflMallowsPayoffSum_const]
    · rw [if_neg hr]
      congr 1
      unfold reflMallowsPayoffSum
      refine Finset.sum_congr rfl ?_
      intro σ _
      change
        q ^ kendallTau (Equiv.refl (Candidate n)) σ *
            bestInSetPrefixCutBeforeInsertIndicator remaining cut p
              (rankingFirstChoiceOrderEquiv n (r, σ)) =
          q ^ kendallTau (Equiv.refl (Candidate n)) σ *
            bestInSetPrefixCutBeforeInsertIndicator
              (firstChoiceTailRemainingOf r remaining)
              (deleteFirstChoicePrefixCut r cut)
              (p.pred hp) σ
      rw [bestInSetPrefixCutBeforeInsertIndicator_rankingFirstChoiceOrderEquiv
        hremaining cut p r σ]
      simp [hp, hr]

/-- Geometric rank-power sum over ranks up to and including `k`. -/
noncomputable def candidateRankInitialPowerSum
    (n : ℕ) (q : ℝ) (k : Candidate n) : ℝ := ∑ i : Candidate n, if i ≤ k then q ^ (i : ℕ) else 0

theorem candidateRankInitialPowerSum_eq_sum_lt_succ
    (n : ℕ) (q : ℝ) (k : Candidate n) :
    candidateRankInitialPowerSum n q k =
      ∑ i : Candidate n, if (i : ℕ) < (k : ℕ) + 1 then q ^ (i : ℕ) else 0 := by
  classical
  unfold candidateRankInitialPowerSum
  refine Finset.sum_congr rfl ?_
  intro i _
  have hiff : i ≤ k ↔ (i : ℕ) < (k : ℕ) + 1 := by
    rw [Fin.le_iff_val_le_val]
    omega
  by_cases hik : i ≤ k
  · rw [if_pos hik, if_pos (hiff.mp hik)]
  · rw [if_neg hik, if_neg (fun h => hik (hiff.mpr h))]

theorem candidateRankPowerSum_sub_rankPower_nonneg
    (n : ℕ) {q : ℝ} (hq_nonneg : 0 ≤ q) (i : Candidate n) :
    0 ≤ candidateRankPowerSum n q - q ^ (i : ℕ) := by
  classical
  have hsingle :
      (∑ j : Candidate n, if j = i then q ^ (i : ℕ) else 0) =
        q ^ (i : ℕ) := by
    simpa using
      (Finset.sum_ite_eq' Finset.univ i
        (fun _ : Candidate n => q ^ (i : ℕ)))
  have hdecomp :
      candidateRankPowerSum n q - q ^ (i : ℕ) =
        ∑ j : Candidate n, if j = i then 0 else q ^ (j : ℕ) := by
    unfold candidateRankPowerSum
    rw [← hsingle, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  rw [hdecomp]
  exact Finset.sum_nonneg (by
    intro j _
    by_cases hji : j = i
    · simp [hji]
    · simp [hji, pow_nonneg hq_nonneg _])

theorem candidateRankInitialPowerSum_eq_prefixPowerSum
    (n : ℕ) (q : ℝ) {k : Candidate n} (hk : (k : ℕ) < n + 1) :
    candidateRankInitialPowerSum n q k =
      candidateRankPrefixPowerSum n q ⟨k.val, hk⟩ := by
  classical
  unfold candidateRankInitialPowerSum candidateRankPrefixPowerSum
  refine Finset.sum_congr rfl ?_
  intro i _
  have hiff : i ≤ k ↔ (i : ℕ) ≤ k.val := by
    rw [Fin.le_iff_val_le_val]
  by_cases hi : i ≤ k
  · rw [if_pos hi, if_pos (hiff.mp hi)]
  · rw [if_neg hi, if_neg (fun h => hi (hiff.mpr h))]

theorem candidateRankInitialPowerSum_eq_powerSum_of_last
    (n : ℕ) (q : ℝ) {k : Candidate n} (hk : (k : ℕ) = n + 1) :
    candidateRankInitialPowerSum n q k = candidateRankPowerSum n q := by
  classical
  unfold candidateRankInitialPowerSum candidateRankPowerSum
  refine Finset.sum_congr rfl ?_
  intro i _
  have hi : i ≤ k := by
    rw [Fin.le_iff_val_le_val]
    omega
  rw [if_pos hi]

theorem candidateRankInitialPowerSum_cross_nonneg
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (k : Candidate n) :
    0 ≤
      candidateRankPowerSum n qLess *
          candidateRankInitialPowerSum n qMore k -
        candidateRankPowerSum n qMore *
          candidateRankInitialPowerSum n qLess k := by
  classical
  by_cases hk_last : (k : ℕ) = n + 1
  · rw [candidateRankInitialPowerSum_eq_powerSum_of_last n qMore hk_last,
      candidateRankInitialPowerSum_eq_powerSum_of_last n qLess hk_last]
    ring_nf
    exact le_rfl
  · have hk_lt : (k : ℕ) < n + 1 := by
      have hk_le : (k : ℕ) ≤ n + 1 := Nat.le_of_lt_succ k.isLt
      exact lt_of_le_of_ne hk_le hk_last
    let k' : Fin (n + 1) := ⟨k.val, hk_lt⟩
    have hpos :
        0 <
          candidateRankPrefixPowerSum n qMore k' *
              candidateRankPowerSum n qLess -
            candidateRankPrefixPowerSum n qLess k' *
              candidateRankPowerSum n qMore :=
      candidateRankPrefix_cross_pos n hqMore_pos hq_lt k'
    rw [candidateRankInitialPowerSum_eq_prefixPowerSum n qMore hk_lt,
      candidateRankInitialPowerSum_eq_prefixPowerSum n qLess hk_lt]
    nlinarith

/--
Reverse-weighted insertion mass strictly after a center rank.  This is the
worst-candidate analogue of an initial rank-power sum: in the `peelWorst`
decomposition, lower inverse Mallows parameters put more insertion weight after
the current tail best candidate.
-/
noncomputable def candidateRankStrictSuffixReversePowerSum
    (n : ℕ) (q : ℝ) (k : Candidate n) : ℝ := ∑ i : Candidate n, if k < i then q ^ (n + 1 - (i : ℕ)) else 0

theorem candidateRankReversePowerSum_eq_powerSum
    (n : ℕ) (q : ℝ) :
    candidateRankReversePowerSum n q = candidateRankPowerSum n q := by
  classical
  unfold candidateRankReversePowerSum candidateRankPowerSum
  calc
    (∑ i : Candidate n, q ^ (n + 1 - (i : ℕ)))
        =
      ∑ i : Candidate n, q ^ ((Fin.rev i : Candidate n) : ℕ) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        congr 1
        rw [Fin.val_rev]
        omega
    _ = ∑ i : Candidate n, q ^ (i : ℕ) := by
        simpa using
          (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Candidate n))
            (fun i : Candidate n => q ^ (i : ℕ)))

theorem candidateRankStrictSuffixReversePowerSum_eq_rev_prefix
    (n : ℕ) (q : ℝ) (k : Candidate n) :
    candidateRankStrictSuffixReversePowerSum n q k =
      ∑ i : Candidate n, if i < Fin.rev k then q ^ (i : ℕ) else 0 := by
  classical
  unfold candidateRankStrictSuffixReversePowerSum
  calc
    (∑ i : Candidate n,
        if k < i then q ^ (n + 1 - (i : ℕ)) else 0)
        =
      ∑ i : Candidate n,
        if Fin.rev i < Fin.rev k then
          q ^ ((Fin.rev i : Candidate n) : ℕ)
        else
          0 := by
        refine Finset.sum_congr rfl ?_
        intro i _
        have hiff : k < i ↔ Fin.rev i < Fin.rev k := by
          simpa using (Fin.rev_lt_rev (i := i) (j := k))
        by_cases hki : k < i
        · rw [if_pos hki, if_pos (hiff.mp hki)]
          congr 1
          rw [Fin.val_rev]
          omega
        · rw [if_neg hki, if_neg (fun h => hki (hiff.mpr h))]
    _ = ∑ i : Candidate n, if i < Fin.rev k then q ^ (i : ℕ) else 0 := by
        simpa using
          (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Candidate n))
            (fun i : Candidate n =>
              if i < Fin.rev k then q ^ (i : ℕ) else 0))

/--
Tail payoff obtained after aggregating the insertion position of a center-best
remaining candidate.  It is parameter-dependent because the insertion-position
weights use the same Mallows parameter as the ranking law.
-/
noncomputable def bestInSetPrefixCutTailInsertPositionValue {n : ℕ}
    (q : ℝ) (remaining : Finset (Candidate n)) (cut : ℕ)
    (σ : Ranking n) : ℝ :=
  if hremaining : remaining.Nonempty then
    if (((bestInSet σ remaining) : Candidate n) : ℕ) < cut then
      candidateRankPowerSum (n + 1) q
    else
      candidateRankInitialPowerSum (n + 1) q
        (rankOf σ (bestInSet σ remaining)).castSucc
  else
    candidateRankPowerSum (n + 1) q

theorem bestInSetPrefixCutTailInsertPositionValue_cross_nonneg
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    (remaining : Finset (Candidate n)) (cut : ℕ) (σ : Ranking n) :
    0 ≤
      candidateRankPowerSum (n + 1) qLess *
          bestInSetPrefixCutTailInsertPositionValue qMore remaining cut σ -
        candidateRankPowerSum (n + 1) qMore *
          bestInSetPrefixCutTailInsertPositionValue qLess remaining cut σ := by
  classical
  by_cases hremaining : remaining.Nonempty
  · by_cases hcut : (((bestInSet σ remaining) : Candidate n) : ℕ) < cut
    · simp [bestInSetPrefixCutTailInsertPositionValue, hremaining, hcut]
      ring_nf
      exact le_rfl
    · simpa [bestInSetPrefixCutTailInsertPositionValue, hremaining, hcut] using
        candidateRankInitialPowerSum_cross_nonneg
          (n + 1) hqMore_pos hq_lt
          (rankOf σ (bestInSet σ remaining)).castSucc
  · simp [bestInSetPrefixCutTailInsertPositionValue, hremaining]
    ring_nf
    exact le_rfl

theorem reflMallowsPayoffSum_tailInsertPositionValue_insertion_cross_nonneg
    {n : ℕ} {qWeight qMore qLess : ℝ} (hqWeight_nonneg : 0 ≤ qWeight)
    (hqMore_pos : 0 < qMore) (hq_lt : qMore < qLess)
    (remaining : Finset (Candidate n)) (cut : ℕ) :
    0 ≤
      candidateRankPowerSum (n + 1) qLess *
          reflMallowsPayoffSum n qWeight
            (bestInSetPrefixCutTailInsertPositionValue qMore remaining cut) -
        candidateRankPowerSum (n + 1) qMore *
          reflMallowsPayoffSum n qWeight
            (bestInSetPrefixCutTailInsertPositionValue qLess remaining cut) := by
  classical
  unfold reflMallowsPayoffSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg ?_
  intro σ _
  have hweight :
      0 ≤ qWeight ^ kendallTau (Equiv.refl (Candidate n)) σ :=
    pow_nonneg hqWeight_nonneg _
  have hpoint :=
    bestInSetPrefixCutTailInsertPositionValue_cross_nonneg
      hqMore_pos hq_lt remaining cut σ
  have hterm :
      candidateRankPowerSum (n + 1) qLess *
            (qWeight ^ kendallTau (Equiv.refl (Candidate n)) σ *
              bestInSetPrefixCutTailInsertPositionValue qMore remaining cut σ) -
          candidateRankPowerSum (n + 1) qMore *
            (qWeight ^ kendallTau (Equiv.refl (Candidate n)) σ *
              bestInSetPrefixCutTailInsertPositionValue qLess remaining cut σ)
        =
      qWeight ^ kendallTau (Equiv.refl (Candidate n)) σ *
        (candidateRankPowerSum (n + 1) qLess *
            bestInSetPrefixCutTailInsertPositionValue qMore remaining cut σ -
          candidateRankPowerSum (n + 1) qMore *
            bestInSetPrefixCutTailInsertPositionValue qLess remaining cut σ) := by
    ring
  rw [hterm]
  exact mul_nonneg hweight hpoint

/--
Aggregate the before-insert branch over all insertion positions.  If the tail
best remaining candidate is already in the prefix, every insertion position
succeeds; otherwise only insertions weakly before that tail best succeed.
-/
theorem bestInSetPrefixCutBeforeInsertIndicator_insertPositionSum
    {n : ℕ} (q : ℝ) (remaining : Finset (Candidate n))
    (cut : ℕ) (σ : Ranking n) :
    (∑ p : Candidate (n + 1),
        q ^ (p : ℕ) *
          bestInSetPrefixCutBeforeInsertIndicator remaining cut p σ) =
      if hremaining : remaining.Nonempty then
        if ((bestInSet σ remaining : Candidate n) : ℕ) < cut then
          candidateRankPowerSum (n + 1) q
        else
          candidateRankInitialPowerSum (n + 1) q
            (rankOf σ (bestInSet σ remaining)).castSucc
      else
        candidateRankPowerSum (n + 1) q := by
  classical
  by_cases hremaining : remaining.Nonempty
  · rw [dif_pos hremaining]
    by_cases hcut : ((bestInSet σ remaining : Candidate n) : ℕ) < cut
    · rw [if_pos hcut]
      unfold candidateRankPowerSum
      refine Finset.sum_congr rfl ?_
      intro p _
      unfold bestInSetPrefixCutBeforeInsertIndicator
      rw [dif_pos hremaining]
      by_cases hbefore :
          (rankOf σ (bestInSet σ remaining)).castSucc < p
      · rw [if_pos hbefore]
        unfold bestInSetPrefixCutIndicator
        rw [if_pos hcut]
        ring
      · rw [if_neg hbefore]
        ring
    · rw [if_neg hcut]
      unfold candidateRankInitialPowerSum
      refine Finset.sum_congr rfl ?_
      intro p _
      unfold bestInSetPrefixCutBeforeInsertIndicator
      rw [dif_pos hremaining]
      by_cases hbefore :
          (rankOf σ (bestInSet σ remaining)).castSucc < p
      · rw [if_pos hbefore]
        unfold bestInSetPrefixCutIndicator
        rw [if_neg hcut]
        have hp_not_le :
            ¬ p ≤ (rankOf σ (bestInSet σ remaining)).castSucc :=
          not_le_of_gt hbefore
        simp [hp_not_le]
      · rw [if_neg hbefore]
        have hp_le :
            p ≤ (rankOf σ (bestInSet σ remaining)).castSucc :=
          le_of_not_gt hbefore
        simp [hp_le]
  · rw [dif_neg hremaining]
    unfold candidateRankPowerSum
    refine Finset.sum_congr rfl ?_
    intro p _
    unfold bestInSetPrefixCutBeforeInsertIndicator
    rw [dif_neg hremaining]
    ring

theorem reflMallowsBestInSetPrefixCutSum_eq_tail_insertPositionSum_of_zero_mem
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hzero : (0 : Candidate (n + 1)) ∈ remaining)
    {cut : ℕ} (hcut : 0 < cut) :
    reflMallowsBestInSetPrefixCutSum (n + 1) q remaining cut =
      reflMallowsPayoffSum n q
        (fun σ : Ranking n =>
          if htail : (tailRemainingOf remaining).Nonempty then
            if (((bestInSet σ (tailRemainingOf remaining)) :
                Candidate n) : ℕ) < cut - 1 then
              candidateRankPowerSum (n + 1) q
            else
              candidateRankInitialPowerSum (n + 1) q
                (rankOf σ
                  (bestInSet σ (tailRemainingOf remaining))).castSucc
          else
            candidateRankPowerSum (n + 1) q) := by
  classical
  have hremaining : remaining.Nonempty := ⟨0, hzero⟩
  rw [reflMallowsBestInSetPrefixCutSum_peelBest n q hremaining cut]
  unfold reflMallowsPayoffSum
  calc
    (∑ p : Candidate (n + 1),
        q ^ (p : ℕ) *
          (∑ σ : Ranking n,
            q ^ kendallTau (Equiv.refl (Candidate n)) σ *
              bestInSetPrefixCutPeelBestIndicator remaining cut p σ))
        =
      ∑ p : Candidate (n + 1), ∑ σ : Ranking n,
        q ^ (p : ℕ) *
          (q ^ kendallTau (Equiv.refl (Candidate n)) σ *
            bestInSetPrefixCutBeforeInsertIndicator
              (tailRemainingOf remaining) (cut - 1) p σ) := by
        refine Finset.sum_congr rfl ?_
        intro p _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro σ _
        unfold bestInSetPrefixCutPeelBestIndicator
        rw [if_pos hzero, if_neg (Nat.ne_of_gt hcut)]
    _ =
      ∑ σ : Ranking n, ∑ p : Candidate (n + 1),
        q ^ (p : ℕ) *
          (q ^ kendallTau (Equiv.refl (Candidate n)) σ *
            bestInSetPrefixCutBeforeInsertIndicator
              (tailRemainingOf remaining) (cut - 1) p σ) := by
        rw [Finset.sum_comm]
    _ =
      ∑ σ : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          (∑ p : Candidate (n + 1),
            q ^ (p : ℕ) *
              bestInSetPrefixCutBeforeInsertIndicator
                (tailRemainingOf remaining) (cut - 1) p σ) := by
        refine Finset.sum_congr rfl ?_
        intro σ _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro p _
        ring
    _ =
      ∑ σ : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          (if htail : (tailRemainingOf remaining).Nonempty then
            if (((bestInSet σ (tailRemainingOf remaining)) :
                Candidate n) : ℕ) < cut - 1 then
              candidateRankPowerSum (n + 1) q
            else
              candidateRankInitialPowerSum (n + 1) q
                (rankOf σ
                  (bestInSet σ (tailRemainingOf remaining))).castSucc
          else
            candidateRankPowerSum (n + 1) q) := by
        refine Finset.sum_congr rfl ?_
        intro σ _
        rw [bestInSetPrefixCutBeforeInsertIndicator_insertPositionSum]

theorem reflMallowsBestInSetPrefixCutSum_eq_tail_insertPositionValue_of_zero_mem
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hzero : (0 : Candidate (n + 1)) ∈ remaining)
    {cut : ℕ} (hcut : 0 < cut) :
    reflMallowsBestInSetPrefixCutSum (n + 1) q remaining cut =
      reflMallowsPayoffSum n q
        (bestInSetPrefixCutTailInsertPositionValue q
          (tailRemainingOf remaining) (cut - 1)) := by
  simpa [bestInSetPrefixCutTailInsertPositionValue] using
    reflMallowsBestInSetPrefixCutSum_eq_tail_insertPositionSum_of_zero_mem
      n q hzero hcut

theorem reflMallowsBestInSetPrefixCutSum_cross_of_zero_mem_from_tail_insertPositionValue
    (n : ℕ) {qMore qLess : ℝ}
    {remaining : Finset (Candidate (n + 1))}
    (hzero : (0 : Candidate (n + 1)) ∈ remaining)
    {cut : ℕ} (hcut : 0 < cut)
    (htail :
      0 ≤
        mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
            reflMallowsPayoffSum n qMore
              (bestInSetPrefixCutTailInsertPositionValue qMore
                (tailRemainingOf remaining) (cut - 1)) -
          mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
            reflMallowsPayoffSum n qLess
              (bestInSetPrefixCutTailInsertPositionValue qLess
                (tailRemainingOf remaining) (cut - 1))) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qMore remaining cut -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qLess remaining cut := by
  rw [
    reflMallowsBestInSetPrefixCutSum_eq_tail_insertPositionValue_of_zero_mem
      n qMore hzero hcut,
    reflMallowsBestInSetPrefixCutSum_eq_tail_insertPositionValue_of_zero_mem
      n qLess hzero hcut]
  exact htail

theorem reflMallowsBestInSetPrefixCutSum_cross_of_zero_mem_from_tail_fixed_insertPositionValue
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hzero : (0 : Candidate (n + 1)) ∈ remaining)
    {cut : ℕ} (hcut : 0 < cut)
    (htail :
      0 ≤
        mallowsPartition qLess (Equiv.refl (Candidate n)) *
            reflMallowsPayoffSum n qMore
              (bestInSetPrefixCutTailInsertPositionValue qLess
                (tailRemainingOf remaining) (cut - 1)) -
          mallowsPartition qMore (Equiv.refl (Candidate n)) *
            reflMallowsPayoffSum n qLess
              (bestInSetPrefixCutTailInsertPositionValue qLess
                (tailRemainingOf remaining) (cut - 1))) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qMore remaining cut -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qLess remaining cut := by
  classical
  let tail : Finset (Candidate n) := tailRemainingOf remaining
  let GMore : Ranking n → ℝ :=
    bestInSetPrefixCutTailInsertPositionValue qMore tail (cut - 1)
  let GLess : Ranking n → ℝ :=
    bestInSetPrefixCutTailInsertPositionValue qLess tail (cut - 1)
  let PMore : ℝ := candidateRankPowerSum (n + 1) qMore
  let PLess : ℝ := candidateRankPowerSum (n + 1) qLess
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let SMoreGMore : ℝ := reflMallowsPayoffSum n qMore GMore
  let SMoreGLess : ℝ := reflMallowsPayoffSum n qMore GLess
  let SLessGLess : ℝ := reflMallowsPayoffSum n qLess GLess
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hZLess_nonneg : 0 ≤ ZLess :=
    le_of_lt (mallowsPartition_pos (hq := hqLess_pos)
      (Equiv.refl (Candidate n)))
  have hPMore_nonneg : 0 ≤ PMore :=
    le_of_lt (candidateRankPowerSum_pos (n + 1) hqMore_pos)
  have hinsert :
      0 ≤ PLess * SMoreGMore - PMore * SMoreGLess := by
    simpa [PLess, PMore, SMoreGMore, SMoreGLess, GMore, GLess, tail] using
      reflMallowsPayoffSum_tailInsertPositionValue_insertion_cross_nonneg
        (n := n) (qWeight := qMore) (qMore := qMore) (qLess := qLess)
        (le_of_lt hqMore_pos) hqMore_pos hq_lt
        (tailRemainingOf remaining) (cut - 1)
  have htail' :
      0 ≤ ZLess * SMoreGLess - ZMore * SLessGLess := by
    simpa [ZLess, ZMore, SMoreGLess, SLessGLess, GLess, tail] using htail
  rw [
    reflMallowsBestInSetPrefixCutSum_eq_tail_insertPositionValue_of_zero_mem
      n qMore hzero hcut,
    reflMallowsBestInSetPrefixCutSum_eq_tail_insertPositionValue_of_zero_mem
      n qLess hzero hcut,
    mallowsPartition_refl_peelBest n qLess,
    mallowsPartition_refl_peelBest n qMore]
  change
    0 ≤
      (PLess * ZLess) * SMoreGMore -
        (PMore * ZMore) * SLessGLess
  have hdecomp :
      (PLess * ZLess) * SMoreGMore -
          (PMore * ZMore) * SLessGLess =
        ZLess * (PLess * SMoreGMore - PMore * SMoreGLess) +
          PMore * (ZLess * SMoreGLess - ZMore * SLessGLess) := by
    ring
  rw [hdecomp]
  exact add_nonneg
    (mul_nonneg hZLess_nonneg hinsert)
    (mul_nonneg hPMore_nonneg htail')

/--
First-choice recursion for the cut-form first-hit mass.  This is the exact
finite-sum recurrence needed for the arbitrary remaining-set part of Theorem 4.
-/
theorem reflMallowsBestInSetPrefixCutSum_firstChoice
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ) :
    reflMallowsBestInSetPrefixCutSum (n + 1) q remaining cut =
      ∑ r : Candidate (n + 1),
        q ^ (r : ℕ) *
          (if r ∈ remaining then
            mallowsPartition q (Equiv.refl (Candidate n)) *
              (if (r : ℕ) < cut then (1 : ℝ) else 0)
          else
            reflMallowsBestInSetPrefixCutSum n q
              (firstChoiceTailRemainingOf r remaining)
              (deleteFirstChoicePrefixCut r cut)) := by
  classical
  unfold reflMallowsBestInSetPrefixCutSum
  rw [reflMallowsPayoffSum_firstChoice n q]
  refine Finset.sum_congr rfl ?_
  intro r _
  by_cases hr : r ∈ remaining
  · rw [if_pos hr]
    have hbranch :
        reflMallowsPayoffSum n q
            (fun σ : Ranking n =>
              bestInSetPrefixCutIndicator remaining cut
                (rankingFirstChoiceOrderEquiv n (r, σ))) =
          reflMallowsPayoffSum n q
            (fun _ : Ranking n =>
              if (r : ℕ) < cut then (1 : ℝ) else 0) := by
      unfold reflMallowsPayoffSum
      refine Finset.sum_congr rfl ?_
      intro σ _
      change
        q ^ kendallTau (Equiv.refl (Candidate n)) σ *
            bestInSetPrefixCutIndicator remaining cut
              (rankingFirstChoiceOrderEquiv n (r, σ)) =
          q ^ kendallTau (Equiv.refl (Candidate n)) σ *
            (if (r : ℕ) < cut then (1 : ℝ) else 0)
      rw [bestInSetPrefixCutIndicator_rankingFirstChoiceOrderEquiv
        hremaining cut r σ]
      simp [hr]
    rw [hbranch, reflMallowsPayoffSum_const]
  · rw [if_neg hr]
    congr 1
    unfold reflMallowsPayoffSum
    refine Finset.sum_congr rfl ?_
    intro σ _
    change
      q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          bestInSetPrefixCutIndicator remaining cut
            (rankingFirstChoiceOrderEquiv n (r, σ)) =
        q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          bestInSetPrefixCutIndicator
            (firstChoiceTailRemainingOf r remaining)
            (deleteFirstChoicePrefixCut r cut) σ
    rw [bestInSetPrefixCutIndicator_rankingFirstChoiceOrderEquiv
      hremaining cut r σ]
    simp [hr]

/--
Weak weighted-average comparison for the geometric rank weights.  Lower inverse
Mallows parameter places weakly more weight on lower center ranks.
-/
theorem candidateRankWeightedAverage_anti
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    {B : Candidate n → ℝ}
    (hB : ∀ i j : Candidate n, i < j → B j ≤ B i) :
    0 ≤
      candidateRankPowerSum n q₂ *
          (∑ i : Candidate n, q₁ ^ (i : ℕ) * B i) -
        candidateRankPowerSum n q₁ *
          (∑ i : Candidate n, q₂ ^ (i : ℕ) * B i) := by
  classical
  let w₁ : Candidate n → ℝ := fun i => q₁ ^ (i : ℕ)
  let w₂ : Candidate n → ℝ := fun i => q₂ ^ (i : ℕ)
  have hpair :
      ∀ i j : Candidate n, i < j →
        0 ≤ w₁ i * w₂ j - w₁ j * w₂ i := by
    intro i j hij
    exact le_of_lt (sub_pos.mpr (by
      simpa [w₁, w₂, mul_comm, mul_left_comm, mul_assoc] using
        rankPower_mul_lt_mul_rankPower hq₁_pos hq_lt hij))
  have h :=
    candidateWeightedAverage_cross_nonneg_of_pairwise
      n (wA := w₁) (wH := w₂) (B := B) hpair hB
  simpa [w₁, w₂, candidateRankPowerSum] using h

theorem candidateRankStrictSuffixReversePowerSum_cross_nonneg
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (k : Candidate n) :
    0 ≤
      candidateRankReversePowerSum n qLess *
          candidateRankStrictSuffixReversePowerSum n qMore k -
        candidateRankReversePowerSum n qMore *
          candidateRankStrictSuffixReversePowerSum n qLess k := by
  classical
  let B : Candidate n → ℝ := fun i =>
    if i < Fin.rev k then (1 : ℝ) else 0
  have hB : ∀ i j : Candidate n, i < j → B j ≤ B i := by
    intro i j hij
    dsimp [B]
    by_cases hj : j < Fin.rev k
    · have hi : i < Fin.rev k := lt_trans hij hj
      simp [hi, hj]
    · by_cases hi : i < Fin.rev k
      · simp [hi, hj]
      · simp [hi, hj]
  have hweighted :=
    candidateRankWeightedAverage_anti
      n hqMore_pos hq_lt (B := B) hB
  rw [candidateRankReversePowerSum_eq_powerSum n qLess,
    candidateRankReversePowerSum_eq_powerSum n qMore,
    candidateRankStrictSuffixReversePowerSum_eq_rev_prefix n qMore k,
    candidateRankStrictSuffixReversePowerSum_eq_rev_prefix n qLess k]
  simpa [B] using hweighted

/--
Tail payoff obtained after aggregating the insertion position of a center-worst
remaining candidate.  If the current tail best is in the prefix, the worst
candidate must be inserted strictly after it; otherwise the prefix event fails.
-/
noncomputable def bestInSetPrefixCutTailWorstInsertPositionValue {n : ℕ}
    (q : ℝ) (remaining : Finset (Candidate n)) (cut : ℕ)
    (σ : Ranking n) : ℝ :=
  if hremaining : remaining.Nonempty then
    if (((bestInSet σ remaining) : Candidate n) : ℕ) < cut then
      candidateRankStrictSuffixReversePowerSum (n + 1) q
        (rankOf σ (bestInSet σ remaining)).castSucc
    else
      0
  else
    0

theorem bestInSetPrefixCutTailWorstInsertPositionValue_insertPositionSum
    {n : ℕ} (q : ℝ) (remaining : Finset (Candidate n))
    (cut : ℕ) (σ : Ranking n) :
    (∑ p : Candidate (n + 1),
        q ^ (n + 2 - (p : ℕ)) *
          (if hremaining : remaining.Nonempty then
            if (rankOf σ (bestInSet σ remaining)).castSucc < p then
              bestInSetPrefixCutIndicator remaining cut σ
            else
              0
          else
            0)) =
      bestInSetPrefixCutTailWorstInsertPositionValue q remaining cut σ := by
  classical
  by_cases hremaining : remaining.Nonempty
  · simp [bestInSetPrefixCutTailWorstInsertPositionValue, hremaining]
    by_cases hcut : (((bestInSet σ remaining) : Candidate n) : ℕ) < cut
    · rw [if_pos hcut]
      unfold bestInSetPrefixCutIndicator
      rw [if_pos hcut]
      unfold candidateRankStrictSuffixReversePowerSum
      refine Finset.sum_congr rfl ?_
      intro p _
      by_cases hp :
          (rankOf σ (bestInSet σ remaining)).castSucc < p
      · rw [if_pos hp]
        simp [hp]
      · rw [if_neg hp]
        simp [hp]
    · rw [if_neg hcut]
      unfold bestInSetPrefixCutIndicator
      rw [if_neg hcut]
      simp
  · simp [bestInSetPrefixCutTailWorstInsertPositionValue, hremaining]

theorem bestInSetPrefixCutIndicator_rankingPeelWorstOrderEquiv_of_last_mem
    {n : ℕ} {remaining : Finset (Candidate (n + 1))}
    (hlast : reflLastCandidate (n + 1) ∈ remaining)
    {cut : ℕ} (hcut : cut ≤ n + 1)
    (p : Candidate (n + 1)) (σ : Ranking n) :
    bestInSetPrefixCutIndicator remaining cut
        (rankingPeelWorstOrderEquiv n (p, σ)) =
      if hinit : (initRemainingOf remaining).Nonempty then
        if (rankOf σ (bestInSet σ (initRemainingOf remaining))).castSucc < p then
          bestInSetPrefixCutIndicator
            (initRemainingOf remaining) cut σ
        else
          0
      else
        0 := by
  classical
  have hlast_not_cut :
      ¬ (((reflLastCandidate (n + 1) : Candidate (n + 1)) : ℕ) < cut) := by
    simp [reflLastCandidate]
    omega
  by_cases hinit : (initRemainingOf remaining).Nonempty
  · by_cases hbefore :
        (rankOf σ (bestInSet σ (initRemainingOf remaining))).castSucc < p
    · have hbest :=
        bestInSet_rankingPeelWorstOrderEquiv_of_last_mem_tail_before
          (n := n) p σ hlast hinit hbefore
      unfold bestInSetPrefixCutIndicator
      rw [hbest]
      simp [hinit, hbefore]
    · have hbest :=
        bestInSet_rankingPeelWorstOrderEquiv_of_last_mem_tail_not_before
          (n := n) p σ hlast hinit hbefore
      unfold bestInSetPrefixCutIndicator
      rw [hbest]
      simp [hlast_not_cut, hinit, hbefore]
  · have hbest :=
      bestInSet_rankingPeelWorstOrderEquiv_of_last_mem_init_empty
        (n := n) p σ hlast hinit
    unfold bestInSetPrefixCutIndicator
    rw [hbest]
    simp [hlast_not_cut, hinit]

theorem reflMallowsBestInSetPrefixCutSum_eq_init_worstInsertPositionValue_of_last_mem
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hlast : reflLastCandidate (n + 1) ∈ remaining)
    {cut : ℕ} (hcut : cut ≤ n + 1) :
    reflMallowsBestInSetPrefixCutSum (n + 1) q remaining cut =
      reflMallowsPayoffSum n q
        (bestInSetPrefixCutTailWorstInsertPositionValue q
          (initRemainingOf remaining) cut) := by
  classical
  unfold reflMallowsBestInSetPrefixCutSum
  rw [reflMallowsPayoffSum_peelWorst n q
    (fun τ : Ranking (n + 1) =>
      bestInSetPrefixCutIndicator remaining cut τ)]
  unfold reflMallowsPayoffSum
  calc
    (∑ p : Candidate (n + 1),
        q ^ (n + 2 - (p : ℕ)) *
          (∑ σ : Ranking n,
            q ^ kendallTau (Equiv.refl (Candidate n)) σ *
              bestInSetPrefixCutIndicator remaining cut
                (rankingPeelWorstOrderEquiv n (p, σ))))
        =
      ∑ σ : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          (∑ p : Candidate (n + 1),
            q ^ (n + 2 - (p : ℕ)) *
              bestInSetPrefixCutIndicator remaining cut
                (rankingPeelWorstOrderEquiv n (p, σ))) := by
        calc
          (∑ p : Candidate (n + 1),
              q ^ (n + 2 - (p : ℕ)) *
                (∑ σ : Ranking n,
                  q ^ kendallTau (Equiv.refl (Candidate n)) σ *
                    bestInSetPrefixCutIndicator remaining cut
                      (rankingPeelWorstOrderEquiv n (p, σ))))
              =
            ∑ p : Candidate (n + 1), ∑ σ : Ranking n,
              q ^ (n + 2 - (p : ℕ)) *
                (q ^ kendallTau (Equiv.refl (Candidate n)) σ *
                  bestInSetPrefixCutIndicator remaining cut
                    (rankingPeelWorstOrderEquiv n (p, σ))) := by
              refine Finset.sum_congr rfl ?_
              intro p _
              rw [Finset.mul_sum]
          _ =
            ∑ σ : Ranking n, ∑ p : Candidate (n + 1),
              q ^ (n + 2 - (p : ℕ)) *
                (q ^ kendallTau (Equiv.refl (Candidate n)) σ *
                  bestInSetPrefixCutIndicator remaining cut
                    (rankingPeelWorstOrderEquiv n (p, σ))) := by
              rw [Finset.sum_comm]
          _ =
            ∑ σ : Ranking n,
              q ^ kendallTau (Equiv.refl (Candidate n)) σ *
                (∑ p : Candidate (n + 1),
                  q ^ (n + 2 - (p : ℕ)) *
                    bestInSetPrefixCutIndicator remaining cut
                      (rankingPeelWorstOrderEquiv n (p, σ))) := by
              refine Finset.sum_congr rfl ?_
              intro σ _
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro p _
              ring
    _ =
      ∑ σ : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          bestInSetPrefixCutTailWorstInsertPositionValue q
            (initRemainingOf remaining) cut σ := by
        refine Finset.sum_congr rfl ?_
        intro σ _
        congr 1
        rw [← bestInSetPrefixCutTailWorstInsertPositionValue_insertPositionSum
          q (initRemainingOf remaining) cut σ]
        refine Finset.sum_congr rfl ?_
        intro p _
        rw [bestInSetPrefixCutIndicator_rankingPeelWorstOrderEquiv_of_last_mem
          hlast hcut p σ]

theorem bestInSetPrefixCutTailWorstInsertPositionValue_cross_nonneg
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    (remaining : Finset (Candidate n)) (cut : ℕ) (σ : Ranking n) :
    0 ≤
      candidateRankReversePowerSum (n + 1) qLess *
          bestInSetPrefixCutTailWorstInsertPositionValue qMore remaining cut σ -
        candidateRankReversePowerSum (n + 1) qMore *
          bestInSetPrefixCutTailWorstInsertPositionValue qLess remaining cut σ := by
  classical
  by_cases hremaining : remaining.Nonempty
  · by_cases hcut : (((bestInSet σ remaining) : Candidate n) : ℕ) < cut
    · simpa [bestInSetPrefixCutTailWorstInsertPositionValue,
        hremaining, hcut] using
        candidateRankStrictSuffixReversePowerSum_cross_nonneg
          (n + 1) hqMore_pos hq_lt
          (rankOf σ (bestInSet σ remaining)).castSucc
    · simp [bestInSetPrefixCutTailWorstInsertPositionValue, hremaining, hcut]
  · simp [bestInSetPrefixCutTailWorstInsertPositionValue, hremaining]

theorem reflMallowsPayoffSum_tailWorstInsertPositionValue_insertion_cross_nonneg
    {n : ℕ} {qWeight qMore qLess : ℝ} (hqWeight_nonneg : 0 ≤ qWeight)
    (hqMore_pos : 0 < qMore) (hq_lt : qMore < qLess)
    (remaining : Finset (Candidate n)) (cut : ℕ) :
    0 ≤
      candidateRankReversePowerSum (n + 1) qLess *
          reflMallowsPayoffSum n qWeight
            (bestInSetPrefixCutTailWorstInsertPositionValue qMore remaining cut) -
        candidateRankReversePowerSum (n + 1) qMore *
          reflMallowsPayoffSum n qWeight
            (bestInSetPrefixCutTailWorstInsertPositionValue qLess remaining cut) := by
  classical
  unfold reflMallowsPayoffSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg ?_
  intro σ _
  have hweight :
      0 ≤ qWeight ^ kendallTau (Equiv.refl (Candidate n)) σ :=
    pow_nonneg hqWeight_nonneg _
  have hpoint :=
    bestInSetPrefixCutTailWorstInsertPositionValue_cross_nonneg
      hqMore_pos hq_lt remaining cut σ
  have hterm :
      candidateRankReversePowerSum (n + 1) qLess *
            (qWeight ^ kendallTau (Equiv.refl (Candidate n)) σ *
              bestInSetPrefixCutTailWorstInsertPositionValue
                qMore remaining cut σ) -
          candidateRankReversePowerSum (n + 1) qMore *
            (qWeight ^ kendallTau (Equiv.refl (Candidate n)) σ *
              bestInSetPrefixCutTailWorstInsertPositionValue
                qLess remaining cut σ)
        =
      qWeight ^ kendallTau (Equiv.refl (Candidate n)) σ *
        (candidateRankReversePowerSum (n + 1) qLess *
            bestInSetPrefixCutTailWorstInsertPositionValue
              qMore remaining cut σ -
          candidateRankReversePowerSum (n + 1) qMore *
            bestInSetPrefixCutTailWorstInsertPositionValue
              qLess remaining cut σ) := by
    ring
  rw [hterm]
  exact mul_nonneg hweight hpoint

theorem reflMallowsBestInSetPrefixCutSum_cross_of_last_mem_from_init_fixed_worstInsertPositionValue
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hlast : reflLastCandidate (n + 1) ∈ remaining)
    {cut : ℕ} (hcut : cut ≤ n + 1)
    (hinit :
      0 ≤
        mallowsPartition qLess (Equiv.refl (Candidate n)) *
            reflMallowsPayoffSum n qMore
              (bestInSetPrefixCutTailWorstInsertPositionValue qLess
                (initRemainingOf remaining) cut) -
          mallowsPartition qMore (Equiv.refl (Candidate n)) *
            reflMallowsPayoffSum n qLess
              (bestInSetPrefixCutTailWorstInsertPositionValue qLess
                (initRemainingOf remaining) cut)) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qMore remaining cut -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qLess remaining cut := by
  classical
  let init : Finset (Candidate n) := initRemainingOf remaining
  let GMore : Ranking n → ℝ :=
    bestInSetPrefixCutTailWorstInsertPositionValue qMore init cut
  let GLess : Ranking n → ℝ :=
    bestInSetPrefixCutTailWorstInsertPositionValue qLess init cut
  let PMore : ℝ := candidateRankReversePowerSum (n + 1) qMore
  let PLess : ℝ := candidateRankReversePowerSum (n + 1) qLess
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let SMoreGMore : ℝ := reflMallowsPayoffSum n qMore GMore
  let SMoreGLess : ℝ := reflMallowsPayoffSum n qMore GLess
  let SLessGLess : ℝ := reflMallowsPayoffSum n qLess GLess
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hZLess_nonneg : 0 ≤ ZLess :=
    le_of_lt (mallowsPartition_pos (hq := hqLess_pos)
      (Equiv.refl (Candidate n)))
  have hPMore_nonneg : 0 ≤ PMore :=
    le_of_lt (candidateRankReversePowerSum_pos (n + 1) hqMore_pos)
  have hinsert :
      0 ≤ PLess * SMoreGMore - PMore * SMoreGLess := by
    simpa [PLess, PMore, SMoreGMore, SMoreGLess, GMore, GLess, init] using
      reflMallowsPayoffSum_tailWorstInsertPositionValue_insertion_cross_nonneg
        (n := n) (qWeight := qMore) (qMore := qMore) (qLess := qLess)
        (le_of_lt hqMore_pos) hqMore_pos hq_lt
        (initRemainingOf remaining) cut
  have hinit' :
      0 ≤ ZLess * SMoreGLess - ZMore * SLessGLess := by
    simpa [ZLess, ZMore, SMoreGLess, SLessGLess, GLess, init] using hinit
  rw [
    reflMallowsBestInSetPrefixCutSum_eq_init_worstInsertPositionValue_of_last_mem
      n qMore hlast hcut,
    reflMallowsBestInSetPrefixCutSum_eq_init_worstInsertPositionValue_of_last_mem
      n qLess hlast hcut,
    mallowsPartition_refl_peelWorst n qLess,
    mallowsPartition_refl_peelWorst n qMore]
  change
    0 ≤
      (PLess * ZLess) * SMoreGMore -
        (PMore * ZMore) * SLessGLess
  have hdecomp :
      (PLess * ZLess) * SMoreGMore -
          (PMore * ZMore) * SLessGLess =
        ZLess * (PLess * SMoreGMore - PMore * SMoreGLess) +
          PMore * (ZLess * SMoreGLess - ZMore * SLessGLess) := by
    ring
  rw [hdecomp]
  exact add_nonneg
    (mul_nonneg hZLess_nonneg hinsert)
    (mul_nonneg hPMore_nonneg hinit')

theorem candidateRankWeightedAverage_cross_eq_pair_sum
    (n : ℕ) (qMore qLess : ℝ) (B : Candidate n → ℝ) :
    candidateRankPowerSum n qLess *
        (∑ i : Candidate n, qMore ^ (i : ℕ) * B i) -
      candidateRankPowerSum n qMore *
        (∑ i : Candidate n, qLess ^ (i : ℕ) * B i) =
      ∑ i : Candidate n, ∑ j : Candidate n,
        if i < j then
          (qMore ^ (i : ℕ) * qLess ^ (j : ℕ) -
              qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
            (B i - B j)
        else 0 := by
  classical
  let t : Candidate n → Candidate n → ℝ := fun i j =>
    qMore ^ (i : ℕ) * B i * qLess ^ (j : ℕ) -
      qLess ^ (i : ℕ) * B i * qMore ^ (j : ℕ)
  have hdouble :
      candidateRankPowerSum n qLess *
          (∑ i : Candidate n, qMore ^ (i : ℕ) * B i) -
        candidateRankPowerSum n qMore *
          (∑ i : Candidate n, qLess ^ (i : ℕ) * B i) =
        ∑ i : Candidate n, ∑ j : Candidate n, t i j := by
    unfold candidateRankPowerSum
    calc
      (∑ j : Candidate n, qLess ^ (j : ℕ)) *
            (∑ i : Candidate n, qMore ^ (i : ℕ) * B i) -
          (∑ j : Candidate n, qMore ^ (j : ℕ)) *
            (∑ i : Candidate n, qLess ^ (i : ℕ) * B i)
          =
        (∑ i : Candidate n, ∑ j : Candidate n,
            qLess ^ (j : ℕ) * (qMore ^ (i : ℕ) * B i)) -
          (∑ i : Candidate n, ∑ j : Candidate n,
            qMore ^ (j : ℕ) * (qLess ^ (i : ℕ) * B i)) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro i _
              rw [Finset.sum_mul]
            · refine Finset.sum_congr rfl ?_
              intro i _
              rw [Finset.sum_mul]
      _ = ∑ i : Candidate n, ∑ j : Candidate n, t i j := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro j _
            simp [t]
            ring
  rw [hdouble]
  rw [MallowsSpec.pair_sum_eq_ordered_swap_sum
    (Equiv.refl (Candidate n)) t
    (by intro i; simp [t]; ring)]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  by_cases hij : i < j
  · have hrank :
        rankOf (Equiv.refl (Candidate n)) i <
          rankOf (Equiv.refl (Candidate n)) j := by
        simpa [rankOf] using hij
    simp [hrank, hij, t]
    ring
  · have hrank :
        ¬ rankOf (Equiv.refl (Candidate n)) i <
          rankOf (Equiv.refl (Candidate n)) j := by
        simpa [rankOf] using hij
    simp [hrank, hij]

/--
Strict weighted-average comparison for geometric rank weights.  If the payoff
profile is antitone and has one genuine drop, the lower inverse Mallows
parameter has strictly larger cleared weighted average.
-/
theorem candidateRankWeightedAverage_anti_strict_of_exists
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    {B : Candidate n → ℝ}
    (hB : ∀ i j : Candidate n, i < j → B j ≤ B i)
    (hB_strict : ∃ i j : Candidate n, i < j ∧ B j < B i) :
    0 <
      candidateRankPowerSum n q₂ *
          (∑ i : Candidate n, q₁ ^ (i : ℕ) * B i) -
        candidateRankPowerSum n q₁ *
          (∑ i : Candidate n, q₂ ^ (i : ℕ) * B i) := by
  classical
  rw [candidateRankWeightedAverage_cross_eq_pair_sum]
  refine Finset.sum_pos' ?nonneg ?pos
  · intro i _
    refine Finset.sum_nonneg ?_
    intro j _
    by_cases hij : i < j
    · have hpow :
          0 < q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
            q₁ ^ (j : ℕ) * q₂ ^ (i : ℕ) :=
        sub_pos.mpr (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            rankPower_mul_lt_mul_rankPower hq₁_pos hq_lt hij)
      have hgap : 0 ≤ B i - B j :=
        sub_nonneg.mpr (hB i j hij)
      simp [hij, mul_nonneg (le_of_lt hpow) hgap]
    · simp [hij]
  · rcases hB_strict with ⟨i, j, hij, hstrict⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    refine Finset.sum_pos' ?inner_nonneg ?inner_pos
    · intro j' _
      by_cases hij' : i < j'
      · have hpow :
            0 < q₁ ^ (i : ℕ) * q₂ ^ (j' : ℕ) -
              q₁ ^ (j' : ℕ) * q₂ ^ (i : ℕ) :=
          sub_pos.mpr (by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              rankPower_mul_lt_mul_rankPower hq₁_pos hq_lt hij')
        have hgap : 0 ≤ B i - B j' :=
          sub_nonneg.mpr (hB i j' hij')
        simp [hij', mul_nonneg (le_of_lt hpow) hgap]
      · simp [hij']
    · refine ⟨j, Finset.mem_univ _, ?_⟩
      have hpow :
          0 < q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
            q₁ ^ (j : ℕ) * q₂ ^ (i : ℕ) :=
        sub_pos.mpr (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            rankPower_mul_lt_mul_rankPower hq₁_pos hq_lt hij)
      have hgap : 0 < B i - B j := sub_pos.mpr hstrict
      simp [hij, mul_pos hpow hgap]

theorem candidateRankWeightedAverage_cross_eq_adjacent_gap_sum
    (n : ℕ) (qMore qLess : ℝ) (B : Candidate n → ℝ) :
    candidateRankPowerSum n qLess *
        (∑ i : Candidate n, qMore ^ (i : ℕ) * B i) -
      candidateRankPowerSum n qMore *
        (∑ i : Candidate n, qLess ^ (i : ℕ) * B i) =
      ∑ k : Fin (n + 1),
        (candidateRankPowerSum n qLess *
            candidateRankInitialPowerSum n qMore k.castSucc -
          candidateRankPowerSum n qMore *
            candidateRankInitialPowerSum n qLess k.castSucc) *
          (B k.castSucc - B k.succ) := by
  classical
  let worst : ℝ := B (reflLastCandidate n)
  let gap : Fin (n + 1) → ℝ := fun k => B k.castSucc - B k.succ
  have hsum :
      ∀ q : ℝ,
        (∑ i : Candidate n, q ^ (i : ℕ) * B i) =
          candidateRankPowerSum n q * worst +
            ∑ k : Fin (n + 1),
              gap k * candidateRankInitialPowerSum n q k.castSucc := by
    intro q
    have hconst :
        (∑ i : Candidate n, q ^ (i : ℕ) * worst) =
          candidateRankPowerSum n q * worst := by
      unfold candidateRankPowerSum
      rw [Finset.sum_mul]
    have hdouble :
        (∑ i : Candidate n,
            q ^ (i : ℕ) *
              (∑ k : Fin (n + 1),
                if i ≤ k.castSucc then gap k else 0))
          =
        ∑ k : Fin (n + 1),
          gap k * candidateRankInitialPowerSum n q k.castSucc := by
      calc
        (∑ i : Candidate n,
            q ^ (i : ℕ) *
              (∑ k : Fin (n + 1),
                if i ≤ k.castSucc then gap k else 0))
            =
          ∑ i : Candidate n, ∑ k : Fin (n + 1),
            q ^ (i : ℕ) * (if i ≤ k.castSucc then gap k else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.mul_sum]
        _ =
          ∑ k : Fin (n + 1), ∑ i : Candidate n,
            q ^ (i : ℕ) * (if i ≤ k.castSucc then gap k else 0) := by
            rw [Finset.sum_comm]
        _ =
          ∑ k : Fin (n + 1),
            gap k * (∑ i : Candidate n,
              if i ≤ k.castSucc then q ^ (i : ℕ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro k _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            by_cases hik : i ≤ k.castSucc
            · simp [hik]
              ring
            · simp [hik]
        _ =
          ∑ k : Fin (n + 1),
            gap k * candidateRankInitialPowerSum n q k.castSucc := by
            rfl
    calc
      (∑ i : Candidate n, q ^ (i : ℕ) * B i)
          =
        ∑ i : Candidate n,
          q ^ (i : ℕ) *
            (worst +
              ∑ k : Fin (n + 1),
                if i ≤ k.castSucc then gap k else 0) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [value_eq_last_add_prefix_gaps B i]
      _ =
        (∑ i : Candidate n, q ^ (i : ℕ) * worst) +
          ∑ i : Candidate n,
            q ^ (i : ℕ) *
              (∑ k : Fin (n + 1),
                if i ≤ k.castSucc then gap k else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
      _ =
        candidateRankPowerSum n q * worst +
          ∑ k : Fin (n + 1),
            gap k * candidateRankInitialPowerSum n q k.castSucc := by
          rw [hconst, hdouble]
  rw [hsum qMore, hsum qLess]
  have hrewrite :
      candidateRankPowerSum n qLess *
            (candidateRankPowerSum n qMore * worst +
              ∑ k : Fin (n + 1),
                gap k * candidateRankInitialPowerSum n qMore k.castSucc) -
          candidateRankPowerSum n qMore *
            (candidateRankPowerSum n qLess * worst +
              ∑ k : Fin (n + 1),
                gap k * candidateRankInitialPowerSum n qLess k.castSucc)
        =
      ∑ k : Fin (n + 1),
        (candidateRankPowerSum n qLess *
            candidateRankInitialPowerSum n qMore k.castSucc -
          candidateRankPowerSum n qMore *
            candidateRankInitialPowerSum n qLess k.castSucc) *
          gap k := by
    calc
      candidateRankPowerSum n qLess *
            (candidateRankPowerSum n qMore * worst +
              ∑ k : Fin (n + 1),
                gap k * candidateRankInitialPowerSum n qMore k.castSucc) -
          candidateRankPowerSum n qMore *
            (candidateRankPowerSum n qLess * worst +
              ∑ k : Fin (n + 1),
                gap k * candidateRankInitialPowerSum n qLess k.castSucc)
          =
        candidateRankPowerSum n qLess *
              (∑ k : Fin (n + 1),
                gap k * candidateRankInitialPowerSum n qMore k.castSucc) -
            candidateRankPowerSum n qMore *
              (∑ k : Fin (n + 1),
                gap k * candidateRankInitialPowerSum n qLess k.castSucc) := by
          ring
      _ =
        ∑ k : Fin (n + 1),
          (candidateRankPowerSum n qLess *
              candidateRankInitialPowerSum n qMore k.castSucc -
            candidateRankPowerSum n qMore *
              candidateRankInitialPowerSum n qLess k.castSucc) *
            gap k := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro k _
          ring
  simpa [gap] using hrewrite

/--
One recursive induction step for identity-center Mallows payoff dominance using
the first-choice decomposition.

The first premise is the induction hypothesis on every tail payoff obtained by
fixing the first choice.  The second premise says the less-accurate tail payoff
sums are weakly decreasing as the first-choice center rank worsens.
-/
theorem reflMallowsPayoffSum_cross_of_firstChoice_step
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (F : Ranking (n + 1) → ℝ)
    (htail :
      ∀ r : Candidate (n + 1),
        0 ≤
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              reflMallowsPayoffSum n qMore
                (fun σ : Ranking n =>
                  F (rankingFirstChoiceOrderEquiv n (r, σ))) -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              reflMallowsPayoffSum n qLess
                (fun σ : Ranking n =>
                  F (rankingFirstChoiceOrderEquiv n (r, σ))))
    (hpos :
      ∀ p r : Candidate (n + 1), p < r →
        reflMallowsPayoffSum n qLess
          (fun σ : Ranking n =>
            F (rankingFirstChoiceOrderEquiv n (r, σ))) ≤
          reflMallowsPayoffSum n qLess
            (fun σ : Ranking n =>
              F (rankingFirstChoiceOrderEquiv n (p, σ)))) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qMore F -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qLess F := by
  classical
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let PMore : ℝ := candidateRankPowerSum (n + 1) qMore
  let PLess : ℝ := candidateRankPowerSum (n + 1) qLess
  let SMore : Candidate (n + 1) → ℝ := fun r =>
    reflMallowsPayoffSum n qMore
      (fun σ : Ranking n => F (rankingFirstChoiceOrderEquiv n (r, σ)))
  let SLess : Candidate (n + 1) → ℝ := fun r =>
    reflMallowsPayoffSum n qLess
      (fun σ : Ranking n => F (rankingFirstChoiceOrderEquiv n (r, σ)))
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have htail_sum :
      0 ≤
        ZLess * (∑ r : Candidate (n + 1),
            qMore ^ (r : ℕ) * SMore r) -
          ZMore * (∑ r : Candidate (n + 1),
            qMore ^ (r : ℕ) * SLess r) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_nonneg ?_
    intro r _
    have hr_nonneg : 0 ≤ qMore ^ (r : ℕ) :=
      pow_nonneg (le_of_lt hqMore_pos) (r : ℕ)
    have hr_tail : 0 ≤ ZLess * SMore r - ZMore * SLess r := by
      simpa [ZLess, ZMore, SMore, SLess] using htail r
    have hterm :
        ZLess * (qMore ^ (r : ℕ) * SMore r) -
            ZMore * (qMore ^ (r : ℕ) * SLess r) =
          qMore ^ (r : ℕ) * (ZLess * SMore r - ZMore * SLess r) := by
      ring
    rw [hterm]
    exact mul_nonneg hr_nonneg hr_tail
  have hweighted :
      0 ≤
        PLess * (∑ r : Candidate (n + 1),
            qMore ^ (r : ℕ) * SLess r) -
          PMore * (∑ r : Candidate (n + 1),
            qLess ^ (r : ℕ) * SLess r) := by
    have hB :
        ∀ p r : Candidate (n + 1), p < r → SLess r ≤ SLess p := by
      intro p r hpr
      exact hpos p r hpr
    simpa [PLess, PMore, SLess] using
      candidateRankWeightedAverage_anti
        (n + 1) hqMore_pos hq_lt (B := SLess) hB
  have hPLess_nonneg : 0 ≤ PLess :=
    le_of_lt (candidateRankPowerSum_pos (n + 1) hqLess_pos)
  have hZMore_nonneg : 0 ≤ ZMore :=
    le_of_lt (mallowsPartition_pos (hq := hqMore_pos)
      (Equiv.refl (Candidate n)))
  rw [mallowsPartition_refl_peelBest n qLess,
    mallowsPartition_refl_peelBest n qMore,
    reflMallowsPayoffSum_firstChoice n qMore F,
    reflMallowsPayoffSum_firstChoice n qLess F]
  change
    0 ≤
      (PLess * ZLess) *
          (∑ r : Candidate (n + 1), qMore ^ (r : ℕ) * SMore r) -
        (PMore * ZMore) *
          (∑ r : Candidate (n + 1), qLess ^ (r : ℕ) * SLess r)
  have hdecomp :
      (PLess * ZLess) *
          (∑ r : Candidate (n + 1), qMore ^ (r : ℕ) * SMore r) -
        (PMore * ZMore) *
          (∑ r : Candidate (n + 1), qLess ^ (r : ℕ) * SLess r)
        =
      PLess *
          (ZLess * (∑ r : Candidate (n + 1),
              qMore ^ (r : ℕ) * SMore r) -
            ZMore * (∑ r : Candidate (n + 1),
              qMore ^ (r : ℕ) * SLess r)) +
        ZMore *
          (PLess * (∑ r : Candidate (n + 1),
              qMore ^ (r : ℕ) * SLess r) -
            PMore * (∑ r : Candidate (n + 1),
              qLess ^ (r : ℕ) * SLess r)) := by
    ring
  rw [hdecomp]
  exact add_nonneg
    (mul_nonneg hPLess_nonneg htail_sum)
    (mul_nonneg hZMore_nonneg hweighted)

/-- Branch payoff sum after fixing the first choice in the first-choice
decomposition. -/
noncomputable def firstChoiceBranchPayoffSum
    (n : ℕ) (q : ℝ) (F : Ranking (n + 1) → ℝ)
    (r : Candidate (n + 1)) : ℝ :=
  reflMallowsPayoffSum n q
    (fun σ : Ranking n => F (rankingFirstChoiceOrderEquiv n (r, σ)))

/--
Cleared weighted first-choice comparison with the tail law held fixed.

This is the scalar expression isolated in
`ReflMallowsBestInSetPrefixCutFirstChoiceWeighted`; packaging it separately
keeps the arbitrary non-convex successor lemmas readable.
-/
noncomputable def firstChoiceBranchWeighted
    (n : ℕ) (qMore qLess qTail : ℝ)
    (F : Ranking (n + 1) → ℝ) : ℝ :=
  candidateRankPowerSum (n + 1) qLess *
      (∑ i : Candidate (n + 1),
        qMore ^ (i : ℕ) * firstChoiceBranchPayoffSum n qTail F i) -
    candidateRankPowerSum (n + 1) qMore *
      (∑ i : Candidate (n + 1),
        qLess ^ (i : ℕ) * firstChoiceBranchPayoffSum n qTail F i)

theorem firstChoiceBranchWeighted_nonneg_of_antitone
    (n : ℕ) {qMore qLess qTail : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (F : Ranking (n + 1) → ℝ)
    (hanti :
      ∀ i j : Candidate (n + 1), i < j →
        firstChoiceBranchPayoffSum n qTail F j ≤
          firstChoiceBranchPayoffSum n qTail F i) :
    0 ≤ firstChoiceBranchWeighted n qMore qLess qTail F := by
  simpa [firstChoiceBranchWeighted] using
    candidateRankWeightedAverage_anti
      (n + 1) hqMore_pos hq_lt
      (B := fun i : Candidate (n + 1) =>
        firstChoiceBranchPayoffSum n qTail F i)
      hanti

theorem firstChoiceBranchPayoffSum_add_const
    (n : ℕ) (q c : ℝ) (F : Ranking (n + 1) → ℝ)
    (r : Candidate (n + 1)) :
    firstChoiceBranchPayoffSum n q (fun τ => F τ + c) r =
      firstChoiceBranchPayoffSum n q F r +
        mallowsPartition q (Equiv.refl (Candidate n)) * c := by
  classical
  unfold firstChoiceBranchPayoffSum reflMallowsPayoffSum
  calc
    (∑ σ : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          (F (rankingFirstChoiceOrderEquiv n (r, σ)) + c))
        =
      ∑ σ : Ranking n,
        (q ^ kendallTau (Equiv.refl (Candidate n)) σ *
            F (rankingFirstChoiceOrderEquiv n (r, σ)) +
          q ^ kendallTau (Equiv.refl (Candidate n)) σ * c) := by
        refine Finset.sum_congr rfl ?_
        intro σ _
        ring
    _ =
      (∑ σ : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          F (rankingFirstChoiceOrderEquiv n (r, σ))) +
        ∑ σ : Ranking n,
          q ^ kendallTau (Equiv.refl (Candidate n)) σ * c := by
        rw [Finset.sum_add_distrib]
    _ =
      (∑ σ : Ranking n,
        q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          F (rankingFirstChoiceOrderEquiv n (r, σ))) +
        mallowsPartition q (Equiv.refl (Candidate n)) * c := by
        rw [← Finset.sum_mul]
        rfl

theorem firstChoiceBranchWeighted_add_const
    (n : ℕ) (qMore qLess qTail c : ℝ)
    (F : Ranking (n + 1) → ℝ) :
    firstChoiceBranchWeighted n qMore qLess qTail (fun τ => F τ + c) =
      firstChoiceBranchWeighted n qMore qLess qTail F := by
  classical
  unfold firstChoiceBranchWeighted
  simp_rw [firstChoiceBranchPayoffSum_add_const n qTail c F]
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hMore :
      (∑ i : Candidate (n + 1),
        qMore ^ (i : ℕ) *
          (mallowsPartition qTail (Equiv.refl (Candidate n)) * c)) =
        candidateRankPowerSum (n + 1) qMore *
          (mallowsPartition qTail (Equiv.refl (Candidate n)) * c) := by
    unfold candidateRankPowerSum
    rw [Finset.sum_mul]
  have hLess :
      (∑ i : Candidate (n + 1),
        qLess ^ (i : ℕ) *
          (mallowsPartition qTail (Equiv.refl (Candidate n)) * c)) =
        candidateRankPowerSum (n + 1) qLess *
          (mallowsPartition qTail (Equiv.refl (Candidate n)) * c) := by
    unfold candidateRankPowerSum
    rw [Finset.sum_mul]
  rw [hMore, hLess]
  ring

theorem firstChoiceBranchWeighted_nonneg_of_branch_covariance
    (n : ℕ) {qMore qLess : ℝ} (hqLess_pos : 0 < qLess)
    (F : Ranking (n + 1) → ℝ)
    (hcov :
      0 ≤
        (∑ i : Candidate (n + 1),
          qMore ^ (i : ℕ) * firstChoiceBranchPayoffSum n qLess F i) *
            (candidateRankPowerSum (n + 1) qLess *
              mallowsPartition qLess (Equiv.refl (Candidate n))) -
          (∑ i : Candidate (n + 1),
            qLess ^ (i : ℕ) * firstChoiceBranchPayoffSum n qLess F i) *
            (candidateRankPowerSum (n + 1) qMore *
              mallowsPartition qLess (Equiv.refl (Candidate n)))) :
    0 ≤ firstChoiceBranchWeighted n qMore qLess qLess F := by
  classical
  let Z : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  have hZpos : 0 < Z := by
    simpa [Z] using
      (mallowsPartition_pos (hq := hqLess_pos)
        (Equiv.refl (Candidate n)))
  have hcov_eq :
      (∑ i : Candidate (n + 1),
          qMore ^ (i : ℕ) * firstChoiceBranchPayoffSum n qLess F i) *
            (candidateRankPowerSum (n + 1) qLess *
              mallowsPartition qLess (Equiv.refl (Candidate n))) -
          (∑ i : Candidate (n + 1),
            qLess ^ (i : ℕ) * firstChoiceBranchPayoffSum n qLess F i) *
            (candidateRankPowerSum (n + 1) qMore *
              mallowsPartition qLess (Equiv.refl (Candidate n))) =
        Z * firstChoiceBranchWeighted n qMore qLess qLess F := by
    simp [Z, firstChoiceBranchWeighted]
    ring
  rw [hcov_eq] at hcov
  exact nonneg_of_mul_nonneg_right hcov hZpos

theorem firstChoiceBranchWeighted_pos_of_branch_covariance
    (n : ℕ) {qMore qLess : ℝ} (hqLess_pos : 0 < qLess)
    (F : Ranking (n + 1) → ℝ)
    (hcov :
      0 <
        (∑ i : Candidate (n + 1),
          qMore ^ (i : ℕ) * firstChoiceBranchPayoffSum n qLess F i) *
            (candidateRankPowerSum (n + 1) qLess *
              mallowsPartition qLess (Equiv.refl (Candidate n))) -
          (∑ i : Candidate (n + 1),
            qLess ^ (i : ℕ) * firstChoiceBranchPayoffSum n qLess F i) *
            (candidateRankPowerSum (n + 1) qMore *
              mallowsPartition qLess (Equiv.refl (Candidate n)))) :
    0 < firstChoiceBranchWeighted n qMore qLess qLess F := by
  classical
  let Z : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  have hZpos : 0 < Z := by
    simpa [Z] using
      (mallowsPartition_pos (hq := hqLess_pos)
        (Equiv.refl (Candidate n)))
  have hcov_eq :
      (∑ i : Candidate (n + 1),
          qMore ^ (i : ℕ) * firstChoiceBranchPayoffSum n qLess F i) *
            (candidateRankPowerSum (n + 1) qLess *
              mallowsPartition qLess (Equiv.refl (Candidate n))) -
          (∑ i : Candidate (n + 1),
            qLess ^ (i : ℕ) * firstChoiceBranchPayoffSum n qLess F i) *
            (candidateRankPowerSum (n + 1) qMore *
              mallowsPartition qLess (Equiv.refl (Candidate n))) =
        Z * firstChoiceBranchWeighted n qMore qLess qLess F := by
    simp [Z, firstChoiceBranchWeighted]
    ring
  rw [hcov_eq] at hcov
  rw [mul_comm] at hcov
  exact pos_of_mul_pos_left hcov hZpos.le

theorem reflMallowsPayoffSum_eq_firstChoiceBranchPayoffSum
    (n : ℕ) (q : ℝ) (F : Ranking (n + 1) → ℝ) :
    reflMallowsPayoffSum (n + 1) q F =
      ∑ i : Candidate (n + 1),
        q ^ (i : ℕ) * firstChoiceBranchPayoffSum n q F i := by
  simpa [firstChoiceBranchPayoffSum] using
    reflMallowsPayoffSum_firstChoice n q F

theorem reflMallowsPayoffSum_firstChoiceGeom_eq_branch
    (n : ℕ) {qMore qLess : ℝ} (hqLess_ne : qLess ≠ 0)
    (F : Ranking (n + 1) → ℝ) :
    reflMallowsPayoffSum (n + 1) qLess
        (fun π =>
          F π * (qMore / qLess) ^
            ((firstChoice π : Candidate (n + 1)) : ℕ)) =
      ∑ i : Candidate (n + 1),
        qMore ^ (i : ℕ) * firstChoiceBranchPayoffSum n qLess F i := by
  classical
  rw [reflMallowsPayoffSum_firstChoice]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp_rw [firstChoice_rankingFirstChoiceOrderEquiv]
  rw [reflMallowsPayoffSum_mul_const]
  have hpow :
      qLess ^ (i : ℕ) * (qMore / qLess) ^ (i : ℕ) =
        qMore ^ (i : ℕ) := by
    rw [div_pow]
    field_simp [pow_ne_zero (i : ℕ) hqLess_ne]
  unfold firstChoiceBranchPayoffSum
  calc
    qLess ^ (i : ℕ) *
        (reflMallowsPayoffSum n qLess
          (fun σ => F (rankingFirstChoiceOrderEquiv n (i, σ))) *
          (qMore / qLess) ^ (i : ℕ))
        =
      (qLess ^ (i : ℕ) * (qMore / qLess) ^ (i : ℕ)) *
        reflMallowsPayoffSum n qLess
          (fun σ => F (rankingFirstChoiceOrderEquiv n (i, σ))) := by
        ring
    _ =
      qMore ^ (i : ℕ) *
        reflMallowsPayoffSum n qLess
          (fun σ => F (rankingFirstChoiceOrderEquiv n (i, σ))) := by
        rw [hpow]
    _ =
      qMore ^ (i : ℕ) *
        reflMallowsPayoffSum n qLess
          (fun σ => F (rankingFirstChoiceOrderEquiv n (i, σ))) := rfl

theorem reflMallowsPayoffSum_firstChoiceGeom_one_eq
    (n : ℕ) {qMore qLess : ℝ} (hqLess_ne : qLess ≠ 0) :
    reflMallowsPayoffSum (n + 1) qLess
        (fun π : Ranking (n + 1) =>
          (qMore / qLess) ^
            ((firstChoice π : Candidate (n + 1)) : ℕ)) =
      candidateRankPowerSum (n + 1) qMore *
        mallowsPartition qLess (Equiv.refl (Candidate n)) := by
  classical
  calc
    reflMallowsPayoffSum (n + 1) qLess
        (fun π : Ranking (n + 1) =>
          (qMore / qLess) ^
            ((firstChoice π : Candidate (n + 1)) : ℕ))
        =
      ∑ i : Candidate (n + 1),
        qMore ^ (i : ℕ) *
          firstChoiceBranchPayoffSum n qLess
            (fun _ : Ranking (n + 1) => (1 : ℝ)) i := by
        simpa using
          reflMallowsPayoffSum_firstChoiceGeom_eq_branch
            n hqLess_ne (fun _ : Ranking (n + 1) => (1 : ℝ))
    _ =
      candidateRankPowerSum (n + 1) qMore *
        mallowsPartition qLess (Equiv.refl (Candidate n)) := by
        have hbranch :
            ∀ i : Candidate (n + 1),
              firstChoiceBranchPayoffSum n qLess
                  (fun _ : Ranking (n + 1) => (1 : ℝ)) i =
                mallowsPartition qLess (Equiv.refl (Candidate n)) := by
          intro i
          unfold firstChoiceBranchPayoffSum
          rw [reflMallowsPayoffSum_const]
          ring
        simp_rw [hbranch]
        unfold candidateRankPowerSum
        rw [Finset.sum_mul]

theorem firstChoiceBranchCovariance_eq_mallowsGeomCovariance
    (n : ℕ) {qMore qLess : ℝ} (hqLess_ne : qLess ≠ 0)
    (F : Ranking (n + 1) → ℝ) :
    (∑ i : Candidate (n + 1),
        qMore ^ (i : ℕ) * firstChoiceBranchPayoffSum n qLess F i) *
        (candidateRankPowerSum (n + 1) qLess *
          mallowsPartition qLess (Equiv.refl (Candidate n))) -
      (∑ i : Candidate (n + 1),
        qLess ^ (i : ℕ) * firstChoiceBranchPayoffSum n qLess F i) *
        (candidateRankPowerSum (n + 1) qMore *
          mallowsPartition qLess (Equiv.refl (Candidate n))) =
      reflMallowsPayoffSum (n + 1) qLess
          (fun π =>
            F π * (qMore / qLess) ^
              ((firstChoice π : Candidate (n + 1)) : ℕ)) *
        mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) -
      reflMallowsPayoffSum (n + 1) qLess F *
        reflMallowsPayoffSum (n + 1) qLess
          (fun π : Ranking (n + 1) =>
            (qMore / qLess) ^
              ((firstChoice π : Candidate (n + 1)) : ℕ)) := by
  rw [reflMallowsPayoffSum_firstChoiceGeom_eq_branch n hqLess_ne F,
    reflMallowsPayoffSum_eq_firstChoiceBranchPayoffSum,
    reflMallowsPayoffSum_firstChoiceGeom_one_eq n hqLess_ne,
    mallowsPartition_refl_peelBest]

theorem firstChoiceRankPairCoeff_nonneg
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) {i j : Candidate (n + 1)}
    (hij : i < j) :
    0 ≤
      qMore ^ (i : ℕ) * qLess ^ (j : ℕ) -
        qMore ^ (j : ℕ) * qLess ^ (i : ℕ) :=
   le_of_lt (sub_pos.mpr (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      rankPower_mul_lt_mul_rankPower hqMore_pos hq_lt hij))

theorem firstChoiceBranchPayoffSum_prefixCut
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ)
    (r : Candidate (n + 1)) :
    firstChoiceBranchPayoffSum n q
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ) r =
      if r ∈ remaining then
        mallowsPartition q (Equiv.refl (Candidate n)) *
          (if (r : ℕ) < cut then (1 : ℝ) else 0)
      else
        reflMallowsBestInSetPrefixCutSum n q
          (firstChoiceTailRemainingOf r remaining)
          (deleteFirstChoicePrefixCut r cut) := by
  classical
  unfold firstChoiceBranchPayoffSum
  by_cases hr : r ∈ remaining
  · rw [if_pos hr]
    have hbranch :
        reflMallowsPayoffSum n q
            (fun σ : Ranking n =>
              bestInSetPrefixCutIndicator remaining cut
                (rankingFirstChoiceOrderEquiv n (r, σ))) =
          reflMallowsPayoffSum n q
            (fun _ : Ranking n =>
              if (r : ℕ) < cut then (1 : ℝ) else 0) := by
      unfold reflMallowsPayoffSum
      refine Finset.sum_congr rfl ?_
      intro σ _
      change
        q ^ kendallTau (Equiv.refl (Candidate n)) σ *
            bestInSetPrefixCutIndicator remaining cut
              (rankingFirstChoiceOrderEquiv n (r, σ)) =
          q ^ kendallTau (Equiv.refl (Candidate n)) σ *
            (if (r : ℕ) < cut then (1 : ℝ) else 0)
      rw [bestInSetPrefixCutIndicator_rankingFirstChoiceOrderEquiv
        hremaining cut r σ]
      simp [hr]
    rw [hbranch, reflMallowsPayoffSum_const]
  · rw [if_neg hr]
    unfold reflMallowsBestInSetPrefixCutSum
    unfold reflMallowsPayoffSum
    refine Finset.sum_congr rfl ?_
    intro σ _
    change
      q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          bestInSetPrefixCutIndicator remaining cut
            (rankingFirstChoiceOrderEquiv n (r, σ)) =
        q ^ kendallTau (Equiv.refl (Candidate n)) σ *
          bestInSetPrefixCutIndicator
            (firstChoiceTailRemainingOf r remaining)
            (deleteFirstChoicePrefixCut r cut) σ
    rw [bestInSetPrefixCutIndicator_rankingFirstChoiceOrderEquiv
      hremaining cut r σ]
    simp [hr]

theorem firstChoiceBranchPayoffSum_prefixCut_eq_sum_bestInSetWeight_of_not_mem
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    {r : Candidate (n + 1)} (hr : r ∉ remaining) :
    firstChoiceBranchPayoffSum n q
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ) r =
      ∑ c : Candidate n,
        if ((c : Candidate n) : ℕ) < deleteFirstChoicePrefixCut r cut then
          reflMallowsBestInSetWeight n q
            (firstChoiceTailRemainingOf r remaining) c
        else
          0 := by
  classical
  rw [firstChoiceBranchPayoffSum_prefixCut n q hremaining cut r]
  rw [if_neg hr]
  exact
    reflMallowsBestInSetPrefixCutSum_eq_sum_bestInSetWeight
      n q
      (firstChoiceTailRemainingOf_nonempty_of_nonempty_of_first_not_mem
        hremaining hr)
      (deleteFirstChoicePrefixCut r cut)

theorem firstChoiceBranchPayoffSum_prefixCut_nonneg
    (n : ℕ) {q : ℝ} (hq_nonneg : 0 ≤ q)
    {remaining : Finset (Candidate (n + 1))} (cut : ℕ)
    (r : Candidate (n + 1)) :
    0 ≤
      firstChoiceBranchPayoffSum n q
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ) r := by
  classical
  unfold firstChoiceBranchPayoffSum reflMallowsPayoffSum
  exact Finset.sum_nonneg (by
    intro σ _
    exact mul_nonneg
      (pow_nonneg hq_nonneg _)
      (bestInSetPrefixCutIndicator_nonneg remaining cut
        (rankingFirstChoiceOrderEquiv n (r, σ))))

theorem firstChoiceBranchPayoffSum_prefixCut_le_partition
    (n : ℕ) {q : ℝ} (hq_nonneg : 0 ≤ q)
    {remaining : Finset (Candidate (n + 1))} (cut : ℕ)
    (r : Candidate (n + 1)) :
    firstChoiceBranchPayoffSum n q
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ) r ≤
      mallowsPartition q (Equiv.refl (Candidate n)) := by
  classical
  unfold firstChoiceBranchPayoffSum reflMallowsPayoffSum
    mallowsPartition mallowsWeight
  refine Finset.sum_le_sum ?_
  intro σ _
  have hweight : 0 ≤ q ^ kendallTau (Equiv.refl (Candidate n)) σ :=
    pow_nonneg hq_nonneg _
  have hindicator :=
    bestInSetPrefixCutIndicator_le_one remaining cut
      (rankingFirstChoiceOrderEquiv n (r, σ))
  calc
    q ^ kendallTau (Equiv.refl (Candidate n)) σ *
        bestInSetPrefixCutIndicator remaining cut
          (rankingFirstChoiceOrderEquiv n (r, σ))
        ≤ q ^ kendallTau (Equiv.refl (Candidate n)) σ * 1 :=
          mul_le_mul_of_nonneg_left hindicator hweight
    _ = q ^ kendallTau (Equiv.refl (Candidate n)) σ := by ring

theorem firstChoiceBranchPayoffSum_prefixCut_eq_partition_of_mem_lt
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    {r : Candidate (n + 1)} (hr : r ∈ remaining)
    (hr_cut : (r : ℕ) < cut) :
    firstChoiceBranchPayoffSum n q
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ) r =
      mallowsPartition q (Equiv.refl (Candidate n)) := by
  rw [firstChoiceBranchPayoffSum_prefixCut n q hremaining cut r]
  simp [hr, hr_cut]

theorem firstChoiceBranchPayoffSum_prefixCut_eq_zero_of_mem_ge
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    {r : Candidate (n + 1)} (hr : r ∈ remaining)
    (hr_cut : cut ≤ (r : ℕ)) :
    firstChoiceBranchPayoffSum n q
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ) r = 0 := by
  rw [firstChoiceBranchPayoffSum_prefixCut n q hremaining cut r]
  have hnot : ¬(r : ℕ) < cut := not_lt_of_ge hr_cut
  simp [hr, hnot]

theorem firstChoiceBranchPayoffSum_prefixCut_eq_of_adjacent_not_mem
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ) (k : Candidate n)
    (hcast : k.castSucc ∉ remaining) (hsucc : k.succ ∉ remaining) :
    firstChoiceBranchPayoffSum n q
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ) k.castSucc =
      firstChoiceBranchPayoffSum n q
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ) k.succ := by
  classical
  rw [firstChoiceBranchPayoffSum_prefixCut n q hremaining cut k.castSucc,
    firstChoiceBranchPayoffSum_prefixCut n q hremaining cut k.succ]
  simp only [hcast, hsucc, if_false]
  have htail_eq :
      firstChoiceTailRemainingOf k.castSucc remaining =
        firstChoiceTailRemainingOf k.succ remaining :=
    firstChoiceTailRemainingOf_castSucc_eq_succ_of_not_mem
      k hcast hsucc
  rw [htail_eq]
  by_cases hsucc_cut : ((k.succ : Candidate (n + 1)) : ℕ) < cut
  · have hcast_cut : ((k.castSucc : Candidate (n + 1)) : ℕ) < cut := by
      have hlt : ((k.castSucc : Candidate (n + 1)) : ℕ) <
          ((k.succ : Candidate (n + 1)) : ℕ) :=
        k.castSucc_lt_succ
      omega
    unfold deleteFirstChoicePrefixCut
    have hk_lt : (k : ℕ) < cut := by
      simpa using hcast_cut
    have hk1_lt : (k : ℕ) + 1 < cut := by
      simpa using hsucc_cut
    simp [hk_lt, hk1_lt]
  · by_cases hcast_cut : ((k.castSucc : Candidate (n + 1)) : ℕ) < cut
    · have hcut_eq : cut = ((k.succ : Candidate (n + 1)) : ℕ) := by
        have hsucc_val :
            ((k.succ : Candidate (n + 1)) : ℕ) =
              ((k.castSucc : Candidate (n + 1)) : ℕ) + 1 := by
          rfl
        omega
      have htail_nonempty :
          (firstChoiceTailRemainingOf k.succ remaining).Nonempty :=
                  firstChoiceTailRemainingOf_nonempty_of_nonempty_of_first_not_mem
            hremaining hsucc
      have hk_tail :
          k ∉ firstChoiceTailRemainingOf k.succ remaining := by
        intro hk
        have hmem : k.succ.succAbove k ∈ remaining := by
          simpa using hk
        have hright : k.succ.succAbove k = k.castSucc := by
          simpa using Fin.succAbove_pred_self k.succ (Fin.succ_ne_zero k)
        exact hcast (by simpa [hright] using hmem)
      have hdel_cast :
          deleteFirstChoicePrefixCut k.castSucc cut = (k : ℕ) := by
        unfold deleteFirstChoicePrefixCut
        simp [hcut_eq]
      have hdel_succ :
          deleteFirstChoicePrefixCut k.succ cut = (k : ℕ) + 1 := by
        unfold deleteFirstChoicePrefixCut
        have hnot : ¬ ((k.succ : Candidate (n + 1)) : ℕ) < cut := by
          simpa [hcut_eq] using hsucc_cut
        simp [hcut_eq]
      rw [hdel_cast, hdel_succ]
      exact
        reflMallowsBestInSetPrefixCutSum_eq_of_adjacent_cut_not_mem
          n q htail_nonempty hk_tail
    · have hsucc_not : ¬ ((k.succ : Candidate (n + 1)) : ℕ) < cut := hsucc_cut
      unfold deleteFirstChoicePrefixCut
      have hk_not : ¬ (k : ℕ) < cut := by
        simpa using hcast_cut
      have hk1_not : ¬ (k : ℕ) + 1 < cut := by
        simpa using hsucc_not
      simp [hk_not, hk1_not]

/--
Outside first-choice branches are constant across a whole consecutive hole in
the remaining set.

This iterates `firstChoiceBranchPayoffSum_prefixCut_eq_of_adjacent_not_mem`;
it is the basic local constancy fact needed for block-cancellation proofs of
the reduced Mallows first-choice target.
-/
theorem firstChoiceBranchPayoffSum_prefixCut_eq_of_not_mem_interval
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ)
    {r s : Candidate (n + 1)} (hrs : r ≤ s)
    (hnot :
      ∀ x : Candidate (n + 1), r ≤ x → x ≤ s → x ∉ remaining) :
    firstChoiceBranchPayoffSum n q
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ) r =
      firstChoiceBranchPayoffSum n q
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ) s := by
  classical
  revert r
  induction s using Fin.strong_induction_on with
  | h s ih =>
      intro r hrs hnot
      by_cases hsr : s = r
      · subst s
        rfl
      · have hr_lt_s : r < s := lt_of_le_of_ne hrs (Ne.symm hsr)
        have hs_ne_zero : s ≠ (0 : Candidate (n + 1)) :=
          Fin.ne_of_gt (lt_of_le_of_lt (Fin.zero_le r) hr_lt_s)
        let prev : Candidate (n + 1) := (s.pred hs_ne_zero).castSucc
        have hprev_lt_s : prev < s := by
          simpa [prev] using (s.pred hs_ne_zero).castSucc_lt_succ
        have hr_le_prev : r ≤ prev := by
          rw [Fin.le_iff_val_le_val]
          have hr_lt_val : r.val < s.val := hr_lt_s
          have hs_val_ne_zero : s.val ≠ 0 := by
            intro hval
            exact hs_ne_zero (Fin.ext hval)
          simp [prev, Fin.val_pred]
          omega
        have htail :
            firstChoiceBranchPayoffSum n q
                (fun τ : Ranking (n + 1) =>
                  bestInSetPrefixCutIndicator remaining cut τ) r =
              firstChoiceBranchPayoffSum n q
                (fun τ : Ranking (n + 1) =>
                  bestInSetPrefixCutIndicator remaining cut τ) prev :=
          ih prev hprev_lt_s hr_le_prev (by
            intro x hrx hxprev
            exact hnot x hrx (le_trans hxprev (le_of_lt hprev_lt_s)))
        have hprev_not : prev ∉ remaining :=
          hnot prev hr_le_prev (le_of_lt hprev_lt_s)
        have hs_not : s ∉ remaining := hnot s hrs le_rfl
        have hs_succ_not : (s.pred hs_ne_zero).succ ∉ remaining := by
          simpa using hs_not
        have hstep :
            firstChoiceBranchPayoffSum n q
                (fun τ : Ranking (n + 1) =>
                  bestInSetPrefixCutIndicator remaining cut τ) prev =
              firstChoiceBranchPayoffSum n q
                (fun τ : Ranking (n + 1) =>
                  bestInSetPrefixCutIndicator remaining cut τ) s := by
          simpa [prev] using
            firstChoiceBranchPayoffSum_prefixCut_eq_of_adjacent_not_mem
              n q hremaining cut (s.pred hs_ne_zero) hprev_not hs_succ_not
        exact htail.trans hstep

theorem firstChoiceBranchWeighted_pairTerm_nonneg_of_remaining_lt_ge
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    {i j : Candidate (n + 1)} (hij : i < j)
    (hi : i ∈ remaining) (hj : j ∈ remaining)
    (hi_cut : (i : ℕ) < cut) (hj_cut : cut ≤ (j : ℕ)) :
    0 ≤
      (qMore ^ (i : ℕ) * qLess ^ (j : ℕ) -
          qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
        (firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) i -
          firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) j) := by
  classical
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hcoeff :=
    firstChoiceRankPairCoeff_nonneg
      (n := n) hqMore_pos hq_lt hij
  have hZ_nonneg :
      0 ≤ mallowsPartition qLess (Equiv.refl (Candidate n)) :=
    le_of_lt (mallowsPartition_pos (hq := hqLess_pos)
      (Equiv.refl (Candidate n)))
  have hi_sum :
      firstChoiceBranchPayoffSum n qLess
          (fun τ : Ranking (n + 1) =>
            bestInSetPrefixCutIndicator remaining cut τ) i =
        mallowsPartition qLess (Equiv.refl (Candidate n)) := by
    rw [firstChoiceBranchPayoffSum_prefixCut n qLess hremaining cut i]
    simp [hi, hi_cut]
  have hj_sum :
      firstChoiceBranchPayoffSum n qLess
          (fun τ : Ranking (n + 1) =>
            bestInSetPrefixCutIndicator remaining cut τ) j = 0 := by
    rw [firstChoiceBranchPayoffSum_prefixCut n qLess hremaining cut j]
    have hnot : ¬(j : ℕ) < cut := not_lt_of_ge hj_cut
    simp [hj, hnot]
  rw [hi_sum, hj_sum, sub_zero]
  exact mul_nonneg hcoeff hZ_nonneg

theorem firstChoiceBranchWeighted_pairTerm_eq_zero_of_remaining_lt_lt
    (n : ℕ) (qMore qLess : ℝ)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    {i j : Candidate (n + 1)}
    (hi : i ∈ remaining) (hj : j ∈ remaining)
    (hi_cut : (i : ℕ) < cut) (hj_cut : (j : ℕ) < cut) :
    (qMore ^ (i : ℕ) * qLess ^ (j : ℕ) -
        qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
      (firstChoiceBranchPayoffSum n qLess
          (fun τ : Ranking (n + 1) =>
            bestInSetPrefixCutIndicator remaining cut τ) i -
        firstChoiceBranchPayoffSum n qLess
          (fun τ : Ranking (n + 1) =>
            bestInSetPrefixCutIndicator remaining cut τ) j) = 0 := by
  rw [
    firstChoiceBranchPayoffSum_prefixCut_eq_partition_of_mem_lt
      n qLess hremaining hi hi_cut,
    firstChoiceBranchPayoffSum_prefixCut_eq_partition_of_mem_lt
      n qLess hremaining hj hj_cut]
  ring

theorem firstChoiceBranchWeighted_pairTerm_eq_zero_of_remaining_ge_ge
    (n : ℕ) (qMore qLess : ℝ)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    {i j : Candidate (n + 1)}
    (hi : i ∈ remaining) (hj : j ∈ remaining)
    (hi_cut : cut ≤ (i : ℕ)) (hj_cut : cut ≤ (j : ℕ)) :
    (qMore ^ (i : ℕ) * qLess ^ (j : ℕ) -
        qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
      (firstChoiceBranchPayoffSum n qLess
          (fun τ : Ranking (n + 1) =>
            bestInSetPrefixCutIndicator remaining cut τ) i -
        firstChoiceBranchPayoffSum n qLess
          (fun τ : Ranking (n + 1) =>
            bestInSetPrefixCutIndicator remaining cut τ) j) = 0 := by
  rw [
    firstChoiceBranchPayoffSum_prefixCut_eq_zero_of_mem_ge
      n qLess hremaining hi hi_cut,
    firstChoiceBranchPayoffSum_prefixCut_eq_zero_of_mem_ge
      n qLess hremaining hj hj_cut]
  ring

theorem firstChoiceBranchWeighted_pairTerm_nonneg_of_remaining_lt_notMem
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    {i j : Candidate (n + 1)} (hij : i < j)
    (hi : i ∈ remaining) (hj : j ∉ remaining)
    (hi_cut : (i : ℕ) < cut) :
    0 ≤
      (qMore ^ (i : ℕ) * qLess ^ (j : ℕ) -
          qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
        (firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) i -
          firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) j) := by
  classical
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hcoeff :=
    firstChoiceRankPairCoeff_nonneg
      (n := n) hqMore_pos hq_lt hij
  have hi_sum :
      firstChoiceBranchPayoffSum n qLess
          (fun τ : Ranking (n + 1) =>
            bestInSetPrefixCutIndicator remaining cut τ) i =
        mallowsPartition qLess (Equiv.refl (Candidate n)) := by
    rw [firstChoiceBranchPayoffSum_prefixCut n qLess hremaining cut i]
    simp [hi, hi_cut]
  have hj_le :
      firstChoiceBranchPayoffSum n qLess
          (fun τ : Ranking (n + 1) =>
            bestInSetPrefixCutIndicator remaining cut τ) j ≤
        mallowsPartition qLess (Equiv.refl (Candidate n)) :=
    firstChoiceBranchPayoffSum_prefixCut_le_partition
      n (le_of_lt hqLess_pos) cut j
  have hdiff :
      0 ≤
        firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) i -
          firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) j := by
    rw [hi_sum]
    exact sub_nonneg.mpr hj_le
  exact mul_nonneg hcoeff hdiff

theorem firstChoiceBranchWeighted_pairTerm_nonneg_of_notMem_remaining_ge
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    {i j : Candidate (n + 1)} (hij : i < j)
    (hi : i ∉ remaining) (hj : j ∈ remaining)
    (hj_cut : cut ≤ (j : ℕ)) :
    0 ≤
      (qMore ^ (i : ℕ) * qLess ^ (j : ℕ) -
          qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
        (firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) i -
          firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) j) := by
  classical
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hcoeff :=
    firstChoiceRankPairCoeff_nonneg
      (n := n) hqMore_pos hq_lt hij
  have hj_sum :
      firstChoiceBranchPayoffSum n qLess
          (fun τ : Ranking (n + 1) =>
            bestInSetPrefixCutIndicator remaining cut τ) j = 0 := by
    rw [firstChoiceBranchPayoffSum_prefixCut n qLess hremaining cut j]
    have hnot : ¬(j : ℕ) < cut := not_lt_of_ge hj_cut
    simp [hj, hnot]
  have hi_nonneg :
      0 ≤ firstChoiceBranchPayoffSum n qLess
          (fun τ : Ranking (n + 1) =>
            bestInSetPrefixCutIndicator remaining cut τ) i :=
    firstChoiceBranchPayoffSum_prefixCut_nonneg
      n (le_of_lt hqLess_pos) cut i
  have hdiff :
      0 ≤
        firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) i -
          firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) j := by
    rw [hj_sum, sub_zero]
    exact hi_nonneg
  exact mul_nonneg hcoeff hdiff

theorem firstChoiceBranchPayoffSum_const
    (n : ℕ) (q a : ℝ) (r : Candidate (n + 1)) :
    firstChoiceBranchPayoffSum n q (fun _ : Ranking (n + 1) => a) r =
      mallowsPartition q (Equiv.refl (Candidate n)) * a := by
  unfold firstChoiceBranchPayoffSum
  rw [reflMallowsPayoffSum_const]

theorem firstChoiceBranchPayoffSum_prefixCut_eq_partition_of_forall_remaining_lt
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    (hcut : ∀ c : Candidate (n + 1), c ∈ remaining → (c : ℕ) < cut)
    (r : Candidate (n + 1)) :
    firstChoiceBranchPayoffSum n q
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ) r =
      mallowsPartition q (Equiv.refl (Candidate n)) := by
  classical
  rw [firstChoiceBranchPayoffSum_prefixCut n q hremaining cut r]
  by_cases hr : r ∈ remaining
  · simp [hr, hcut r hr]
  · have htail :
        ∀ c : Candidate n, c ∈ firstChoiceTailRemainingOf r remaining →
          (c : ℕ) < deleteFirstChoicePrefixCut r cut := by
      intro c hc
      have hc_full : r.succAbove c ∈ remaining := by
        simpa using hc
      exact
        (succAbove_val_lt_deleteFirstChoicePrefixCut_iff r c cut).mp
          (hcut (r.succAbove c) hc_full)
    have htail_nonempty :
        (firstChoiceTailRemainingOf r remaining).Nonempty :=
      firstChoiceTailRemainingOf_nonempty_of_nonempty_of_first_not_mem
        hremaining hr
    simp [hr,
      reflMallowsBestInSetPrefixCutSum_eq_partition_of_forall_remaining_lt
        n q htail_nonempty htail]

theorem firstChoiceBranchPayoffSum_prefixCut_eq_zero_of_forall_remaining_ge
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    (hcut : ∀ c : Candidate (n + 1), c ∈ remaining → cut ≤ (c : ℕ))
    (r : Candidate (n + 1)) :
    firstChoiceBranchPayoffSum n q
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ) r = 0 := by
  classical
  rw [firstChoiceBranchPayoffSum_prefixCut n q hremaining cut r]
  by_cases hr : r ∈ remaining
  · have hnot : ¬(r : ℕ) < cut := not_lt_of_ge (hcut r hr)
    simp [hr, hnot]
  · have htail :
        ∀ c : Candidate n, c ∈ firstChoiceTailRemainingOf r remaining →
          deleteFirstChoicePrefixCut r cut ≤ (c : ℕ) := by
      intro c hc
      have hc_full : r.succAbove c ∈ remaining := by
        simpa using hc
      exact Nat.le_of_not_gt (by
        intro hc_lt
        have hsucc_lt :
            ((r.succAbove c : Candidate (n + 1)) : ℕ) < cut :=
          (succAbove_val_lt_deleteFirstChoicePrefixCut_iff r c cut).mpr
            hc_lt
        exact not_lt_of_ge (hcut (r.succAbove c) hc_full) hsucc_lt)
    have htail_nonempty :
        (firstChoiceTailRemainingOf r remaining).Nonempty :=
      firstChoiceTailRemainingOf_nonempty_of_nonempty_of_first_not_mem
        hremaining hr
    simp [hr,
      reflMallowsBestInSetPrefixCutSum_eq_zero_of_forall_remaining_ge
        n q htail_nonempty htail]

theorem firstChoiceBranchPayoffSum_prefixCut_diag_nonneg_of_tail
    (n : ℕ) {qMore qLess : ℝ}
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ)
    (htail :
      ∀ r : Candidate (n + 1), r ∉ remaining →
        0 ≤
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixCutSum n qMore
                (firstChoiceTailRemainingOf r remaining)
                (deleteFirstChoicePrefixCut r cut) -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixCutSum n qLess
                (firstChoiceTailRemainingOf r remaining)
                (deleteFirstChoicePrefixCut r cut)) :
    ∀ r : Candidate (n + 1),
      0 ≤
        mallowsPartition qLess (Equiv.refl (Candidate n)) *
            firstChoiceBranchPayoffSum n qMore
              (fun τ : Ranking (n + 1) =>
                bestInSetPrefixCutIndicator remaining cut τ) r -
          mallowsPartition qMore (Equiv.refl (Candidate n)) *
            firstChoiceBranchPayoffSum n qLess
              (fun τ : Ranking (n + 1) =>
                bestInSetPrefixCutIndicator remaining cut τ) r := by
  classical
  intro r
  by_cases hr : r ∈ remaining
  · rw [firstChoiceBranchPayoffSum_prefixCut n qMore hremaining cut r,
      firstChoiceBranchPayoffSum_prefixCut n qLess hremaining cut r]
    by_cases hcut : (r : ℕ) < cut
    · simp [hr, hcut, mul_comm]
    · simp [hr, hcut]
  · rw [firstChoiceBranchPayoffSum_prefixCut n qMore hremaining cut r,
      firstChoiceBranchPayoffSum_prefixCut n qLess hremaining cut r]
    simpa [hr] using htail r hr

/-- Two-branch bracket in the first-choice decomposition. -/
noncomputable def firstChoiceBranchBracket
    (n : ℕ) (qMore qLess : ℝ) (F : Ranking (n + 1) → ℝ)
    (i j : Candidate (n + 1)) : ℝ :=
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let SMore : Candidate (n + 1) → ℝ :=
    firstChoiceBranchPayoffSum n qMore F
  let SLess : Candidate (n + 1) → ℝ :=
    firstChoiceBranchPayoffSum n qLess F
  (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) *
      (ZLess * SMore i) -
    (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
      (ZMore * SLess i) +
  ((qLess ^ (i : ℕ) * qMore ^ (j : ℕ)) *
      (ZLess * SMore j) -
    (qMore ^ (i : ℕ) * qLess ^ (j : ℕ)) *
      (ZMore * SLess j))

/--
First-choice branch comparison from diagonal and two-branch brackets.

This is the non-monotone replacement for `candidateRankWeightedAverage_anti`.
The older first-choice step is convenient when the less-accurate branch sums are
antitone in the first-choice rank.  Prefix first-hit events for arbitrary
remaining sets do not have that property.  This lemma keeps all pairwise
first-choice interactions explicit instead.
-/
theorem candidateRankBranchCross_nonneg_of_diag_pair
    (m : ℕ) {qMore qLess ZMore ZLess : ℝ}
    (hqMore_nonneg : 0 ≤ qMore) (hqLess_nonneg : 0 ≤ qLess)
    {SMore SLess : Candidate m → ℝ}
    (hdiag :
      ∀ i : Candidate m, 0 ≤ ZLess * SMore i - ZMore * SLess i)
    (hpair :
      ∀ i j : Candidate m, i < j →
        0 ≤
          (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) *
              (ZLess * SMore i) -
            (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
              (ZMore * SLess i) +
          ((qLess ^ (i : ℕ) * qMore ^ (j : ℕ)) *
              (ZLess * SMore j) -
            (qMore ^ (i : ℕ) * qLess ^ (j : ℕ)) *
              (ZMore * SLess j))) :
    0 ≤
      candidateRankPowerSum m qLess * ZLess *
          (∑ i : Candidate m, qMore ^ (i : ℕ) * SMore i) -
        candidateRankPowerSum m qMore * ZMore *
          (∑ i : Candidate m, qLess ^ (i : ℕ) * SLess i) := by
  classical
  let t : Candidate m → Candidate m → ℝ := fun i j =>
    (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) * (ZLess * SMore i) -
      (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) * (ZMore * SLess i)
  let off : Candidate m → Candidate m → ℝ := fun i j =>
    if i = j then 0 else t i j
  have hdouble :
      candidateRankPowerSum m qLess * ZLess *
            (∑ i : Candidate m, qMore ^ (i : ℕ) * SMore i) -
          candidateRankPowerSum m qMore * ZMore *
            (∑ i : Candidate m, qLess ^ (i : ℕ) * SLess i)
        =
      ∑ i : Candidate m, ∑ j : Candidate m, t i j := by
    unfold candidateRankPowerSum
    have hleft :
        (∑ j : Candidate m, qLess ^ (j : ℕ)) * ZLess *
            (∑ i : Candidate m, qMore ^ (i : ℕ) * SMore i) =
          ∑ i : Candidate m, ∑ j : Candidate m,
            (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) *
              (ZLess * SMore i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      calc
        ((∑ j : Candidate m, qLess ^ (j : ℕ)) * ZLess) *
            (qMore ^ (i : ℕ) * SMore i)
            =
          (∑ j : Candidate m, qLess ^ (j : ℕ)) *
            (ZLess * (qMore ^ (i : ℕ) * SMore i)) := by
              ring
        _ =
          ∑ j : Candidate m,
            qLess ^ (j : ℕ) *
              (ZLess * (qMore ^ (i : ℕ) * SMore i)) := by
              rw [Finset.sum_mul]
        _ =
          ∑ j : Candidate m,
            (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) *
              (ZLess * SMore i) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
    have hright :
        (∑ j : Candidate m, qMore ^ (j : ℕ)) * ZMore *
            (∑ i : Candidate m, qLess ^ (i : ℕ) * SLess i) =
          ∑ i : Candidate m, ∑ j : Candidate m,
            (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
              (ZMore * SLess i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      calc
        ((∑ j : Candidate m, qMore ^ (j : ℕ)) * ZMore) *
            (qLess ^ (i : ℕ) * SLess i)
            =
          (∑ j : Candidate m, qMore ^ (j : ℕ)) *
            (ZMore * (qLess ^ (i : ℕ) * SLess i)) := by
              ring
        _ =
          ∑ j : Candidate m,
            qMore ^ (j : ℕ) *
              (ZMore * (qLess ^ (i : ℕ) * SLess i)) := by
              rw [Finset.sum_mul]
        _ =
          ∑ j : Candidate m,
            (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
              (ZMore * SLess i) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
    calc
      (∑ j : Candidate m, qLess ^ (j : ℕ)) * ZLess *
            (∑ i : Candidate m, qMore ^ (i : ℕ) * SMore i) -
          (∑ j : Candidate m, qMore ^ (j : ℕ)) * ZMore *
            (∑ i : Candidate m, qLess ^ (i : ℕ) * SLess i)
          =
        (∑ i : Candidate m, ∑ j : Candidate m,
            (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) *
              (ZLess * SMore i)) -
          (∑ i : Candidate m, ∑ j : Candidate m,
            (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
              (ZMore * SLess i)) := by rw [hleft, hright]
      _ = ∑ i : Candidate m, ∑ j : Candidate m, t i j := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [← Finset.sum_sub_distrib]
  rw [hdouble]
  have hsplit :
      (∑ i : Candidate m, ∑ j : Candidate m, t i j) =
        (∑ i : Candidate m, t i i) +
          ∑ i : Candidate m, ∑ j : Candidate m, off i j := by
    calc
      (∑ i : Candidate m, ∑ j : Candidate m, t i j)
          =
        ∑ i : Candidate m, ∑ j : Candidate m,
          ((if j = i then t i i else 0) + off i j) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            refine Finset.sum_congr rfl ?_
            intro j _
            by_cases hji : j = i
            · subst j
              simp [off]
            · have hij : i ≠ j := by exact fun h => hji h.symm
              simp [off, hji, hij]
      _ =
        (∑ i : Candidate m, ∑ j : Candidate m,
            (if j = i then t i i else 0)) +
          ∑ i : Candidate m, ∑ j : Candidate m, off i j := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [← Finset.sum_add_distrib]
      _ =
        (∑ i : Candidate m, t i i) +
          ∑ i : Candidate m, ∑ j : Candidate m, off i j := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i _
            simp
  rw [hsplit]
  apply add_nonneg
  · refine Finset.sum_nonneg ?_
    intro i _
    have hweight :
        0 ≤ qLess ^ (i : ℕ) * qMore ^ (i : ℕ) :=
      mul_nonneg (pow_nonneg hqLess_nonneg _) (pow_nonneg hqMore_nonneg _)
    have hdiag_i := hdiag i
    have htii :
        t i i =
          (qLess ^ (i : ℕ) * qMore ^ (i : ℕ)) *
            (ZLess * SMore i - ZMore * SLess i) := by
      simp [t]
      ring
    rw [htii]
    exact mul_nonneg hweight hdiag_i
  · rw [MallowsSpec.pair_sum_eq_ordered_swap_sum
      (Equiv.refl (Candidate m)) off
      (by intro i; simp [off])]
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    by_cases hij_rank :
        rankOf (Equiv.refl (Candidate m)) i <
          rankOf (Equiv.refl (Candidate m)) j
    · have hij : i < j := by
        simpa [rankOf] using hij_rank
      have hne : i ≠ j := ne_of_lt hij
      have hne' : j ≠ i := hne.symm
      have hoff :
          off i j + off j i =
            (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) *
                (ZLess * SMore i) -
              (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
                (ZMore * SLess i) +
            ((qLess ^ (i : ℕ) * qMore ^ (j : ℕ)) *
                (ZLess * SMore j) -
              (qMore ^ (i : ℕ) * qLess ^ (j : ℕ)) *
              (ZMore * SLess j)) := by
        simp [off, t, hne, hne']
      rw [if_pos hij_rank, hoff]
      exact hpair i j hij
    · simp [hij_rank]

/--
First-choice induction step with explicit two-branch brackets.

This is intended for arbitrary remaining-set prefix/fiber work where the
first-choice branch sums need not be monotone in the first-choice rank.
-/
theorem reflMallowsPayoffSum_cross_of_firstChoice_pair_brackets
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (F : Ranking (n + 1) → ℝ)
    (hdiag :
      ∀ r : Candidate (n + 1),
        0 ≤
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qMore F r -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qLess F r)
    (hpair :
      ∀ i j : Candidate (n + 1), i < j →
        0 ≤ firstChoiceBranchBracket n qMore qLess F i j) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qMore F -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qLess F := by
  classical
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let SMore : Candidate (n + 1) → ℝ := fun r =>
    firstChoiceBranchPayoffSum n qMore F r
  let SLess : Candidate (n + 1) → ℝ := fun r =>
    firstChoiceBranchPayoffSum n qLess F r
  have hqLess_nonneg : 0 ≤ qLess := le_of_lt (lt_trans hqMore_pos hq_lt)
  have hcore :
      0 ≤
        candidateRankPowerSum (n + 1) qLess * ZLess *
            (∑ i : Candidate (n + 1), qMore ^ (i : ℕ) * SMore i) -
          candidateRankPowerSum (n + 1) qMore * ZMore *
            (∑ i : Candidate (n + 1), qLess ^ (i : ℕ) * SLess i) :=
    candidateRankBranchCross_nonneg_of_diag_pair
      (n + 1) (le_of_lt hqMore_pos) hqLess_nonneg
      (SMore := SMore) (SLess := SLess)
      (by
        intro i
        simpa [ZLess, ZMore, SMore, SLess] using hdiag i)
      (by
        intro i j hij
        simpa [firstChoiceBranchBracket, ZLess, ZMore, SMore, SLess]
          using hpair i j hij)
  rw [mallowsPartition_refl_peelBest n qLess,
    mallowsPartition_refl_peelBest n qMore,
    reflMallowsPayoffSum_firstChoice n qMore F,
    reflMallowsPayoffSum_firstChoice n qLess F]
  simpa [firstChoiceBranchPayoffSum, ZLess, ZMore, SMore, SLess,
    mul_comm, mul_left_comm, mul_assoc]
    using hcore

/--
First-choice branch comparison from diagonal terms and the aggregate
off-diagonal two-branch bracket sum.

The pointwise pair-bracket condition in
`candidateRankBranchCross_nonneg_of_diag_pair` is convenient but too strong for
arbitrary prefix first-hit events: some individual first-choice pairs can be
negative even when the full off-diagonal contribution is nonnegative.  This
version exposes exactly the aggregate off-diagonal obligation.
-/
theorem candidateRankBranchCross_nonneg_of_diag_pair_sum
    (m : ℕ) {qMore qLess ZMore ZLess : ℝ}
    (hqMore_nonneg : 0 ≤ qMore) (hqLess_nonneg : 0 ≤ qLess)
    {SMore SLess : Candidate m → ℝ}
    (hdiag :
      ∀ i : Candidate m, 0 ≤ ZLess * SMore i - ZMore * SLess i)
    (hpair_sum :
      0 ≤
        ∑ i : Candidate m, ∑ j : Candidate m,
          if i < j then
            (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) *
                (ZLess * SMore i) -
              (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
                (ZMore * SLess i) +
            ((qLess ^ (i : ℕ) * qMore ^ (j : ℕ)) *
                (ZLess * SMore j) -
              (qMore ^ (i : ℕ) * qLess ^ (j : ℕ)) *
                (ZMore * SLess j))
          else 0) :
    0 ≤
      candidateRankPowerSum m qLess * ZLess *
          (∑ i : Candidate m, qMore ^ (i : ℕ) * SMore i) -
        candidateRankPowerSum m qMore * ZMore *
          (∑ i : Candidate m, qLess ^ (i : ℕ) * SLess i) := by
  classical
  let t : Candidate m → Candidate m → ℝ := fun i j =>
    (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) * (ZLess * SMore i) -
      (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) * (ZMore * SLess i)
  let off : Candidate m → Candidate m → ℝ := fun i j =>
    if i = j then 0 else t i j
  have hdouble :
      candidateRankPowerSum m qLess * ZLess *
            (∑ i : Candidate m, qMore ^ (i : ℕ) * SMore i) -
          candidateRankPowerSum m qMore * ZMore *
            (∑ i : Candidate m, qLess ^ (i : ℕ) * SLess i)
        =
      ∑ i : Candidate m, ∑ j : Candidate m, t i j := by
    unfold candidateRankPowerSum
    have hleft :
        (∑ j : Candidate m, qLess ^ (j : ℕ)) * ZLess *
            (∑ i : Candidate m, qMore ^ (i : ℕ) * SMore i) =
          ∑ i : Candidate m, ∑ j : Candidate m,
            (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) *
              (ZLess * SMore i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      calc
        ((∑ j : Candidate m, qLess ^ (j : ℕ)) * ZLess) *
            (qMore ^ (i : ℕ) * SMore i)
            =
          (∑ j : Candidate m, qLess ^ (j : ℕ)) *
            (ZLess * (qMore ^ (i : ℕ) * SMore i)) := by
              ring
        _ =
          ∑ j : Candidate m,
            qLess ^ (j : ℕ) *
              (ZLess * (qMore ^ (i : ℕ) * SMore i)) := by
              rw [Finset.sum_mul]
        _ =
          ∑ j : Candidate m,
            (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) *
              (ZLess * SMore i) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
    have hright :
        (∑ j : Candidate m, qMore ^ (j : ℕ)) * ZMore *
            (∑ i : Candidate m, qLess ^ (i : ℕ) * SLess i) =
          ∑ i : Candidate m, ∑ j : Candidate m,
            (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
              (ZMore * SLess i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      calc
        ((∑ j : Candidate m, qMore ^ (j : ℕ)) * ZMore) *
            (qLess ^ (i : ℕ) * SLess i)
            =
          (∑ j : Candidate m, qMore ^ (j : ℕ)) *
            (ZMore * (qLess ^ (i : ℕ) * SLess i)) := by
              ring
        _ =
          ∑ j : Candidate m,
            qMore ^ (j : ℕ) *
              (ZMore * (qLess ^ (i : ℕ) * SLess i)) := by
              rw [Finset.sum_mul]
        _ =
          ∑ j : Candidate m,
            (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
              (ZMore * SLess i) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
    calc
      (∑ j : Candidate m, qLess ^ (j : ℕ)) * ZLess *
            (∑ i : Candidate m, qMore ^ (i : ℕ) * SMore i) -
          (∑ j : Candidate m, qMore ^ (j : ℕ)) * ZMore *
            (∑ i : Candidate m, qLess ^ (i : ℕ) * SLess i)
          =
        (∑ i : Candidate m, ∑ j : Candidate m,
            (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) *
              (ZLess * SMore i)) -
          (∑ i : Candidate m, ∑ j : Candidate m,
            (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
              (ZMore * SLess i)) := by rw [hleft, hright]
      _ = ∑ i : Candidate m, ∑ j : Candidate m, t i j := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [← Finset.sum_sub_distrib]
  rw [hdouble]
  have hsplit :
      (∑ i : Candidate m, ∑ j : Candidate m, t i j) =
        (∑ i : Candidate m, t i i) +
          ∑ i : Candidate m, ∑ j : Candidate m, off i j := by
    calc
      (∑ i : Candidate m, ∑ j : Candidate m, t i j)
          =
        ∑ i : Candidate m, ∑ j : Candidate m,
          ((if j = i then t i i else 0) + off i j) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            refine Finset.sum_congr rfl ?_
            intro j _
            by_cases hji : j = i
            · subst j
              simp [off]
            · have hij : i ≠ j := by exact fun h => hji h.symm
              simp [off, hji, hij]
      _ =
        (∑ i : Candidate m, ∑ j : Candidate m,
            (if j = i then t i i else 0)) +
          ∑ i : Candidate m, ∑ j : Candidate m, off i j := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [← Finset.sum_add_distrib]
      _ =
        (∑ i : Candidate m, t i i) +
          ∑ i : Candidate m, ∑ j : Candidate m, off i j := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i _
            simp
  rw [hsplit]
  apply add_nonneg
  · refine Finset.sum_nonneg ?_
    intro i _
    have hweight :
        0 ≤ qLess ^ (i : ℕ) * qMore ^ (i : ℕ) :=
      mul_nonneg (pow_nonneg hqLess_nonneg _) (pow_nonneg hqMore_nonneg _)
    have hdiag_i := hdiag i
    have htii :
        t i i =
          (qLess ^ (i : ℕ) * qMore ^ (i : ℕ)) *
            (ZLess * SMore i - ZMore * SLess i) := by
      simp [t]
      ring
    rw [htii]
    exact mul_nonneg hweight hdiag_i
  · rw [MallowsSpec.pair_sum_eq_ordered_swap_sum
      (Equiv.refl (Candidate m)) off
      (by intro i; simp [off])]
    have hoff_sum_eq :
        (∑ i : Candidate m, ∑ j : Candidate m,
          if rankOf (Equiv.refl (Candidate m)) i <
              rankOf (Equiv.refl (Candidate m)) j then
            off i j + off j i
          else 0) =
        ∑ i : Candidate m, ∑ j : Candidate m,
          if i < j then
            (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) *
                (ZLess * SMore i) -
              (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
                (ZMore * SLess i) +
            ((qLess ^ (i : ℕ) * qMore ^ (j : ℕ)) *
                (ZLess * SMore j) -
              (qMore ^ (i : ℕ) * qLess ^ (j : ℕ)) *
                (ZMore * SLess j))
          else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      by_cases hij : i < j
      · have hne : i ≠ j := ne_of_lt hij
        have hne' : j ≠ i := hne.symm
        simp [rankOf, hij, off, t, hne, hne']
      · have hrank_not :
            ¬ rankOf (Equiv.refl (Candidate m)) i <
              rankOf (Equiv.refl (Candidate m)) j := by
          simpa [rankOf] using hij
        simp [rankOf, hij]
    rw [hoff_sum_eq]
    exact hpair_sum

theorem candidateRankBranchCross_pos_of_diag_pair_sum
    (m : ℕ) {qMore qLess ZMore ZLess : ℝ}
    (hqMore_nonneg : 0 ≤ qMore) (hqLess_nonneg : 0 ≤ qLess)
    {SMore SLess : Candidate m → ℝ}
    (hdiag :
      ∀ i : Candidate m, 0 ≤ ZLess * SMore i - ZMore * SLess i)
    (hpair_sum :
      0 <
        ∑ i : Candidate m, ∑ j : Candidate m,
          if i < j then
            (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) *
                (ZLess * SMore i) -
              (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
                (ZMore * SLess i) +
            ((qLess ^ (i : ℕ) * qMore ^ (j : ℕ)) *
                (ZLess * SMore j) -
              (qMore ^ (i : ℕ) * qLess ^ (j : ℕ)) *
                (ZMore * SLess j))
          else 0) :
    0 <
      candidateRankPowerSum m qLess * ZLess *
          (∑ i : Candidate m, qMore ^ (i : ℕ) * SMore i) -
        candidateRankPowerSum m qMore * ZMore *
          (∑ i : Candidate m, qLess ^ (i : ℕ) * SLess i) := by
  classical
  let t : Candidate m → Candidate m → ℝ := fun i j =>
    (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) * (ZLess * SMore i) -
      (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) * (ZMore * SLess i)
  let off : Candidate m → Candidate m → ℝ := fun i j =>
    if i = j then 0 else t i j
  have hdouble :
      candidateRankPowerSum m qLess * ZLess *
            (∑ i : Candidate m, qMore ^ (i : ℕ) * SMore i) -
          candidateRankPowerSum m qMore * ZMore *
            (∑ i : Candidate m, qLess ^ (i : ℕ) * SLess i)
        =
      ∑ i : Candidate m, ∑ j : Candidate m, t i j := by
    unfold candidateRankPowerSum
    have hleft :
        (∑ j : Candidate m, qLess ^ (j : ℕ)) * ZLess *
            (∑ i : Candidate m, qMore ^ (i : ℕ) * SMore i) =
          ∑ i : Candidate m, ∑ j : Candidate m,
            (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) *
              (ZLess * SMore i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      calc
        ((∑ j : Candidate m, qLess ^ (j : ℕ)) * ZLess) *
            (qMore ^ (i : ℕ) * SMore i)
            =
          (∑ j : Candidate m, qLess ^ (j : ℕ)) *
            (ZLess * (qMore ^ (i : ℕ) * SMore i)) := by
              ring
        _ =
          ∑ j : Candidate m,
            qLess ^ (j : ℕ) *
              (ZLess * (qMore ^ (i : ℕ) * SMore i)) := by
              rw [Finset.sum_mul]
        _ =
          ∑ j : Candidate m,
            (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) *
              (ZLess * SMore i) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
    have hright :
        (∑ j : Candidate m, qMore ^ (j : ℕ)) * ZMore *
            (∑ i : Candidate m, qLess ^ (i : ℕ) * SLess i) =
          ∑ i : Candidate m, ∑ j : Candidate m,
            (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
              (ZMore * SLess i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      calc
        ((∑ j : Candidate m, qMore ^ (j : ℕ)) * ZMore) *
            (qLess ^ (i : ℕ) * SLess i)
            =
          (∑ j : Candidate m, qMore ^ (j : ℕ)) *
            (ZMore * (qLess ^ (i : ℕ) * SLess i)) := by
              ring
        _ =
          ∑ j : Candidate m,
            qMore ^ (j : ℕ) *
              (ZMore * (qLess ^ (i : ℕ) * SLess i)) := by
              rw [Finset.sum_mul]
        _ =
          ∑ j : Candidate m,
            (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
              (ZMore * SLess i) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
    calc
      (∑ j : Candidate m, qLess ^ (j : ℕ)) * ZLess *
            (∑ i : Candidate m, qMore ^ (i : ℕ) * SMore i) -
          (∑ j : Candidate m, qMore ^ (j : ℕ)) * ZMore *
            (∑ i : Candidate m, qLess ^ (i : ℕ) * SLess i)
          =
        (∑ i : Candidate m, ∑ j : Candidate m,
            (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) *
              (ZLess * SMore i)) -
          (∑ i : Candidate m, ∑ j : Candidate m,
            (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
              (ZMore * SLess i)) := by rw [hleft, hright]
      _ = ∑ i : Candidate m, ∑ j : Candidate m, t i j := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [← Finset.sum_sub_distrib]
  rw [hdouble]
  have hsplit :
      (∑ i : Candidate m, ∑ j : Candidate m, t i j) =
        (∑ i : Candidate m, t i i) +
          ∑ i : Candidate m, ∑ j : Candidate m, off i j := by
    calc
      (∑ i : Candidate m, ∑ j : Candidate m, t i j)
          =
        ∑ i : Candidate m, ∑ j : Candidate m,
          ((if j = i then t i i else 0) + off i j) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            refine Finset.sum_congr rfl ?_
            intro j _
            by_cases hji : j = i
            · subst j
              simp [off]
            · have hij : i ≠ j := by exact fun h => hji h.symm
              simp [off, hji, hij]
      _ =
        (∑ i : Candidate m, ∑ j : Candidate m,
            (if j = i then t i i else 0)) +
          ∑ i : Candidate m, ∑ j : Candidate m, off i j := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [← Finset.sum_add_distrib]
      _ =
        (∑ i : Candidate m, t i i) +
          ∑ i : Candidate m, ∑ j : Candidate m, off i j := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i _
            simp
  rw [hsplit]
  apply add_pos_of_nonneg_of_pos
  · refine Finset.sum_nonneg ?_
    intro i _
    have hweight :
        0 ≤ qLess ^ (i : ℕ) * qMore ^ (i : ℕ) :=
      mul_nonneg (pow_nonneg hqLess_nonneg _) (pow_nonneg hqMore_nonneg _)
    have hdiag_i := hdiag i
    have htii :
        t i i =
          (qLess ^ (i : ℕ) * qMore ^ (i : ℕ)) *
            (ZLess * SMore i - ZMore * SLess i) := by
      simp [t]
      ring
    rw [htii]
    exact mul_nonneg hweight hdiag_i
  · rw [MallowsSpec.pair_sum_eq_ordered_swap_sum
      (Equiv.refl (Candidate m)) off
      (by intro i; simp [off])]
    have hoff_sum_eq :
        (∑ i : Candidate m, ∑ j : Candidate m,
          if rankOf (Equiv.refl (Candidate m)) i <
              rankOf (Equiv.refl (Candidate m)) j then
            off i j + off j i
          else 0) =
        ∑ i : Candidate m, ∑ j : Candidate m,
          if i < j then
            (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) *
                (ZLess * SMore i) -
              (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
                (ZMore * SLess i) +
            ((qLess ^ (i : ℕ) * qMore ^ (j : ℕ)) *
                (ZLess * SMore j) -
              (qMore ^ (i : ℕ) * qLess ^ (j : ℕ)) *
                (ZMore * SLess j))
          else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      by_cases hij : i < j
      · have hne : i ≠ j := ne_of_lt hij
        have hne' : j ≠ i := hne.symm
        simp [rankOf, hij, off, t, hne, hne']
      · have hrank_not :
            ¬ rankOf (Equiv.refl (Candidate m)) i <
              rankOf (Equiv.refl (Candidate m)) j := by
          simpa [rankOf] using hij
        simp [rankOf, hij]
    rw [hoff_sum_eq]
    exact hpair_sum

noncomputable def firstChoiceBranchBracketSum
    (n : ℕ) (qMore qLess : ℝ) (F : Ranking (n + 1) → ℝ) : ℝ :=
  ∑ i : Candidate (n + 1), ∑ j : Candidate (n + 1),
    if i < j then firstChoiceBranchBracket n qMore qLess F i j else 0

theorem firstChoiceBranchBracket_const
    (n : ℕ) (qMore qLess a : ℝ)
    (i j : Candidate (n + 1)) :
    firstChoiceBranchBracket n qMore qLess
        (fun _ : Ranking (n + 1) => a) i j = 0 := by
  unfold firstChoiceBranchBracket
  simp_rw [firstChoiceBranchPayoffSum_const]
  ring

theorem firstChoiceBranchBracketSum_const
    (n : ℕ) (qMore qLess a : ℝ) :
    firstChoiceBranchBracketSum n qMore qLess
        (fun _ : Ranking (n + 1) => a) = 0 := by
  classical
  unfold firstChoiceBranchBracketSum
  refine Finset.sum_eq_zero ?_
  intro i _
  refine Finset.sum_eq_zero ?_
  intro j _
  by_cases hij : i < j
  · rw [if_pos hij]
    exact firstChoiceBranchBracket_const n qMore qLess a i j
  · simp [hij]

theorem firstChoiceBranchBracketSum_eq_offDiagonal
    (n : ℕ) (qMore qLess : ℝ) (F : Ranking (n + 1) → ℝ) :
    firstChoiceBranchBracketSum n qMore qLess F =
      ∑ i : Candidate (n + 1), ∑ j : Candidate (n + 1),
        if i = j then 0 else
          (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) *
              (mallowsPartition qLess (Equiv.refl (Candidate n)) *
                firstChoiceBranchPayoffSum n qMore F i) -
            (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
              (mallowsPartition qMore (Equiv.refl (Candidate n)) *
                firstChoiceBranchPayoffSum n qLess F i) := by
  classical
  let t : Candidate (n + 1) → Candidate (n + 1) → ℝ := fun i j =>
    if i = j then 0 else
      (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) *
          (mallowsPartition qLess (Equiv.refl (Candidate n)) *
            firstChoiceBranchPayoffSum n qMore F i) -
        (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
          (mallowsPartition qMore (Equiv.refl (Candidate n)) *
            firstChoiceBranchPayoffSum n qLess F i)
  have hordered :
      (∑ i : Candidate (n + 1), ∑ j : Candidate (n + 1), t i j) =
        ∑ i : Candidate (n + 1), ∑ j : Candidate (n + 1),
          if i < j then firstChoiceBranchBracket n qMore qLess F i j else 0 := by
    rw [MallowsSpec.pair_sum_eq_ordered_swap_sum
      (Equiv.refl (Candidate (n + 1))) t (by intro i; simp [t])]
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases hij : i < j
    · have hne : i ≠ j := ne_of_lt hij
      have hne' : j ≠ i := hne.symm
      simp [rankOf, hij, t, firstChoiceBranchBracket, hne, hne']
    · have hrank_not :
          ¬ rankOf (Equiv.refl (Candidate (n + 1))) i <
            rankOf (Equiv.refl (Candidate (n + 1))) j := by
        simpa [rankOf] using hij
      simp [hrank_not, hij]
  rw [firstChoiceBranchBracketSum, ← hordered]

theorem firstChoiceBranchBracketSum_eq_complementPower
    (n : ℕ) (qMore qLess : ℝ) (F : Ranking (n + 1) → ℝ) :
    firstChoiceBranchBracketSum n qMore qLess F =
      ∑ i : Candidate (n + 1),
        (qMore ^ (i : ℕ) *
            (candidateRankPowerSum (n + 1) qLess - qLess ^ (i : ℕ)) *
            (mallowsPartition qLess (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qMore F i) -
          qLess ^ (i : ℕ) *
            (candidateRankPowerSum (n + 1) qMore - qMore ^ (i : ℕ)) *
            (mallowsPartition qMore (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qLess F i)) := by
  classical
  let A : Candidate (n + 1) → ℝ := fun i =>
    mallowsPartition qLess (Equiv.refl (Candidate n)) *
      firstChoiceBranchPayoffSum n qMore F i
  let B : Candidate (n + 1) → ℝ := fun i =>
    mallowsPartition qMore (Equiv.refl (Candidate n)) *
      firstChoiceBranchPayoffSum n qLess F i
  let u : Candidate (n + 1) → Candidate (n + 1) → ℝ := fun i j =>
    (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) * A i -
      (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) * B i
  rw [firstChoiceBranchBracketSum_eq_offDiagonal]
  change
    (∑ i : Candidate (n + 1), ∑ j : Candidate (n + 1),
        if i = j then 0 else u i j) = _
  refine Finset.sum_congr rfl ?_
  intro i _
  have hrow :
      (∑ j : Candidate (n + 1), if i = j then 0 else u i j) =
        (∑ j : Candidate (n + 1), u i j) - u i i := by
    calc
      (∑ j : Candidate (n + 1), if i = j then 0 else u i j)
          =
        ∑ j : Candidate (n + 1), (u i j - if j = i then u i i else 0) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          by_cases hji : j = i
          · subst j
            simp
          · have hij : i ≠ j := by exact fun h => hji h.symm
            simp [hji, hij]
      _ =
        (∑ j : Candidate (n + 1), u i j) -
          ∑ j : Candidate (n + 1), (if j = i then u i i else 0) := by
          rw [Finset.sum_sub_distrib]
      _ = (∑ j : Candidate (n + 1), u i j) - u i i := by
          have hsingle :
              (∑ j : Candidate (n + 1),
                  (if j = i then u i i else 0)) = u i i := by
            simpa using
              (Finset.sum_ite_eq' Finset.univ i
                (fun _ : Candidate (n + 1) => u i i))
          rw [hsingle]
  have hsum_u :
      (∑ j : Candidate (n + 1), u i j) =
        (∑ j : Candidate (n + 1), qLess ^ (j : ℕ)) *
            (qMore ^ (i : ℕ) * A i) -
          (∑ j : Candidate (n + 1), qMore ^ (j : ℕ)) *
            (qLess ^ (i : ℕ) * B i) := by
    unfold u
    rw [Finset.sum_sub_distrib]
    congr 1
    · calc
        (∑ j : Candidate (n + 1),
            (qLess ^ (j : ℕ) * qMore ^ (i : ℕ)) * A i)
            =
          ∑ j : Candidate (n + 1),
            qLess ^ (j : ℕ) * (qMore ^ (i : ℕ) * A i) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            ring
        _ =
          (∑ j : Candidate (n + 1), qLess ^ (j : ℕ)) *
            (qMore ^ (i : ℕ) * A i) := by
            rw [Finset.sum_mul]
    · calc
        (∑ j : Candidate (n + 1),
            (qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) * B i)
            =
          ∑ j : Candidate (n + 1),
            qMore ^ (j : ℕ) * (qLess ^ (i : ℕ) * B i) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            ring
        _ =
          (∑ j : Candidate (n + 1), qMore ^ (j : ℕ)) *
            (qLess ^ (i : ℕ) * B i) := by
            rw [Finset.sum_mul]
  rw [hrow, hsum_u]
  unfold u candidateRankPowerSum A B
  ring

theorem firstChoiceBranchBracketSum_eq_diag_add_weighted
    (n : ℕ) (qMore qLess : ℝ) (F : Ranking (n + 1) → ℝ) :
    firstChoiceBranchBracketSum n qMore qLess F =
      (∑ i : Candidate (n + 1),
        qMore ^ (i : ℕ) *
          (candidateRankPowerSum (n + 1) qLess - qLess ^ (i : ℕ)) *
          (mallowsPartition qLess (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qMore F i -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qLess F i)) +
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          (candidateRankPowerSum (n + 1) qLess *
              (∑ i : Candidate (n + 1),
                qMore ^ (i : ℕ) *
                  firstChoiceBranchPayoffSum n qLess F i) -
            candidateRankPowerSum (n + 1) qMore *
              (∑ i : Candidate (n + 1),
                qLess ^ (i : ℕ) *
                  firstChoiceBranchPayoffSum n qLess F i)) := by
  classical
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let PMore : ℝ := candidateRankPowerSum (n + 1) qMore
  let PLess : ℝ := candidateRankPowerSum (n + 1) qLess
  let SMore : Candidate (n + 1) → ℝ := fun i =>
    firstChoiceBranchPayoffSum n qMore F i
  let SLess : Candidate (n + 1) → ℝ := fun i =>
    firstChoiceBranchPayoffSum n qLess F i
  rw [firstChoiceBranchBracketSum_eq_complementPower]
  calc
    (∑ i : Candidate (n + 1),
        (qMore ^ (i : ℕ) *
            (candidateRankPowerSum (n + 1) qLess - qLess ^ (i : ℕ)) *
            (mallowsPartition qLess (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qMore F i) -
          qLess ^ (i : ℕ) *
            (candidateRankPowerSum (n + 1) qMore - qMore ^ (i : ℕ)) *
            (mallowsPartition qMore (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qLess F i)))
        =
      ∑ i : Candidate (n + 1),
        (qMore ^ (i : ℕ) * (PLess - qLess ^ (i : ℕ)) *
            (ZLess * SMore i - ZMore * SLess i) +
          (qMore ^ (i : ℕ) * PLess - qLess ^ (i : ℕ) * PMore) *
            (ZMore * SLess i)) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        simp [ZMore, ZLess, PMore, PLess, SMore, SLess]
        ring
    _ =
      (∑ i : Candidate (n + 1),
        qMore ^ (i : ℕ) * (PLess - qLess ^ (i : ℕ)) *
          (ZLess * SMore i - ZMore * SLess i)) +
        ∑ i : Candidate (n + 1),
          (qMore ^ (i : ℕ) * PLess - qLess ^ (i : ℕ) * PMore) *
            (ZMore * SLess i) := by
        rw [← Finset.sum_add_distrib]
    _ =
      (∑ i : Candidate (n + 1),
        qMore ^ (i : ℕ) * (PLess - qLess ^ (i : ℕ)) *
          (ZLess * SMore i - ZMore * SLess i)) +
        ZMore *
          (PLess *
              (∑ i : Candidate (n + 1), qMore ^ (i : ℕ) * SLess i) -
            PMore *
              (∑ i : Candidate (n + 1), qLess ^ (i : ℕ) * SLess i)) := by
        congr 1
        calc
          (∑ i : Candidate (n + 1),
              (qMore ^ (i : ℕ) * PLess - qLess ^ (i : ℕ) * PMore) *
                (ZMore * SLess i))
              =
            ∑ i : Candidate (n + 1),
              ZMore *
                (PLess * (qMore ^ (i : ℕ) * SLess i) -
                  PMore * (qLess ^ (i : ℕ) * SLess i)) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              ring
          _ =
            ZMore *
              (∑ i : Candidate (n + 1),
                (PLess * (qMore ^ (i : ℕ) * SLess i) -
                  PMore * (qLess ^ (i : ℕ) * SLess i))) := by
              rw [← Finset.mul_sum]
          _ =
            ZMore *
              (PLess *
                  (∑ i : Candidate (n + 1), qMore ^ (i : ℕ) * SLess i) -
                PMore *
                  (∑ i : Candidate (n + 1), qLess ^ (i : ℕ) * SLess i)) := by
              congr 1
              rw [Finset.sum_sub_distrib]
              rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ =
      (∑ i : Candidate (n + 1),
        qMore ^ (i : ℕ) *
          (candidateRankPowerSum (n + 1) qLess - qLess ^ (i : ℕ)) *
          (mallowsPartition qLess (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qMore F i -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qLess F i)) +
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          (candidateRankPowerSum (n + 1) qLess *
              (∑ i : Candidate (n + 1),
                qMore ^ (i : ℕ) *
                  firstChoiceBranchPayoffSum n qLess F i) -
            candidateRankPowerSum (n + 1) qMore *
              (∑ i : Candidate (n + 1),
                qLess ^ (i : ℕ) *
                  firstChoiceBranchPayoffSum n qLess F i)) := by
        simp [ZMore, ZLess, PMore, PLess, SMore, SLess]

theorem firstChoiceBranchBracketSum_nonneg_of_diag_weighted
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hqLess_nonneg : 0 ≤ qLess) (F : Ranking (n + 1) → ℝ)
    (hdiag :
      ∀ i : Candidate (n + 1),
        0 ≤
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qMore F i -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qLess F i)
    (hweighted :
      0 ≤
        candidateRankPowerSum (n + 1) qLess *
            (∑ i : Candidate (n + 1),
              qMore ^ (i : ℕ) *
                firstChoiceBranchPayoffSum n qLess F i) -
          candidateRankPowerSum (n + 1) qMore *
            (∑ i : Candidate (n + 1),
              qLess ^ (i : ℕ) *
                firstChoiceBranchPayoffSum n qLess F i)) :
    0 ≤ firstChoiceBranchBracketSum n qMore qLess F := by
  classical
  rw [firstChoiceBranchBracketSum_eq_diag_add_weighted]
  apply add_nonneg
  · refine Finset.sum_nonneg ?_
    intro i _
    have hqMore_nonneg : 0 ≤ qMore := le_of_lt hqMore_pos
    have hcoeff :
        0 ≤
          qMore ^ (i : ℕ) *
            (candidateRankPowerSum (n + 1) qLess - qLess ^ (i : ℕ)) :=
      mul_nonneg (pow_nonneg hqMore_nonneg _)
        (candidateRankPowerSum_sub_rankPower_nonneg
          (n + 1) hqLess_nonneg i)
    exact mul_nonneg hcoeff (hdiag i)
  · have hZMore_nonneg :
        0 ≤ mallowsPartition qMore (Equiv.refl (Candidate n)) :=
      le_of_lt (mallowsPartition_pos (hq := hqMore_pos)
        (Equiv.refl (Candidate n)))
    exact mul_nonneg hZMore_nonneg hweighted

theorem firstChoiceBranchBracketSum_pos_of_diag_weighted
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hqLess_nonneg : 0 ≤ qLess) (F : Ranking (n + 1) → ℝ)
    (hdiag :
      ∀ i : Candidate (n + 1),
        0 ≤
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qMore F i -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qLess F i)
    (hweighted :
      0 <
        candidateRankPowerSum (n + 1) qLess *
            (∑ i : Candidate (n + 1),
              qMore ^ (i : ℕ) *
                firstChoiceBranchPayoffSum n qLess F i) -
          candidateRankPowerSum (n + 1) qMore *
            (∑ i : Candidate (n + 1),
              qLess ^ (i : ℕ) *
                firstChoiceBranchPayoffSum n qLess F i)) :
    0 < firstChoiceBranchBracketSum n qMore qLess F := by
  classical
  rw [firstChoiceBranchBracketSum_eq_diag_add_weighted]
  apply add_pos_of_nonneg_of_pos
  · refine Finset.sum_nonneg ?_
    intro i _
    have hqMore_nonneg : 0 ≤ qMore := le_of_lt hqMore_pos
    have hcoeff :
        0 ≤
          qMore ^ (i : ℕ) *
            (candidateRankPowerSum (n + 1) qLess - qLess ^ (i : ℕ)) :=
      mul_nonneg (pow_nonneg hqMore_nonneg _)
        (candidateRankPowerSum_sub_rankPower_nonneg
          (n + 1) hqLess_nonneg i)
    exact mul_nonneg hcoeff (hdiag i)
  · have hZMore_pos :
        0 < mallowsPartition qMore (Equiv.refl (Candidate n)) :=
      mallowsPartition_pos (hq := hqMore_pos)
        (Equiv.refl (Candidate n))
    exact mul_pos hZMore_pos hweighted

theorem firstChoiceBranchBracketSum_prefixCut_eq_zero_of_forall_remaining_lt
    (n : ℕ) (qMore qLess : ℝ)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    (hcut : ∀ c : Candidate (n + 1), c ∈ remaining → (c : ℕ) < cut) :
    firstChoiceBranchBracketSum n qMore qLess
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ) = 0 := by
  classical
  unfold firstChoiceBranchBracketSum
  refine Finset.sum_eq_zero ?_
  intro i _
  refine Finset.sum_eq_zero ?_
  intro j _
  by_cases hij : i < j
  · rw [if_pos hij]
    unfold firstChoiceBranchBracket
    simp_rw [
      firstChoiceBranchPayoffSum_prefixCut_eq_partition_of_forall_remaining_lt
        n qMore hremaining hcut,
      firstChoiceBranchPayoffSum_prefixCut_eq_partition_of_forall_remaining_lt
        n qLess hremaining hcut]
    ring
  · simp [hij]

theorem firstChoiceBranchBracketSum_prefixCut_eq_zero_of_forall_remaining_ge
    (n : ℕ) (qMore qLess : ℝ)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    (hcut : ∀ c : Candidate (n + 1), c ∈ remaining → cut ≤ (c : ℕ)) :
    firstChoiceBranchBracketSum n qMore qLess
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ) = 0 := by
  classical
  unfold firstChoiceBranchBracketSum
  refine Finset.sum_eq_zero ?_
  intro i _
  refine Finset.sum_eq_zero ?_
  intro j _
  by_cases hij : i < j
  · rw [if_pos hij]
    unfold firstChoiceBranchBracket
    simp_rw [
      firstChoiceBranchPayoffSum_prefixCut_eq_zero_of_forall_remaining_ge
        n qMore hremaining hcut,
      firstChoiceBranchPayoffSum_prefixCut_eq_zero_of_forall_remaining_ge
        n qLess hremaining hcut]
    ring
  · simp [hij]

theorem firstChoiceBranchWeighted_prefixCut_eq_zero_of_forall_remaining_lt
    (n : ℕ) (qMore qLess : ℝ)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    (hcut : ∀ c : Candidate (n + 1), c ∈ remaining → (c : ℕ) < cut) :
    candidateRankPowerSum (n + 1) qLess *
        (∑ i : Candidate (n + 1),
          qMore ^ (i : ℕ) *
            firstChoiceBranchPayoffSum n qLess
              (fun τ : Ranking (n + 1) =>
                bestInSetPrefixCutIndicator remaining cut τ) i) -
      candidateRankPowerSum (n + 1) qMore *
        (∑ i : Candidate (n + 1),
          qLess ^ (i : ℕ) *
            firstChoiceBranchPayoffSum n qLess
              (fun τ : Ranking (n + 1) =>
                bestInSetPrefixCutIndicator remaining cut τ) i) = 0 := by
  classical
  simp_rw [
    firstChoiceBranchPayoffSum_prefixCut_eq_partition_of_forall_remaining_lt
      n qLess hremaining hcut]
  let Z : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let PMore : ℝ := candidateRankPowerSum (n + 1) qMore
  let PLess : ℝ := candidateRankPowerSum (n + 1) qLess
  change
    PLess * (∑ i : Candidate (n + 1), qMore ^ (i : ℕ) * Z) -
      PMore * (∑ i : Candidate (n + 1), qLess ^ (i : ℕ) * Z) = 0
  dsimp [PMore, PLess, Z]
  unfold candidateRankPowerSum
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

theorem firstChoiceBranchWeighted_prefixCut_eq_zero_of_forall_remaining_ge
    (n : ℕ) (qMore qLess : ℝ)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ}
    (hcut : ∀ c : Candidate (n + 1), c ∈ remaining → cut ≤ (c : ℕ)) :
    candidateRankPowerSum (n + 1) qLess *
        (∑ i : Candidate (n + 1),
          qMore ^ (i : ℕ) *
            firstChoiceBranchPayoffSum n qLess
              (fun τ : Ranking (n + 1) =>
                bestInSetPrefixCutIndicator remaining cut τ) i) -
      candidateRankPowerSum (n + 1) qMore *
        (∑ i : Candidate (n + 1),
          qLess ^ (i : ℕ) *
            firstChoiceBranchPayoffSum n qLess
              (fun τ : Ranking (n + 1) =>
                bestInSetPrefixCutIndicator remaining cut τ) i) = 0 := by
  classical
  simp_rw [
    firstChoiceBranchPayoffSum_prefixCut_eq_zero_of_forall_remaining_ge
      n qLess hremaining hcut]
  simp

theorem firstChoiceBranchWeighted_singleton_eq_zero
    (n : ℕ) (qMore qLess : ℝ) (c : Candidate (n + 1)) (cut : ℕ) :
    candidateRankPowerSum (n + 1) qLess *
        (∑ i : Candidate (n + 1),
          qMore ^ (i : ℕ) *
            firstChoiceBranchPayoffSum n qLess
              (fun τ : Ranking (n + 1) =>
                bestInSetPrefixCutIndicator
                  ({c} : Finset (Candidate (n + 1))) cut τ) i) -
      candidateRankPowerSum (n + 1) qMore *
        (∑ i : Candidate (n + 1),
          qLess ^ (i : ℕ) *
            firstChoiceBranchPayoffSum n qLess
              (fun τ : Ranking (n + 1) =>
                bestInSetPrefixCutIndicator
                  ({c} : Finset (Candidate (n + 1))) cut τ) i) = 0 := by
  classical
  have hremaining : ({c} : Finset (Candidate (n + 1))).Nonempty :=
    ⟨c, by simp⟩
  by_cases hcut : (c : ℕ) < cut
  · rw [firstChoiceBranchWeighted_prefixCut_eq_zero_of_forall_remaining_lt
      n qMore qLess hremaining (cut := cut)]
    intro d hd
    have hd_eq : d = c := by simpa using hd
    simpa [hd_eq] using hcut
  · rw [firstChoiceBranchWeighted_prefixCut_eq_zero_of_forall_remaining_ge
      n qMore qLess hremaining (cut := cut)]
    intro d hd
    have hd_eq : d = c := by simpa using hd
    simpa [hd_eq] using Nat.le_of_not_gt hcut

theorem firstChoiceBranchBracketSum_univ_prefix_nonneg
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (k : Candidate (n + 1)) :
    0 ≤ firstChoiceBranchBracketSum n qMore qLess
      (fun τ : Ranking (n + 1) =>
        bestInSetPrefixCutIndicator
          (Finset.univ : Finset (Candidate (n + 1))) ((k : ℕ) + 1) τ) := by
  classical
  let F : Ranking (n + 1) → ℝ := fun τ =>
    bestInSetPrefixCutIndicator
      (Finset.univ : Finset (Candidate (n + 1))) ((k : ℕ) + 1) τ
  let I : Candidate (n + 1) → ℝ := fun i =>
    if (i : ℕ) < (k : ℕ) + 1 then 1 else 0
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let PMore : ℝ := candidateRankPowerSum (n + 1) qMore
  let PLess : ℝ := candidateRankPowerSum (n + 1) qLess
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hZ_nonneg : 0 ≤ ZLess * ZMore :=
    mul_nonneg
      (le_of_lt (mallowsPartition_pos (hq := hqLess_pos)
        (Equiv.refl (Candidate n))))
      (le_of_lt (mallowsPartition_pos (hq := hqMore_pos)
        (Equiv.refl (Candidate n))))
  have hremaining :
      (Finset.univ : Finset (Candidate (n + 1))).Nonempty :=
    ⟨0, by simp⟩
  have hbranchMore :
      ∀ i : Candidate (n + 1),
        firstChoiceBranchPayoffSum n qMore F i = ZMore * I i := by
    intro i
    rw [firstChoiceBranchPayoffSum_prefixCut n qMore hremaining ((k : ℕ) + 1) i]
    simp [I, ZMore]
  have hbranchLess :
      ∀ i : Candidate (n + 1),
        firstChoiceBranchPayoffSum n qLess F i = ZLess * I i := by
    intro i
    rw [firstChoiceBranchPayoffSum_prefixCut n qLess hremaining ((k : ℕ) + 1) i]
    simp [I, ZLess]
  have hinitMore :
      (∑ i : Candidate (n + 1), qMore ^ (i : ℕ) * I i) =
        candidateRankInitialPowerSum (n + 1) qMore k := by
    calc
      (∑ i : Candidate (n + 1), qMore ^ (i : ℕ) * I i)
          =
        ∑ i : Candidate (n + 1),
          if (i : ℕ) < (k : ℕ) + 1 then qMore ^ (i : ℕ) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          change
            qMore ^ (i : ℕ) *
                (if (i : ℕ) < (k : ℕ) + 1 then (1 : ℝ) else 0) =
              if (i : ℕ) < (k : ℕ) + 1 then qMore ^ (i : ℕ) else 0
          by_cases hik : (i : ℕ) < (k : ℕ) + 1
          · rw [if_pos hik, if_pos hik]
            ring
          · rw [if_neg hik, if_neg hik]
            ring
      _ = candidateRankInitialPowerSum (n + 1) qMore k := by
          rw [← candidateRankInitialPowerSum_eq_sum_lt_succ]
  have hinitLess :
      (∑ i : Candidate (n + 1), qLess ^ (i : ℕ) * I i) =
        candidateRankInitialPowerSum (n + 1) qLess k := by
    calc
      (∑ i : Candidate (n + 1), qLess ^ (i : ℕ) * I i)
          =
        ∑ i : Candidate (n + 1),
          if (i : ℕ) < (k : ℕ) + 1 then qLess ^ (i : ℕ) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          change
            qLess ^ (i : ℕ) *
                (if (i : ℕ) < (k : ℕ) + 1 then (1 : ℝ) else 0) =
              if (i : ℕ) < (k : ℕ) + 1 then qLess ^ (i : ℕ) else 0
          by_cases hik : (i : ℕ) < (k : ℕ) + 1
          · rw [if_pos hik, if_pos hik]
            ring
          · rw [if_neg hik, if_neg hik]
            ring
      _ = candidateRankInitialPowerSum (n + 1) qLess k := by
          rw [← candidateRankInitialPowerSum_eq_sum_lt_succ]
  have hsum :
      firstChoiceBranchBracketSum n qMore qLess F =
        ZLess * ZMore *
          (PLess * candidateRankInitialPowerSum (n + 1) qMore k -
            PMore * candidateRankInitialPowerSum (n + 1) qLess k) := by
    rw [firstChoiceBranchBracketSum_eq_complementPower]
    calc
      (∑ i : Candidate (n + 1),
        (qMore ^ (i : ℕ) *
            (candidateRankPowerSum (n + 1) qLess - qLess ^ (i : ℕ)) *
            (mallowsPartition qLess (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qMore F i) -
          qLess ^ (i : ℕ) *
            (candidateRankPowerSum (n + 1) qMore - qMore ^ (i : ℕ)) *
            (mallowsPartition qMore (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qLess F i)))
          =
        ∑ i : Candidate (n + 1),
          ZLess * ZMore *
            (PLess * (qMore ^ (i : ℕ) * I i) -
              PMore * (qLess ^ (i : ℕ) * I i)) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hbranchMore i, hbranchLess i]
          simp [ZLess, ZMore, PMore, PLess]
          ring
      _ =
        ZLess * ZMore *
          (∑ i : Candidate (n + 1),
            (PLess * (qMore ^ (i : ℕ) * I i) -
              PMore * (qLess ^ (i : ℕ) * I i))) := by
          rw [← Finset.mul_sum]
      _ =
        ZLess * ZMore *
          (PLess * (∑ i : Candidate (n + 1), qMore ^ (i : ℕ) * I i) -
            PMore * (∑ i : Candidate (n + 1), qLess ^ (i : ℕ) * I i)) := by
          congr 1
          rw [Finset.sum_sub_distrib]
          rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ =
        ZLess * ZMore *
          (PLess * candidateRankInitialPowerSum (n + 1) qMore k -
            PMore * candidateRankInitialPowerSum (n + 1) qLess k) := by
          rw [hinitMore, hinitLess]
  rw [hsum]
  exact mul_nonneg hZ_nonneg
    (by
      simpa [PMore, PLess] using
        candidateRankInitialPowerSum_cross_nonneg
          (n + 1) hqMore_pos hq_lt k)

theorem firstChoiceBranchBracketSum_univ_cut_nonneg
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (cut : ℕ) :
    0 ≤ firstChoiceBranchBracketSum n qMore qLess
      (fun τ : Ranking (n + 1) =>
        bestInSetPrefixCutIndicator
          (Finset.univ : Finset (Candidate (n + 1))) cut τ) := by
  classical
  have hremaining :
      (Finset.univ : Finset (Candidate (n + 1))).Nonempty :=
    ⟨0, by simp⟩
  by_cases hcut0 : cut = 0
  · rw [firstChoiceBranchBracketSum_prefixCut_eq_zero_of_forall_remaining_ge
      n qMore qLess hremaining (by
        intro c _
        omega)]
  · by_cases hbig : n + 2 < cut
    · rw [firstChoiceBranchBracketSum_prefixCut_eq_zero_of_forall_remaining_lt
        n qMore qLess hremaining (by
          intro c _
          have hc_le : (c : ℕ) ≤ n + 2 := Nat.le_of_lt_succ c.isLt
          omega)]
    · have hcut_le : cut ≤ n + 2 := Nat.le_of_not_gt hbig
      let k : Candidate (n + 1) := ⟨cut - 1, by omega⟩
      have hk : (k : ℕ) + 1 = cut := by
        dsimp [k]
        omega
      simpa [hk] using
        firstChoiceBranchBracketSum_univ_prefix_nonneg
          n hqMore_pos hq_lt k

theorem firstChoiceBranchWeighted_univ_prefix_nonneg
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (k : Candidate (n + 1)) :
    0 ≤
      candidateRankPowerSum (n + 1) qLess *
          (∑ i : Candidate (n + 1),
            qMore ^ (i : ℕ) *
              firstChoiceBranchPayoffSum n qLess
                (fun τ : Ranking (n + 1) =>
                  bestInSetPrefixCutIndicator
                    (Finset.univ : Finset (Candidate (n + 1)))
                    ((k : ℕ) + 1) τ) i) -
        candidateRankPowerSum (n + 1) qMore *
          (∑ i : Candidate (n + 1),
            qLess ^ (i : ℕ) *
              firstChoiceBranchPayoffSum n qLess
                (fun τ : Ranking (n + 1) =>
                  bestInSetPrefixCutIndicator
                    (Finset.univ : Finset (Candidate (n + 1)))
                    ((k : ℕ) + 1) τ) i) := by
  classical
  let F : Ranking (n + 1) → ℝ := fun τ =>
    bestInSetPrefixCutIndicator
      (Finset.univ : Finset (Candidate (n + 1))) ((k : ℕ) + 1) τ
  let I : Candidate (n + 1) → ℝ := fun i =>
    if (i : ℕ) < (k : ℕ) + 1 then 1 else 0
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let PMore : ℝ := candidateRankPowerSum (n + 1) qMore
  let PLess : ℝ := candidateRankPowerSum (n + 1) qLess
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hZLess_nonneg : 0 ≤ ZLess :=
    le_of_lt (mallowsPartition_pos (hq := hqLess_pos)
      (Equiv.refl (Candidate n)))
  have hremaining :
      (Finset.univ : Finset (Candidate (n + 1))).Nonempty :=
    ⟨0, by simp⟩
  have hbranchLess :
      ∀ i : Candidate (n + 1),
        firstChoiceBranchPayoffSum n qLess F i = ZLess * I i := by
    intro i
    rw [firstChoiceBranchPayoffSum_prefixCut n qLess hremaining ((k : ℕ) + 1) i]
    simp [I, ZLess]
  have hinitMore :
      (∑ i : Candidate (n + 1), qMore ^ (i : ℕ) * I i) =
        candidateRankInitialPowerSum (n + 1) qMore k := by
    calc
      (∑ i : Candidate (n + 1), qMore ^ (i : ℕ) * I i)
          =
        ∑ i : Candidate (n + 1),
          if (i : ℕ) < (k : ℕ) + 1 then qMore ^ (i : ℕ) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          change
            qMore ^ (i : ℕ) *
                (if (i : ℕ) < (k : ℕ) + 1 then (1 : ℝ) else 0) =
              if (i : ℕ) < (k : ℕ) + 1 then qMore ^ (i : ℕ) else 0
          by_cases hik : (i : ℕ) < (k : ℕ) + 1
          · rw [if_pos hik, if_pos hik]
            ring
          · rw [if_neg hik, if_neg hik]
            ring
      _ = candidateRankInitialPowerSum (n + 1) qMore k := by
          rw [← candidateRankInitialPowerSum_eq_sum_lt_succ]
  have hinitLess :
      (∑ i : Candidate (n + 1), qLess ^ (i : ℕ) * I i) =
        candidateRankInitialPowerSum (n + 1) qLess k := by
    calc
      (∑ i : Candidate (n + 1), qLess ^ (i : ℕ) * I i)
          =
        ∑ i : Candidate (n + 1),
          if (i : ℕ) < (k : ℕ) + 1 then qLess ^ (i : ℕ) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          change
            qLess ^ (i : ℕ) *
                (if (i : ℕ) < (k : ℕ) + 1 then (1 : ℝ) else 0) =
              if (i : ℕ) < (k : ℕ) + 1 then qLess ^ (i : ℕ) else 0
          by_cases hik : (i : ℕ) < (k : ℕ) + 1
          · rw [if_pos hik, if_pos hik]
            ring
          · rw [if_neg hik, if_neg hik]
            ring
      _ = candidateRankInitialPowerSum (n + 1) qLess k := by
          rw [← candidateRankInitialPowerSum_eq_sum_lt_succ]
  have hrewrite :
      candidateRankPowerSum (n + 1) qLess *
          (∑ i : Candidate (n + 1),
            qMore ^ (i : ℕ) * firstChoiceBranchPayoffSum n qLess F i) -
        candidateRankPowerSum (n + 1) qMore *
          (∑ i : Candidate (n + 1),
            qLess ^ (i : ℕ) * firstChoiceBranchPayoffSum n qLess F i)
        =
      ZLess *
        (PLess * candidateRankInitialPowerSum (n + 1) qMore k -
          PMore * candidateRankInitialPowerSum (n + 1) qLess k) := by
    rw [show
        (∑ i : Candidate (n + 1),
          qMore ^ (i : ℕ) * firstChoiceBranchPayoffSum n qLess F i) =
          ZLess * (∑ i : Candidate (n + 1), qMore ^ (i : ℕ) * I i) by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hbranchLess i]
        ring,
      show
        (∑ i : Candidate (n + 1),
          qLess ^ (i : ℕ) * firstChoiceBranchPayoffSum n qLess F i) =
          ZLess * (∑ i : Candidate (n + 1), qLess ^ (i : ℕ) * I i) by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hbranchLess i]
        ring]
    rw [hinitMore, hinitLess]
    simp [PMore, PLess]
    ring
  change
    0 ≤
      candidateRankPowerSum (n + 1) qLess *
          (∑ i : Candidate (n + 1),
            qMore ^ (i : ℕ) * firstChoiceBranchPayoffSum n qLess F i) -
        candidateRankPowerSum (n + 1) qMore *
          (∑ i : Candidate (n + 1),
            qLess ^ (i : ℕ) * firstChoiceBranchPayoffSum n qLess F i)
  rw [hrewrite]
  exact mul_nonneg hZLess_nonneg
    (by
      simpa [PMore, PLess] using
        candidateRankInitialPowerSum_cross_nonneg
          (n + 1) hqMore_pos hq_lt k)

theorem firstChoiceBranchWeighted_univ_cut_nonneg
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (cut : ℕ) :
    0 ≤
      candidateRankPowerSum (n + 1) qLess *
          (∑ i : Candidate (n + 1),
            qMore ^ (i : ℕ) *
              firstChoiceBranchPayoffSum n qLess
                (fun τ : Ranking (n + 1) =>
                  bestInSetPrefixCutIndicator
                    (Finset.univ : Finset (Candidate (n + 1))) cut τ) i) -
        candidateRankPowerSum (n + 1) qMore *
          (∑ i : Candidate (n + 1),
            qLess ^ (i : ℕ) *
              firstChoiceBranchPayoffSum n qLess
                (fun τ : Ranking (n + 1) =>
                  bestInSetPrefixCutIndicator
                    (Finset.univ : Finset (Candidate (n + 1))) cut τ) i) := by
  classical
  have hremaining :
      (Finset.univ : Finset (Candidate (n + 1))).Nonempty :=
    ⟨0, by simp⟩
  by_cases hcut0 : cut = 0
  · rw [firstChoiceBranchWeighted_prefixCut_eq_zero_of_forall_remaining_ge
      n qMore qLess hremaining (by
        intro c _
        omega)]
  · by_cases hbig : n + 2 < cut
    · rw [firstChoiceBranchWeighted_prefixCut_eq_zero_of_forall_remaining_lt
        n qMore qLess hremaining (by
          intro c _
          have hc_le : (c : ℕ) ≤ n + 2 := Nat.le_of_lt_succ c.isLt
          omega)]
    · have hcut_le : cut ≤ n + 2 := Nat.le_of_not_gt hbig
      let k : Candidate (n + 1) := ⟨cut - 1, by omega⟩
      have hk : (k : ℕ) + 1 = cut := by
        dsimp [k]
        omega
      simpa [hk] using
        firstChoiceBranchWeighted_univ_prefix_nonneg
          n hqMore_pos hq_lt k

theorem firstChoiceBranchWeighted_eq_pair_sum
    (n : ℕ) (qMore qLess qTail : ℝ) (F : Ranking (n + 1) → ℝ) :
    candidateRankPowerSum (n + 1) qLess *
        (∑ i : Candidate (n + 1),
          qMore ^ (i : ℕ) * firstChoiceBranchPayoffSum n qTail F i) -
      candidateRankPowerSum (n + 1) qMore *
        (∑ i : Candidate (n + 1),
          qLess ^ (i : ℕ) * firstChoiceBranchPayoffSum n qTail F i) =
      ∑ i : Candidate (n + 1), ∑ j : Candidate (n + 1),
        if i < j then
          (qMore ^ (i : ℕ) * qLess ^ (j : ℕ) -
              qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
            (firstChoiceBranchPayoffSum n qTail F i -
              firstChoiceBranchPayoffSum n qTail F j)
        else 0 :=
    candidateRankWeightedAverage_cross_eq_pair_sum
      (n + 1) qMore qLess
      (fun i : Candidate (n + 1) =>
        firstChoiceBranchPayoffSum n qTail F i)

theorem firstChoiceBranchWeighted_eq_pair_sum'
    (n : ℕ) (qMore qLess qTail : ℝ) (F : Ranking (n + 1) → ℝ) :
    firstChoiceBranchWeighted n qMore qLess qTail F =
      ∑ i : Candidate (n + 1), ∑ j : Candidate (n + 1),
        if i < j then
          (qMore ^ (i : ℕ) * qLess ^ (j : ℕ) -
              qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
            (firstChoiceBranchPayoffSum n qTail F i -
              firstChoiceBranchPayoffSum n qTail F j)
        else 0 := by
  simpa [firstChoiceBranchWeighted] using
    firstChoiceBranchWeighted_eq_pair_sum n qMore qLess qTail F

theorem firstChoiceBranchWeighted_eq_adjacent_gap_sum
    (n : ℕ) (qMore qLess qTail : ℝ) (F : Ranking (n + 1) → ℝ) :
    firstChoiceBranchWeighted n qMore qLess qTail F =
      ∑ k : Fin (n + 2),
        (candidateRankPowerSum (n + 1) qLess *
            candidateRankInitialPowerSum (n + 1) qMore k.castSucc -
          candidateRankPowerSum (n + 1) qMore *
            candidateRankInitialPowerSum (n + 1) qLess k.castSucc) *
          (firstChoiceBranchPayoffSum n qTail F k.castSucc -
            firstChoiceBranchPayoffSum n qTail F k.succ) := by
  simpa [firstChoiceBranchWeighted] using
    candidateRankWeightedAverage_cross_eq_adjacent_gap_sum
      (n + 1) qMore qLess
      (fun i : Candidate (n + 1) =>
        firstChoiceBranchPayoffSum n qTail F i)

/-- The nonnegative coefficient multiplying an adjacent first-choice branch gap. -/
noncomputable def firstChoiceBranchAdjacentGapCoeff
    (n : ℕ) (qMore qLess : ℝ) (k : Fin (n + 2)) : ℝ :=
  candidateRankPowerSum (n + 1) qLess *
      candidateRankInitialPowerSum (n + 1) qMore k.castSucc -
    candidateRankPowerSum (n + 1) qMore *
      candidateRankInitialPowerSum (n + 1) qLess k.castSucc

theorem firstChoiceBranchAdjacentGapCoeff_nonneg
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (k : Fin (n + 2)) :
    0 ≤ firstChoiceBranchAdjacentGapCoeff n qMore qLess k := by
  simpa [firstChoiceBranchAdjacentGapCoeff] using
    candidateRankInitialPowerSum_cross_nonneg
      (n + 1) hqMore_pos hq_lt k.castSucc

theorem firstChoiceBranchWeighted_eq_adjacent_gap_sum_boundary
    (n : ℕ) (qMore qLess : ℝ)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ) :
    firstChoiceBranchWeighted n qMore qLess qLess
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ) =
      ∑ k : Fin (n + 2),
        if k.castSucc ∈ remaining ∨ k.succ ∈ remaining then
          firstChoiceBranchAdjacentGapCoeff n qMore qLess k *
            (firstChoiceBranchPayoffSum n qLess
                (fun τ : Ranking (n + 1) =>
                  bestInSetPrefixCutIndicator remaining cut τ) k.castSucc -
              firstChoiceBranchPayoffSum n qLess
                (fun τ : Ranking (n + 1) =>
                  bestInSetPrefixCutIndicator remaining cut τ) k.succ)
        else
          0 := by
  classical
  rw [firstChoiceBranchWeighted_eq_adjacent_gap_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  by_cases hboundary : k.castSucc ∈ remaining ∨ k.succ ∈ remaining
  · rw [if_pos hboundary]
    rfl
  · rw [if_neg hboundary]
    have hcast : k.castSucc ∉ remaining := by
      intro hk
      exact hboundary (Or.inl hk)
    have hsucc : k.succ ∉ remaining := by
      intro hk
      exact hboundary (Or.inr hk)
    have hgap :
        firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) k.castSucc =
          firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) k.succ :=
      firstChoiceBranchPayoffSum_prefixCut_eq_of_adjacent_not_mem
        n qLess hremaining cut k hcast hsucc
    rw [hgap]
    ring

theorem firstChoiceBranchWeighted_adjacentGapTerm_nonneg_of_left_mem_lt
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ} (k : Fin (n + 2))
    (hleft_mem : k.castSucc ∈ remaining)
    (hleft_cut : ((k.castSucc : Candidate (n + 1)) : ℕ) < cut) :
    0 ≤
      firstChoiceBranchAdjacentGapCoeff n qMore qLess k *
        (firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) k.castSucc -
          firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) k.succ) := by
  classical
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hcoeff :
      0 ≤ firstChoiceBranchAdjacentGapCoeff n qMore qLess k :=
    firstChoiceBranchAdjacentGapCoeff_nonneg n hqMore_pos hq_lt k
  have hleft :
      firstChoiceBranchPayoffSum n qLess
          (fun τ : Ranking (n + 1) =>
            bestInSetPrefixCutIndicator remaining cut τ) k.castSucc =
        mallowsPartition qLess (Equiv.refl (Candidate n)) :=
    firstChoiceBranchPayoffSum_prefixCut_eq_partition_of_mem_lt
      n qLess hremaining hleft_mem hleft_cut
  have hright_le :
      firstChoiceBranchPayoffSum n qLess
          (fun τ : Ranking (n + 1) =>
            bestInSetPrefixCutIndicator remaining cut τ) k.succ ≤
        mallowsPartition qLess (Equiv.refl (Candidate n)) :=
    firstChoiceBranchPayoffSum_prefixCut_le_partition
      n (le_of_lt hqLess_pos) cut k.succ
  have hgap :
      0 ≤
        firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) k.castSucc -
          firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) k.succ := by
    rw [hleft]
    exact sub_nonneg.mpr hright_le
  exact mul_nonneg hcoeff hgap

theorem firstChoiceBranchWeighted_adjacentGapTerm_nonneg_of_right_mem_ge
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ} (k : Fin (n + 2))
    (hright_mem : k.succ ∈ remaining)
    (hright_cut : cut ≤ ((k.succ : Candidate (n + 1)) : ℕ)) :
    0 ≤
      firstChoiceBranchAdjacentGapCoeff n qMore qLess k *
        (firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) k.castSucc -
          firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) k.succ) := by
  classical
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hcoeff :
      0 ≤ firstChoiceBranchAdjacentGapCoeff n qMore qLess k :=
    firstChoiceBranchAdjacentGapCoeff_nonneg n hqMore_pos hq_lt k
  have hright :
      firstChoiceBranchPayoffSum n qLess
          (fun τ : Ranking (n + 1) =>
            bestInSetPrefixCutIndicator remaining cut τ) k.succ = 0 :=
    firstChoiceBranchPayoffSum_prefixCut_eq_zero_of_mem_ge
      n qLess hremaining hright_mem hright_cut
  have hleft_nonneg :
      0 ≤
        firstChoiceBranchPayoffSum n qLess
          (fun τ : Ranking (n + 1) =>
            bestInSetPrefixCutIndicator remaining cut τ) k.castSucc :=
    firstChoiceBranchPayoffSum_prefixCut_nonneg
      n (le_of_lt hqLess_pos) cut k.castSucc
  have hgap :
      0 ≤
        firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) k.castSucc -
          firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) k.succ := by
    rw [hright, sub_zero]
    exact hleft_nonneg
  exact mul_nonneg hcoeff hgap

theorem firstChoiceBranchWeighted_adjacentGapTerm_nonneg_of_mem_mem
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ} (k : Fin (n + 2))
    (hleft_mem : k.castSucc ∈ remaining)
    (hright_mem : k.succ ∈ remaining) :
    0 ≤
      firstChoiceBranchAdjacentGapCoeff n qMore qLess k *
        (firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) k.castSucc -
          firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) k.succ) := by
  classical
  by_cases hleft_cut :
      ((k.castSucc : Candidate (n + 1)) : ℕ) < cut
  · exact
      firstChoiceBranchWeighted_adjacentGapTerm_nonneg_of_left_mem_lt
        n hqMore_pos hq_lt hremaining k hleft_mem hleft_cut
  · have hleft_ge : cut ≤ ((k.castSucc : Candidate (n + 1)) : ℕ) :=
      Nat.le_of_not_gt hleft_cut
    have hright_ge : cut ≤ ((k.succ : Candidate (n + 1)) : ℕ) := by
      have hcast_le_succ :
          ((k.castSucc : Candidate (n + 1)) : ℕ) ≤
            ((k.succ : Candidate (n + 1)) : ℕ) :=
        Nat.le_of_lt k.castSucc_lt_succ
      omega
    rw [
      firstChoiceBranchPayoffSum_prefixCut_eq_zero_of_mem_ge
        n qLess hremaining hleft_mem hleft_ge,
      firstChoiceBranchPayoffSum_prefixCut_eq_zero_of_mem_ge
        n qLess hremaining hright_mem hright_ge]
    ring_nf
    exact le_rfl

theorem firstChoiceBranchWeighted_adjacentGapTerm_nonneg
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ} (k : Fin (n + 2))
    (hleft_mixed :
      k.castSucc ∈ remaining → k.succ ∉ remaining →
        ((k.castSucc : Candidate (n + 1)) : ℕ) < cut)
    (hright_mixed :
      k.castSucc ∉ remaining → k.succ ∈ remaining →
        cut ≤ ((k.succ : Candidate (n + 1)) : ℕ)) :
    0 ≤
      firstChoiceBranchAdjacentGapCoeff n qMore qLess k *
        (firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) k.castSucc -
          firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) k.succ) := by
  classical
  by_cases hleft : k.castSucc ∈ remaining
  · by_cases hright : k.succ ∈ remaining
    · exact
        firstChoiceBranchWeighted_adjacentGapTerm_nonneg_of_mem_mem
          n hqMore_pos hq_lt hremaining k hleft hright
    · exact
        firstChoiceBranchWeighted_adjacentGapTerm_nonneg_of_left_mem_lt
          n hqMore_pos hq_lt hremaining k hleft
          (hleft_mixed hleft hright)
  · by_cases hright : k.succ ∈ remaining
    · exact
        firstChoiceBranchWeighted_adjacentGapTerm_nonneg_of_right_mem_ge
          n hqMore_pos hq_lt hremaining k hright
          (hright_mixed hleft hright)
    · have hgap :
          firstChoiceBranchPayoffSum n qLess
              (fun τ : Ranking (n + 1) =>
                bestInSetPrefixCutIndicator remaining cut τ) k.castSucc =
            firstChoiceBranchPayoffSum n qLess
              (fun τ : Ranking (n + 1) =>
                bestInSetPrefixCutIndicator remaining cut τ) k.succ :=
        firstChoiceBranchPayoffSum_prefixCut_eq_of_adjacent_not_mem
          n qLess hremaining cut k hleft hright
      rw [hgap]
      ring_nf
      exact le_rfl

theorem firstChoiceBranchWeighted_prefixCut_nonneg_of_adjacentGapTerms
    (n : ℕ) {qMore qLess : ℝ}
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ)
    (hterm :
      ∀ k : Fin (n + 2),
        k.castSucc ∈ remaining ∨ k.succ ∈ remaining →
          0 ≤
            firstChoiceBranchAdjacentGapCoeff n qMore qLess k *
              (firstChoiceBranchPayoffSum n qLess
                  (fun τ : Ranking (n + 1) =>
                    bestInSetPrefixCutIndicator remaining cut τ) k.castSucc -
                firstChoiceBranchPayoffSum n qLess
                  (fun τ : Ranking (n + 1) =>
                    bestInSetPrefixCutIndicator remaining cut τ) k.succ)) :
    0 ≤
      firstChoiceBranchWeighted n qMore qLess qLess
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ) := by
  classical
  rw [firstChoiceBranchWeighted_eq_adjacent_gap_sum_boundary
    n qMore qLess hremaining cut]
  refine Finset.sum_nonneg ?_
  intro k _
  by_cases hboundary : k.castSucc ∈ remaining ∨ k.succ ∈ remaining
  · simpa [hboundary] using hterm k hboundary
  · simp [hboundary]

theorem firstChoiceBranchWeighted_prefixCut_nonneg_of_no_bad_mixed_adjacent
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ)
    (hleft_mixed :
      ∀ k : Fin (n + 2),
        k.castSucc ∈ remaining → k.succ ∉ remaining →
          ((k.castSucc : Candidate (n + 1)) : ℕ) < cut)
    (hright_mixed :
      ∀ k : Fin (n + 2),
        k.castSucc ∉ remaining → k.succ ∈ remaining →
          cut ≤ ((k.succ : Candidate (n + 1)) : ℕ)) :
    0 ≤
      firstChoiceBranchWeighted n qMore qLess qLess
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ) :=
  firstChoiceBranchWeighted_prefixCut_nonneg_of_adjacentGapTerms
    n hremaining cut
    (fun k _ =>
      firstChoiceBranchWeighted_adjacentGapTerm_nonneg
        n hqMore_pos hq_lt hremaining k
        (hleft_mixed k) (hright_mixed k))

/--
Targeted positive-correlation theorem for first-choice prefix events.

This is now the narrow FKG/interleaving boundary: under identity-center Mallows
weight, any 0/1 event monotone under adjacent inversion corrections is
positively correlated with the event that the first candidate lies in a fixed
center prefix.  The proof splits full rankings into internal low/high orders and
a binary interleaving, then applies the averaged binary FKG theorem.
-/
theorem reflMallowsPayoffSum_firstChoicePrefixCovariance_nonneg_of_adjacentSwapImproves
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) (F : Ranking (n + 1) → ℝ)
    (hF01 : ∀ τ, F τ = 0 ∨ F τ = 1)
    (hF : AdjacentSwapImproves (Equiv.refl (Candidate (n + 1))) F)
    (k : Fin (n + 2)) :
    0 ≤
      reflMallowsCovariance (n + 1) q F
        (fun π : Ranking (n + 1) =>
          firstChoicePrefixIndicator n k.castSucc π) := by
  classical
  let kc : Candidate (n + 1) := k.castSucc
  let A : Equiv.Perm (Fin (kc.val + 1)) ×
      Equiv.Perm (Fin (n + 2 - kc.val)) → ℝ :=
    fun a => prefixSplitInternalWeight n kc q a.1 a.2
  have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
  have hA_nonneg : ∀ a, 0 ≤ A a := by
    intro a
    exact prefixSplitInternalWeight_nonneg n kc hq_nonneg a.1 a.2
  have hcorr :=
    binaryHeightInterleavingWeight_firstChoicePrefix_positiveAssociation_mergeRanking_averaged
      n kc hq_nonneg A hA_nonneg F hF01 hF
  unfold reflMallowsCovariance
  rw [reflMallowsPayoffSum_prefixSplit_pair
    (n := n) (k := kc) (q := q)
    (H := fun τ => F τ * firstChoicePrefixIndicator n kc τ)]
  rw [mallowsPartition_refl_prefixSplit_product
    (n := n) (k := kc) (q := q)]
  rw [reflMallowsPayoffSum_prefixSplit_pair
    (n := n) (k := kc) (q := q) (H := F)]
  rw [reflMallowsPayoffSum_prefixSplit_pair
    (n := n) (k := kc) (q := q)
    (H := fun τ : Ranking (n + 1) =>
      firstChoicePrefixIndicator n kc τ)]
  simpa [A, kc] using hcorr

theorem reflMallowsPayoffSum_firstChoiceGeomCovariance_nonneg_of_adjacentSwapImproves
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (F : Ranking (n + 1) → ℝ)
    (hF01 : ∀ τ, F τ = 0 ∨ F τ = 1)
    (hF : AdjacentSwapImproves (Equiv.refl (Candidate (n + 1))) F) :
    0 ≤
      reflMallowsPayoffSum (n + 1) qLess
          (fun π =>
            F π * (qMore / qLess) ^
              ((firstChoice π : Candidate (n + 1)) : ℕ)) *
        mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) -
      reflMallowsPayoffSum (n + 1) qLess F *
        reflMallowsPayoffSum (n + 1) qLess
          (fun π : Ranking (n + 1) =>
            (qMore / qLess) ^
              ((firstChoice π : Candidate (n + 1)) : ℕ)) := by
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hratio_nonneg : 0 ≤ qMore / qLess :=
    div_nonneg hqMore_pos.le hqLess_pos.le
  have hratio_le_one : qMore / qLess ≤ 1 :=
    div_le_one_of_le₀ (le_of_lt hq_lt) hqLess_pos.le
  have hcov :=
    reflMallowsCovariance_firstChoiceGeom_nonneg_of_prefix
      n qLess (qMore / qLess) hratio_nonneg hratio_le_one F
      (fun k =>
        reflMallowsPayoffSum_firstChoicePrefixCovariance_nonneg_of_adjacentSwapImproves
          n hqLess_pos F hF01 hF k)
  simpa [reflMallowsCovariance] using hcov

theorem reflMallowsPayoffSum_firstChoicePrefixCovariance_pos_prefixCut_one_of_zero_mem_card_gt_one
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q)
    {remaining : Finset (Candidate (n + 1))}
    (hzero : (0 : Candidate (n + 1)) ∈ remaining)
    (hcard : 1 < remaining.card) :
    0 <
      reflMallowsCovariance (n + 1) q
        (fun π : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining 1 π)
        (fun π : Ranking (n + 1) =>
          firstChoicePrefixIndicator n (0 : Candidate (n + 1)) π) := by
  classical
  refine
    reflMallowsCovariance_pos_of_subset_not_total
      (n + 1) q
      (fun π : Ranking (n + 1) =>
        bestInSetPrefixCutIndicator remaining 1 π)
      (fun π : Ranking (n + 1) =>
        firstChoicePrefixIndicator n (0 : Candidate (n + 1)) π)
      ?subset
      (reflMallowsPayoffSum_firstChoicePrefix_zero_pos n hq_pos)
      ?not_total
  · intro τ
    unfold bestInSetPrefixCutIndicator firstChoicePrefixIndicator
    by_cases hfirst : firstChoice τ ≤ (0 : Candidate (n + 1))
    · have hfirst_eq : firstChoice τ = 0 :=
        le_antisymm hfirst (Fin.zero_le _)
      have hfirst0 : τ 0 = 0 := by
        simpa [firstChoice] using hfirst_eq
      have hbest : bestInSet τ remaining = 0 := by
        refine bestInSet_eq_of_forall_rank_le τ remaining hzero ?_
        intro d hd
        rw [← hfirst_eq]
        rw [rankOf_firstChoice]
        exact Fin.zero_le _
      have hcut : ((bestInSet τ remaining : Candidate (n + 1)) : ℕ) < 1 := by
        simp [hbest]
      simp [firstChoice, hfirst0, hcut]
    · have hfirst0 : τ 0 ≠ 0 := by
        intro hτ0
        exact hfirst (by simp [firstChoice, hτ0])
      simp [firstChoice, hfirst0]
  · simpa [reflMallowsBestInSetPrefixCutSum] using
      reflMallowsBestInSetPrefixCutSum_one_lt_partition_of_zero_mem_card_gt_one
        n hq_pos hzero hcard

theorem reflMallowsPayoffSum_firstChoiceGeomCovariance_pos_prefixCut_one_of_zero_mem_card_gt_one
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hzero : (0 : Candidate (n + 1)) ∈ remaining)
    (hcard : 1 < remaining.card) :
    0 <
      reflMallowsPayoffSum (n + 1) qLess
          (fun π =>
            bestInSetPrefixCutIndicator remaining 1 π *
              (qMore / qLess) ^
                ((firstChoice π : Candidate (n + 1)) : ℕ)) *
        mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) -
      reflMallowsPayoffSum (n + 1) qLess
          (fun π : Ranking (n + 1) =>
            bestInSetPrefixCutIndicator remaining 1 π) *
        reflMallowsPayoffSum (n + 1) qLess
          (fun π : Ranking (n + 1) =>
            (qMore / qLess) ^
              ((firstChoice π : Candidate (n + 1)) : ℕ)) := by
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hratio_nonneg : 0 ≤ qMore / qLess :=
    div_nonneg hqMore_pos.le hqLess_pos.le
  have hratio_le_one : qMore / qLess ≤ 1 :=
    div_le_one_of_le₀ (le_of_lt hq_lt) hqLess_pos.le
  have hratio_lt_one : qMore / qLess < 1 :=
    (div_lt_one hqLess_pos).mpr hq_lt
  have hgap :
      0 <
        (qMore / qLess) ^ (((0 : Fin (n + 2)) : ℕ)) -
          (qMore / qLess) ^ (((0 : Fin (n + 2)) : ℕ) + 1) := by
    simpa using sub_pos.mpr hratio_lt_one
  have hcov :=
    reflMallowsCovariance_firstChoiceGeom_pos_of_prefix
      n qLess (qMore / qLess) hratio_nonneg hratio_le_one
      (fun π : Ranking (n + 1) =>
        bestInSetPrefixCutIndicator remaining 1 π)
      (fun k =>
        reflMallowsPayoffSum_firstChoicePrefixCovariance_nonneg_of_adjacentSwapImproves
          n hqLess_pos
          (fun π : Ranking (n + 1) =>
            bestInSetPrefixCutIndicator remaining 1 π)
          (bestInSetPrefixCutIndicator_eq_zero_or_one remaining 1)
          (adjacentSwapImproves_bestInSetPrefixCutIndicator
            ⟨0, hzero⟩ 1)
          k)
      (0 : Fin (n + 2)) hgap
      (by
        simpa using
          reflMallowsPayoffSum_firstChoicePrefixCovariance_pos_prefixCut_one_of_zero_mem_card_gt_one
            n hqLess_pos hzero hcard)
  simpa [reflMallowsCovariance] using hcov

theorem firstChoiceBranchCovariance_pos_prefixCut_one_of_zero_mem_card_gt_one
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hzero : (0 : Candidate (n + 1)) ∈ remaining)
    (hcard : 1 < remaining.card) :
    0 <
      (∑ i : Candidate (n + 1),
        qMore ^ (i : ℕ) *
          firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining 1 τ) i) *
          (candidateRankPowerSum (n + 1) qLess *
            mallowsPartition qLess (Equiv.refl (Candidate n))) -
        (∑ i : Candidate (n + 1),
          qLess ^ (i : ℕ) *
            firstChoiceBranchPayoffSum n qLess
              (fun τ : Ranking (n + 1) =>
                bestInSetPrefixCutIndicator remaining 1 τ) i) *
          (candidateRankPowerSum (n + 1) qMore *
            mallowsPartition qLess (Equiv.refl (Candidate n))) := by
  have hgeom :=
    reflMallowsPayoffSum_firstChoiceGeomCovariance_pos_prefixCut_one_of_zero_mem_card_gt_one
      n hqMore_pos hq_lt hzero hcard
  rwa [firstChoiceBranchCovariance_eq_mallowsGeomCovariance
      n (ne_of_gt (lt_trans hqMore_pos hq_lt))
      (fun τ : Ranking (n + 1) =>
        bestInSetPrefixCutIndicator remaining 1 τ)]

theorem firstChoiceBranchWeighted_prefixCut_one_pos_of_zero_mem_card_gt_one
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hzero : (0 : Candidate (n + 1)) ∈ remaining)
    (hcard : 1 < remaining.card) :
    0 <
      firstChoiceBranchWeighted n qMore qLess qLess
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining 1 τ) :=
  firstChoiceBranchWeighted_pos_of_branch_covariance
    n (lt_trans hqMore_pos hq_lt)
    (fun τ : Ranking (n + 1) =>
      bestInSetPrefixCutIndicator remaining 1 τ)
    (firstChoiceBranchCovariance_pos_prefixCut_one_of_zero_mem_card_gt_one
      n hqMore_pos hq_lt hzero hcard)

theorem firstChoiceBranchCovariance_nonneg_of_adjacentSwapImproves
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (F : Ranking (n + 1) → ℝ)
    (hF01 : ∀ τ, F τ = 0 ∨ F τ = 1)
    (hF : AdjacentSwapImproves (Equiv.refl (Candidate (n + 1))) F) :
    0 ≤
      (∑ i : Candidate (n + 1),
        qMore ^ (i : ℕ) * firstChoiceBranchPayoffSum n qLess F i) *
          (candidateRankPowerSum (n + 1) qLess *
            mallowsPartition qLess (Equiv.refl (Candidate n))) -
        (∑ i : Candidate (n + 1),
          qLess ^ (i : ℕ) * firstChoiceBranchPayoffSum n qLess F i) *
          (candidateRankPowerSum (n + 1) qMore *
            mallowsPartition qLess (Equiv.refl (Candidate n))) := by
  have hgeom :
      0 ≤
        reflMallowsPayoffSum (n + 1) qLess
            (fun π =>
              F π * (qMore / qLess) ^
                ((firstChoice π : Candidate (n + 1)) : ℕ)) *
          mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) -
        reflMallowsPayoffSum (n + 1) qLess F *
          reflMallowsPayoffSum (n + 1) qLess
            (fun π : Ranking (n + 1) =>
              (qMore / qLess) ^
                ((firstChoice π : Candidate (n + 1)) : ℕ)) :=
    reflMallowsPayoffSum_firstChoiceGeomCovariance_nonneg_of_adjacentSwapImproves
      n hqMore_pos hq_lt F hF01 hF
  rwa [firstChoiceBranchCovariance_eq_mallowsGeomCovariance
      n (ne_of_gt (lt_trans hqMore_pos hq_lt)) F]

theorem firstChoiceBranchWeighted_nonneg_of_adjacentSwapImproves
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (F : Ranking (n + 1) → ℝ)
    (hF01 : ∀ τ, F τ = 0 ∨ F τ = 1)
    (hF : AdjacentSwapImproves (Equiv.refl (Candidate (n + 1))) F) :
    0 ≤ firstChoiceBranchWeighted n qMore qLess qLess F :=
  firstChoiceBranchWeighted_nonneg_of_branch_covariance
    n (lt_trans hqMore_pos hq_lt) F
    (firstChoiceBranchCovariance_nonneg_of_adjacentSwapImproves
      n hqMore_pos hq_lt F hF01 hF)

theorem firstChoiceBranchWeighted_adjacentGapTerm_eq_tail_sub_partition
    (n : ℕ) (qMore qLess : ℝ)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ} (k : Fin (n + 2))
    (hleft_not : k.castSucc ∉ remaining)
    (hright_mem : k.succ ∈ remaining)
    (hright_cut : ((k.succ : Candidate (n + 1)) : ℕ) < cut) :
    firstChoiceBranchAdjacentGapCoeff n qMore qLess k *
        (firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) k.castSucc -
          firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) k.succ) =
      firstChoiceBranchAdjacentGapCoeff n qMore qLess k *
        (reflMallowsBestInSetPrefixCutSum n qLess
            (firstChoiceTailRemainingOf k.castSucc remaining)
            (deleteFirstChoicePrefixCut k.castSucc cut) -
          mallowsPartition qLess (Equiv.refl (Candidate n))) := by
  rw [
    firstChoiceBranchPayoffSum_prefixCut n qLess hremaining cut k.castSucc,
    firstChoiceBranchPayoffSum_prefixCut_eq_partition_of_mem_lt
      n qLess hremaining hright_mem hright_cut]
  simp [hleft_not]

theorem firstChoiceBranchWeighted_adjacentGapTerm_eq_neg_tail
    (n : ℕ) (qMore qLess : ℝ)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) {cut : ℕ} (k : Fin (n + 2))
    (hleft_mem : k.castSucc ∈ remaining)
    (hleft_cut : cut ≤ ((k.castSucc : Candidate (n + 1)) : ℕ))
    (hright_not : k.succ ∉ remaining) :
    firstChoiceBranchAdjacentGapCoeff n qMore qLess k *
        (firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) k.castSucc -
          firstChoiceBranchPayoffSum n qLess
            (fun τ : Ranking (n + 1) =>
              bestInSetPrefixCutIndicator remaining cut τ) k.succ) =
      firstChoiceBranchAdjacentGapCoeff n qMore qLess k *
        (0 -
          reflMallowsBestInSetPrefixCutSum n qLess
            (firstChoiceTailRemainingOf k.succ remaining)
            (deleteFirstChoicePrefixCut k.succ cut)) := by
  rw [
    firstChoiceBranchPayoffSum_prefixCut_eq_zero_of_mem_ge
      n qLess hremaining hleft_mem hleft_cut,
    firstChoiceBranchPayoffSum_prefixCut n qLess hremaining cut k.succ]
  simp [hright_not]

theorem firstChoiceBranchWeighted_nonneg_of_pair_terms
    (n : ℕ) (qMore qLess qTail : ℝ) (F : Ranking (n + 1) → ℝ)
    (hpair :
      ∀ i j : Candidate (n + 1), i < j →
        0 ≤
          (qMore ^ (i : ℕ) * qLess ^ (j : ℕ) -
              qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) *
            (firstChoiceBranchPayoffSum n qTail F i -
              firstChoiceBranchPayoffSum n qTail F j)) :
    0 ≤ firstChoiceBranchWeighted n qMore qLess qTail F := by
  classical
  rw [firstChoiceBranchWeighted_eq_pair_sum']
  refine Finset.sum_nonneg ?_
  intro i _
  refine Finset.sum_nonneg ?_
  intro j _
  by_cases hij : i < j
  · simpa [hij] using hpair i j hij
  · simp [hij]

/--
First-choice induction step with an aggregate off-diagonal bracket condition.

This is the version intended for arbitrary remaining-set work: the proof only
needs the total off-diagonal first-choice contribution to be nonnegative, not
every individual two-branch bracket.
-/
theorem reflMallowsPayoffSum_cross_of_firstChoice_pair_bracket_sum
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (F : Ranking (n + 1) → ℝ)
    (hdiag :
      ∀ r : Candidate (n + 1),
        0 ≤
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qMore F r -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qLess F r)
    (hpair_sum :
      0 ≤ firstChoiceBranchBracketSum n qMore qLess F) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qMore F -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qLess F := by
  classical
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let SMore : Candidate (n + 1) → ℝ := fun r =>
    firstChoiceBranchPayoffSum n qMore F r
  let SLess : Candidate (n + 1) → ℝ := fun r =>
    firstChoiceBranchPayoffSum n qLess F r
  have hqLess_nonneg : 0 ≤ qLess := le_of_lt (lt_trans hqMore_pos hq_lt)
  have hcore :
      0 ≤
        candidateRankPowerSum (n + 1) qLess * ZLess *
            (∑ i : Candidate (n + 1), qMore ^ (i : ℕ) * SMore i) -
          candidateRankPowerSum (n + 1) qMore * ZMore *
            (∑ i : Candidate (n + 1), qLess ^ (i : ℕ) * SLess i) :=
    candidateRankBranchCross_nonneg_of_diag_pair_sum
      (n + 1) (le_of_lt hqMore_pos) hqLess_nonneg
      (SMore := SMore) (SLess := SLess)
      (by
        intro i
        simpa [ZLess, ZMore, SMore, SLess] using hdiag i)
      (by
        simpa [firstChoiceBranchBracketSum, firstChoiceBranchBracket,
          ZLess, ZMore, SMore, SLess] using hpair_sum)
  rw [mallowsPartition_refl_peelBest n qLess,
    mallowsPartition_refl_peelBest n qMore,
    reflMallowsPayoffSum_firstChoice n qMore F,
    reflMallowsPayoffSum_firstChoice n qLess F]
  simpa [firstChoiceBranchPayoffSum, ZLess, ZMore, SMore, SLess,
    mul_comm, mul_left_comm, mul_assoc]
    using hcore

theorem reflMallowsPayoffSum_cross_pos_of_firstChoice_pair_bracket_sum
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (F : Ranking (n + 1) → ℝ)
    (hdiag :
      ∀ r : Candidate (n + 1),
        0 ≤
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qMore F r -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qLess F r)
    (hpair_sum :
      0 < firstChoiceBranchBracketSum n qMore qLess F) :
    0 <
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qMore F -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qLess F := by
  classical
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let SMore : Candidate (n + 1) → ℝ := fun r =>
    firstChoiceBranchPayoffSum n qMore F r
  let SLess : Candidate (n + 1) → ℝ := fun r =>
    firstChoiceBranchPayoffSum n qLess F r
  have hqLess_nonneg : 0 ≤ qLess := le_of_lt (lt_trans hqMore_pos hq_lt)
  have hcore :
      0 <
        candidateRankPowerSum (n + 1) qLess * ZLess *
            (∑ i : Candidate (n + 1), qMore ^ (i : ℕ) * SMore i) -
          candidateRankPowerSum (n + 1) qMore * ZMore *
            (∑ i : Candidate (n + 1), qLess ^ (i : ℕ) * SLess i) :=
    candidateRankBranchCross_pos_of_diag_pair_sum
      (n + 1) (le_of_lt hqMore_pos) hqLess_nonneg
      (SMore := SMore) (SLess := SLess)
      (by
        intro i
        simpa [ZLess, ZMore, SMore, SLess] using hdiag i)
      (by
        simpa [firstChoiceBranchBracketSum, firstChoiceBranchBracket,
          ZLess, ZMore, SMore, SLess] using hpair_sum)
  rw [mallowsPartition_refl_peelBest n qLess,
    mallowsPartition_refl_peelBest n qMore,
    reflMallowsPayoffSum_firstChoice n qMore F,
    reflMallowsPayoffSum_firstChoice n qLess F]
  simpa [firstChoiceBranchPayoffSum, ZLess, ZMore, SMore, SLess,
    mul_comm, mul_left_comm, mul_assoc]
    using hcore

/--
Prefix-cut first-hit dominance from the aggregate first-choice bracket target.

This is the arbitrary remaining-set specialization of
`reflMallowsPayoffSum_cross_of_firstChoice_pair_bracket_sum`.
-/
theorem reflMallowsBestInSetPrefixCutSum_cross_of_firstChoice_pair_bracket_sum
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ)
    (hdiag :
      ∀ r : Candidate (n + 1),
        0 ≤
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qMore
                (fun τ : Ranking (n + 1) =>
                  bestInSetPrefixCutIndicator remaining cut τ) r -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              firstChoiceBranchPayoffSum n qLess
                (fun τ : Ranking (n + 1) =>
                  bestInSetPrefixCutIndicator remaining cut τ) r)
    (hpair_sum :
      0 ≤ firstChoiceBranchBracketSum n qMore qLess
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ)) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qMore remaining cut -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qLess remaining cut := by
  classical
  unfold reflMallowsBestInSetPrefixCutSum
  exact
    reflMallowsPayoffSum_cross_of_firstChoice_pair_bracket_sum
      n hqMore_pos hq_lt
      (fun τ : Ranking (n + 1) =>
        bestInSetPrefixCutIndicator remaining cut τ)
      hdiag hpair_sum

/--
Prefix-cut first-hit dominance from tail prefix dominance and an aggregate
first-choice bracket-sum condition.

This packages the diagonal branch obligations using
`firstChoiceBranchPayoffSum_prefixCut_diag_nonneg_of_tail`, leaving the
off-diagonal aggregate bracket sum as the remaining arbitrary-size obligation.
-/
theorem reflMallowsBestInSetPrefixCutSum_cross_of_firstChoice_tail_pair_bracket_sum
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ)
    (htail :
      ∀ r : Candidate (n + 1), r ∉ remaining →
        0 ≤
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixCutSum n qMore
                (firstChoiceTailRemainingOf r remaining)
                (deleteFirstChoicePrefixCut r cut) -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixCutSum n qLess
                (firstChoiceTailRemainingOf r remaining)
                (deleteFirstChoicePrefixCut r cut))
    (hpair_sum :
      0 ≤ firstChoiceBranchBracketSum n qMore qLess
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ)) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qMore remaining cut -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qLess remaining cut :=
    reflMallowsBestInSetPrefixCutSum_cross_of_firstChoice_pair_bracket_sum
      n hqMore_pos hq_lt hremaining cut
      (firstChoiceBranchPayoffSum_prefixCut_diag_nonneg_of_tail
        n hremaining cut htail)
      hpair_sum

theorem reflMallowsBestInSetPrefixCutSum_cross_pos_of_firstChoice_tail_pair_bracket_sum
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ)
    (htail :
      ∀ r : Candidate (n + 1), r ∉ remaining →
        0 ≤
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixCutSum n qMore
                (firstChoiceTailRemainingOf r remaining)
                (deleteFirstChoicePrefixCut r cut) -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixCutSum n qLess
                (firstChoiceTailRemainingOf r remaining)
                (deleteFirstChoicePrefixCut r cut))
    (hpair_sum :
      0 < firstChoiceBranchBracketSum n qMore qLess
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ)) :
    0 <
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qMore remaining cut -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qLess remaining cut := by
  classical
  unfold reflMallowsBestInSetPrefixCutSum
  exact
    reflMallowsPayoffSum_cross_pos_of_firstChoice_pair_bracket_sum
      n hqMore_pos hq_lt
      (fun τ : Ranking (n + 1) =>
        bestInSetPrefixCutIndicator remaining cut τ)
      (firstChoiceBranchPayoffSum_prefixCut_diag_nonneg_of_tail
        n hremaining cut htail)
      hpair_sum

/-- Prefix-cut dominance target for all nonempty remaining sets. -/
def ReflMallowsBestInSetPrefixCutDominance
    (n : ℕ) (qMore qLess : ℝ) : Prop :=
  ∀ {remaining : Finset (Candidate n)}, remaining.Nonempty → ∀ cut : ℕ,
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixCutSum n qMore remaining cut -
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixCutSum n qLess remaining cut

/--
Aggregate first-choice bracket-sum target for prefix first-hit events in the
`n + 1` candidate universe.
-/
def ReflMallowsBestInSetPrefixCutFirstChoiceBracketSum
    (n : ℕ) (qMore qLess : ℝ) : Prop :=
  ∀ {remaining : Finset (Candidate (n + 1))}, remaining.Nonempty →
    ∀ cut : ℕ,
      0 ≤ firstChoiceBranchBracketSum n qMore qLess
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ)

/--
Weighted first-choice target for prefix first-hit events, with the tail law
held fixed at the less accurate Mallows parameter.

Together with smaller-size prefix-cut dominance, this implies the aggregate
first-choice bracket target.  It is narrower than proving the raw bracket sum
directly and isolates the remaining non-monotone first-choice ordering issue.
-/
def ReflMallowsBestInSetPrefixCutFirstChoiceWeighted
    (n : ℕ) (qMore qLess : ℝ) : Prop :=
  ∀ {remaining : Finset (Candidate (n + 1))}, remaining.Nonempty →
    ∀ cut : ℕ,
      0 ≤
        candidateRankPowerSum (n + 1) qLess *
            (∑ i : Candidate (n + 1),
              qMore ^ (i : ℕ) *
                firstChoiceBranchPayoffSum n qLess
                  (fun τ : Ranking (n + 1) =>
                    bestInSetPrefixCutIndicator remaining cut τ) i) -
          candidateRankPowerSum (n + 1) qMore *
            (∑ i : Candidate (n + 1),
              qLess ^ (i : ℕ) *
                firstChoiceBranchPayoffSum n qLess
                  (fun τ : Ranking (n + 1) =>
                    bestInSetPrefixCutIndicator remaining cut τ) i)

/--
Narrow same-size first-choice target after absent center extremes have been
removed by the prefix-cut deletion recurrences.  The remaining genuinely hard
case has both the center-best and center-worst candidates present and a
nontrivial cut between them.
-/
def ReflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes
    (n : ℕ) (qMore qLess : ℝ) : Prop :=
  ∀ {remaining : Finset (Candidate (n + 1))}, remaining.Nonempty →
    (0 : Candidate (n + 1)) ∈ remaining →
    reflLastCandidate (n + 1) ∈ remaining →
    ∀ {cut : ℕ}, 0 < cut → cut ≤ n + 2 →
      0 ≤
        candidateRankPowerSum (n + 1) qLess *
            (∑ i : Candidate (n + 1),
              qMore ^ (i : ℕ) *
                firstChoiceBranchPayoffSum n qLess
                  (fun τ : Ranking (n + 1) =>
                    bestInSetPrefixCutIndicator remaining cut τ) i) -
          candidateRankPowerSum (n + 1) qMore *
            (∑ i : Candidate (n + 1),
              qLess ^ (i : ℕ) *
                firstChoiceBranchPayoffSum n qLess
                  (fun τ : Ranking (n + 1) =>
                    bestInSetPrefixCutIndicator remaining cut τ) i)

/--
Reduced same-size first-choice target in the easy adjacent-boundary case.

This is the exact expression used by
`ReflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes`; it closes whenever
every mixed adjacent boundary is on the benign side of the prefix cut.  The
remaining hard case is therefore precisely aggregate cancellation of mixed
boundaries that violate one of these two orientation hypotheses.
-/
theorem reflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes_case_of_no_bad_mixed_adjacent
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ)
    (hleft_mixed :
      ∀ k : Fin (n + 2),
        k.castSucc ∈ remaining → k.succ ∉ remaining →
          ((k.castSucc : Candidate (n + 1)) : ℕ) < cut)
    (hright_mixed :
      ∀ k : Fin (n + 2),
        k.castSucc ∉ remaining → k.succ ∈ remaining →
          cut ≤ ((k.succ : Candidate (n + 1)) : ℕ)) :
    0 ≤
      candidateRankPowerSum (n + 1) qLess *
          (∑ i : Candidate (n + 1),
            qMore ^ (i : ℕ) *
              firstChoiceBranchPayoffSum n qLess
                (fun τ : Ranking (n + 1) =>
                  bestInSetPrefixCutIndicator remaining cut τ) i) -
        candidateRankPowerSum (n + 1) qMore *
          (∑ i : Candidate (n + 1),
            qLess ^ (i : ℕ) *
              firstChoiceBranchPayoffSum n qLess
                (fun τ : Ranking (n + 1) =>
                  bestInSetPrefixCutIndicator remaining cut τ) i) := by
  simpa [firstChoiceBranchWeighted] using
    firstChoiceBranchWeighted_prefixCut_nonneg_of_no_bad_mixed_adjacent
      n hqMore_pos hq_lt hremaining cut hleft_mixed hright_mixed

/--
Endpoint-present center-convex remaining sets satisfy the reduced
first-choice weighted target.  With both center extremes present, center
convexity forces the remaining set to be the full candidate set, so there are
no mixed adjacent boundaries.
-/
theorem reflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes_case_of_centerConvex
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hconv : CenterConvex remaining)
    (hzero : (0 : Candidate (n + 1)) ∈ remaining)
    (hlast : reflLastCandidate (n + 1) ∈ remaining)
    (cut : ℕ) :
    0 ≤
      candidateRankPowerSum (n + 1) qLess *
          (∑ i : Candidate (n + 1),
            qMore ^ (i : ℕ) *
              firstChoiceBranchPayoffSum n qLess
                (fun τ : Ranking (n + 1) =>
                  bestInSetPrefixCutIndicator remaining cut τ) i) -
        candidateRankPowerSum (n + 1) qMore *
          (∑ i : Candidate (n + 1),
            qLess ^ (i : ℕ) *
              firstChoiceBranchPayoffSum n qLess
                (fun τ : Ranking (n + 1) =>
                  bestInSetPrefixCutIndicator remaining cut τ) i) := by
  classical
  have hremaining_univ : remaining = Finset.univ :=
    centerConvex_eq_univ_of_zero_last_mem hconv hzero hlast
  subst remaining
  refine
    reflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes_case_of_no_bad_mixed_adjacent
      n hqMore_pos hq_lt (by exact ⟨0, Finset.mem_univ _⟩) cut ?_ ?_
  · intro k _ hright_not
    exact False.elim (hright_not (Finset.mem_univ _))
  · intro k hleft_not _
    exact False.elim (hleft_not (Finset.mem_univ _))

/--
Reduced same-size Mallows first-choice weighted theorem needed by the
arbitrary-remaining-set Theorem 4 proof.

This is intentionally narrower than the generic right-weak-Bruhat stochastic
monotonicity theorem: absent center extremes and trivial cuts are already
handled by verified deletion/zero recurrences, so the remaining library theorem
only covers the nontrivial same-size prefix-cut case with both center extremes
present.
-/
theorem reflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes_of_q_lt
    (n : ℕ) {qMore qLess : ℝ}
    (hqMore_pos : 0 < qMore) (hq_lt : qMore < qLess) :
    ReflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes n qMore qLess := by
  classical
  intro remaining hremaining _hzero _hlast cut _hcut_pos _hcut_le
  change
    0 ≤ firstChoiceBranchWeighted n qMore qLess qLess
      (fun τ : Ranking (n + 1) =>
        bestInSetPrefixCutIndicator remaining cut τ)
  exact
    firstChoiceBranchWeighted_nonneg_of_adjacentSwapImproves
      n hqMore_pos hq_lt
      (fun τ : Ranking (n + 1) =>
        bestInSetPrefixCutIndicator remaining cut τ)
      (bestInSetPrefixCutIndicator_eq_zero_or_one remaining cut)
      (adjacentSwapImproves_bestInSetPrefixCutIndicator hremaining cut)

/--
Adjacent-boundary form of the weighted first-choice target.  Outside/outside
adjacent gaps have already been erased, so this is the exact cancellation
statement left by the adjacent-gap decomposition.
-/
def ReflMallowsBestInSetPrefixCutFirstChoiceAdjacentBoundary
    (n : ℕ) (qMore qLess : ℝ) : Prop :=
  ∀ {remaining : Finset (Candidate (n + 1))}, remaining.Nonempty →
    ∀ cut : ℕ,
      0 ≤
        ∑ k : Fin (n + 2),
          if k.castSucc ∈ remaining ∨ k.succ ∈ remaining then
            firstChoiceBranchAdjacentGapCoeff n qMore qLess k *
              (firstChoiceBranchPayoffSum n qLess
                  (fun τ : Ranking (n + 1) =>
                    bestInSetPrefixCutIndicator remaining cut τ) k.castSucc -
                firstChoiceBranchPayoffSum n qLess
                  (fun τ : Ranking (n + 1) =>
                    bestInSetPrefixCutIndicator remaining cut τ) k.succ)
          else
            0

theorem ReflMallowsBestInSetPrefixCutFirstChoiceWeighted.of_adjacentBoundary
    {n : ℕ} {qMore qLess : ℝ}
    (hboundary :
      ReflMallowsBestInSetPrefixCutFirstChoiceAdjacentBoundary
        n qMore qLess) :
    ReflMallowsBestInSetPrefixCutFirstChoiceWeighted n qMore qLess := by
  classical
  intro remaining hremaining cut
  change
    0 ≤
      firstChoiceBranchWeighted n qMore qLess qLess
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ)
  rw [firstChoiceBranchWeighted_eq_adjacent_gap_sum_boundary
    n qMore qLess hremaining cut]
  exact hboundary hremaining cut

theorem ReflMallowsBestInSetPrefixCutFirstChoiceAdjacentBoundary.of_weighted
    {n : ℕ} {qMore qLess : ℝ}
    (hweighted :
      ReflMallowsBestInSetPrefixCutFirstChoiceWeighted n qMore qLess) :
    ReflMallowsBestInSetPrefixCutFirstChoiceAdjacentBoundary
      n qMore qLess := by
  classical
  intro remaining hremaining cut
  have h :
      0 ≤ firstChoiceBranchWeighted n qMore qLess qLess
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining cut τ) :=
    hweighted hremaining cut
  rw [firstChoiceBranchWeighted_eq_adjacent_gap_sum_boundary
    n qMore qLess hremaining cut] at h
  exact h

theorem ReflMallowsBestInSetPrefixCutFirstChoiceBracketSum.of_dominance_weighted
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    (hprev : ReflMallowsBestInSetPrefixCutDominance n qMore qLess)
    (hweighted :
      ReflMallowsBestInSetPrefixCutFirstChoiceWeighted n qMore qLess) :
    ReflMallowsBestInSetPrefixCutFirstChoiceBracketSum n qMore qLess := by
  classical
  intro remaining hremaining cut
  refine
    firstChoiceBranchBracketSum_nonneg_of_diag_weighted
      n hqMore_pos (le_of_lt (lt_trans hqMore_pos hq_lt))
      (fun τ : Ranking (n + 1) =>
        bestInSetPrefixCutIndicator remaining cut τ) ?hdiag ?hweighted
  · exact
      firstChoiceBranchPayoffSum_prefixCut_diag_nonneg_of_tail
        n hremaining cut
        (by
          intro r hr
          exact hprev
            (firstChoiceTailRemainingOf_nonempty_of_nonempty_of_first_not_mem
              hremaining hr)
            (deleteFirstChoicePrefixCut r cut))
  · exact hweighted hremaining cut

/--
Induction step for arbitrary prefix-cut dominance.

The diagonal branch terms are discharged by the previous-size prefix dominance
target on every nonempty first-choice tail.  The only new same-size obligation
is the aggregate first-choice bracket sum.
-/
theorem ReflMallowsBestInSetPrefixCutDominance.succ
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    (hprev : ReflMallowsBestInSetPrefixCutDominance n qMore qLess)
    (hbracket :
      ReflMallowsBestInSetPrefixCutFirstChoiceBracketSum n qMore qLess) :
    ReflMallowsBestInSetPrefixCutDominance (n + 1) qMore qLess := by
  intro remaining hremaining cut
  exact
    reflMallowsBestInSetPrefixCutSum_cross_of_firstChoice_tail_pair_bracket_sum
      n hqMore_pos hq_lt hremaining cut
      (by
        intro r hr
        exact hprev
          (firstChoiceTailRemainingOf_nonempty_of_nonempty_of_first_not_mem
            hremaining hr)
          (deleteFirstChoicePrefixCut r cut))
      (hbracket hremaining cut)

/--
Conditional first-choice cross step for before-insert masses.

This is an algebraic bridge only: the branch-position premise is not true for
all before-insert events, so the arbitrary remaining-set proof should use the
aggregate insertion-position route below instead of trying to discharge this
premise branch by branch.
-/
theorem reflMallowsBestInSetPrefixCutBeforeInsertSum_cross_of_firstChoice_branches
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ)
    (p : Candidate (n + 2))
    (htail :
      ∀ (hp : p ≠ 0) (r : Candidate (n + 1)), r ∉ remaining →
        0 ≤
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixCutBeforeInsertSum n qMore
                (firstChoiceTailRemainingOf r remaining)
                (deleteFirstChoicePrefixCut r cut) (p.pred hp) -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixCutBeforeInsertSum n qLess
                (firstChoiceTailRemainingOf r remaining)
                (deleteFirstChoicePrefixCut r cut) (p.pred hp))
    (hpos :
      ∀ a b : Candidate (n + 1), a < b →
        reflMallowsPayoffSum n qLess
          (fun σ : Ranking n =>
            bestInSetPrefixCutBeforeInsertIndicator remaining cut p
              (rankingFirstChoiceOrderEquiv n (b, σ))) ≤
          reflMallowsPayoffSum n qLess
            (fun σ : Ranking n =>
              bestInSetPrefixCutBeforeInsertIndicator remaining cut p
                (rankingFirstChoiceOrderEquiv n (a, σ)))) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutBeforeInsertSum
            (n + 1) qMore remaining cut p -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutBeforeInsertSum
            (n + 1) qLess remaining cut p := by
  classical
  let F : Ranking (n + 1) → ℝ := fun τ =>
    bestInSetPrefixCutBeforeInsertIndicator remaining cut p τ
  unfold reflMallowsBestInSetPrefixCutBeforeInsertSum
  refine
    reflMallowsPayoffSum_cross_of_firstChoice_step
      n hqMore_pos hq_lt F ?htail ?hpos
  · intro r
    by_cases hp : p = 0
    · have hbranch :
          ∀ q : ℝ,
            reflMallowsPayoffSum n q
                (fun σ : Ranking n =>
                  F (rankingFirstChoiceOrderEquiv n (r, σ))) =
              mallowsPartition q (Equiv.refl (Candidate n)) := by
        intro q
        calc
          reflMallowsPayoffSum n q
              (fun σ : Ranking n =>
                F (rankingFirstChoiceOrderEquiv n (r, σ))) =
            reflMallowsPayoffSum n q (fun _ : Ranking n => (1 : ℝ)) := by
              unfold reflMallowsPayoffSum
              refine Finset.sum_congr rfl ?_
              intro σ _
              change
                q ^ kendallTau (Equiv.refl (Candidate n)) σ *
                    F (rankingFirstChoiceOrderEquiv n (r, σ)) =
                  q ^ kendallTau (Equiv.refl (Candidate n)) σ * (1 : ℝ)
              dsimp [F]
              rw [bestInSetPrefixCutBeforeInsertIndicator_rankingFirstChoiceOrderEquiv
                hremaining cut p r σ]
              simp [hp]
          _ = mallowsPartition q (Equiv.refl (Candidate n)) := by
              rw [reflMallowsPayoffSum_const]
              ring
      rw [hbranch qMore, hbranch qLess]
      ring_nf
      exact le_rfl
    · by_cases hr : r ∈ remaining
      · have hbranch :
            ∀ q : ℝ,
              reflMallowsPayoffSum n q
                  (fun σ : Ranking n =>
                    F (rankingFirstChoiceOrderEquiv n (r, σ))) =
                mallowsPartition q (Equiv.refl (Candidate n)) *
                  (if (r : ℕ) < cut then (1 : ℝ) else 0) := by
          intro q
          calc
            reflMallowsPayoffSum n q
                (fun σ : Ranking n =>
                  F (rankingFirstChoiceOrderEquiv n (r, σ))) =
              reflMallowsPayoffSum n q
                (fun _ : Ranking n =>
                  if (r : ℕ) < cut then (1 : ℝ) else 0) := by
                unfold reflMallowsPayoffSum
                refine Finset.sum_congr rfl ?_
                intro σ _
                change
                  q ^ kendallTau (Equiv.refl (Candidate n)) σ *
                      F (rankingFirstChoiceOrderEquiv n (r, σ)) =
                    q ^ kendallTau (Equiv.refl (Candidate n)) σ *
                      (if (r : ℕ) < cut then (1 : ℝ) else 0)
                dsimp [F]
                rw [bestInSetPrefixCutBeforeInsertIndicator_rankingFirstChoiceOrderEquiv
                  hremaining cut p r σ]
                simp [hp, hr]
            _ =
                mallowsPartition q (Equiv.refl (Candidate n)) *
                  (if (r : ℕ) < cut then (1 : ℝ) else 0) := by
                rw [reflMallowsPayoffSum_const]
        rw [hbranch qMore, hbranch qLess]
        ring_nf
        exact le_rfl
      · have hbranch :
            ∀ q : ℝ,
              reflMallowsPayoffSum n q
                  (fun σ : Ranking n =>
                    F (rankingFirstChoiceOrderEquiv n (r, σ))) =
                reflMallowsBestInSetPrefixCutBeforeInsertSum n q
                  (firstChoiceTailRemainingOf r remaining)
                  (deleteFirstChoicePrefixCut r cut) (p.pred hp) := by
          intro q
          unfold reflMallowsBestInSetPrefixCutBeforeInsertSum
          unfold reflMallowsPayoffSum
          refine Finset.sum_congr rfl ?_
          intro σ _
          change
            q ^ kendallTau (Equiv.refl (Candidate n)) σ *
                F (rankingFirstChoiceOrderEquiv n (r, σ)) =
              q ^ kendallTau (Equiv.refl (Candidate n)) σ *
                bestInSetPrefixCutBeforeInsertIndicator
                  (firstChoiceTailRemainingOf r remaining)
                  (deleteFirstChoicePrefixCut r cut) (p.pred hp) σ
          dsimp [F]
          rw [bestInSetPrefixCutBeforeInsertIndicator_rankingFirstChoiceOrderEquiv
            hremaining cut p r σ]
          simp [hp, hr]
        rw [hbranch qMore, hbranch qLess]
        exact htail hp r hr
  · intro a b hab
    exact hpos a b hab

/-- The unique two-candidate ranking with prescribed first choice. -/
noncomputable def rankingZeroOfFirstChoice (c : Candidate 0) : Ranking 0 :=
  if c = 0 then
    Equiv.refl (Candidate 0)
  else
    Equiv.swap (0 : Candidate 0) 1

@[simp] theorem firstChoice_rankingZeroOfFirstChoice (c : Candidate 0) :
    firstChoice (rankingZeroOfFirstChoice c) = c := by
  classical
  unfold rankingZeroOfFirstChoice firstChoice
  by_cases hc : c = 0
  · simp [hc]
  · have hc1 : c = 1 := Fin.eq_one_of_ne_zero c hc
    simp [hc1]

theorem ranking_zero_eq_of_firstChoice {π σ : Ranking 0}
    (h : firstChoice π = firstChoice σ) : π = σ := by
  classical
  apply Equiv.ext
  intro x
  fin_cases x
  · simpa [firstChoice] using h
  · have hπ_ne_first : π 1 ≠ firstChoice π := by
      intro hπ
      have hidx : (1 : Candidate 0) = 0 :=
        π.injective (by simpa [firstChoice] using hπ)
      norm_num at hidx
    have hσ_ne_first : σ 1 ≠ firstChoice σ := by
      intro hσ
      have hidx : (1 : Candidate 0) = 0 :=
        σ.injective (by simpa [firstChoice] using hσ)
      norm_num at hidx
    by_cases hπ0 : firstChoice π = (0 : Candidate 0)
    · have hσ0 : firstChoice σ = (0 : Candidate 0) :=
        h.symm.trans hπ0
      have hπ1 : π 1 = (1 : Candidate 0) := by
        apply Fin.eq_one_of_ne_zero
        intro hzero
        exact hπ_ne_first (by rw [hzero, hπ0])
      have hσ1 : σ 1 = (1 : Candidate 0) := by
        apply Fin.eq_one_of_ne_zero
        intro hzero
        exact hσ_ne_first (by rw [hzero, hσ0])
      simpa using hπ1.trans hσ1.symm
    · have hπfirst1 : firstChoice π = (1 : Candidate 0) :=
        Fin.eq_one_of_ne_zero _ hπ0
      have hσfirst1 : firstChoice σ = (1 : Candidate 0) :=
        h.symm.trans hπfirst1
      have hπ1 : π 1 = (0 : Candidate 0) := by
        by_contra hzero
        have hone : π 1 = (1 : Candidate 0) :=
          Fin.eq_one_of_ne_zero _ hzero
        exact hπ_ne_first (by rw [hone, hπfirst1])
      have hσ1 : σ 1 = (0 : Candidate 0) := by
        by_contra hzero
        have hone : σ 1 = (1 : Candidate 0) :=
          Fin.eq_one_of_ne_zero _ hzero
        exact hσ_ne_first (by rw [hone, hσfirst1])
      simpa using hπ1.trans hσ1.symm

/-- Two-candidate rankings are equivalent to their first choice. -/
noncomputable def rankingZeroFirstChoiceEquiv : Ranking 0 ≃ Candidate 0 where
  toFun π := firstChoice π
  invFun c := rankingZeroOfFirstChoice c
  left_inv π := by
    apply ranking_zero_eq_of_firstChoice
    simpa [firstChoice] using
      firstChoice_rankingZeroOfFirstChoice (firstChoice π)
  right_inv c :=
    firstChoice_rankingZeroOfFirstChoice c

@[simp] theorem rankingZeroFirstChoiceEquiv_symm_apply (c : Candidate 0) :
    rankingZeroFirstChoiceEquiv.symm c = rankingZeroOfFirstChoice c := rfl

theorem kendallTau_refl_rankingZeroOfFirstChoice (c : Candidate 0) :
    kendallTau (Equiv.refl (Candidate 0)) (rankingZeroOfFirstChoice c) =
      (c : ℕ) := by
  classical
  unfold rankingZeroOfFirstChoice
  by_cases hc : c = 0
  · simp [hc, kendallTau]
  · have hc1 : c = 1 := Fin.eq_one_of_ne_zero c hc
    subst c
    change
      (inversionFinset (Equiv.refl (Candidate 0))
        (Equiv.swap (0 : Candidate 0) 1)).card = 1
    have hset :
        inversionFinset (Equiv.refl (Candidate 0))
          (Equiv.swap (0 : Candidate 0) 1) =
          {((0 : Candidate 0), (1 : Candidate 0))} := by
      ext ab
      rcases ab with ⟨a, b⟩
      fin_cases a <;> fin_cases b <;>
        norm_num [inversionFinset, invertedPair, rankOf]
    rw [hset]
    simp

theorem reflMallowsPayoffSum_zero_eq_candidateRankSum
    (q : ℝ) (F : Ranking 0 → ℝ) :
    reflMallowsPayoffSum 0 q F =
      ∑ c : Candidate 0, q ^ (c : ℕ) * F (rankingZeroOfFirstChoice c) := by
  classical
  unfold reflMallowsPayoffSum
  calc
    (∑ π : Ranking 0,
        q ^ kendallTau (Equiv.refl (Candidate 0)) π * F π)
        =
      ∑ c : Candidate 0,
        q ^ kendallTau (Equiv.refl (Candidate 0))
              (rankingZeroFirstChoiceEquiv.symm c) *
          F (rankingZeroFirstChoiceEquiv.symm c) := by
        simpa using
          (Equiv.sum_comp rankingZeroFirstChoiceEquiv.symm
            (fun π : Ranking 0 =>
              q ^ kendallTau (Equiv.refl (Candidate 0)) π * F π)).symm
    _ =
      ∑ c : Candidate 0, q ^ (c : ℕ) * F (rankingZeroOfFirstChoice c) := by
        refine Finset.sum_congr rfl ?_
        intro c _
        rw [rankingZeroFirstChoiceEquiv_symm_apply,
          kendallTau_refl_rankingZeroOfFirstChoice]

theorem mallowsPartition_refl_zero_eq_candidateRankPowerSum
    (q : ℝ) :
    mallowsPartition q (Equiv.refl (Candidate 0)) =
      candidateRankPowerSum 0 q := by
  classical
  have h :=
    reflMallowsPayoffSum_zero_eq_candidateRankSum q
      (fun _ : Ranking 0 => (1 : ℝ))
  unfold reflMallowsPayoffSum at h
  unfold mallowsPartition mallowsWeight candidateRankPowerSum
  simpa using h

theorem firstChoiceWeighted_three_Z01_nonneg
    {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) :
    0 ≤
      candidateRankPowerSum 1 qLess *
          (mallowsPartition qLess (Equiv.refl (Candidate 0)) +
            qMore ^ (2 : ℕ)) -
        candidateRankPowerSum 1 qMore *
          (mallowsPartition qLess (Equiv.refl (Candidate 0)) +
            qLess ^ (2 : ℕ)) := by
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hdiff : 0 ≤ qLess - qMore := sub_nonneg.mpr (le_of_lt hq_lt)
  have hPLess_nonneg : 0 ≤ candidateRankPowerSum 1 qLess :=
    le_of_lt (candidateRankPowerSum_pos 1 hqLess_pos)
  rw [mallowsPartition_refl_zero_eq_candidateRankPowerSum]
  have hrewrite :
      candidateRankPowerSum 1 qLess *
          (candidateRankPowerSum 0 qLess + qMore ^ (2 : ℕ)) -
        candidateRankPowerSum 1 qMore *
          (candidateRankPowerSum 0 qLess + qLess ^ (2 : ℕ)) =
        (qLess - qMore) * candidateRankPowerSum 1 qLess := by
    unfold candidateRankPowerSum
    rw [Fin.sum_univ_three, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num
    ring
  rw [hrewrite]
  exact mul_nonneg hdiff hPLess_nonneg

theorem firstChoiceWeighted_three_Z10_nonneg
    {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) :
    0 ≤
      candidateRankPowerSum 1 qLess *
          (mallowsPartition qLess (Equiv.refl (Candidate 0)) + qMore) -
        candidateRankPowerSum 1 qMore *
          (mallowsPartition qLess (Equiv.refl (Candidate 0)) + qLess) := by
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hdiff : 0 ≤ qLess - qMore := sub_nonneg.mpr (le_of_lt hq_lt)
  have hqMore_nonneg : 0 ≤ qMore := le_of_lt hqMore_pos
  have hqLess_nonneg : 0 ≤ qLess := le_of_lt hqLess_pos
  rw [mallowsPartition_refl_zero_eq_candidateRankPowerSum]
  have hrewrite :
      candidateRankPowerSum 1 qLess *
          (candidateRankPowerSum 0 qLess + qMore) -
        candidateRankPowerSum 1 qMore *
          (candidateRankPowerSum 0 qLess + qLess) =
        (qLess - qMore) *
          (2 * qMore * qLess + qMore + qLess ^ (2 : ℕ) +
            2 * qLess) := by
    unfold candidateRankPowerSum
    rw [Fin.sum_univ_three, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num
    ring
  have hcoef :
      0 ≤ 2 * qMore * qLess + qMore + qLess ^ (2 : ℕ) + 2 * qLess := by
    nlinarith [mul_nonneg hqMore_nonneg hqLess_nonneg,
      sq_nonneg qLess]
  rw [hrewrite]
  exact mul_nonneg hdiff hcoef

theorem firstChoiceWeighted_three_1Z0_nonneg
    {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) :
    0 ≤
      candidateRankPowerSum 1 qLess *
          (1 + qMore *
            mallowsPartition qLess (Equiv.refl (Candidate 0))) -
        candidateRankPowerSum 1 qMore *
          (1 + qLess *
            mallowsPartition qLess (Equiv.refl (Candidate 0))) := by
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hdiff : 0 ≤ qLess - qMore := sub_nonneg.mpr (le_of_lt hq_lt)
  have hqMore_nonneg : 0 ≤ qMore := le_of_lt hqMore_pos
  have hPLess_nonneg : 0 ≤ candidateRankPowerSum 1 qLess :=
    le_of_lt (candidateRankPowerSum_pos 1 hqLess_pos)
  rw [mallowsPartition_refl_zero_eq_candidateRankPowerSum]
  have hrewrite :
      candidateRankPowerSum 1 qLess *
          (1 + qMore * candidateRankPowerSum 0 qLess) -
        candidateRankPowerSum 1 qMore *
          (1 + qLess * candidateRankPowerSum 0 qLess) =
        qMore * (qLess - qMore) * candidateRankPowerSum 1 qLess := by
    unfold candidateRankPowerSum
    rw [Fin.sum_univ_three, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num
    ring
  rw [hrewrite]
  exact mul_nonneg (mul_nonneg hqMore_nonneg hdiff) hPLess_nonneg

/-- Base case for Mallows payoff dominance under inversion-improving payoffs. -/
theorem reflMallowsPayoffSum_cross_of_swapImprovesOn_univ_zero
    {qMore qLess : ℝ} (hqMore_pos : 0 < qMore) (hq_lt : qMore < qLess)
    (F : Ranking 0 → ℝ)
    (hF : SwapImprovesOn Finset.univ (Equiv.refl (Candidate 0)) F) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate 0)) *
          reflMallowsPayoffSum 0 qMore F -
        mallowsPartition qMore (Equiv.refl (Candidate 0)) *
          reflMallowsPayoffSum 0 qLess F := by
  classical
  let B : Candidate 0 → ℝ := fun c => F (rankingZeroOfFirstChoice c)
  have h01 : B 1 ≤ B 0 := by
    have hcenter :
        rankOf (Equiv.refl (Candidate 0)) (0 : Candidate 0) <
          rankOf (Equiv.refl (Candidate 0)) (1 : Candidate 0) := by
      norm_num [rankOf]
    have hpos :
        rankOf (rankingZeroOfFirstChoice 1) (1 : Candidate 0) <
          rankOf (rankingZeroOfFirstChoice 1) (0 : Candidate 0) := by
      norm_num [rankingZeroOfFirstChoice, rankOf]
    have hstep :=
      hF (rankingZeroOfFirstChoice 1)
        (0 : Candidate 0) (1 : Candidate 0)
        (Finset.mem_univ _) (Finset.mem_univ _) hcenter hpos
    have hswap :
        swapCandidatePositions (rankingZeroOfFirstChoice 1)
            (0 : Candidate 0) (1 : Candidate 0) =
          rankingZeroOfFirstChoice 0 := by
      ext x
      fin_cases x <;>
        norm_num [rankingZeroOfFirstChoice, swapCandidatePositions, rankOf]
    rw [hswap] at hstep
    simpa [B] using hstep
  have hB : ∀ i j : Candidate 0, i < j → B j ≤ B i := by
    intro i j hij
    have hi_val : i.val = 0 := by
      have hij_val : i.val < j.val := hij
      have hj_lt : j.val < 2 := j.isLt
      omega
    have hj_val : j.val = 1 := by
      have hij_val : i.val < j.val := hij
      have hi_lt : i.val < 2 := i.isLt
      have hj_lt : j.val < 2 := j.isLt
      omega
    have hi_eq : i = (0 : Candidate 0) := Fin.ext hi_val
    have hj_eq : j = (1 : Candidate 0) := Fin.ext hj_val
    subst i
    subst j
    exact h01
  have h :=
    candidateRankWeightedAverage_anti
      0 hqMore_pos hq_lt (B := B) hB
  rw [mallowsPartition_refl_zero_eq_candidateRankPowerSum,
    mallowsPartition_refl_zero_eq_candidateRankPowerSum,
    reflMallowsPayoffSum_zero_eq_candidateRankSum,
    reflMallowsPayoffSum_zero_eq_candidateRankSum]
  simpa [B] using h

/-- Base case for adjacent-swap Mallows stochastic dominance. -/
theorem reflMallowsAdjacentStochasticDominance_zero
    {qMore qLess : ℝ} (hqMore_pos : 0 < qMore) (hq_lt : qMore < qLess) :
    ReflMallowsAdjacentStochasticDominance 0 qMore qLess := by
  classical
  intro F hF
  let B : Candidate 0 → ℝ := fun c => F (rankingZeroOfFirstChoice c)
  have h01 : B 1 ≤ B 0 := by
    let k : Fin 1 := 0
    have hcenter :
        rankOf (Equiv.refl (Candidate 0))
            (rankingZeroOfFirstChoice 1 k.succ) <
          rankOf (Equiv.refl (Candidate 0))
            (rankingZeroOfFirstChoice 1 k.castSucc) := by
      norm_num [k, rankingZeroOfFirstChoice, rankOf]
    have hstep := hF (rankingZeroOfFirstChoice 1) k hcenter
    have hswap :
        swapCandidatePositions (rankingZeroOfFirstChoice 1)
            (rankingZeroOfFirstChoice 1 k.succ)
            (rankingZeroOfFirstChoice 1 k.castSucc) =
          rankingZeroOfFirstChoice 0 := by
      ext x
      fin_cases x <;>
        norm_num [k, rankingZeroOfFirstChoice, swapCandidatePositions, rankOf]
    rw [hswap] at hstep
    simpa [B] using hstep
  have hB : ∀ i j : Candidate 0, i < j → B j ≤ B i := by
    intro i j hij
    have hi_val : i.val = 0 := by
      have hij_val : i.val < j.val := hij
      have hj_lt : j.val < 2 := j.isLt
      omega
    have hj_val : j.val = 1 := by
      have hij_val : i.val < j.val := hij
      have hi_lt : i.val < 2 := i.isLt
      have hj_lt : j.val < 2 := j.isLt
      omega
    have hi_eq : i = (0 : Candidate 0) := Fin.ext hi_val
    have hj_eq : j = (1 : Candidate 0) := Fin.ext hj_val
    subst i
    subst j
    exact h01
  have h :=
    candidateRankWeightedAverage_anti
      0 hqMore_pos hq_lt (B := B) hB
  rw [mallowsPartition_refl_zero_eq_candidateRankPowerSum,
    mallowsPartition_refl_zero_eq_candidateRankPowerSum,
    reflMallowsPayoffSum_zero_eq_candidateRankSum,
    reflMallowsPayoffSum_zero_eq_candidateRankSum]
  simpa [B] using h

/-- Base case for prefix-cut dominance. -/
theorem ReflMallowsBestInSetPrefixCutDominance.zero
    {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) :
    ReflMallowsBestInSetPrefixCutDominance 0 qMore qLess := by
  intro remaining hremaining cut
  exact
    reflMallowsBestInSetPrefixCutSum_cross_of_adjacentStochasticDominance
      (reflMallowsAdjacentStochasticDominance_zero hqMore_pos hq_lt)
      hremaining cut

/--
Aggregate first-choice bracket sums at every recursive size imply arbitrary
prefix-cut dominance at the requested size.
-/
theorem ReflMallowsBestInSetPrefixCutDominance.of_firstChoiceBracketSums
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    (hbracket :
      ∀ m : ℕ,
        ReflMallowsBestInSetPrefixCutFirstChoiceBracketSum
          m qMore qLess) :
    ReflMallowsBestInSetPrefixCutDominance n qMore qLess := by
  induction n with
  | zero =>
      exact ReflMallowsBestInSetPrefixCutDominance.zero
        hqMore_pos hq_lt
  | succ n ih =>
      exact ReflMallowsBestInSetPrefixCutDominance.succ
        hqMore_pos hq_lt ih (hbracket n)

/--
Weighted first-choice targets at every recursive size imply arbitrary
prefix-cut dominance.

This packages the newest decomposition: smaller prefix-cut dominance supplies
the diagonal part of the aggregate bracket, while the weighted first-choice
target supplies the remaining off-diagonal mass.
-/
theorem ReflMallowsBestInSetPrefixCutDominance.of_firstChoiceWeighted
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    (hweighted :
      ∀ m : ℕ,
        ReflMallowsBestInSetPrefixCutFirstChoiceWeighted
          m qMore qLess) :
    ReflMallowsBestInSetPrefixCutDominance n qMore qLess := by
  induction n with
  | zero =>
      exact ReflMallowsBestInSetPrefixCutDominance.zero
        hqMore_pos hq_lt
  | succ n ih =>
      exact ReflMallowsBestInSetPrefixCutDominance.succ
        hqMore_pos hq_lt ih
        (ReflMallowsBestInSetPrefixCutFirstChoiceBracketSum.of_dominance_weighted
          hqMore_pos hq_lt ih (hweighted n))

theorem reflMallowsBestInSetPrefixSum_cross_of_firstChoiceBracketSums
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    (hbracket :
      ∀ m : ℕ,
        ReflMallowsBestInSetPrefixCutFirstChoiceBracketSum
          m qMore qLess)
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty)
    (k : Fin (n + 1)) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixSum n qMore remaining k -
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixSum n qLess remaining k := by
  rw [reflMallowsBestInSetPrefixSum_eq_cut,
    reflMallowsBestInSetPrefixSum_eq_cut]
  exact
    ReflMallowsBestInSetPrefixCutDominance.of_firstChoiceBracketSums
      n hqMore_pos hq_lt hbracket hremaining (k.val + 1)

theorem reflMallowsBestInSetPrefixSum_cross_of_firstChoiceWeighted
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    (hweighted :
      ∀ m : ℕ,
        ReflMallowsBestInSetPrefixCutFirstChoiceWeighted
          m qMore qLess)
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty)
    (k : Fin (n + 1)) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixSum n qMore remaining k -
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixSum n qLess remaining k := by
  rw [reflMallowsBestInSetPrefixSum_eq_cut,
    reflMallowsBestInSetPrefixSum_eq_cut]
  exact
    ReflMallowsBestInSetPrefixCutDominance.of_firstChoiceWeighted
      n hqMore_pos hq_lt hweighted hremaining (k.val + 1)

/-- Multiplicity of each Kendall-rank layer for the three-candidate weak order. -/
noncomputable def rankLayerCountThree (r : Candidate 2) : ℝ := if r = (0 : Candidate 2) ∨ r = (3 : Candidate 2) then 1 else 2

theorem rankLayerCountThree_nonneg (r : Candidate 2) :
    0 ≤ rankLayerCountThree r := by
  unfold rankLayerCountThree
  by_cases h : r = (0 : Candidate 2) ∨ r = (3 : Candidate 2)
  · simp [h]
  · simp [h]

theorem rankLayerCountThree_pos (r : Candidate 2) :
    0 < rankLayerCountThree r := by
  unfold rankLayerCountThree
  by_cases h : r = (0 : Candidate 2) ∨ r = (3 : Candidate 2)
  · simp [h]
  · simp [h]

theorem rankLayerCountThree_weightedSum_eq
    (q : ℝ) (B : Candidate 2 → ℝ) :
    (∑ r : Candidate 2, rankLayerCountThree r * q ^ (r : ℕ) * B r) =
      B 0 + q * (2 * B 1) + q ^ 2 * (2 * B 2) + q ^ 3 * B 3 := by
  rw [Fin.sum_univ_four]
  simp [rankLayerCountThree]
  ring

theorem rankLayerCountThree_sum_eq (q : ℝ) :
    (∑ r : Candidate 2, rankLayerCountThree r * q ^ (r : ℕ)) =
      1 + 2 * q + 2 * q ^ 2 + q ^ 3 := by
  have h := rankLayerCountThree_weightedSum_eq q
    (fun _ : Candidate 2 => (1 : ℝ))
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

theorem rankLayerCountThree_weight_cross_nonneg
    {qMore qLess : ℝ} (hqMore_pos : 0 < qMore) (hq_lt : qMore < qLess)
    {i j : Candidate 2} (hij : i < j) :
    0 ≤
      (rankLayerCountThree i * qMore ^ (i : ℕ)) *
          (rankLayerCountThree j * qLess ^ (j : ℕ)) -
        (rankLayerCountThree j * qMore ^ (j : ℕ)) *
          (rankLayerCountThree i * qLess ^ (i : ℕ)) := by
  have hcount_nonneg :
      0 ≤ rankLayerCountThree i * rankLayerCountThree j :=
    mul_nonneg (rankLayerCountThree_nonneg i) (rankLayerCountThree_nonneg j)
  have hpow :
      0 ≤ qMore ^ (i : ℕ) * qLess ^ (j : ℕ) -
        qMore ^ (j : ℕ) * qLess ^ (i : ℕ) :=
    le_of_lt (sub_pos.mpr (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        rankPower_mul_lt_mul_rankPower hqMore_pos hq_lt hij))
  have heq :
      (rankLayerCountThree i * qMore ^ (i : ℕ)) *
          (rankLayerCountThree j * qLess ^ (j : ℕ)) -
        (rankLayerCountThree j * qMore ^ (j : ℕ)) *
          (rankLayerCountThree i * qLess ^ (i : ℕ)) =
        (rankLayerCountThree i * rankLayerCountThree j) *
          (qMore ^ (i : ℕ) * qLess ^ (j : ℕ) -
            qMore ^ (j : ℕ) * qLess ^ (i : ℕ)) := by
    ring
  rw [heq]
  exact mul_nonneg hcount_nonneg hpow

theorem rankLayerCountThree_weightedAverage_anti
    {qMore qLess : ℝ} (hqMore_pos : 0 < qMore) (hq_lt : qMore < qLess)
    {B : Candidate 2 → ℝ}
    (hB : ∀ i j : Candidate 2, i < j → B j ≤ B i) :
    0 ≤
      (∑ j : Candidate 2, rankLayerCountThree j * qLess ^ (j : ℕ)) *
          (∑ i : Candidate 2,
            (rankLayerCountThree i * qMore ^ (i : ℕ)) * B i) -
        (∑ j : Candidate 2, rankLayerCountThree j * qMore ^ (j : ℕ)) *
          (∑ i : Candidate 2,
            (rankLayerCountThree i * qLess ^ (i : ℕ)) * B i) :=
   candidateWeightedAverage_cross_nonneg_of_pairwise
    2
    (wA := fun i : Candidate 2 => rankLayerCountThree i * qMore ^ (i : ℕ))
    (wH := fun i : Candidate 2 => rankLayerCountThree i * qLess ^ (i : ℕ))
    (B := B)
    (by
      intro i j hij
      exact rankLayerCountThree_weight_cross_nonneg hqMore_pos hq_lt hij)
    hB

/--
The three-candidate ranking with prescribed first choice and prescribed
two-candidate tail order.
-/
noncomputable def rankingOneOfFirstTail
    (r : Candidate 1) (t : Candidate 0) : Ranking 1 := rankingFirstChoiceOrderEquiv 0 (r, rankingZeroOfFirstChoice t)

@[simp] theorem firstChoice_rankingOneOfFirstTail
    (r : Candidate 1) (t : Candidate 0) :
    firstChoice (rankingOneOfFirstTail r t) = r := by
  simpa [rankingOneOfFirstTail] using
    firstChoice_rankingFirstChoiceOrderEquiv 0 r (rankingZeroOfFirstChoice t)

@[simp] theorem rankingOneOfFirstTail_apply_zero
    (r : Candidate 1) (t : Candidate 0) :
    rankingOneOfFirstTail r t 0 = r := by
  simpa [firstChoice] using firstChoice_rankingOneOfFirstTail r t

@[simp] theorem rankOf_rankingOneOfFirstTail_first
    (r : Candidate 1) (t : Candidate 0) :
    rankOf (rankingOneOfFirstTail r t) r = 0 := by
  simpa [rankingOneOfFirstTail] using
    rankOf_rankingFirstChoiceOrderEquiv_first 0 r (rankingZeroOfFirstChoice t)

theorem rankOf_rankingOneOfFirstTail_succAbove
    (r : Candidate 1) (t c : Candidate 0) :
    rankOf (rankingOneOfFirstTail r t) (r.succAbove c) =
      (rankOf (rankingZeroOfFirstChoice t) c).succ := by
  simpa [rankingOneOfFirstTail] using
    rankOf_rankingFirstChoiceOrderEquiv_succAbove
      0 r (rankingZeroOfFirstChoice t) c

theorem rankingOneOfFirstTail_apply_tail
    (r : Candidate 1) (t c : Candidate 0) :
    rankingOneOfFirstTail r t
        ((rankOf (rankingZeroOfFirstChoice t) c).succ) =
      r.succAbove c :=  apply_eq_of_rankOf _ (rankOf_rankingOneOfFirstTail_succAbove r t c)

@[simp] theorem rankOf_rankingOneOfFirstTail_00_one :
    rankOf (rankingOneOfFirstTail 0 0) (1 : Candidate 1) = 1 := by
  change
    rankOf (rankingOneOfFirstTail 0 0)
        ((0 : Candidate 1).succAbove (0 : Candidate 0)) = 1
  rw [rankOf_rankingOneOfFirstTail_succAbove]
  simp [rankingZeroOfFirstChoice, rankOf]

@[simp] theorem rankOf_rankingOneOfFirstTail_00_two :
    rankOf (rankingOneOfFirstTail 0 0) (2 : Candidate 1) = 2 := by
  change
    rankOf (rankingOneOfFirstTail 0 0)
        ((0 : Candidate 1).succAbove (1 : Candidate 0)) = 2
  rw [rankOf_rankingOneOfFirstTail_succAbove]
  simp [rankingZeroOfFirstChoice, rankOf]

@[simp] theorem rankOf_rankingOneOfFirstTail_01_one :
    rankOf (rankingOneOfFirstTail 0 1) (1 : Candidate 1) = 2 := by
  change
    rankOf (rankingOneOfFirstTail 0 1)
        ((0 : Candidate 1).succAbove (0 : Candidate 0)) = 2
  rw [rankOf_rankingOneOfFirstTail_succAbove]
  simp [rankingZeroOfFirstChoice, rankOf]

@[simp] theorem rankOf_rankingOneOfFirstTail_01_two :
    rankOf (rankingOneOfFirstTail 0 1) (2 : Candidate 1) = 1 := by
  change
    rankOf (rankingOneOfFirstTail 0 1)
        ((0 : Candidate 1).succAbove (1 : Candidate 0)) = 1
  rw [rankOf_rankingOneOfFirstTail_succAbove]
  simp [rankingZeroOfFirstChoice, rankOf]

@[simp] theorem rankOf_rankingOneOfFirstTail_10_zero :
    rankOf (rankingOneOfFirstTail 1 0) (0 : Candidate 1) = 1 := by
  change
    rankOf (rankingOneOfFirstTail 1 0)
        ((1 : Candidate 1).succAbove (0 : Candidate 0)) = 1
  rw [rankOf_rankingOneOfFirstTail_succAbove]
  simp [rankingZeroOfFirstChoice, rankOf]

@[simp] theorem rankOf_rankingOneOfFirstTail_10_two :
    rankOf (rankingOneOfFirstTail 1 0) (2 : Candidate 1) = 2 := by
  change
    rankOf (rankingOneOfFirstTail 1 0)
        ((1 : Candidate 1).succAbove (1 : Candidate 0)) = 2
  rw [rankOf_rankingOneOfFirstTail_succAbove]
  simp [rankingZeroOfFirstChoice, rankOf]

@[simp] theorem rankOf_rankingOneOfFirstTail_11_zero :
    rankOf (rankingOneOfFirstTail 1 1) (0 : Candidate 1) = 2 := by
  change
    rankOf (rankingOneOfFirstTail 1 1)
        ((1 : Candidate 1).succAbove (0 : Candidate 0)) = 2
  rw [rankOf_rankingOneOfFirstTail_succAbove]
  simp [rankingZeroOfFirstChoice, rankOf]

@[simp] theorem rankOf_rankingOneOfFirstTail_11_two :
    rankOf (rankingOneOfFirstTail 1 1) (2 : Candidate 1) = 1 := by
  change
    rankOf (rankingOneOfFirstTail 1 1)
        ((1 : Candidate 1).succAbove (1 : Candidate 0)) = 1
  rw [rankOf_rankingOneOfFirstTail_succAbove]
  simp [rankingZeroOfFirstChoice, rankOf]

@[simp] theorem rankOf_rankingOneOfFirstTail_20_zero :
    rankOf (rankingOneOfFirstTail 2 0) (0 : Candidate 1) = 1 := by
  change
    rankOf (rankingOneOfFirstTail 2 0)
        ((2 : Candidate 1).succAbove (0 : Candidate 0)) = 1
  rw [rankOf_rankingOneOfFirstTail_succAbove]
  simp [rankingZeroOfFirstChoice, rankOf]

@[simp] theorem rankOf_rankingOneOfFirstTail_20_one :
    rankOf (rankingOneOfFirstTail 2 0) (1 : Candidate 1) = 2 := by
  change
    rankOf (rankingOneOfFirstTail 2 0)
        ((2 : Candidate 1).succAbove (1 : Candidate 0)) = 2
  rw [rankOf_rankingOneOfFirstTail_succAbove]
  simp [rankingZeroOfFirstChoice, rankOf]

@[simp] theorem rankOf_rankingOneOfFirstTail_21_zero :
    rankOf (rankingOneOfFirstTail 2 1) (0 : Candidate 1) = 2 := by
  change
    rankOf (rankingOneOfFirstTail 2 1)
        ((2 : Candidate 1).succAbove (0 : Candidate 0)) = 2
  rw [rankOf_rankingOneOfFirstTail_succAbove]
  simp [rankingZeroOfFirstChoice, rankOf]

@[simp] theorem rankOf_rankingOneOfFirstTail_21_one :
    rankOf (rankingOneOfFirstTail 2 1) (1 : Candidate 1) = 1 := by
  change
    rankOf (rankingOneOfFirstTail 2 1)
        ((2 : Candidate 1).succAbove (1 : Candidate 0)) = 1
  rw [rankOf_rankingOneOfFirstTail_succAbove]
  simp [rankingZeroOfFirstChoice, rankOf]

/-- Kendall-layer average for a three-candidate payoff. -/
noncomputable def rankLayerAverageThree (F : Ranking 1 → ℝ)
    (r : Candidate 2) : ℝ :=
  if r = (0 : Candidate 2) then
    F (rankingOneOfFirstTail 0 0)
  else if r = (1 : Candidate 2) then
    (F (rankingOneOfFirstTail 0 1) +
      F (rankingOneOfFirstTail 1 0)) / 2
  else if r = (2 : Candidate 2) then
    (F (rankingOneOfFirstTail 1 1) +
      F (rankingOneOfFirstTail 2 0)) / 2
  else
    F (rankingOneOfFirstTail 2 1)

theorem reflMallowsPayoffSum_one_eq_rankLayerAverageThree
    (q : ℝ) (F : Ranking 1 → ℝ) :
    reflMallowsPayoffSum 1 q F =
      ∑ r : Candidate 2,
        rankLayerCountThree r * q ^ (r : ℕ) *
          rankLayerAverageThree F r := by
  classical
  rw [reflMallowsPayoffSum_firstChoice 0 q F]
  simp_rw [reflMallowsPayoffSum_zero_eq_candidateRankSum]
  rw [Fin.sum_univ_three]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [rankLayerCountThree_weightedSum_eq]
  simp [rankLayerAverageThree, rankingOneOfFirstTail]
  ring

theorem mallowsPartition_refl_one_eq_rankLayerCountThree_sum
    (q : ℝ) :
    mallowsPartition q (Equiv.refl (Candidate 1)) =
      ∑ r : Candidate 2, rankLayerCountThree r * q ^ (r : ℕ) := by
  classical
  have h :=
    reflMallowsPayoffSum_one_eq_rankLayerAverageThree q
      (fun _ : Ranking 1 => (1 : ℝ))
  unfold reflMallowsPayoffSum at h
  unfold mallowsPartition mallowsWeight
  simpa [rankLayerAverageThree, mul_comm, mul_left_comm, mul_assoc] using h

theorem rankLayerAverageThree_anti_of_adjacentSwapImproves
    {F : Ranking 1 → ℝ}
    (hF : AdjacentSwapImproves (Equiv.refl (Candidate 1)) F) :
    ∀ i j : Candidate 2, i < j →
      rankLayerAverageThree F j ≤ rankLayerAverageThree F i := by
  classical
  have h10_00 :
      F (rankingOneOfFirstTail 1 0) ≤
        F (rankingOneOfFirstTail 0 0) := by
    let k : Fin 2 := 0
    have hsucc :
        rankingOneOfFirstTail 1 0 k.succ = (0 : Candidate 1) := by
      simpa [k, rankingZeroOfFirstChoice, rankOf] using
        rankingOneOfFirstTail_apply_tail
          (1 : Candidate 1) (0 : Candidate 0) (0 : Candidate 0)
    have hcast :
        rankingOneOfFirstTail 1 0 k.castSucc = (1 : Candidate 1) := by
      simp [k]
    have hcenter :
        rankOf (Equiv.refl (Candidate 1))
            (rankingOneOfFirstTail 1 0 k.succ) <
          rankOf (Equiv.refl (Candidate 1))
            (rankingOneOfFirstTail 1 0 k.castSucc) := by
      simp [hsucc, hcast, rankOf]
    have hstep := hF (rankingOneOfFirstTail 1 0) k hcenter
    rw [hsucc, hcast] at hstep
    have hswap :
        swapCandidatePositions (rankingOneOfFirstTail 1 0)
            (0 : Candidate 1) (1 : Candidate 1) =
          rankingOneOfFirstTail 0 0 := by
      apply ranking_ext_of_rankOf
      intro e
      fin_cases e <;>
        simp [rankOf_swapCandidatePositions_of_ne]
    simpa [hswap] using hstep
  have h01_00 :
      F (rankingOneOfFirstTail 0 1) ≤
        F (rankingOneOfFirstTail 0 0) := by
    let k : Fin 2 := 1
    have hsucc :
        rankingOneOfFirstTail 0 1 k.succ = (1 : Candidate 1) := by
      simpa [k, rankingZeroOfFirstChoice, rankOf] using
        rankingOneOfFirstTail_apply_tail
          (0 : Candidate 1) (1 : Candidate 0) (0 : Candidate 0)
    have hcast :
        rankingOneOfFirstTail 0 1 k.castSucc = (2 : Candidate 1) := by
      simpa [k, rankingZeroOfFirstChoice, rankOf] using
        rankingOneOfFirstTail_apply_tail
          (0 : Candidate 1) (1 : Candidate 0) (1 : Candidate 0)
    have hcenter :
        rankOf (Equiv.refl (Candidate 1))
            (rankingOneOfFirstTail 0 1 k.succ) <
          rankOf (Equiv.refl (Candidate 1))
            (rankingOneOfFirstTail 0 1 k.castSucc) := by
      simp [hsucc, hcast, rankOf]
    have hstep := hF (rankingOneOfFirstTail 0 1) k hcenter
    rw [hsucc, hcast] at hstep
    have hswap :
        swapCandidatePositions (rankingOneOfFirstTail 0 1)
            (1 : Candidate 1) (2 : Candidate 1) =
          rankingOneOfFirstTail 0 0 := by
      apply ranking_ext_of_rankOf
      intro e
      fin_cases e <;>
        simp [rankOf_swapCandidatePositions_of_ne]
    simpa [hswap] using hstep
  have h11_10 :
      F (rankingOneOfFirstTail 1 1) ≤
        F (rankingOneOfFirstTail 1 0) := by
    let k : Fin 2 := 1
    have hsucc :
        rankingOneOfFirstTail 1 1 k.succ = (0 : Candidate 1) := by
      simpa [k, rankingZeroOfFirstChoice, rankOf] using
        rankingOneOfFirstTail_apply_tail
          (1 : Candidate 1) (1 : Candidate 0) (0 : Candidate 0)
    have hcast :
        rankingOneOfFirstTail 1 1 k.castSucc = (2 : Candidate 1) := by
      simpa [k, rankingZeroOfFirstChoice, rankOf] using
        rankingOneOfFirstTail_apply_tail
          (1 : Candidate 1) (1 : Candidate 0) (1 : Candidate 0)
    have hcenter :
        rankOf (Equiv.refl (Candidate 1))
            (rankingOneOfFirstTail 1 1 k.succ) <
          rankOf (Equiv.refl (Candidate 1))
            (rankingOneOfFirstTail 1 1 k.castSucc) := by
      simp [hsucc, hcast, rankOf]
    have hstep := hF (rankingOneOfFirstTail 1 1) k hcenter
    rw [hsucc, hcast] at hstep
    have hswap :
        swapCandidatePositions (rankingOneOfFirstTail 1 1)
            (0 : Candidate 1) (2 : Candidate 1) =
          rankingOneOfFirstTail 1 0 := by
      apply ranking_ext_of_rankOf
      intro e
      fin_cases e <;>
        simp [rankOf_swapCandidatePositions_of_ne]
    simpa [hswap] using hstep
  have h20_01 :
      F (rankingOneOfFirstTail 2 0) ≤
        F (rankingOneOfFirstTail 0 1) := by
    let k : Fin 2 := 0
    have hsucc :
        rankingOneOfFirstTail 2 0 k.succ = (0 : Candidate 1) := by
      simpa [k, rankingZeroOfFirstChoice, rankOf] using
        rankingOneOfFirstTail_apply_tail
          (2 : Candidate 1) (0 : Candidate 0) (0 : Candidate 0)
    have hcast :
        rankingOneOfFirstTail 2 0 k.castSucc = (2 : Candidate 1) := by
      simp [k]
    have hcenter :
        rankOf (Equiv.refl (Candidate 1))
            (rankingOneOfFirstTail 2 0 k.succ) <
          rankOf (Equiv.refl (Candidate 1))
            (rankingOneOfFirstTail 2 0 k.castSucc) := by
      simp [hsucc, hcast, rankOf]
    have hstep := hF (rankingOneOfFirstTail 2 0) k hcenter
    rw [hsucc, hcast] at hstep
    have hswap :
        swapCandidatePositions (rankingOneOfFirstTail 2 0)
            (0 : Candidate 1) (2 : Candidate 1) =
          rankingOneOfFirstTail 0 1 := by
      apply ranking_ext_of_rankOf
      intro e
      fin_cases e <;>
        simp [rankOf_swapCandidatePositions_of_ne]
    simpa [hswap] using hstep
  have h21_11 :
      F (rankingOneOfFirstTail 2 1) ≤
        F (rankingOneOfFirstTail 1 1) := by
    let k : Fin 2 := 0
    have hsucc :
        rankingOneOfFirstTail 2 1 k.succ = (1 : Candidate 1) := by
      simpa [k, rankingZeroOfFirstChoice, rankOf] using
        rankingOneOfFirstTail_apply_tail
          (2 : Candidate 1) (1 : Candidate 0) (1 : Candidate 0)
    have hcast :
        rankingOneOfFirstTail 2 1 k.castSucc = (2 : Candidate 1) := by
      simp [k]
    have hcenter :
        rankOf (Equiv.refl (Candidate 1))
            (rankingOneOfFirstTail 2 1 k.succ) <
          rankOf (Equiv.refl (Candidate 1))
            (rankingOneOfFirstTail 2 1 k.castSucc) := by
      simp [hsucc, hcast, rankOf]
    have hstep := hF (rankingOneOfFirstTail 2 1) k hcenter
    rw [hsucc, hcast] at hstep
    have hswap :
        swapCandidatePositions (rankingOneOfFirstTail 2 1)
            (1 : Candidate 1) (2 : Candidate 1) =
          rankingOneOfFirstTail 1 1 := by
      apply ranking_ext_of_rankOf
      intro e
      fin_cases e <;>
        simp [rankOf_swapCandidatePositions_of_ne]
    simpa [hswap] using hstep
  have h21_20 :
      F (rankingOneOfFirstTail 2 1) ≤
        F (rankingOneOfFirstTail 2 0) := by
    let k : Fin 2 := 1
    have hsucc :
        rankingOneOfFirstTail 2 1 k.succ = (0 : Candidate 1) := by
      simpa [k, rankingZeroOfFirstChoice, rankOf] using
        rankingOneOfFirstTail_apply_tail
          (2 : Candidate 1) (1 : Candidate 0) (0 : Candidate 0)
    have hcast :
        rankingOneOfFirstTail 2 1 k.castSucc = (1 : Candidate 1) := by
      simpa [k, rankingZeroOfFirstChoice, rankOf] using
        rankingOneOfFirstTail_apply_tail
          (2 : Candidate 1) (1 : Candidate 0) (1 : Candidate 0)
    have hcenter :
        rankOf (Equiv.refl (Candidate 1))
            (rankingOneOfFirstTail 2 1 k.succ) <
          rankOf (Equiv.refl (Candidate 1))
            (rankingOneOfFirstTail 2 1 k.castSucc) := by
      simp [hsucc, hcast, rankOf]
    have hstep := hF (rankingOneOfFirstTail 2 1) k hcenter
    rw [hsucc, hcast] at hstep
    have hswap :
        swapCandidatePositions (rankingOneOfFirstTail 2 1)
            (0 : Candidate 1) (1 : Candidate 1) =
          rankingOneOfFirstTail 2 0 := by
      apply ranking_ext_of_rankOf
      intro e
      fin_cases e <;>
        simp [rankOf_swapCandidatePositions_of_ne]
    simpa [hswap] using hstep
  have h_layer01 :
      rankLayerAverageThree F 1 ≤ rankLayerAverageThree F 0 := by
    simp [rankLayerAverageThree]
    linarith
  have h_layer12 :
      rankLayerAverageThree F 2 ≤ rankLayerAverageThree F 1 := by
    simp [rankLayerAverageThree]
    linarith
  have h_layer23 :
      rankLayerAverageThree F 3 ≤ rankLayerAverageThree F 2 := by
    simp [rankLayerAverageThree]
    linarith
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    try norm_num at hij <;>
    simp [rankLayerAverageThree] at * <;>
    linarith

/-- Three-candidate adjacent-swap Mallows stochastic dominance. -/
theorem reflMallowsAdjacentStochasticDominance_one
    {qMore qLess : ℝ} (hqMore_pos : 0 < qMore) (hq_lt : qMore < qLess) :
    ReflMallowsAdjacentStochasticDominance 1 qMore qLess := by
  classical
  intro F hF
  let B : Candidate 2 → ℝ := rankLayerAverageThree F
  have hB : ∀ i j : Candidate 2, i < j → B j ≤ B i :=
    rankLayerAverageThree_anti_of_adjacentSwapImproves hF
  have h :=
    rankLayerCountThree_weightedAverage_anti
      hqMore_pos hq_lt (B := B) hB
  rw [mallowsPartition_refl_one_eq_rankLayerCountThree_sum,
    mallowsPartition_refl_one_eq_rankLayerCountThree_sum,
    reflMallowsPayoffSum_one_eq_rankLayerAverageThree,
    reflMallowsPayoffSum_one_eq_rankLayerAverageThree]
  simpa [B, mul_comm, mul_left_comm, mul_assoc] using h

/--
One recursive induction step for identity-center Mallows payoff dominance.

The first premise is the induction hypothesis on every tail payoff obtained by
fixing the insertion position of the center-best candidate.  The second premise
says the less-accurate tail payoff sums are weakly decreasing as that insertion
position moves down the center order.  Together they imply the full
cross-multiplied payoff comparison.
-/
theorem reflMallowsPayoffSum_cross_of_peelBest_step
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (F : Ranking (n + 1) → ℝ)
    (htail :
      ∀ p : Candidate (n + 1),
        0 ≤
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              reflMallowsPayoffSum n qMore
                (fun σ : Ranking n =>
                  F (rankingPeelBestOrderEquiv n (p, σ))) -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              reflMallowsPayoffSum n qLess
                (fun σ : Ranking n =>
                  F (rankingPeelBestOrderEquiv n (p, σ))))
    (hpos :
      ∀ p r : Candidate (n + 1), p < r →
        reflMallowsPayoffSum n qLess
          (fun σ : Ranking n =>
            F (rankingPeelBestOrderEquiv n (r, σ))) ≤
          reflMallowsPayoffSum n qLess
            (fun σ : Ranking n =>
              F (rankingPeelBestOrderEquiv n (p, σ)))) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qMore F -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qLess F := by
  classical
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let PMore : ℝ := candidateRankPowerSum (n + 1) qMore
  let PLess : ℝ := candidateRankPowerSum (n + 1) qLess
  let SMore : Candidate (n + 1) → ℝ := fun p =>
    reflMallowsPayoffSum n qMore
      (fun σ : Ranking n => F (rankingPeelBestOrderEquiv n (p, σ)))
  let SLess : Candidate (n + 1) → ℝ := fun p =>
    reflMallowsPayoffSum n qLess
      (fun σ : Ranking n => F (rankingPeelBestOrderEquiv n (p, σ)))
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have htail_sum :
      0 ≤
        ZLess * (∑ p : Candidate (n + 1),
            qMore ^ (p : ℕ) * SMore p) -
          ZMore * (∑ p : Candidate (n + 1),
            qMore ^ (p : ℕ) * SLess p) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_nonneg ?_
    intro p _
    have hp_nonneg : 0 ≤ qMore ^ (p : ℕ) :=
      pow_nonneg (le_of_lt hqMore_pos) (p : ℕ)
    have hp_tail : 0 ≤ ZLess * SMore p - ZMore * SLess p := by
      simpa [ZLess, ZMore, SMore, SLess] using htail p
    have hterm :
        ZLess * (qMore ^ (p : ℕ) * SMore p) -
            ZMore * (qMore ^ (p : ℕ) * SLess p) =
          qMore ^ (p : ℕ) * (ZLess * SMore p - ZMore * SLess p) := by
      ring
    rw [hterm]
    exact mul_nonneg hp_nonneg hp_tail
  have hweighted :
      0 ≤
        PLess * (∑ p : Candidate (n + 1),
            qMore ^ (p : ℕ) * SLess p) -
          PMore * (∑ p : Candidate (n + 1),
            qLess ^ (p : ℕ) * SLess p) := by
    have hB :
        ∀ p r : Candidate (n + 1), p < r → SLess r ≤ SLess p := by
      intro p r hpr
      exact hpos p r hpr
    simpa [PLess, PMore, SLess] using
      candidateRankWeightedAverage_anti
        (n + 1) hqMore_pos hq_lt (B := SLess) hB
  have hPLess_nonneg : 0 ≤ PLess :=
    le_of_lt (candidateRankPowerSum_pos (n + 1) hqLess_pos)
  have hZMore_nonneg : 0 ≤ ZMore :=
    le_of_lt (mallowsPartition_pos (hq := hqMore_pos)
      (Equiv.refl (Candidate n)))
  rw [mallowsPartition_refl_peelBest n qLess,
    mallowsPartition_refl_peelBest n qMore,
    reflMallowsPayoffSum_peelBest n qMore F,
    reflMallowsPayoffSum_peelBest n qLess F]
  change
    0 ≤
      (PLess * ZLess) *
          (∑ p : Candidate (n + 1), qMore ^ (p : ℕ) * SMore p) -
        (PMore * ZMore) *
          (∑ p : Candidate (n + 1), qLess ^ (p : ℕ) * SLess p)
  have hdecomp :
      (PLess * ZLess) *
          (∑ p : Candidate (n + 1), qMore ^ (p : ℕ) * SMore p) -
        (PMore * ZMore) *
          (∑ p : Candidate (n + 1), qLess ^ (p : ℕ) * SLess p)
        =
      PLess *
          (ZLess * (∑ p : Candidate (n + 1),
              qMore ^ (p : ℕ) * SMore p) -
            ZMore * (∑ p : Candidate (n + 1),
              qMore ^ (p : ℕ) * SLess p)) +
        ZMore *
          (PLess * (∑ p : Candidate (n + 1),
              qMore ^ (p : ℕ) * SLess p) -
            PMore * (∑ p : Candidate (n + 1),
              qLess ^ (p : ℕ) * SLess p)) := by
    ring
  rw [hdecomp]
  exact add_nonneg
    (mul_nonneg hPLess_nonneg htail_sum)
    (mul_nonneg hZMore_nonneg hweighted)

/--
Strict peel-best induction step.  The recursive branch comparisons remain weak,
but a genuine drop in the less-accurate insertion-position payoff makes the
geometric weighted-average part strict.
-/
theorem reflMallowsPayoffSum_cross_of_peelBest_step_strict
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (F : Ranking (n + 1) → ℝ)
    (htail :
      ∀ p : Candidate (n + 1),
        0 ≤
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              reflMallowsPayoffSum n qMore
                (fun σ : Ranking n =>
                  F (rankingPeelBestOrderEquiv n (p, σ))) -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              reflMallowsPayoffSum n qLess
                (fun σ : Ranking n =>
                  F (rankingPeelBestOrderEquiv n (p, σ))))
    (hpos :
      ∀ p r : Candidate (n + 1), p < r →
        reflMallowsPayoffSum n qLess
          (fun σ : Ranking n =>
            F (rankingPeelBestOrderEquiv n (r, σ))) ≤
          reflMallowsPayoffSum n qLess
            (fun σ : Ranking n =>
              F (rankingPeelBestOrderEquiv n (p, σ))))
    (hpos_strict :
      ∃ p r : Candidate (n + 1), p < r ∧
        reflMallowsPayoffSum n qLess
          (fun σ : Ranking n =>
            F (rankingPeelBestOrderEquiv n (r, σ))) <
          reflMallowsPayoffSum n qLess
            (fun σ : Ranking n =>
              F (rankingPeelBestOrderEquiv n (p, σ)))) :
    0 <
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qMore F -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qLess F := by
  classical
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let PMore : ℝ := candidateRankPowerSum (n + 1) qMore
  let PLess : ℝ := candidateRankPowerSum (n + 1) qLess
  let SMore : Candidate (n + 1) → ℝ := fun p =>
    reflMallowsPayoffSum n qMore
      (fun σ : Ranking n => F (rankingPeelBestOrderEquiv n (p, σ)))
  let SLess : Candidate (n + 1) → ℝ := fun p =>
    reflMallowsPayoffSum n qLess
      (fun σ : Ranking n => F (rankingPeelBestOrderEquiv n (p, σ)))
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have htail_sum :
      0 ≤
        ZLess * (∑ p : Candidate (n + 1),
            qMore ^ (p : ℕ) * SMore p) -
          ZMore * (∑ p : Candidate (n + 1),
            qMore ^ (p : ℕ) * SLess p) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_nonneg ?_
    intro p _
    have hp_nonneg : 0 ≤ qMore ^ (p : ℕ) :=
      pow_nonneg (le_of_lt hqMore_pos) (p : ℕ)
    have hp_tail : 0 ≤ ZLess * SMore p - ZMore * SLess p := by
      simpa [ZLess, ZMore, SMore, SLess] using htail p
    have hterm :
        ZLess * (qMore ^ (p : ℕ) * SMore p) -
            ZMore * (qMore ^ (p : ℕ) * SLess p) =
          qMore ^ (p : ℕ) * (ZLess * SMore p - ZMore * SLess p) := by
      ring
    rw [hterm]
    exact mul_nonneg hp_nonneg hp_tail
  have hweighted :
      0 <
        PLess * (∑ p : Candidate (n + 1),
            qMore ^ (p : ℕ) * SLess p) -
          PMore * (∑ p : Candidate (n + 1),
            qLess ^ (p : ℕ) * SLess p) := by
    have hB :
        ∀ p r : Candidate (n + 1), p < r → SLess r ≤ SLess p := by
      intro p r hpr
      exact hpos p r hpr
    have hB_strict :
        ∃ p r : Candidate (n + 1), p < r ∧ SLess r < SLess p := by
      simpa [SLess] using hpos_strict
    simpa [PLess, PMore, SLess] using
      candidateRankWeightedAverage_anti_strict_of_exists
        (n + 1) hqMore_pos hq_lt (B := SLess) hB hB_strict
  have hPLess_nonneg : 0 ≤ PLess :=
    le_of_lt (candidateRankPowerSum_pos (n + 1) hqLess_pos)
  have hZMore_pos : 0 < ZMore :=
    mallowsPartition_pos (hq := hqMore_pos) (Equiv.refl (Candidate n))
  rw [mallowsPartition_refl_peelBest n qLess,
    mallowsPartition_refl_peelBest n qMore,
    reflMallowsPayoffSum_peelBest n qMore F,
    reflMallowsPayoffSum_peelBest n qLess F]
  change
    0 <
      (PLess * ZLess) *
          (∑ p : Candidate (n + 1), qMore ^ (p : ℕ) * SMore p) -
        (PMore * ZMore) *
          (∑ p : Candidate (n + 1), qLess ^ (p : ℕ) * SLess p)
  have hdecomp :
      (PLess * ZLess) *
          (∑ p : Candidate (n + 1), qMore ^ (p : ℕ) * SMore p) -
        (PMore * ZMore) *
          (∑ p : Candidate (n + 1), qLess ^ (p : ℕ) * SLess p)
        =
      PLess *
          (ZLess * (∑ p : Candidate (n + 1),
              qMore ^ (p : ℕ) * SMore p) -
            ZMore * (∑ p : Candidate (n + 1),
              qMore ^ (p : ℕ) * SLess p)) +
        ZMore *
          (PLess * (∑ p : Candidate (n + 1),
              qMore ^ (p : ℕ) * SLess p) -
            PMore * (∑ p : Candidate (n + 1),
              qLess ^ (p : ℕ) * SLess p)) := by
    ring
  rw [hdecomp]
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg hPLess_nonneg htail_sum)
    (mul_pos hZMore_pos hweighted)

/--
Peel-best induction step specialized to adjacent-swap-improving payoffs.

The adjacent-swap hypothesis supplies the insertion-position monotonicity
premise of `reflMallowsPayoffSum_cross_of_peelBest_step`; the remaining input
is exactly the family of tail branch cross-comparisons.
-/
theorem reflMallowsPayoffSum_cross_of_peelBest_step_of_adjacentSwapImproves
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (F : Ranking (n + 1) → ℝ)
    (hF : AdjacentSwapImproves (Equiv.refl (Candidate (n + 1))) F)
    (htail :
      ∀ p : Candidate (n + 1),
        0 ≤
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              reflMallowsPayoffSum n qMore
                (fun σ : Ranking n =>
                  F (rankingPeelBestOrderEquiv n (p, σ))) -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              reflMallowsPayoffSum n qLess
                (fun σ : Ranking n =>
                  F (rankingPeelBestOrderEquiv n (p, σ)))) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qMore F -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsPayoffSum (n + 1) qLess F := by
  refine
    reflMallowsPayoffSum_cross_of_peelBest_step
      n hqMore_pos hq_lt F htail ?_
  intro p r hpr
  exact
    reflMallowsPayoffSum_peelBest_position_anti_of_adjacentSwapImproves
      (q := qLess) (le_of_lt (lt_trans hqMore_pos hq_lt)) hF hpr

theorem reflMallowsBestInSetPrefixCutSum_cross_of_peelBest_branches
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty) (cut : ℕ)
    (htail :
      ∀ p : Candidate (n + 1),
        0 ≤
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              reflMallowsPayoffSum n qMore
                (fun σ : Ranking n =>
                  bestInSetPrefixCutPeelBestIndicator remaining cut p σ) -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              reflMallowsPayoffSum n qLess
                (fun σ : Ranking n =>
                  bestInSetPrefixCutPeelBestIndicator remaining cut p σ)) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qMore remaining cut -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qLess remaining cut := by
  classical
  let F : Ranking (n + 1) → ℝ := fun τ =>
    bestInSetPrefixCutIndicator remaining cut τ
  unfold reflMallowsBestInSetPrefixCutSum
  refine
    reflMallowsPayoffSum_cross_of_peelBest_step
      n hqMore_pos hq_lt F ?htail ?hpos
  · intro p
    rw [reflMallowsPayoffSum_prefix_peelBest_branch_eq
        n qMore hremaining cut p,
      reflMallowsPayoffSum_prefix_peelBest_branch_eq
        n qLess hremaining cut p]
    exact htail p
  · intro p r hpr
    exact
      reflMallowsPayoffSum_peelBest_position_anti_of_adjacentSwapImproves
        (q := qLess) (le_of_lt (lt_trans hqMore_pos hq_lt))
        (adjacentSwapImproves_bestInSetPrefixCutIndicator
          hremaining cut)
        hpr

theorem reflMallowsBestInSetPrefixCutSum_cross_of_zero_not_mem_from_tail
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hzero : (0 : Candidate (n + 1)) ∉ remaining)
    (cut : ℕ)
    (htail :
      0 ≤
        mallowsPartition qLess (Equiv.refl (Candidate n)) *
            reflMallowsBestInSetPrefixCutSum n qMore
              (tailRemainingOf remaining) (cut - 1) -
          mallowsPartition qMore (Equiv.refl (Candidate n)) *
            reflMallowsBestInSetPrefixCutSum n qLess
              (tailRemainingOf remaining) (cut - 1)) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qMore remaining cut -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qLess remaining cut := by
  refine
    reflMallowsBestInSetPrefixCutSum_cross_of_peelBest_branches
      n hqMore_pos hq_lt hremaining cut ?_
  intro p
  simpa [reflMallowsBestInSetPrefixCutSum,
    bestInSetPrefixCutPeelBestIndicator_of_zero_not_mem
      hzero cut p] using htail

theorem reflMallowsBestInSetPrefixCutSum_eq_tail_of_zero_not_mem
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hzero : (0 : Candidate (n + 1)) ∉ remaining) (cut : ℕ) :
    reflMallowsBestInSetPrefixCutSum (n + 1) q remaining cut =
      candidateRankPowerSum (n + 1) q *
        reflMallowsBestInSetPrefixCutSum n q
          (tailRemainingOf remaining) (cut - 1) := by
  classical
  unfold reflMallowsBestInSetPrefixCutSum
  rw [reflMallowsPayoffSum_peelBest n q
    (fun τ : Ranking (n + 1) =>
      bestInSetPrefixCutIndicator remaining cut τ)]
  simp_rw [
    bestInSetPrefixCutIndicator_rankingPeelBestOrderEquiv_of_zero_not_mem
      hremaining hzero cut]
  change
    (∑ p : Candidate (n + 1),
      q ^ (p : ℕ) *
        reflMallowsPayoffSum n q
          (fun τ : Ranking n =>
            bestInSetPrefixCutIndicator (tailRemainingOf remaining)
              (cut - 1) τ)) =
      candidateRankPowerSum (n + 1) q *
        reflMallowsPayoffSum n q
          (fun τ : Ranking n =>
            bestInSetPrefixCutIndicator (tailRemainingOf remaining)
              (cut - 1) τ)
  rw [← Finset.sum_mul]
  rfl

theorem reflMallowsBestInSetPrefixCutSum_cross_pos_of_zero_not_mem_from_tail
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hzero : (0 : Candidate (n + 1)) ∉ remaining)
    (cut : ℕ)
    (htail :
      0 <
        mallowsPartition qLess (Equiv.refl (Candidate n)) *
            reflMallowsBestInSetPrefixCutSum n qMore
              (tailRemainingOf remaining) (cut - 1) -
          mallowsPartition qMore (Equiv.refl (Candidate n)) *
            reflMallowsBestInSetPrefixCutSum n qLess
              (tailRemainingOf remaining) (cut - 1)) :
    0 <
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qMore remaining cut -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qLess remaining cut := by
  classical
  let PMore : ℝ := candidateRankPowerSum (n + 1) qMore
  let PLess : ℝ := candidateRankPowerSum (n + 1) qLess
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let SMore : ℝ :=
    reflMallowsBestInSetPrefixCutSum n qMore
      (tailRemainingOf remaining) (cut - 1)
  let SLess : ℝ :=
    reflMallowsBestInSetPrefixCutSum n qLess
      (tailRemainingOf remaining) (cut - 1)
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hPMore_pos : 0 < PMore :=
    candidateRankPowerSum_pos (n + 1) hqMore_pos
  have hPLess_pos : 0 < PLess :=
    candidateRankPowerSum_pos (n + 1) hqLess_pos
  rw [
    reflMallowsBestInSetPrefixCutSum_eq_tail_of_zero_not_mem
      n qMore hremaining hzero cut,
    reflMallowsBestInSetPrefixCutSum_eq_tail_of_zero_not_mem
      n qLess hremaining hzero cut,
    mallowsPartition_refl_peelBest n qLess,
    mallowsPartition_refl_peelBest n qMore]
  change
    0 <
      (PLess * ZLess) * (PMore * SMore) -
        (PMore * ZMore) * (PLess * SLess)
  have hfactor :
      (PLess * ZLess) * (PMore * SMore) -
          (PMore * ZMore) * (PLess * SLess) =
        PLess * PMore * (ZLess * SMore - ZMore * SLess) := by
    ring
  rw [hfactor]
  exact mul_pos (mul_pos hPLess_pos hPMore_pos)
    (by simpa [ZLess, ZMore, SMore, SLess] using htail)

theorem bestInSetPrefixCutIndicator_rankingPeelWorstOrderEquiv_of_last_not_mem
    {n : ℕ} {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hlast : reflLastCandidate (n + 1) ∉ remaining)
    (cut : ℕ) (p : Candidate (n + 1)) (σ : Ranking n) :
    bestInSetPrefixCutIndicator remaining cut
        (rankingPeelWorstOrderEquiv n (p, σ)) =
      bestInSetPrefixCutIndicator (initRemainingOf remaining) cut σ := by
  classical
  have hbest :=
    bestInSet_rankingPeelWorstOrderEquiv_of_last_not_mem
      (n := n) p σ hremaining hlast
  unfold bestInSetPrefixCutIndicator
  rw [hbest]
  simp

theorem reflMallowsBestInSetPrefixCutSum_eq_init_of_last_not_mem
    (n : ℕ) (q : ℝ) {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hlast : reflLastCandidate (n + 1) ∉ remaining) (cut : ℕ) :
    reflMallowsBestInSetPrefixCutSum (n + 1) q remaining cut =
      candidateRankReversePowerSum (n + 1) q *
        reflMallowsBestInSetPrefixCutSum n q
          (initRemainingOf remaining) cut := by
  classical
  unfold reflMallowsBestInSetPrefixCutSum
  rw [reflMallowsPayoffSum_peelWorst n q
    (fun τ : Ranking (n + 1) =>
      bestInSetPrefixCutIndicator remaining cut τ)]
  simp_rw [
    bestInSetPrefixCutIndicator_rankingPeelWorstOrderEquiv_of_last_not_mem
      hremaining hlast cut]
  change
    (∑ p : Candidate (n + 1),
      q ^ (n + 2 - (p : ℕ)) *
        reflMallowsPayoffSum n q
          (fun τ : Ranking n =>
            bestInSetPrefixCutIndicator (initRemainingOf remaining) cut τ)) =
      candidateRankReversePowerSum (n + 1) q *
        reflMallowsPayoffSum n q
          (fun τ : Ranking n =>
            bestInSetPrefixCutIndicator (initRemainingOf remaining) cut τ)
  rw [← Finset.sum_mul]
  rfl

theorem reflMallowsBestInSetPrefixCutSum_cross_of_last_not_mem_from_init
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hlast : reflLastCandidate (n + 1) ∉ remaining)
    (cut : ℕ)
    (hinit :
      0 ≤
        mallowsPartition qLess (Equiv.refl (Candidate n)) *
            reflMallowsBestInSetPrefixCutSum n qMore
              (initRemainingOf remaining) cut -
          mallowsPartition qMore (Equiv.refl (Candidate n)) *
            reflMallowsBestInSetPrefixCutSum n qLess
              (initRemainingOf remaining) cut) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qMore remaining cut -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qLess remaining cut := by
  classical
  let init : Finset (Candidate n) := initRemainingOf remaining
  let PMore : ℝ := candidateRankReversePowerSum (n + 1) qMore
  let PLess : ℝ := candidateRankReversePowerSum (n + 1) qLess
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let SMore : ℝ := reflMallowsBestInSetPrefixCutSum n qMore init cut
  let SLess : ℝ := reflMallowsBestInSetPrefixCutSum n qLess init cut
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hPMore_nonneg : 0 ≤ PMore :=
    le_of_lt (candidateRankReversePowerSum_pos (n + 1) hqMore_pos)
  have hPLess_nonneg : 0 ≤ PLess :=
    le_of_lt (candidateRankReversePowerSum_pos (n + 1) hqLess_pos)
  rw [
    reflMallowsBestInSetPrefixCutSum_eq_init_of_last_not_mem
      n qMore hremaining hlast cut,
    reflMallowsBestInSetPrefixCutSum_eq_init_of_last_not_mem
      n qLess hremaining hlast cut,
    mallowsPartition_refl_peelWorst n qLess,
    mallowsPartition_refl_peelWorst n qMore]
  change
    0 ≤
      (PLess * ZLess) * (PMore * SMore) -
        (PMore * ZMore) * (PLess * SLess)
  have hfactor :
      (PLess * ZLess) * (PMore * SMore) -
          (PMore * ZMore) * (PLess * SLess) =
        PLess * PMore * (ZLess * SMore - ZMore * SLess) := by
    ring
  rw [hfactor]
  exact mul_nonneg (mul_nonneg hPLess_nonneg hPMore_nonneg)
    (by simpa [ZLess, ZMore, SMore, SLess, init] using hinit)

theorem reflMallowsBestInSetPrefixCutSum_cross_pos_of_last_not_mem_from_init
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hlast : reflLastCandidate (n + 1) ∉ remaining)
    (cut : ℕ)
    (hinit :
      0 <
        mallowsPartition qLess (Equiv.refl (Candidate n)) *
            reflMallowsBestInSetPrefixCutSum n qMore
              (initRemainingOf remaining) cut -
          mallowsPartition qMore (Equiv.refl (Candidate n)) *
            reflMallowsBestInSetPrefixCutSum n qLess
              (initRemainingOf remaining) cut) :
    0 <
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qMore remaining cut -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qLess remaining cut := by
  classical
  let init : Finset (Candidate n) := initRemainingOf remaining
  let PMore : ℝ := candidateRankReversePowerSum (n + 1) qMore
  let PLess : ℝ := candidateRankReversePowerSum (n + 1) qLess
  let ZMore : ℝ := mallowsPartition qMore (Equiv.refl (Candidate n))
  let ZLess : ℝ := mallowsPartition qLess (Equiv.refl (Candidate n))
  let SMore : ℝ := reflMallowsBestInSetPrefixCutSum n qMore init cut
  let SLess : ℝ := reflMallowsBestInSetPrefixCutSum n qLess init cut
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hPMore_pos : 0 < PMore :=
    candidateRankReversePowerSum_pos (n + 1) hqMore_pos
  have hPLess_pos : 0 < PLess :=
    candidateRankReversePowerSum_pos (n + 1) hqLess_pos
  rw [
    reflMallowsBestInSetPrefixCutSum_eq_init_of_last_not_mem
      n qMore hremaining hlast cut,
    reflMallowsBestInSetPrefixCutSum_eq_init_of_last_not_mem
      n qLess hremaining hlast cut,
    mallowsPartition_refl_peelWorst n qLess,
    mallowsPartition_refl_peelWorst n qMore]
  change
    0 <
      (PLess * ZLess) * (PMore * SMore) -
        (PMore * ZMore) * (PLess * SLess)
  have hfactor :
      (PLess * ZLess) * (PMore * SMore) -
          (PMore * ZMore) * (PLess * SLess) =
        PLess * PMore * (ZLess * SMore - ZMore * SLess) := by
    ring
  rw [hfactor]
  exact mul_pos (mul_pos hPLess_pos hPMore_pos)
    (by simpa [ZLess, ZMore, SMore, SLess, init] using hinit)

theorem reflMallowsBestInSetPrefixCutSum_cross_of_extreme_not_mem_from_prev
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    (hprev : ReflMallowsBestInSetPrefixCutDominance n qMore qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hextreme :
      (0 : Candidate (n + 1)) ∉ remaining ∨
        reflLastCandidate (n + 1) ∉ remaining)
    (cut : ℕ) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qMore remaining cut -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qLess remaining cut := by
  rcases hextreme with hzero | hlast
  · exact
      reflMallowsBestInSetPrefixCutSum_cross_of_zero_not_mem_from_tail
        n hqMore_pos hq_lt hremaining hzero cut
        (hprev
          (tailRemainingOf_nonempty_of_nonempty_of_zero_not_mem
            hremaining hzero)
          (cut - 1))
  · exact
      reflMallowsBestInSetPrefixCutSum_cross_of_last_not_mem_from_init
        n hqMore_pos hq_lt hremaining hlast cut
        (hprev
          (initRemainingOf_nonempty_of_nonempty_of_last_not_mem
            hremaining hlast)
          cut)

theorem ReflMallowsBestInSetPrefixCutDominance.succ_of_extremeWeighted
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    (hprev : ReflMallowsBestInSetPrefixCutDominance n qMore qLess)
    (hweighted :
      ReflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes
        n qMore qLess) :
    ReflMallowsBestInSetPrefixCutDominance (n + 1) qMore qLess := by
  classical
  intro remaining hremaining cut
  by_cases hzero : (0 : Candidate (n + 1)) ∈ remaining
  · by_cases hlast : reflLastCandidate (n + 1) ∈ remaining
    · by_cases hcut0 : cut = 0
      · subst cut
        exact
          reflMallowsBestInSetPrefixCutSum_cross_of_forall_remaining_ge
            (n + 1) qMore qLess hremaining (by
              intro c _
              omega)
      · by_cases hcut_big : n + 2 < cut
        · exact
            reflMallowsBestInSetPrefixCutSum_cross_of_forall_remaining_lt
              (n + 1) qMore qLess hremaining (by
                intro c _
                have hc_le : (c : ℕ) ≤ n + 2 :=
                  Nat.le_of_lt_succ c.isLt
                omega)
        · have hcut_pos : 0 < cut := Nat.pos_of_ne_zero hcut0
          have hcut_le : cut ≤ n + 2 := Nat.le_of_not_gt hcut_big
          refine
            reflMallowsBestInSetPrefixCutSum_cross_of_firstChoice_tail_pair_bracket_sum
              n hqMore_pos hq_lt hremaining cut ?htail ?hpair_sum
          · intro r hr
            exact hprev
              (firstChoiceTailRemainingOf_nonempty_of_nonempty_of_first_not_mem
                hremaining hr)
              (deleteFirstChoicePrefixCut r cut)
          · refine
              firstChoiceBranchBracketSum_nonneg_of_diag_weighted
                n hqMore_pos (le_of_lt (lt_trans hqMore_pos hq_lt))
                (fun τ : Ranking (n + 1) =>
                  bestInSetPrefixCutIndicator remaining cut τ) ?hdiag ?hweighted
            · exact
                firstChoiceBranchPayoffSum_prefixCut_diag_nonneg_of_tail
                  n hremaining cut
                  (by
                    intro r hr
                    exact hprev
                      (firstChoiceTailRemainingOf_nonempty_of_nonempty_of_first_not_mem
                        hremaining hr)
                      (deleteFirstChoicePrefixCut r cut))
            · exact hweighted hremaining hzero hlast hcut_pos hcut_le
    · exact
        reflMallowsBestInSetPrefixCutSum_cross_of_extreme_not_mem_from_prev
          n hqMore_pos hq_lt hprev hremaining (Or.inr hlast) cut
  · exact
      reflMallowsBestInSetPrefixCutSum_cross_of_extreme_not_mem_from_prev
        n hqMore_pos hq_lt hprev hremaining (Or.inl hzero) cut

/--
Extreme weighted first-choice targets at every recursive size imply arbitrary
prefix-cut dominance.

This packages the current reduced route: absent center extremes are deleted by
the successor step, and only the same-size case with both center extremes
remaining is supplied by `hweighted`.
-/
theorem ReflMallowsBestInSetPrefixCutDominance.of_extremeWeighted
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    (hweighted :
      ∀ m : ℕ,
        ReflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes
          m qMore qLess) :
    ReflMallowsBestInSetPrefixCutDominance n qMore qLess := by
  induction n with
  | zero =>
      exact ReflMallowsBestInSetPrefixCutDominance.zero
        hqMore_pos hq_lt
  | succ n ih =>
      exact ReflMallowsBestInSetPrefixCutDominance.succ_of_extremeWeighted
        hqMore_pos hq_lt ih (hweighted n)

theorem reflMallowsBestInSetPrefixSum_cross_of_extremeWeighted
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    (hweighted :
      ∀ m : ℕ,
        ReflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes
          m qMore qLess)
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty)
    (k : Fin (n + 1)) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixSum n qMore remaining k -
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixSum n qLess remaining k := by
  rw [reflMallowsBestInSetPrefixSum_eq_cut,
    reflMallowsBestInSetPrefixSum_eq_cut]
  exact
    ReflMallowsBestInSetPrefixCutDominance.of_extremeWeighted
      n hqMore_pos hq_lt hweighted hremaining (k.val + 1)

theorem reflMallowsBestInSetPrefixCutSum_cross_pos_cut_one_of_zero_mem_card_gt_one
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hzero : (0 : Candidate (n + 1)) ∈ remaining)
    (hcard : 1 < remaining.card) :
    0 <
      mallowsPartition qLess (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qMore remaining 1 -
        mallowsPartition qMore (Equiv.refl (Candidate (n + 1))) *
          reflMallowsBestInSetPrefixCutSum (n + 1) qLess remaining 1 := by
  classical
  have hremaining : remaining.Nonempty := ⟨0, hzero⟩
  have hprev :
      ReflMallowsBestInSetPrefixCutDominance n qMore qLess :=
    ReflMallowsBestInSetPrefixCutDominance.of_extremeWeighted
      n hqMore_pos hq_lt
      (fun m =>
        reflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes_of_q_lt
          m hqMore_pos hq_lt)
  have hdiag :
      ∀ r : Candidate (n + 1), r ∉ remaining →
        0 ≤
          mallowsPartition qLess (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixCutSum n qMore
                (firstChoiceTailRemainingOf r remaining)
                (deleteFirstChoicePrefixCut r 1) -
            mallowsPartition qMore (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixCutSum n qLess
                (firstChoiceTailRemainingOf r remaining)
                (deleteFirstChoicePrefixCut r 1) := by
    intro r hr
    exact hprev
      (firstChoiceTailRemainingOf_nonempty_of_nonempty_of_first_not_mem
        hremaining hr)
      (deleteFirstChoicePrefixCut r 1)
  have hbracket :
      0 < firstChoiceBranchBracketSum n qMore qLess
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining 1 τ) := by
    refine
      firstChoiceBranchBracketSum_pos_of_diag_weighted
        n hqMore_pos (le_of_lt (lt_trans hqMore_pos hq_lt))
        (fun τ : Ranking (n + 1) =>
          bestInSetPrefixCutIndicator remaining 1 τ) ?hdiag ?hweighted
    · exact
        firstChoiceBranchPayoffSum_prefixCut_diag_nonneg_of_tail
          n hremaining 1 hdiag
    · simpa [firstChoiceBranchWeighted] using
        firstChoiceBranchWeighted_prefixCut_one_pos_of_zero_mem_card_gt_one
          n hqMore_pos hq_lt hzero hcard
  exact
    reflMallowsBestInSetPrefixCutSum_cross_pos_of_firstChoice_tail_pair_bracket_sum
      n hqMore_pos hq_lt hremaining 1 hdiag hbracket

/-- If all candidates remain, `bestInSet` is the first choice. -/
@[simp] theorem bestInSet_univ {n : ℕ} (π : Ranking n) :
    bestInSet π Finset.univ = firstChoice π := by
  simpa [bestInSet, AppliedModelingLib.SocialChoice.Ranking.bestInSet] using
    AppliedModelingLib.SocialChoice.Ranking.bestInSet_univ π

theorem reflMallowsBestInSetPrefixCutSum_zero_univ_one (q : ℝ) :
    reflMallowsBestInSetPrefixCutSum 0 q
        (Finset.univ : Finset (Candidate 0)) 1 = 1 := by
  classical
  unfold reflMallowsBestInSetPrefixCutSum
  rw [reflMallowsPayoffSum_zero_eq_candidateRankSum]
  rw [Fin.sum_univ_two]
  simp [bestInSetPrefixCutIndicator, rankingZeroOfFirstChoice]

theorem reflMallowsBestInSetPrefixSum_cross_exists_pos_of_q_lt
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) (hcard : 1 < remaining.card) :
    ∃ k : Fin (n + 1),
      0 <
        mallowsPartition qLess (Equiv.refl (Candidate n)) *
            reflMallowsBestInSetPrefixSum n qMore remaining k -
          mallowsPartition qMore (Equiv.refl (Candidate n)) *
            reflMallowsBestInSetPrefixSum n qLess remaining k := by
  classical
  induction n with
  | zero =>
      have hcard_le_two : remaining.card ≤ 2 := by
        have h := Finset.card_le_univ remaining
        simpa [Candidate] using h
      have hcard_two : remaining.card = Fintype.card (Candidate 0) := by
        have htwo : remaining.card = 2 := by omega
        simpa [Candidate] using htwo
      have hremaining_univ : remaining = Finset.univ :=
        remaining.eq_univ_of_card hcard_two
      subst remaining
      refine ⟨0, ?_⟩
      rw [reflMallowsBestInSetPrefixSum_eq_cut,
        reflMallowsBestInSetPrefixSum_eq_cut]
      change
        0 <
          mallowsPartition qLess (Equiv.refl (Candidate 0)) *
              reflMallowsBestInSetPrefixCutSum 0 qMore
                (Finset.univ : Finset (Candidate 0)) 1 -
            mallowsPartition qMore (Equiv.refl (Candidate 0)) *
              reflMallowsBestInSetPrefixCutSum 0 qLess
                (Finset.univ : Finset (Candidate 0)) 1
      rw [reflMallowsBestInSetPrefixCutSum_zero_univ_one qMore,
        reflMallowsBestInSetPrefixCutSum_zero_univ_one qLess]
      rw [mallowsPartition_refl_zero_eq_candidateRankPowerSum,
        mallowsPartition_refl_zero_eq_candidateRankPowerSum]
      unfold candidateRankPowerSum
      rw [Fin.sum_univ_two, Fin.sum_univ_two]
      norm_num
      linarith
  | succ n ih =>
      by_cases hzero : (0 : Candidate (n + 1)) ∈ remaining
      · refine ⟨0, ?_⟩
        rw [reflMallowsBestInSetPrefixSum_eq_cut,
          reflMallowsBestInSetPrefixSum_eq_cut]
        simpa using
          reflMallowsBestInSetPrefixCutSum_cross_pos_cut_one_of_zero_mem_card_gt_one
            n hqMore_pos hq_lt hzero hcard
      · have htail_nonempty :
            (tailRemainingOf remaining).Nonempty :=
          tailRemainingOf_nonempty_of_nonempty_of_zero_not_mem
            hremaining hzero
        have htail_card : 1 < (tailRemainingOf remaining).card := by
          rw [tailRemainingOf_card_eq_of_zero_not_mem hzero]
          exact hcard
        rcases ih htail_nonempty htail_card with ⟨k, hk⟩
        rw [reflMallowsBestInSetPrefixSum_eq_cut,
          reflMallowsBestInSetPrefixSum_eq_cut] at hk
        refine ⟨k.succ, ?_⟩
        rw [reflMallowsBestInSetPrefixSum_eq_cut,
          reflMallowsBestInSetPrefixSum_eq_cut]
        have htail_cut :
            0 <
              mallowsPartition qLess (Equiv.refl (Candidate n)) *
                  reflMallowsBestInSetPrefixCutSum n qMore
                    (tailRemainingOf remaining) (k.val + 2 - 1) -
                mallowsPartition qMore (Equiv.refl (Candidate n)) *
                  reflMallowsBestInSetPrefixCutSum n qLess
                    (tailRemainingOf remaining) (k.val + 2 - 1) := by
          have hcut : k.val + 2 - 1 = k.val + 1 := by omega
          simpa [hcut] using hk
        have hlift :=
          reflMallowsBestInSetPrefixCutSum_cross_pos_of_zero_not_mem_from_tail
            n hqMore_pos hq_lt hremaining hzero (k.val + 2) htail_cut
        simpa [Fin.val_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hlift

/--
Identity-center Mallows payoff dominance for every payoff that weakly improves
when inverted center-ordered pairs are corrected.
-/
theorem reflMallowsPayoffSum_cross_of_swapImprovesOn_univ
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (F : Ranking n → ℝ)
    (hF : SwapImprovesOn Finset.univ (Equiv.refl (Candidate n)) F) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate n)) *
          reflMallowsPayoffSum n qMore F -
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          reflMallowsPayoffSum n qLess F := by
  classical
  induction n with
  | zero =>
      exact
        reflMallowsPayoffSum_cross_of_swapImprovesOn_univ_zero
          hqMore_pos hq_lt F hF
  | succ n ih =>
      refine
        reflMallowsPayoffSum_cross_of_peelBest_step
          n hqMore_pos hq_lt F ?htail ?hpos
      · intro p
        have htailF :
            SwapImprovesOn (Finset.univ : Finset (Candidate n))
              (Equiv.refl (Candidate n))
              (fun σ : Ranking n =>
                F (rankingPeelBestOrderEquiv n (p, σ))) := by
          refine
            swapImprovesOn_peelBest_succ
              (remainingTail := (Finset.univ : Finset (Candidate n)))
              (remainingFull := (Finset.univ : Finset (Candidate (n + 1))))
              (F := F) ?_ hF p
          intro c _
          exact Finset.mem_univ _
        exact ih
          (fun σ : Ranking n => F (rankingPeelBestOrderEquiv n (p, σ)))
          htailF
      · intro p r hpr
        have hqLess_nonneg : 0 ≤ qLess :=
          le_of_lt (lt_trans hqMore_pos hq_lt)
        unfold reflMallowsPayoffSum
        refine Finset.sum_le_sum ?_
        intro σ _
        have hweight :
            0 ≤ qLess ^ kendallTau (Equiv.refl (Candidate n)) σ :=
          pow_nonneg hqLess_nonneg _
        have hpoint :
            F (rankingPeelBestOrderEquiv n (r, σ)) ≤
              F (rankingPeelBestOrderEquiv n (p, σ)) :=
          rankingPeelBestOrderEquiv_position_anti_of_swapImprovesOn
            (n := n) (F := F) hF σ hpr
        exact mul_le_mul_of_nonneg_left hpoint hweight

theorem firstChoiceBranchWeighted_pair01_cut_one_nonneg
    {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) :
    0 ≤
      candidateRankPowerSum 1 qLess *
          (∑ i : Candidate 1,
            qMore ^ (i : ℕ) *
              firstChoiceBranchPayoffSum 0 qLess
                (fun τ : Ranking 1 =>
                  bestInSetPrefixCutIndicator
                    ({(0 : Candidate 1), (1 : Candidate 1)} :
                      Finset (Candidate 1)) 1 τ) i) -
        candidateRankPowerSum 1 qMore *
          (∑ i : Candidate 1,
            qLess ^ (i : ℕ) *
              firstChoiceBranchPayoffSum 0 qLess
                (fun τ : Ranking 1 =>
                  bestInSetPrefixCutIndicator
                    ({(0 : Candidate 1), (1 : Candidate 1)} :
                      Finset (Candidate 1)) 1 τ) i) := by
  classical
  let remaining : Finset (Candidate 1) :=
    ({(0 : Candidate 1), (1 : Candidate 1)} : Finset (Candidate 1))
  let F : Ranking 1 → ℝ := fun τ =>
    bestInSetPrefixCutIndicator remaining 1 τ
  have hremaining : remaining.Nonempty := ⟨0, by simp [remaining]⟩
  have h0 :
      firstChoiceBranchPayoffSum 0 qLess F (0 : Candidate 1) =
        mallowsPartition qLess (Equiv.refl (Candidate 0)) := by
    rw [firstChoiceBranchPayoffSum_prefixCut 0 qLess hremaining 1
      (0 : Candidate 1)]
    simp [remaining]
  have h1 :
      firstChoiceBranchPayoffSum 0 qLess F (1 : Candidate 1) = 0 := by
    rw [firstChoiceBranchPayoffSum_prefixCut 0 qLess hremaining 1
      (1 : Candidate 1)]
    simp [remaining]
  have h2 :
      firstChoiceBranchPayoffSum 0 qLess F (2 : Candidate 1) = 1 := by
    rw [firstChoiceBranchPayoffSum_prefixCut 0 qLess hremaining 1
      (2 : Candidate 1)]
    have hnot : (2 : Candidate 1) ∉ remaining := by
      simp [remaining]
    have htail :
        firstChoiceTailRemainingOf (2 : Candidate 1) remaining =
          (Finset.univ : Finset (Candidate 0)) := by
      ext c
      fin_cases c <;> decide
    have hcut : deleteFirstChoicePrefixCut (2 : Candidate 1) 1 = 1 := by
      simp [deleteFirstChoicePrefixCut]
    rw [if_neg hnot, htail, hcut,
      reflMallowsBestInSetPrefixCutSum_zero_univ_one]
  change
    0 ≤
      candidateRankPowerSum 1 qLess *
          (∑ i : Candidate 1,
            qMore ^ (i : ℕ) * firstChoiceBranchPayoffSum 0 qLess F i) -
        candidateRankPowerSum 1 qMore *
          (∑ i : Candidate 1,
            qLess ^ (i : ℕ) * firstChoiceBranchPayoffSum 0 qLess F i)
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  rw [h0, h1, h2]
  norm_num
  simpa [pow_two] using
    firstChoiceWeighted_three_Z01_nonneg hqMore_pos hq_lt

theorem firstChoiceBranchWeighted_pair02_cut_one_nonneg
    {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) :
    0 ≤
      candidateRankPowerSum 1 qLess *
          (∑ i : Candidate 1,
            qMore ^ (i : ℕ) *
              firstChoiceBranchPayoffSum 0 qLess
                (fun τ : Ranking 1 =>
                  bestInSetPrefixCutIndicator
                    ({(0 : Candidate 1), (2 : Candidate 1)} :
                      Finset (Candidate 1)) 1 τ) i) -
        candidateRankPowerSum 1 qMore *
          (∑ i : Candidate 1,
            qLess ^ (i : ℕ) *
              firstChoiceBranchPayoffSum 0 qLess
                (fun τ : Ranking 1 =>
                  bestInSetPrefixCutIndicator
                    ({(0 : Candidate 1), (2 : Candidate 1)} :
                      Finset (Candidate 1)) 1 τ) i) := by
  classical
  let remaining : Finset (Candidate 1) :=
    ({(0 : Candidate 1), (2 : Candidate 1)} : Finset (Candidate 1))
  let F : Ranking 1 → ℝ := fun τ =>
    bestInSetPrefixCutIndicator remaining 1 τ
  have hremaining : remaining.Nonempty := ⟨0, by simp [remaining]⟩
  have h0 :
      firstChoiceBranchPayoffSum 0 qLess F (0 : Candidate 1) =
        mallowsPartition qLess (Equiv.refl (Candidate 0)) := by
    rw [firstChoiceBranchPayoffSum_prefixCut 0 qLess hremaining 1
      (0 : Candidate 1)]
    simp [remaining]
  have h1 :
      firstChoiceBranchPayoffSum 0 qLess F (1 : Candidate 1) = 1 := by
    rw [firstChoiceBranchPayoffSum_prefixCut 0 qLess hremaining 1
      (1 : Candidate 1)]
    have hnot : (1 : Candidate 1) ∉ remaining := by
      simp [remaining]
    have htail :
        firstChoiceTailRemainingOf (1 : Candidate 1) remaining =
          (Finset.univ : Finset (Candidate 0)) := by
      ext c
      fin_cases c <;> decide
    have hcut : deleteFirstChoicePrefixCut (1 : Candidate 1) 1 = 1 := by
      simp [deleteFirstChoicePrefixCut]
    rw [if_neg hnot, htail, hcut,
      reflMallowsBestInSetPrefixCutSum_zero_univ_one]
  have h2 :
      firstChoiceBranchPayoffSum 0 qLess F (2 : Candidate 1) = 0 := by
    rw [firstChoiceBranchPayoffSum_prefixCut 0 qLess hremaining 1
      (2 : Candidate 1)]
    simp [remaining]
  change
    0 ≤
      candidateRankPowerSum 1 qLess *
          (∑ i : Candidate 1,
            qMore ^ (i : ℕ) * firstChoiceBranchPayoffSum 0 qLess F i) -
        candidateRankPowerSum 1 qMore *
          (∑ i : Candidate 1,
            qLess ^ (i : ℕ) * firstChoiceBranchPayoffSum 0 qLess F i)
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  rw [h0, h1, h2]
  norm_num
  simpa using firstChoiceWeighted_three_Z10_nonneg hqMore_pos hq_lt

theorem firstChoiceBranchWeighted_pair02_cut_two_nonneg
    {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) :
    0 ≤
      candidateRankPowerSum 1 qLess *
          (∑ i : Candidate 1,
            qMore ^ (i : ℕ) *
              firstChoiceBranchPayoffSum 0 qLess
                (fun τ : Ranking 1 =>
                  bestInSetPrefixCutIndicator
                    ({(0 : Candidate 1), (2 : Candidate 1)} :
                      Finset (Candidate 1)) 2 τ) i) -
        candidateRankPowerSum 1 qMore *
          (∑ i : Candidate 1,
            qLess ^ (i : ℕ) *
              firstChoiceBranchPayoffSum 0 qLess
                (fun τ : Ranking 1 =>
                  bestInSetPrefixCutIndicator
                    ({(0 : Candidate 1), (2 : Candidate 1)} :
                      Finset (Candidate 1)) 2 τ) i) := by
  classical
  let remaining : Finset (Candidate 1) :=
    ({(0 : Candidate 1), (2 : Candidate 1)} : Finset (Candidate 1))
  let F : Ranking 1 → ℝ := fun τ =>
    bestInSetPrefixCutIndicator remaining 2 τ
  have hremaining : remaining.Nonempty := ⟨0, by simp [remaining]⟩
  have h0 :
      firstChoiceBranchPayoffSum 0 qLess F (0 : Candidate 1) =
        mallowsPartition qLess (Equiv.refl (Candidate 0)) := by
    rw [firstChoiceBranchPayoffSum_prefixCut 0 qLess hremaining 2
      (0 : Candidate 1)]
    simp [remaining]
  have h1 :
      firstChoiceBranchPayoffSum 0 qLess F (1 : Candidate 1) = 1 := by
    rw [firstChoiceBranchPayoffSum_prefixCut 0 qLess hremaining 2
      (1 : Candidate 1)]
    have hnot : (1 : Candidate 1) ∉ remaining := by
      simp [remaining]
    have htail :
        firstChoiceTailRemainingOf (1 : Candidate 1) remaining =
          (Finset.univ : Finset (Candidate 0)) := by
      ext c
      fin_cases c <;> decide
    have hcut : deleteFirstChoicePrefixCut (1 : Candidate 1) 2 = 1 := by
      simp [deleteFirstChoicePrefixCut]
    rw [if_neg hnot, htail, hcut,
      reflMallowsBestInSetPrefixCutSum_zero_univ_one]
  have h2 :
      firstChoiceBranchPayoffSum 0 qLess F (2 : Candidate 1) = 0 := by
    rw [firstChoiceBranchPayoffSum_prefixCut 0 qLess hremaining 2
      (2 : Candidate 1)]
    simp [remaining]
  change
    0 ≤
      candidateRankPowerSum 1 qLess *
          (∑ i : Candidate 1,
            qMore ^ (i : ℕ) * firstChoiceBranchPayoffSum 0 qLess F i) -
        candidateRankPowerSum 1 qMore *
          (∑ i : Candidate 1,
            qLess ^ (i : ℕ) * firstChoiceBranchPayoffSum 0 qLess F i)
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  rw [h0, h1, h2]
  norm_num
  simpa using firstChoiceWeighted_three_Z10_nonneg hqMore_pos hq_lt

theorem firstChoiceBranchWeighted_pair12_cut_two_nonneg
    {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) :
    0 ≤
      candidateRankPowerSum 1 qLess *
          (∑ i : Candidate 1,
            qMore ^ (i : ℕ) *
              firstChoiceBranchPayoffSum 0 qLess
                (fun τ : Ranking 1 =>
                  bestInSetPrefixCutIndicator
                    ({(1 : Candidate 1), (2 : Candidate 1)} :
                      Finset (Candidate 1)) 2 τ) i) -
        candidateRankPowerSum 1 qMore *
          (∑ i : Candidate 1,
            qLess ^ (i : ℕ) *
              firstChoiceBranchPayoffSum 0 qLess
                (fun τ : Ranking 1 =>
                  bestInSetPrefixCutIndicator
                    ({(1 : Candidate 1), (2 : Candidate 1)} :
                      Finset (Candidate 1)) 2 τ) i) := by
  classical
  let remaining : Finset (Candidate 1) :=
    ({(1 : Candidate 1), (2 : Candidate 1)} : Finset (Candidate 1))
  let F : Ranking 1 → ℝ := fun τ =>
    bestInSetPrefixCutIndicator remaining 2 τ
  have hremaining : remaining.Nonempty := ⟨1, by simp [remaining]⟩
  have h0 :
      firstChoiceBranchPayoffSum 0 qLess F (0 : Candidate 1) = 1 := by
    rw [firstChoiceBranchPayoffSum_prefixCut 0 qLess hremaining 2
      (0 : Candidate 1)]
    have hnot : (0 : Candidate 1) ∉ remaining := by
      simp [remaining]
    have htail :
        firstChoiceTailRemainingOf (0 : Candidate 1) remaining =
          (Finset.univ : Finset (Candidate 0)) := by
      ext c
      fin_cases c <;> decide
    have hcut : deleteFirstChoicePrefixCut (0 : Candidate 1) 2 = 1 := by
      simp [deleteFirstChoicePrefixCut]
    rw [if_neg hnot, htail, hcut,
      reflMallowsBestInSetPrefixCutSum_zero_univ_one]
  have h1 :
      firstChoiceBranchPayoffSum 0 qLess F (1 : Candidate 1) =
        mallowsPartition qLess (Equiv.refl (Candidate 0)) := by
    rw [firstChoiceBranchPayoffSum_prefixCut 0 qLess hremaining 2
      (1 : Candidate 1)]
    simp [remaining]
  have h2 :
      firstChoiceBranchPayoffSum 0 qLess F (2 : Candidate 1) = 0 := by
    rw [firstChoiceBranchPayoffSum_prefixCut 0 qLess hremaining 2
      (2 : Candidate 1)]
    simp [remaining]
  change
    0 ≤
      candidateRankPowerSum 1 qLess *
          (∑ i : Candidate 1,
            qMore ^ (i : ℕ) * firstChoiceBranchPayoffSum 0 qLess F i) -
        candidateRankPowerSum 1 qMore *
          (∑ i : Candidate 1,
            qLess ^ (i : ℕ) * firstChoiceBranchPayoffSum 0 qLess F i)
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  rw [h0, h1, h2]
  norm_num
  simpa using firstChoiceWeighted_three_1Z0_nonneg hqMore_pos hq_lt

theorem ReflMallowsBestInSetPrefixCutFirstChoiceWeighted.zero
    {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) :
    ReflMallowsBestInSetPrefixCutFirstChoiceWeighted 0 qMore qLess := by
  classical
  intro remaining hremaining cut
  by_cases hcut0 : cut = 0
  · subst cut
    have hzero :=
      firstChoiceBranchWeighted_prefixCut_eq_zero_of_forall_remaining_ge
        0 qMore qLess hremaining (cut := 0) (by
          intro c _
          omega)
    rw [hzero]
  · by_cases hcut_big : 2 < cut
    · have hzero :=
        firstChoiceBranchWeighted_prefixCut_eq_zero_of_forall_remaining_lt
          0 qMore qLess hremaining (cut := cut) (by
            intro c _
            have hc_le : (c : ℕ) ≤ 2 :=
              Nat.le_of_lt_succ c.isLt
            omega)
      rw [hzero]
    · have hcut_cases : cut = 1 ∨ cut = 2 := by omega
      rcases hcut_cases with hcut_one | hcut_two
      · subst cut
        by_cases h0 : (0 : Candidate 1) ∈ remaining
        · by_cases h1 : (1 : Candidate 1) ∈ remaining
          · by_cases h2 : (2 : Candidate 1) ∈ remaining
            · have hrem : remaining = Finset.univ := by
                ext c
                fin_cases c <;> simp [h0, h1, h2]
              simpa [hrem] using
                firstChoiceBranchWeighted_univ_cut_nonneg
                  0 hqMore_pos hq_lt 1
            · have hrem :
                  remaining =
                    ({(0 : Candidate 1), (1 : Candidate 1)} :
                      Finset (Candidate 1)) := by
                ext c
                fin_cases c <;> simp [h0, h1, h2]
              simpa [hrem] using
                firstChoiceBranchWeighted_pair01_cut_one_nonneg
                  hqMore_pos hq_lt
          · by_cases h2 : (2 : Candidate 1) ∈ remaining
            · have hrem :
                  remaining =
                    ({(0 : Candidate 1), (2 : Candidate 1)} :
                      Finset (Candidate 1)) := by
                ext c
                fin_cases c <;> simp [h0, h1, h2]
              simpa [hrem] using
                firstChoiceBranchWeighted_pair02_cut_one_nonneg
                  hqMore_pos hq_lt
            · have hzero :=
                firstChoiceBranchWeighted_prefixCut_eq_zero_of_forall_remaining_lt
                  0 qMore qLess hremaining (cut := 1) (by
                    intro c hc
                    fin_cases c <;> simp [h1, h2] at hc ⊢)
              rw [hzero]
        · have hzero :=
            firstChoiceBranchWeighted_prefixCut_eq_zero_of_forall_remaining_ge
              0 qMore qLess hremaining (cut := 1) (by
                intro c hc
                fin_cases c <;> simp [h0] at hc ⊢)
          rw [hzero]
      · subst cut
        by_cases h2 : (2 : Candidate 1) ∈ remaining
        · by_cases h0 : (0 : Candidate 1) ∈ remaining
          · by_cases h1 : (1 : Candidate 1) ∈ remaining
            · have hrem : remaining = Finset.univ := by
                ext c
                fin_cases c <;> simp [h0, h1, h2]
              simpa [hrem] using
                firstChoiceBranchWeighted_univ_cut_nonneg
                  0 hqMore_pos hq_lt 2
            · have hrem :
                  remaining =
                    ({(0 : Candidate 1), (2 : Candidate 1)} :
                      Finset (Candidate 1)) := by
                ext c
                fin_cases c <;> simp [h0, h1, h2]
              simpa [hrem] using
                firstChoiceBranchWeighted_pair02_cut_two_nonneg
                  hqMore_pos hq_lt
          · by_cases h1 : (1 : Candidate 1) ∈ remaining
            · have hrem :
                  remaining =
                    ({(1 : Candidate 1), (2 : Candidate 1)} :
                      Finset (Candidate 1)) := by
                ext c
                fin_cases c <;> simp [h0, h1, h2]
              simpa [hrem] using
                firstChoiceBranchWeighted_pair12_cut_two_nonneg
                  hqMore_pos hq_lt
            · have hzero :=
                firstChoiceBranchWeighted_prefixCut_eq_zero_of_forall_remaining_ge
                  0 qMore qLess hremaining (cut := 2) (by
                    intro c hc
                    fin_cases c <;> simp [h0, h1] at hc ⊢)
              rw [hzero]
        · have hzero :=
            firstChoiceBranchWeighted_prefixCut_eq_zero_of_forall_remaining_lt
              0 qMore qLess hremaining (cut := 2) (by
            intro c hc
            fin_cases c <;> simp [h2] at hc ⊢)
          rw [hzero]

theorem ReflMallowsBestInSetPrefixCutFirstChoiceAdjacentBoundary.zero
    {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) :
    ReflMallowsBestInSetPrefixCutFirstChoiceAdjacentBoundary
      0 qMore qLess :=
  ReflMallowsBestInSetPrefixCutFirstChoiceAdjacentBoundary.of_weighted
    (ReflMallowsBestInSetPrefixCutFirstChoiceWeighted.zero
      hqMore_pos hq_lt)

/-- On the full remaining set, best-in-set fiber weights are first-choice weights. -/
theorem reflMallowsBestInSetWeight_univ_eq_reflFirstWeight
    (n : ℕ) (q : ℝ) (c : Candidate n) :
    reflMallowsBestInSetWeight n q Finset.univ c =
      reflFirstWeight n q c := by
  classical
  unfold reflMallowsBestInSetWeight reflMallowsPayoffSum
    reflFirstWeight reflFirstChoiceFiber
  rw [Finset.sum_filter]
  simp [bestInSet_univ, mul_ite]
  rfl

/-- If exactly candidate `c` has been removed, `bestInSet` is the existing
two-firm `bestRemainingAfter`. -/
theorem bestInSet_univ_sdiff_singleton {n : ℕ} (π : Ranking n)
    (c : Candidate n) :
    bestInSet π (Finset.univ \ ({c} : Finset (Candidate n))) =
      bestRemainingAfter π c := by
  simpa [bestInSet, AppliedModelingLib.SocialChoice.Ranking.bestInSet,
      bestRemainingAfter, AppliedModelingLib.SocialChoice.Ranking.bestRemainingAfter] using
    AppliedModelingLib.SocialChoice.Ranking.bestInSet_univ_sdiff_singleton π c

/-- If exactly one candidate remains, that candidate is chosen under every ranking. -/
@[simp] theorem bestInSet_singleton {n : ℕ} (π : Ranking n)
    (c : Candidate n) :
    bestInSet π ({c} : Finset (Candidate n)) = c := by
  simpa [bestInSet, AppliedModelingLib.SocialChoice.Ranking.bestInSet] using
    AppliedModelingLib.SocialChoice.Ranking.bestInSet_singleton π c

theorem bestInSet_pair_eq_if_rank_lt {n : ℕ} (π : Ranking n)
    {c d : Candidate n} (hcd : c ≠ d) :
    bestInSet π ({c, d} : Finset (Candidate n)) =
      if rankOf π c < rankOf π d then c else d := by
  simpa [bestInSet, AppliedModelingLib.SocialChoice.Ranking.bestInSet,
      rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using
    AppliedModelingLib.SocialChoice.Ranking.bestInSet_pair_eq_if_rank_lt π hcd

/-- Expected value of the best remaining candidate under a ranking law. -/
noncomputable def expectedBestInSet {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (remaining : Finset (Candidate n)) : ℝ := pmfExp μ (fun π => value (bestInSet π remaining))

@[simp] theorem expectedBestInSet_univ {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedBestInSet μ value Finset.univ =
      expectedFirstMoverUtility μ value := by
  simpa [expectedBestInSet, AppliedModelingLib.SocialChoice.Ranking.expectedBestInSet,
      bestInSet, AppliedModelingLib.SocialChoice.Ranking.bestInSet,
      expectedFirstMoverUtility,
      AppliedModelingLib.SocialChoice.Ranking.expectedFirstMoverUtility] using
    AppliedModelingLib.SocialChoice.Ranking.expectedBestInSet_univ μ value

theorem expectedBestInSet_univ_sdiff_singleton {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) (c : Candidate n) :
    expectedBestInSet μ value
        (Finset.univ \ ({c} : Finset (Candidate n))) =
      AccuracyFamily.expectedBestAfterRemoval μ value c := by
  simpa [expectedBestInSet, AppliedModelingLib.SocialChoice.Ranking.expectedBestInSet,
      AccuracyFamily.expectedBestAfterRemoval,
      AppliedModelingLib.SocialChoice.Ranking.expectedBestAfterRemoval,
      bestInSet, AppliedModelingLib.SocialChoice.Ranking.bestInSet,
      bestRemainingAfter, AppliedModelingLib.SocialChoice.Ranking.bestRemainingAfter] using
    AppliedModelingLib.SocialChoice.Ranking.expectedBestInSet_univ_sdiff_singleton
      μ value c

@[simp] theorem expectedBestInSet_singleton {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (c : Candidate n) :
    expectedBestInSet μ value ({c} : Finset (Candidate n)) =
      value c := by
  simpa [expectedBestInSet, AppliedModelingLib.SocialChoice.Ranking.expectedBestInSet,
      bestInSet, AppliedModelingLib.SocialChoice.Ranking.bestInSet] using
    AppliedModelingLib.SocialChoice.Ranking.expectedBestInSet_singleton μ value c

namespace MallowsSpec

variable {n : ℕ} (M : MallowsSpec n)

theorem expectedBestInSet_pair_eq_pairCorrectProb
    (value : Candidate n → ℝ) {c d : Candidate n}
    (hcd : rankOf M.center c < rankOf M.center d) :
    expectedBestInSet M.law value ({c, d} : Finset (Candidate n)) =
      M.pairCorrectProb c d * value c +
        (1 - M.pairCorrectProb c d) * value d := by
  have hcd_shared :
      AppliedModelingLib.SocialChoice.Ranking.rankOf M.center c <
        AppliedModelingLib.SocialChoice.Ranking.rankOf M.center d := by
    simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hcd
  simpa [expectedBestInSet,
      AppliedModelingLib.SocialChoice.Ranking.expectedBestInSet,
      bestInSet, AppliedModelingLib.SocialChoice.Ranking.bestInSet,
      pairCorrectProb,
      AppliedModelingLib.SocialChoice.Ranking.MallowsSpec.pairCorrectProb,
      rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using
    (M.toShared).expectedBestInSet_pair_eq_pairCorrectProb value hcd_shared

theorem expectedBestInSet_pair_le_of_pairCorrectProb_le
    {Mmore Mless : MallowsSpec n} (hcenter : Mmore.center = Mless.center)
    {value : Candidate n → ℝ} {c d : Candidate n}
    (hcd : rankOf Mmore.center c < rankOf Mmore.center d)
    (hvalue : WeaklyOrderedBy Mmore.center value)
    (hprob : Mless.pairCorrectProb c d ≤ Mmore.pairCorrectProb c d) :
    expectedBestInSet Mless.law value ({c, d} : Finset (Candidate n)) ≤
      expectedBestInSet Mmore.law value ({c, d} : Finset (Candidate n)) := by
  have hcenter_shared :
      (Mmore.toShared).center = (Mless.toShared).center := by
    simpa using hcenter
  have hcd_shared :
      AppliedModelingLib.SocialChoice.Ranking.rankOf (Mmore.toShared).center c <
        AppliedModelingLib.SocialChoice.Ranking.rankOf (Mmore.toShared).center d := by
    simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hcd
  have hvalue_shared :
      AppliedModelingLib.SocialChoice.Ranking.WeaklyOrderedBy
        (Mmore.toShared).center value := by
    intro a b hab
    exact hvalue (by
      simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hab)
  have hprob_shared :
      (Mless.toShared).pairCorrectProb c d ≤
        (Mmore.toShared).pairCorrectProb c d := by
    simpa [pairCorrectProb,
      AppliedModelingLib.SocialChoice.Ranking.MallowsSpec.pairCorrectProb] using hprob
  simpa [expectedBestInSet,
      AppliedModelingLib.SocialChoice.Ranking.expectedBestInSet,
      bestInSet, AppliedModelingLib.SocialChoice.Ranking.bestInSet,
      pairCorrectProb,
      AppliedModelingLib.SocialChoice.Ranking.MallowsSpec.pairCorrectProb,
      rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using
    AppliedModelingLib.SocialChoice.Ranking.MallowsSpec.expectedBestInSet_pair_le_of_pairCorrectProb_le
        (Mmore := Mmore.toShared) (Mless := Mless.toShared)
        hcenter_shared hcd_shared hvalue_shared hprob_shared

theorem expectedBestInSet_pair_lt_of_pairCorrectProb_lt
    {Mmore Mless : MallowsSpec n} (hcenter : Mmore.center = Mless.center)
    {value : Candidate n → ℝ} {c d : Candidate n}
    (hcd : rankOf Mmore.center c < rankOf Mmore.center d)
    (hvalue : StrictlyOrderedBy Mmore.center value)
    (hprob : Mless.pairCorrectProb c d < Mmore.pairCorrectProb c d) :
    expectedBestInSet Mless.law value ({c, d} : Finset (Candidate n)) <
      expectedBestInSet Mmore.law value ({c, d} : Finset (Candidate n)) := by
  have hcenter_shared :
      (Mmore.toShared).center = (Mless.toShared).center := by
    simpa using hcenter
  have hcd_shared :
      AppliedModelingLib.SocialChoice.Ranking.rankOf (Mmore.toShared).center c <
        AppliedModelingLib.SocialChoice.Ranking.rankOf (Mmore.toShared).center d := by
    simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hcd
  have hvalue_shared :
      AppliedModelingLib.SocialChoice.Ranking.StrictlyOrderedBy
        (Mmore.toShared).center value := by
    intro a b hab
    exact hvalue (by
      simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hab)
  have hprob_shared :
      (Mless.toShared).pairCorrectProb c d <
        (Mmore.toShared).pairCorrectProb c d := by
    simpa [pairCorrectProb,
      AppliedModelingLib.SocialChoice.Ranking.MallowsSpec.pairCorrectProb] using hprob
  simpa [expectedBestInSet,
      AppliedModelingLib.SocialChoice.Ranking.expectedBestInSet,
      bestInSet, AppliedModelingLib.SocialChoice.Ranking.bestInSet,
      pairCorrectProb,
      AppliedModelingLib.SocialChoice.Ranking.MallowsSpec.pairCorrectProb,
      rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using
    AppliedModelingLib.SocialChoice.Ranking.MallowsSpec.expectedBestInSet_pair_lt_of_pairCorrectProb_lt
        (Mmore := Mmore.toShared) (Mless := Mless.toShared)
        hcenter_shared hcd_shared hvalue_shared hprob_shared

/-- Unnormalized Mallows weight of rankings whose best candidate in `remaining`
is `c`. -/
noncomputable def bestInSetWeight
    (remaining : Finset (Candidate n)) (c : Candidate n) : ℝ :=
  ∑ π : Ranking n,
    if c = bestInSet π remaining then mallowsWeight M.q M.center π else 0

@[simp] theorem toShared_bestInSetWeight
    (remaining : Finset (Candidate n)) (c : Candidate n) :
    (M.toShared).bestInSetWeight remaining c =
      M.bestInSetWeight remaining c := by
  simp [bestInSetWeight,
    toShared,
    AppliedModelingLib.SocialChoice.Ranking.MallowsSpec.bestInSetWeight,
    shared_bestInSet_eq,
    mallowsWeight, AppliedModelingLib.SocialChoice.Ranking.mallowsWeight,
    kendallTau, AppliedModelingLib.SocialChoice.Ranking.kendallTau,
    inversionFinset, AppliedModelingLib.SocialChoice.Ranking.inversionFinset,
    invertedPair, AppliedModelingLib.SocialChoice.Ranking.invertedPair,
    rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf]
  rfl

/-- On a center-ordered pair, the better candidate's best-in-set fiber is the
usual pair-correct Mallows weight. -/
theorem bestInSetWeight_pair_eq_pairCorrectWeight
    {c d : Candidate n} (hcd : rankOf M.center c < rankOf M.center d) :
    M.bestInSetWeight ({c, d} : Finset (Candidate n)) c =
      M.pairCorrectWeight c d := by
  have hcd_shared :
      AppliedModelingLib.SocialChoice.Ranking.rankOf (M.toShared).center c <
        AppliedModelingLib.SocialChoice.Ranking.rankOf (M.toShared).center d := by
    simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hcd
  simpa using
    (M.toShared).bestInSetWeight_pair_eq_pairCorrectWeight hcd_shared

/-- On a center-ordered pair, the worse candidate's best-in-set fiber is the
usual pair-wrong Mallows weight. -/
theorem bestInSetWeight_pair_eq_pairWrongWeight
    {c d : Candidate n} (hcd : rankOf M.center c < rankOf M.center d) :
    M.bestInSetWeight ({c, d} : Finset (Candidate n)) d =
      M.pairWrongWeight c d := by
  have hcd_shared :
      AppliedModelingLib.SocialChoice.Ranking.rankOf (M.toShared).center c <
        AppliedModelingLib.SocialChoice.Ranking.rankOf (M.toShared).center d := by
    simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hcd
  simpa using
    (M.toShared).bestInSetWeight_pair_eq_pairWrongWeight hcd_shared

/-- Pair-position reductions imply the best-in-set fiber cross inequality on a
two-element remaining set. -/
theorem bestInSetWeight_pair_cross_pos_of_pairPositionReduction
    {Mmore Mless : MallowsSpec n} {m : ℕ} {c d : Candidate n}
    (hcd_more : rankOf Mmore.center c < rankOf Mmore.center d)
    (hcd_less : rankOf Mless.center c < rankOf Mless.center d)
    (red_more : PairPositionReduction Mmore c d m)
    (red_less : PairPositionReduction Mless c d m)
    (hq_lt : Mmore.q < Mless.q) :
    0 <
      Mmore.bestInSetWeight ({c, d} : Finset (Candidate n)) c *
          Mless.bestInSetWeight ({c, d} : Finset (Candidate n)) d -
        Mmore.bestInSetWeight ({c, d} : Finset (Candidate n)) d *
          Mless.bestInSetWeight ({c, d} : Finset (Candidate n)) c := by
  rw [Mmore.bestInSetWeight_pair_eq_pairCorrectWeight hcd_more,
    Mless.bestInSetWeight_pair_eq_pairWrongWeight hcd_less,
    Mmore.bestInSetWeight_pair_eq_pairWrongWeight hcd_more,
    Mless.bestInSetWeight_pair_eq_pairCorrectWeight hcd_less]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (pairWeight_cross_pos_of_pairPositionReduction
      red_more red_less hq_lt)

/-- The concrete identity-center `MallowsSpec` fiber is the local refl fiber sum. -/
theorem bestInSetWeight_ofQ_refl
    (q : ℝ) (hq : 0 < q)
    (remaining : Finset (Candidate n)) (c : Candidate n) :
    (MallowsSpec.ofQ (Equiv.refl (Candidate n)) q hq).bestInSetWeight
        remaining c =
      reflMallowsBestInSetWeight n q remaining c := by
  classical
  unfold bestInSetWeight reflMallowsBestInSetWeight reflMallowsPayoffSum
  refine Finset.sum_congr rfl ?_
  intro π _
  by_cases h : c = bestInSet π remaining
  · simp [MallowsSpec.ofQ, mallowsWeight, h]
  · simp [h]

/--
Relabeling candidates by center rank turns arbitrary-center best-in-set fibers
into identity-center fiber weights.
-/
theorem bestInSetWeight_eq_reflMallowsBestInSetWeight_centerCoords
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty)
    (c : Candidate n) :
    M.bestInSetWeight remaining c =
      reflMallowsBestInSetWeight n M.q
        (remaining.image (rankOf M.center)) (rankOf M.center c) := by
  classical
  unfold bestInSetWeight reflMallowsBestInSetWeight reflMallowsPayoffSum
  calc
    (∑ π : Ranking n,
        if c = bestInSet π remaining then mallowsWeight M.q M.center π else 0)
        =
      ∑ τ : Ranking n,
        if c = bestInSet (τ.trans M.center) remaining then
          mallowsWeight M.q M.center (τ.trans M.center)
        else
          0 := by
        simpa using
          (Equiv.sum_comp (rankingRightTransEquiv M.center)
            (fun π : Ranking n =>
              if c = bestInSet π remaining then
                mallowsWeight M.q M.center π
              else
                0)).symm
    _ =
      ∑ τ : Ranking n,
        M.q ^ kendallTau (Equiv.refl (Candidate n)) τ *
          (if rankOf M.center c =
              bestInSet τ (remaining.image (rankOf M.center)) then
            (1 : ℝ)
          else
            0) := by
        refine Finset.sum_congr rfl ?_
        intro τ _
        have hcoord :=
          bestInSet_trans_center_symm M.center (τ.trans M.center)
            hremaining
        have htrans :
            (τ.trans M.center).trans M.center.symm = τ := by
          ext x
          simp
        rw [htrans] at hcoord
        have hbest :
            bestInSet (τ.trans M.center) remaining =
              M.center
                (bestInSet τ (remaining.image (rankOf M.center))) := by
          calc
            bestInSet (τ.trans M.center) remaining =
                M.center (rankOf M.center
                  (bestInSet (τ.trans M.center) remaining)) := by
                  simp [rankOf]
            _ = M.center
                (bestInSet τ (remaining.image (rankOf M.center))) := by
                  rw [← hcoord]
        have hiff :
            c = bestInSet (τ.trans M.center) remaining ↔
              rankOf M.center c =
                bestInSet τ (remaining.image (rankOf M.center)) := by
          rw [hbest]
          constructor
          · intro h
            rw [h]
            simp [rankOf]
          · intro h
            calc
              c = M.center (rankOf M.center c) := by
                    simp [rankOf]
              _ =
                  M.center
                    (bestInSet τ (remaining.image (rankOf M.center))) := by
                    rw [h]
        have hkend :
            kendallTau M.center (τ.trans M.center) =
              kendallTau (Equiv.refl (Candidate n)) τ :=
          kendallTau_center_trans M.center τ
        by_cases h :
            rankOf M.center c =
              bestInSet τ (remaining.image (rankOf M.center))
        · rw [if_pos (hiff.mpr h), if_pos h]
          simp [mallowsWeight, hkend]
        · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]
          ring

/--
Reindex a best-in-set fiber by swapping two remaining candidates.  This is the
finite-sum normal form for the remaining Mallows MLR proof: the `c` fiber is the
image of the `d` fiber under the candidate-position swap.
-/
theorem bestInSetWeight_eq_sum_swapCandidatePositions
    (remaining : Finset (Candidate n)) {c d : Candidate n}
    (hc : c ∈ remaining) (hd : d ∈ remaining) :
    M.bestInSetWeight remaining c =
      ∑ π : Ranking n,
        if d = bestInSet π remaining then
          mallowsWeight M.q M.center (swapCandidatePositions π c d)
        else
          0 := by
  have hshared :=
    (M.toShared).bestInSetWeight_eq_sum_swapCandidatePositions
      remaining hc hd
  rw [M.toShared_bestInSetWeight remaining c] at hshared
  convert hshared using 1

/-- Best-in-set fiber weights are nonnegative. -/
theorem bestInSetWeight_nonneg
    (remaining : Finset (Candidate n)) (c : Candidate n) :
    0 ≤ M.bestInSetWeight remaining c := by
  simpa using (M.toShared).bestInSetWeight_nonneg remaining c

/-- A candidate outside a nonempty remaining set has zero best-in-set mass. -/
theorem bestInSetWeight_eq_zero_of_not_mem
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty)
    {c : Candidate n} (hc : c ∉ remaining) :
    M.bestInSetWeight remaining c = 0 := by
  simpa using (M.toShared).bestInSetWeight_eq_zero_of_not_mem hremaining hc

/--
Double-sum reduction for the best-in-set fiber cross-ratio.

After reindexing the `c`-best fibers by the `c`/`d` position swap, the whole
cross-ratio is a sum over two rankings in the `d`-best fiber.  This is the
finite algebraic target left by the swap/Kendall construction.
-/
theorem bestInSetWeight_cross_nonneg_of_swap_pairwise_cross
    {Mmore Mless : MallowsSpec n} (remaining : Finset (Candidate n))
    {c d : Candidate n} (hc : c ∈ remaining) (hd : d ∈ remaining)
    (hpair :
      ∀ π σ : Ranking n,
        d = bestInSet π remaining →
        d = bestInSet σ remaining →
        0 ≤
          mallowsWeight Mmore.q Mmore.center
              (swapCandidatePositions π c d) *
            mallowsWeight Mless.q Mless.center σ -
          mallowsWeight Mmore.q Mmore.center π *
            mallowsWeight Mless.q Mless.center
              (swapCandidatePositions σ c d)) :
    0 ≤
      Mmore.bestInSetWeight remaining c *
          Mless.bestInSetWeight remaining d -
        Mmore.bestInSetWeight remaining d *
          Mless.bestInSetWeight remaining c := by
  have hpair_shared :
      ∀ π σ : Ranking n,
        d = AppliedModelingLib.SocialChoice.Ranking.bestInSet π remaining →
        d = AppliedModelingLib.SocialChoice.Ranking.bestInSet σ remaining →
        0 ≤
          AppliedModelingLib.SocialChoice.Ranking.mallowsWeight
              Mmore.toShared.q Mmore.toShared.center
              (AppliedModelingLib.SocialChoice.Ranking.swapCandidatePositions π c d) *
            AppliedModelingLib.SocialChoice.Ranking.mallowsWeight
              Mless.toShared.q Mless.toShared.center σ -
          AppliedModelingLib.SocialChoice.Ranking.mallowsWeight
              Mmore.toShared.q Mmore.toShared.center π *
            AppliedModelingLib.SocialChoice.Ranking.mallowsWeight
              Mless.toShared.q Mless.toShared.center
              (AppliedModelingLib.SocialChoice.Ranking.swapCandidatePositions σ c d) := by
    intro π σ hπ hσ
    have hπ_local : d = bestInSet π remaining := by
      simpa [shared_bestInSet_eq] using hπ
    have hσ_local : d = bestInSet σ remaining := by
      simpa [shared_bestInSet_eq] using hσ
    convert hpair π σ hπ_local hσ_local using 1
  simpa [toShared_bestInSetWeight] using
    AppliedModelingLib.SocialChoice.Ranking.MallowsSpec.bestInSetWeight_cross_nonneg_of_swap_pairwise_cross
        (Mmore := Mmore.toShared) (Mless := Mless.toShared)
        remaining hc hd hpair_shared

/-- The best-in-set fibers partition the Mallows partition. -/
theorem sum_bestInSetWeight_eq_partition
    (remaining : Finset (Candidate n)) :
    (∑ c : Candidate n, M.bestInSetWeight remaining c) = M.partition := by
  simpa [toShared, toShared_bestInSetWeight] using
    (M.toShared).sum_bestInSetWeight_eq_partition remaining

/-- The probability that a candidate is best in a remaining set is its
normalized Mallows best-in-set fiber mass. -/
theorem bestInSetProbability_eq_weight_div_partition
    {n : ℕ} (M : MallowsSpec n)
    (remaining : Finset (Candidate n)) (c : Candidate n) :
    pmfProb M.law (fun pi => c = bestInSet pi remaining) =
      M.bestInSetWeight remaining c / M.partition := by
  classical
  unfold pmfProb pmfExp MallowsSpec.bestInSetWeight
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro pi _
  rw [M.law_apply_toReal]
  by_cases h : c = bestInSet pi remaining <;> simp [h]

/-- Expected best-in-set value in terms of unnormalized Mallows fibers. -/
theorem expectedBestInSet_eq_sum_bestInSetWeight_div_partition
    (value : Candidate n → ℝ) (remaining : Finset (Candidate n)) :
    expectedBestInSet M.law value remaining =
      (∑ c : Candidate n, M.bestInSetWeight remaining c * value c) /
        M.partition := by
  simpa [toShared, expectedBestInSet,
      AppliedModelingLib.SocialChoice.Ranking.expectedBestInSet,
      shared_bestInSet_eq, toShared_bestInSetWeight] using
    (M.toShared).expectedBestInSet_eq_sum_bestInSetWeight_div_partition
      value remaining

/--
Identity-center coordinate form of the expected best-in-set payoff.  Relabeling
each ranking by the Mallows center turns the center into `refl`, and relabels
the remaining set by center ranks.
-/
theorem expectedBestInSet_eq_reflMallowsPayoffSum_centerCoords
    (value : Candidate n → ℝ) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) :
    expectedBestInSet M.law value remaining =
      reflMallowsPayoffSum n M.q
        (fun τ : Ranking n =>
          value (M.center
            (bestInSet τ (remaining.image (rankOf M.center))))) /
        M.partition := by
  classical
  unfold expectedBestInSet pmfExp reflMallowsPayoffSum
  calc
    (∑ π : Ranking n, (M.law π).toReal * value (bestInSet π remaining))
        =
      ∑ π : Ranking n,
        (mallowsWeight M.q M.center π / M.partition) *
          value (bestInSet π remaining) := by
        refine Finset.sum_congr rfl ?_
        intro π _
        rw [M.law_apply_toReal]
    _ =
      ∑ π : Ranking n,
        (mallowsWeight M.q M.center π *
          value (bestInSet π remaining)) / M.partition := by
        refine Finset.sum_congr rfl ?_
        intro π _
        ring
    _ =
      (∑ π : Ranking n,
        mallowsWeight M.q M.center π *
          value (bestInSet π remaining)) / M.partition := by
        rw [Finset.sum_div]
    _ =
      (∑ τ : Ranking n,
        mallowsWeight M.q M.center (τ.trans M.center) *
          value (bestInSet (τ.trans M.center) remaining)) /
        M.partition := by
        congr 1
        simpa using
          (Equiv.sum_comp (rankingRightTransEquiv M.center)
            (fun π : Ranking n =>
              mallowsWeight M.q M.center π *
                value (bestInSet π remaining))).symm
    _ =
      (∑ τ : Ranking n,
        M.q ^ kendallTau (Equiv.refl (Candidate n)) τ *
          value (M.center
            (bestInSet τ (remaining.image (rankOf M.center))))) /
        M.partition := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro τ _
        have hcoord :=
          bestInSet_trans_center_symm M.center (τ.trans M.center)
            hremaining
        have htrans :
            (τ.trans M.center).trans M.center.symm = τ := by
          ext x
          simp
        rw [htrans] at hcoord
        have hbest :
            bestInSet (τ.trans M.center) remaining =
              M.center
                (bestInSet τ (remaining.image (rankOf M.center))) := by
          calc
            bestInSet (τ.trans M.center) remaining =
                M.center (rankOf M.center
                  (bestInSet (τ.trans M.center) remaining)) := by
                  simp [rankOf]
            _ = M.center
                (bestInSet τ (remaining.image (rankOf M.center))) := by
                  rw [← hcoord]
        have hkend :
            kendallTau M.center (τ.trans M.center) =
              kendallTau (Equiv.refl (Candidate n)) τ :=
          kendallTau_center_trans M.center τ
        simp [mallowsWeight, hbest, hkend]

end MallowsSpec

/--
Cross-ratio dominance of the best-in-set Mallows fibers lifts to expected
best-of-remaining-set utility dominance.

This is the exact algebraic bridge still needed to make Theorem 4
assumption-free for arbitrary histories.
-/
theorem expectedBestInSet_le_of_bestInSetWeight_cross
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (remaining : Finset (Candidate n)) {value : Candidate n → ℝ}
    (hvalue : WeaklyOrderedBy Mmore.center value)
    (hcross :
      ∀ c d : Candidate n, rankOf Mmore.center c < rankOf Mmore.center d →
        0 ≤
          Mmore.bestInSetWeight remaining c *
              Mless.bestInSetWeight remaining d -
            Mmore.bestInSetWeight remaining d *
              Mless.bestInSetWeight remaining c) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining := by
  have hvalue_shared :
      AppliedModelingLib.SocialChoice.Ranking.WeaklyOrderedBy
        Mmore.toShared.center value := by
    intro a b hab
    exact hvalue (by
      simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hab)
  have hcross_shared :
      ∀ c d : Candidate n,
        AppliedModelingLib.SocialChoice.Ranking.rankOf Mmore.toShared.center c <
          AppliedModelingLib.SocialChoice.Ranking.rankOf Mmore.toShared.center d →
        0 ≤
          Mmore.toShared.bestInSetWeight remaining c *
              Mless.toShared.bestInSetWeight remaining d -
            Mmore.toShared.bestInSetWeight remaining d *
              Mless.toShared.bestInSetWeight remaining c := by
    intro c d hcd
    have hcd_local : rankOf Mmore.center c < rankOf Mmore.center d := by
      simpa [rankOf, AppliedModelingLib.SocialChoice.Ranking.rankOf] using hcd
    simpa [MallowsSpec.toShared_bestInSetWeight] using
      hcross c d hcd_local
  simpa [expectedBestInSet,
      AppliedModelingLib.SocialChoice.Ranking.expectedBestInSet,
      shared_bestInSet_eq] using
    AppliedModelingLib.SocialChoice.Ranking.expectedBestInSet_le_of_bestInSetWeight_cross
      (Mmore := Mmore.toShared) (Mless := Mless.toShared)
      remaining hvalue_shared hcross_shared

/-- Identity-center two-candidate best-in-set fibers satisfy a strict Mallows
cross inequality.  This is the pair case of the remaining arbitrary-set MLR
target. -/
theorem reflMallowsBestInSetWeight_pair_cross_pos
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) {c d : Candidate n} (hcd : c < d) :
    0 <
      reflMallowsBestInSetWeight n qMore
          ({c, d} : Finset (Candidate n)) c *
        reflMallowsBestInSetWeight n qLess
          ({c, d} : Finset (Candidate n)) d -
      reflMallowsBestInSetWeight n qMore
          ({c, d} : Finset (Candidate n)) d *
        reflMallowsBestInSetWeight n qLess
          ({c, d} : Finset (Candidate n)) c := by
  classical
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  let Mmore : MallowsSpec n :=
    MallowsSpec.ofQ (Equiv.refl (Candidate n)) qMore hqMore_pos
  let Mless : MallowsSpec n :=
    MallowsSpec.ofQ (Equiv.refl (Candidate n)) qLess hqLess_pos
  have hcd_more : rankOf Mmore.center c < rankOf Mmore.center d := by
    simpa [Mmore, MallowsSpec.ofQ, rankOf] using hcd
  have hcd_less : rankOf Mless.center c < rankOf Mless.center d := by
    simpa [Mless, MallowsSpec.ofQ, rankOf] using hcd
  let m : ℕ := (d : ℕ) - (c : ℕ) - 1
  have red_more : PairPositionReduction Mmore c d m := by
    simpa [Mmore, MallowsSpec.ofQ, rankOf, m] using
      Mmore.pairPositionReduction_of_center_lt hcd_more
  have red_less : PairPositionReduction Mless c d m := by
    simpa [Mless, MallowsSpec.ofQ, rankOf, m] using
      Mless.pairPositionReduction_of_center_lt hcd_less
  have hcross :
      0 <
        Mmore.bestInSetWeight ({c, d} : Finset (Candidate n)) c *
            Mless.bestInSetWeight ({c, d} : Finset (Candidate n)) d -
          Mmore.bestInSetWeight ({c, d} : Finset (Candidate n)) d *
            Mless.bestInSetWeight ({c, d} : Finset (Candidate n)) c :=
    MallowsSpec.bestInSetWeight_pair_cross_pos_of_pairPositionReduction
      hcd_more hcd_less red_more red_less hq_lt
  dsimp [Mmore, Mless] at hcross
  rw [MallowsSpec.bestInSetWeight_ofQ_refl
        (n := n) qMore hqMore_pos ({c, d} : Finset (Candidate n)) c,
      MallowsSpec.bestInSetWeight_ofQ_refl
        (n := n) qLess hqLess_pos ({c, d} : Finset (Candidate n)) d,
      MallowsSpec.bestInSetWeight_ofQ_refl
        (n := n) qMore hqMore_pos ({c, d} : Finset (Candidate n)) d,
      MallowsSpec.bestInSetWeight_ofQ_refl
        (n := n) qLess hqLess_pos ({c, d} : Finset (Candidate n)) c] at hcross
  exact hcross

/--
Identity-center MLR target for best-in-set fibers.  This is narrower than the
generic adjacent-swap stochastic-dominance interface: it asks only that the
candidate distribution induced by `bestInSet` has monotone likelihood ratios in
the center order.
-/
def ReflMallowsBestInSetWeightMLR
    (n : ℕ) (qMore qLess : ℝ) : Prop :=
  ∀ {remaining : Finset (Candidate n)}, remaining.Nonempty →
    ∀ {c d : Candidate n}, c ∈ remaining → d ∈ remaining → c < d →
      0 ≤
        reflMallowsBestInSetWeight n qMore remaining c *
            reflMallowsBestInSetWeight n qLess remaining d -
          reflMallowsBestInSetWeight n qMore remaining d *
            reflMallowsBestInSetWeight n qLess remaining c

/-- A single tail fiber cross inequality lifts when the center-best candidate
is absent from the larger remaining set. -/
theorem reflMallowsBestInSetWeight_cross_nonneg_succ_of_zero_not_mem
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hzero : (0 : Candidate (n + 1)) ∉ remaining)
    {c d : Candidate n}
    (htail_cross :
      0 ≤
        reflMallowsBestInSetWeight n qMore
            (tailRemainingOf remaining) c *
          reflMallowsBestInSetWeight n qLess
            (tailRemainingOf remaining) d -
        reflMallowsBestInSetWeight n qMore
            (tailRemainingOf remaining) d *
          reflMallowsBestInSetWeight n qLess
            (tailRemainingOf remaining) c) :
    0 ≤
      reflMallowsBestInSetWeight (n + 1) qMore remaining c.succ *
          reflMallowsBestInSetWeight (n + 1) qLess remaining d.succ -
        reflMallowsBestInSetWeight (n + 1) qMore remaining d.succ *
          reflMallowsBestInSetWeight (n + 1) qLess remaining c.succ := by
  classical
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hPMore_nonneg :
      0 ≤ candidateRankPowerSum (n + 1) qMore :=
    le_of_lt (candidateRankPowerSum_pos (n + 1) hqMore_pos)
  have hPLess_nonneg :
      0 ≤ candidateRankPowerSum (n + 1) qLess :=
    le_of_lt (candidateRankPowerSum_pos (n + 1) hqLess_pos)
  rw [reflMallowsBestInSetWeight_eq_tail_of_zero_not_mem
        qMore hremaining hzero c,
      reflMallowsBestInSetWeight_eq_tail_of_zero_not_mem
        qLess hremaining hzero d,
      reflMallowsBestInSetWeight_eq_tail_of_zero_not_mem
        qMore hremaining hzero d,
      reflMallowsBestInSetWeight_eq_tail_of_zero_not_mem
        qLess hremaining hzero c]
  have hfactor :
      (candidateRankPowerSum (n + 1) qMore *
            reflMallowsBestInSetWeight n qMore
              (tailRemainingOf remaining) c) *
          (candidateRankPowerSum (n + 1) qLess *
            reflMallowsBestInSetWeight n qLess
              (tailRemainingOf remaining) d) -
        (candidateRankPowerSum (n + 1) qMore *
            reflMallowsBestInSetWeight n qMore
              (tailRemainingOf remaining) d) *
          (candidateRankPowerSum (n + 1) qLess *
            reflMallowsBestInSetWeight n qLess
              (tailRemainingOf remaining) c) =
        (candidateRankPowerSum (n + 1) qMore *
            candidateRankPowerSum (n + 1) qLess) *
          (reflMallowsBestInSetWeight n qMore
                (tailRemainingOf remaining) c *
              reflMallowsBestInSetWeight n qLess
                (tailRemainingOf remaining) d -
            reflMallowsBestInSetWeight n qMore
                (tailRemainingOf remaining) d *
              reflMallowsBestInSetWeight n qLess
                (tailRemainingOf remaining) c) := by
    ring
  rw [hfactor]
  exact mul_nonneg
    (mul_nonneg hPMore_nonneg hPLess_nonneg) htail_cross

/-- A single initial fiber cross inequality lifts when the center-worst
candidate is absent from the larger remaining set. -/
theorem reflMallowsBestInSetWeight_cross_nonneg_castSucc_of_last_not_mem
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hlast : reflLastCandidate (n + 1) ∉ remaining)
    {c d : Candidate n}
    (hinit_cross :
      0 ≤
        reflMallowsBestInSetWeight n qMore
            (initRemainingOf remaining) c *
          reflMallowsBestInSetWeight n qLess
            (initRemainingOf remaining) d -
        reflMallowsBestInSetWeight n qMore
            (initRemainingOf remaining) d *
          reflMallowsBestInSetWeight n qLess
            (initRemainingOf remaining) c) :
    0 ≤
      reflMallowsBestInSetWeight (n + 1) qMore remaining c.castSucc *
          reflMallowsBestInSetWeight (n + 1) qLess remaining d.castSucc -
        reflMallowsBestInSetWeight (n + 1) qMore remaining d.castSucc *
          reflMallowsBestInSetWeight (n + 1) qLess remaining c.castSucc := by
  classical
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hPMore_nonneg :
      0 ≤ candidateRankReversePowerSum (n + 1) qMore :=
    le_of_lt (candidateRankReversePowerSum_pos (n + 1) hqMore_pos)
  have hPLess_nonneg :
      0 ≤ candidateRankReversePowerSum (n + 1) qLess :=
    le_of_lt (candidateRankReversePowerSum_pos (n + 1) hqLess_pos)
  rw [reflMallowsBestInSetWeight_eq_init_of_last_not_mem
        qMore hremaining hlast c,
      reflMallowsBestInSetWeight_eq_init_of_last_not_mem
        qLess hremaining hlast d,
      reflMallowsBestInSetWeight_eq_init_of_last_not_mem
        qMore hremaining hlast d,
      reflMallowsBestInSetWeight_eq_init_of_last_not_mem
        qLess hremaining hlast c]
  have hfactor :
      (candidateRankReversePowerSum (n + 1) qMore *
            reflMallowsBestInSetWeight n qMore
              (initRemainingOf remaining) c) *
          (candidateRankReversePowerSum (n + 1) qLess *
            reflMallowsBestInSetWeight n qLess
              (initRemainingOf remaining) d) -
        (candidateRankReversePowerSum (n + 1) qMore *
            reflMallowsBestInSetWeight n qMore
              (initRemainingOf remaining) d) *
          (candidateRankReversePowerSum (n + 1) qLess *
            reflMallowsBestInSetWeight n qLess
              (initRemainingOf remaining) c) =
        (candidateRankReversePowerSum (n + 1) qMore *
            candidateRankReversePowerSum (n + 1) qLess) *
          (reflMallowsBestInSetWeight n qMore
                (initRemainingOf remaining) c *
              reflMallowsBestInSetWeight n qLess
                (initRemainingOf remaining) d -
            reflMallowsBestInSetWeight n qMore
                (initRemainingOf remaining) d *
              reflMallowsBestInSetWeight n qLess
                (initRemainingOf remaining) c) := by
    ring
  rw [hfactor]
  exact mul_nonneg
    (mul_nonneg hPMore_nonneg hPLess_nonneg) hinit_cross

/-- If the center-best candidate is absent, fiber MLR lifts from the tail
candidate universe by the exact common-scale deletion formula. -/
theorem reflMallowsBestInSetWeight_cross_nonneg_of_zero_not_mem
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    (hmlr : ReflMallowsBestInSetWeightMLR n qMore qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hzero : (0 : Candidate (n + 1)) ∉ remaining)
    {c d : Candidate (n + 1)} (hc : c ∈ remaining) (hd : d ∈ remaining)
    (hcd : c < d) :
    0 ≤
      reflMallowsBestInSetWeight (n + 1) qMore remaining c *
          reflMallowsBestInSetWeight (n + 1) qLess remaining d -
        reflMallowsBestInSetWeight (n + 1) qMore remaining d *
          reflMallowsBestInSetWeight (n + 1) qLess remaining c := by
  classical
  cases c using Fin.cases with
  | zero =>
      exact False.elim (hzero hc)
  | succ ctail =>
      cases d using Fin.cases with
      | zero =>
          exact False.elim ((not_lt_of_ge (Fin.zero_le ctail.succ)) hcd)
      | succ dtail =>
          have htail :
              (tailRemainingOf remaining).Nonempty :=
            tailRemainingOf_nonempty_of_nonempty_of_zero_not_mem
              hremaining hzero
          have hc_tail : ctail ∈ tailRemainingOf remaining :=
            (mem_tailRemainingOf (remaining := remaining)
              (c := ctail)).mpr hc
          have hd_tail : dtail ∈ tailRemainingOf remaining :=
            (mem_tailRemainingOf (remaining := remaining)
              (c := dtail)).mpr hd
          have hcd_tail : ctail < dtail := by
            rw [Fin.lt_def] at hcd ⊢
            simpa [Fin.val_succ] using (Nat.succ_lt_succ_iff.mp hcd)
          have htail_cross :=
            hmlr htail hc_tail hd_tail hcd_tail
          have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
          have hPMore_nonneg :
              0 ≤ candidateRankPowerSum (n + 1) qMore :=
            le_of_lt (candidateRankPowerSum_pos (n + 1) hqMore_pos)
          have hPLess_nonneg :
              0 ≤ candidateRankPowerSum (n + 1) qLess :=
            le_of_lt (candidateRankPowerSum_pos (n + 1) hqLess_pos)
          rw [reflMallowsBestInSetWeight_eq_tail_of_zero_not_mem
                qMore hremaining hzero ctail,
              reflMallowsBestInSetWeight_eq_tail_of_zero_not_mem
                qLess hremaining hzero dtail,
              reflMallowsBestInSetWeight_eq_tail_of_zero_not_mem
                qMore hremaining hzero dtail,
              reflMallowsBestInSetWeight_eq_tail_of_zero_not_mem
                qLess hremaining hzero ctail]
          have hfactor :
              (candidateRankPowerSum (n + 1) qMore *
                    reflMallowsBestInSetWeight n qMore
                      (tailRemainingOf remaining) ctail) *
                  (candidateRankPowerSum (n + 1) qLess *
                    reflMallowsBestInSetWeight n qLess
                      (tailRemainingOf remaining) dtail) -
                (candidateRankPowerSum (n + 1) qMore *
                    reflMallowsBestInSetWeight n qMore
                      (tailRemainingOf remaining) dtail) *
                  (candidateRankPowerSum (n + 1) qLess *
                    reflMallowsBestInSetWeight n qLess
                      (tailRemainingOf remaining) ctail) =
                (candidateRankPowerSum (n + 1) qMore *
                    candidateRankPowerSum (n + 1) qLess) *
                  (reflMallowsBestInSetWeight n qMore
                        (tailRemainingOf remaining) ctail *
                      reflMallowsBestInSetWeight n qLess
                        (tailRemainingOf remaining) dtail -
                    reflMallowsBestInSetWeight n qMore
                        (tailRemainingOf remaining) dtail *
                      reflMallowsBestInSetWeight n qLess
                        (tailRemainingOf remaining) ctail) := by
            ring
          rw [hfactor]
          exact mul_nonneg
            (mul_nonneg hPMore_nonneg hPLess_nonneg) htail_cross

/-- If the center-worst candidate is absent, fiber MLR lifts from the initial
candidate universe by the exact common-scale deletion formula. -/
theorem reflMallowsBestInSetWeight_cross_nonneg_of_last_not_mem
    {n : ℕ} {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    (hmlr : ReflMallowsBestInSetWeightMLR n qMore qLess)
    {remaining : Finset (Candidate (n + 1))}
    (hremaining : remaining.Nonempty)
    (hlast : reflLastCandidate (n + 1) ∉ remaining)
    {c d : Candidate (n + 1)} (hc : c ∈ remaining) (hd : d ∈ remaining)
    (hcd : c < d) :
    0 ≤
      reflMallowsBestInSetWeight (n + 1) qMore remaining c *
          reflMallowsBestInSetWeight (n + 1) qLess remaining d -
        reflMallowsBestInSetWeight (n + 1) qMore remaining d *
          reflMallowsBestInSetWeight (n + 1) qLess remaining c := by
  classical
  have hc_ne_last : c ≠ reflLastCandidate (n + 1) := by
    intro h
    exact hlast (by simpa [h] using hc)
  have hd_ne_last : d ≠ reflLastCandidate (n + 1) := by
    intro h
    exact hlast (by simpa [h] using hd)
  rcases Fin.eq_castSucc_of_ne_last
      (x := c) (by simpa [reflLastCandidate] using hc_ne_last)
      with ⟨ctail, hc_eq⟩
  rcases Fin.eq_castSucc_of_ne_last
      (x := d) (by simpa [reflLastCandidate] using hd_ne_last)
      with ⟨dtail, hd_eq⟩
  subst c
  subst d
  have hinit :
      (initRemainingOf remaining).Nonempty :=
    initRemainingOf_nonempty_of_nonempty_of_last_not_mem
      hremaining hlast
  have hc_init : ctail ∈ initRemainingOf remaining :=
    (mem_initRemainingOf (remaining := remaining)
      (c := ctail)).mpr hc
  have hd_init : dtail ∈ initRemainingOf remaining :=
    (mem_initRemainingOf (remaining := remaining)
      (c := dtail)).mpr hd
  have hcd_init : ctail < dtail :=
    Fin.castSucc_lt_castSucc_iff.mp hcd
  have hinit_cross :=
    hmlr hinit hc_init hd_init hcd_init
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hPMore_nonneg :
      0 ≤ candidateRankReversePowerSum (n + 1) qMore :=
    le_of_lt (candidateRankReversePowerSum_pos (n + 1) hqMore_pos)
  have hPLess_nonneg :
      0 ≤ candidateRankReversePowerSum (n + 1) qLess :=
    le_of_lt (candidateRankReversePowerSum_pos (n + 1) hqLess_pos)
  rw [reflMallowsBestInSetWeight_eq_init_of_last_not_mem
        qMore hremaining hlast ctail,
      reflMallowsBestInSetWeight_eq_init_of_last_not_mem
        qLess hremaining hlast dtail,
      reflMallowsBestInSetWeight_eq_init_of_last_not_mem
        qMore hremaining hlast dtail,
      reflMallowsBestInSetWeight_eq_init_of_last_not_mem
        qLess hremaining hlast ctail]
  have hfactor :
      (candidateRankReversePowerSum (n + 1) qMore *
            reflMallowsBestInSetWeight n qMore
              (initRemainingOf remaining) ctail) *
          (candidateRankReversePowerSum (n + 1) qLess *
            reflMallowsBestInSetWeight n qLess
              (initRemainingOf remaining) dtail) -
        (candidateRankReversePowerSum (n + 1) qMore *
            reflMallowsBestInSetWeight n qMore
              (initRemainingOf remaining) dtail) *
          (candidateRankReversePowerSum (n + 1) qLess *
            reflMallowsBestInSetWeight n qLess
              (initRemainingOf remaining) ctail) =
        (candidateRankReversePowerSum (n + 1) qMore *
            candidateRankReversePowerSum (n + 1) qLess) *
          (reflMallowsBestInSetWeight n qMore
                (initRemainingOf remaining) ctail *
              reflMallowsBestInSetWeight n qLess
                (initRemainingOf remaining) dtail -
            reflMallowsBestInSetWeight n qMore
                (initRemainingOf remaining) dtail *
              reflMallowsBestInSetWeight n qLess
                (initRemainingOf remaining) ctail) := by
    ring
  rw [hfactor]
  exact mul_nonneg
    (mul_nonneg hPMore_nonneg hPLess_nonneg) hinit_cross

/-- Two-candidate base case for best-in-set fiber MLR. -/
theorem reflMallowsBestInSetWeightMLR_zero
    {qMore qLess : ℝ} (hq_le : qMore ≤ qLess) :
    ReflMallowsBestInSetWeightMLR 0 qMore qLess := by
  classical
  intro remaining _hremaining c d hc hd hcd
  have hc0 : c = (0 : Candidate 0) := by
    fin_cases c
    · rfl
    · have hnot : ¬ (1 : Candidate 0) < d := by
        fin_cases d <;> norm_num
      exact False.elim (hnot (by simpa using hcd))
  have hd1 : d = (1 : Candidate 0) := by
    subst c
    fin_cases d
    · exact False.elim ((lt_irrefl (0 : Candidate 0)) hcd)
    · rfl
  subst c
  subst d
  have hremaining_univ : remaining = Finset.univ := by
    ext x
    fin_cases x
    · simp [hc]
    · simp [hd]
  subst remaining
  simp [reflMallowsBestInSetWeight,
    reflMallowsPayoffSum_zero_eq_candidateRankSum, bestInSet_univ]
  repeat rw [Fin.sum_univ_two]
  norm_num [rankingZeroOfFirstChoice, firstChoice]
  exact hq_le

/-- The identity-center best-in-set fiber MLR target is proved for every
remaining set of cardinality at most two. -/
theorem reflMallowsBestInSetWeight_cross_nonneg_card_le_two
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) (hcard : remaining.card ≤ 2)
    {c d : Candidate n} (hc : c ∈ remaining) (hd : d ∈ remaining)
    (hcd : c < d) :
    0 ≤
      reflMallowsBestInSetWeight n qMore remaining c *
          reflMallowsBestInSetWeight n qLess remaining d -
        reflMallowsBestInSetWeight n qMore remaining d *
          reflMallowsBestInSetWeight n qLess remaining c := by
  classical
  have hcard_pos : 0 < remaining.card := Finset.card_pos.mpr hremaining
  have hcases : remaining.card = 1 ∨ remaining.card = 2 := by omega
  rcases hcases with hcard_one | hcard_two
  · exfalso
    have hcard_le_one : remaining.card ≤ 1 := by omega
    exact (ne_of_lt hcd)
      ((Finset.card_le_one.mp hcard_le_one) c hc d hd)
  · have hpair_subset :
        ({c, d} : Finset (Candidate n)) ⊆ remaining := by
      intro x hx
      have hx_cases : x = c ∨ x = d := by
        simpa using hx
      rcases hx_cases with rfl | rfl
      · exact hc
      · exact hd
    have hpair_card :
        ({c, d} : Finset (Candidate n)).card = 2 :=
      Finset.card_pair (ne_of_lt hcd)
    have hpair_eq_remaining :
        ({c, d} : Finset (Candidate n)) = remaining :=
      Finset.eq_of_subset_of_card_le hpair_subset (by
        rw [hcard_two, hpair_card])
    rw [← hpair_eq_remaining]
    exact le_of_lt
      (reflMallowsBestInSetWeight_pair_cross_pos
        n hqMore_pos hq_lt hcd)

/-- The identity-center first-choice fiber at rank zero has positive raw mass. -/
theorem reflFirstWeight_zero_pos
    (n : ℕ) {q : ℝ} (hq : 0 < q) :
    0 < reflFirstWeight n q 0 := by
  unfold reflFirstWeight
  refine Finset.sum_pos' ?_ ?_
  · intro tau _
    exact pow_nonneg hq.le _
  · refine ⟨Equiv.refl (Candidate n), ?_, ?_⟩
    · simp [reflFirstChoiceFiber, firstChoice]
    · simp

/-- Full remaining-set best-in-set fiber MLR reduces to first-choice MLR. -/
theorem reflMallowsBestInSetWeight_univ_cross_nonneg
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) {c d : Candidate n} (hcd : c < d) :
    0 ≤
      reflMallowsBestInSetWeight n qMore Finset.univ c *
          reflMallowsBestInSetWeight n qLess Finset.univ d -
        reflMallowsBestInSetWeight n qMore Finset.univ d *
          reflMallowsBestInSetWeight n qLess Finset.univ c := by
  classical
  rw [reflMallowsBestInSetWeight_univ_eq_reflFirstWeight,
    reflMallowsBestInSetWeight_univ_eq_reflFirstWeight,
    reflMallowsBestInSetWeight_univ_eq_reflFirstWeight,
    reflMallowsBestInSetWeight_univ_eq_reflFirstWeight]
  rw [reflFirstWeight_eq_rank_mul_zero n qMore c,
    reflFirstWeight_eq_rank_mul_zero n qMore d,
    reflFirstWeight_eq_rank_mul_zero n qLess c,
    reflFirstWeight_eq_rank_mul_zero n qLess d]
  let AMore : ℝ := reflFirstWeight n qMore 0
  let ALess : ℝ := reflFirstWeight n qLess 0
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hAMore_nonneg : 0 ≤ AMore := by
    unfold AMore reflFirstWeight
    exact Finset.sum_nonneg (by
      intro τ _
      exact pow_nonneg (le_of_lt hqMore_pos)
        (kendallTau (Equiv.refl (Candidate n)) τ))
  have hALess_nonneg : 0 ≤ ALess := by
    unfold ALess reflFirstWeight
    exact Finset.sum_nonneg (by
      intro τ _
      exact pow_nonneg (le_of_lt hqLess_pos)
        (kendallTau (Equiv.refl (Candidate n)) τ))
  have hrank :
      0 ≤
        qMore ^ (c : ℕ) * qLess ^ (d : ℕ) -
          qMore ^ (d : ℕ) * qLess ^ (c : ℕ) :=
    le_of_lt (sub_pos.mpr (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        rankPower_mul_lt_mul_rankPower hqMore_pos hq_lt hcd))
  change
    0 ≤
      (qMore ^ (c : ℕ) * AMore) * (qLess ^ (d : ℕ) * ALess) -
        (qMore ^ (d : ℕ) * AMore) * (qLess ^ (c : ℕ) * ALess)
  have hfactor :
      (qMore ^ (c : ℕ) * AMore) * (qLess ^ (d : ℕ) * ALess) -
          (qMore ^ (d : ℕ) * AMore) * (qLess ^ (c : ℕ) * ALess) =
        (AMore * ALess) *
          (qMore ^ (c : ℕ) * qLess ^ (d : ℕ) -
            qMore ^ (d : ℕ) * qLess ^ (c : ℕ)) := by
    ring
  rw [hfactor]
  exact mul_nonneg (mul_nonneg hAMore_nonneg hALess_nonneg) hrank

/-- The full remaining-set fiber MLR is strict for distinct center ranks. -/
theorem reflMallowsBestInSetWeight_univ_cross_pos
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) {c d : Candidate n} (hcd : c < d) :
    0 <
      reflMallowsBestInSetWeight n qMore Finset.univ c *
          reflMallowsBestInSetWeight n qLess Finset.univ d -
        reflMallowsBestInSetWeight n qMore Finset.univ d *
          reflMallowsBestInSetWeight n qLess Finset.univ c := by
  classical
  rw [reflMallowsBestInSetWeight_univ_eq_reflFirstWeight,
    reflMallowsBestInSetWeight_univ_eq_reflFirstWeight,
    reflMallowsBestInSetWeight_univ_eq_reflFirstWeight,
    reflMallowsBestInSetWeight_univ_eq_reflFirstWeight]
  rw [reflFirstWeight_eq_rank_mul_zero n qMore c,
    reflFirstWeight_eq_rank_mul_zero n qMore d,
    reflFirstWeight_eq_rank_mul_zero n qLess c,
    reflFirstWeight_eq_rank_mul_zero n qLess d]
  let AMore : ℝ := reflFirstWeight n qMore 0
  let ALess : ℝ := reflFirstWeight n qLess 0
  have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
  have hAMore_pos : 0 < AMore := by
    exact reflFirstWeight_zero_pos n hqMore_pos
  have hALess_pos : 0 < ALess := by
    exact reflFirstWeight_zero_pos n hqLess_pos
  have hrank :
      0 <
        qMore ^ (c : ℕ) * qLess ^ (d : ℕ) -
          qMore ^ (d : ℕ) * qLess ^ (c : ℕ) :=
    sub_pos.mpr (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        rankPower_mul_lt_mul_rankPower hqMore_pos hq_lt hcd)
  change
    0 <
      (qMore ^ (c : ℕ) * AMore) * (qLess ^ (d : ℕ) * ALess) -
        (qMore ^ (d : ℕ) * AMore) * (qLess ^ (c : ℕ) * ALess)
  have hfactor :
      (qMore ^ (c : ℕ) * AMore) * (qLess ^ (d : ℕ) * ALess) -
          (qMore ^ (d : ℕ) * AMore) * (qLess ^ (c : ℕ) * ALess) =
        (AMore * ALess) *
          (qMore ^ (c : ℕ) * qLess ^ (d : ℕ) -
            qMore ^ (d : ℕ) * qLess ^ (c : ℕ)) := by
    ring
  rw [hfactor]
  exact mul_pos (mul_pos hAMore_pos hALess_pos) hrank

/-- In the three-candidate universe, the best-in-set fiber MLR target is fully
closed: remaining sets are singletons, pairs, or the full set. -/
theorem reflMallowsBestInSetWeightMLR_one
    {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) :
    ReflMallowsBestInSetWeightMLR 1 qMore qLess := by
  classical
  intro remaining hremaining c d hc hd hcd
  have hcard_pos : 0 < remaining.card := Finset.card_pos.mpr hremaining
  have hcard_le_three : remaining.card ≤ 3 := by
    have h := Finset.card_le_univ remaining
    simpa [Candidate] using h
  have hcases :
      remaining.card = 1 ∨ remaining.card = 2 ∨ remaining.card = 3 := by
    omega
  rcases hcases with hcard_one | hcard_two | hcard_three
  · exact
      reflMallowsBestInSetWeight_cross_nonneg_card_le_two
        1 hqMore_pos hq_lt hremaining (by omega) hc hd hcd
  · exact
      reflMallowsBestInSetWeight_cross_nonneg_card_le_two
        1 hqMore_pos hq_lt hremaining (by omega) hc hd hcd
  · have hcard_univ :
        remaining.card = Fintype.card (Candidate 1) := by
      simpa [Candidate] using hcard_three
    have hremaining_univ : remaining = Finset.univ :=
      remaining.eq_univ_of_card hcard_univ
    subst remaining
    exact reflMallowsBestInSetWeight_univ_cross_nonneg
      1 hqMore_pos hq_lt hcd

/-- In the three-candidate universe, every nonvacuous ordered fiber comparison
is strict: a remaining set containing an ordered pair has size two or three. -/
theorem reflMallowsBestInSetWeightMLR_one_strict
    {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) :
    ∀ {remaining : Finset (Candidate 1)}, remaining.Nonempty →
      ∀ {c d : Candidate 1}, c ∈ remaining → d ∈ remaining → c < d →
        0 <
          reflMallowsBestInSetWeight 1 qMore remaining c *
              reflMallowsBestInSetWeight 1 qLess remaining d -
            reflMallowsBestInSetWeight 1 qMore remaining d *
              reflMallowsBestInSetWeight 1 qLess remaining c := by
  classical
  intro remaining hremaining c d hc hd hcd
  have hcard_pos : 0 < remaining.card := Finset.card_pos.mpr hremaining
  have hcard_le_three : remaining.card ≤ 3 := by
    have h := Finset.card_le_univ remaining
    simpa [Candidate] using h
  have hcases :
      remaining.card = 1 ∨ remaining.card = 2 ∨ remaining.card = 3 := by
    omega
  rcases hcases with hcard_one | hcard_two | hcard_three
  · exfalso
    have hcard_le_one : remaining.card ≤ 1 := by omega
    exact (ne_of_lt hcd)
      ((Finset.card_le_one.mp hcard_le_one) c hc d hd)
  · have hpair_subset :
        ({c, d} : Finset (Candidate 1)) ⊆ remaining := by
      intro x hx
      have hx_cases : x = c ∨ x = d := by
        simpa using hx
      rcases hx_cases with rfl | rfl
      · exact hc
      · exact hd
    have hpair_card :
        ({c, d} : Finset (Candidate 1)).card = 2 :=
      Finset.card_pair (ne_of_lt hcd)
    have hpair_eq_remaining :
        ({c, d} : Finset (Candidate 1)) = remaining :=
      Finset.eq_of_subset_of_card_le hpair_subset (by
        rw [hcard_two, hpair_card])
    rw [← hpair_eq_remaining]
    exact reflMallowsBestInSetWeight_pair_cross_pos
      1 hqMore_pos hq_lt hcd
  · have hcard_univ :
        remaining.card = Fintype.card (Candidate 1) := by
      simpa [Candidate] using hcard_three
    have hremaining_univ : remaining = Finset.univ :=
      remaining.eq_univ_of_card hcard_univ
    subst remaining
    exact reflMallowsBestInSetWeight_univ_cross_pos
      1 hqMore_pos hq_lt hcd

/--
Normalized best-in-set Mallows MLR in the three-candidate universe, with an
arbitrary common center. Smaller `q` denotes the more accurate law.
-/
theorem mallowsBestInSetProbabilityMLR_three_candidates
    {MAcc MNoisy : MallowsSpec 1}
    (hcenter : MAcc.center = MNoisy.center)
    (hq_lt : MAcc.q < MNoisy.q)
    {remaining : Finset (Candidate 1)} (hremaining : remaining.Nonempty)
    {better worse : Candidate 1}
    (hbetter : better ∈ remaining) (hworse : worse ∈ remaining)
    (hcenter_order : rankOf MAcc.center better < rankOf MAcc.center worse) :
    0 ≤
      pmfProb MAcc.law (fun pi => better = bestInSet pi remaining) *
          pmfProb MNoisy.law (fun pi => worse = bestInSet pi remaining) -
        pmfProb MAcc.law (fun pi => worse = bestInSet pi remaining) *
          pmfProb MNoisy.law (fun pi => better = bestInSet pi remaining) := by
  rw [MAcc.bestInSetProbability_eq_weight_div_partition,
    MNoisy.bestInSetProbability_eq_weight_div_partition,
    MAcc.bestInSetProbability_eq_weight_div_partition,
    MNoisy.bestInSetProbability_eq_weight_div_partition]
  classical
  have hraw :
      0 ≤
        MAcc.bestInSetWeight remaining better *
            MNoisy.bestInSetWeight remaining worse -
          MAcc.bestInSetWeight remaining worse *
            MNoisy.bestInSetWeight remaining better := by
    rw [MAcc.bestInSetWeight_eq_reflMallowsBestInSetWeight_centerCoords hremaining better,
      MAcc.bestInSetWeight_eq_reflMallowsBestInSetWeight_centerCoords hremaining worse,
      MNoisy.bestInSetWeight_eq_reflMallowsBestInSetWeight_centerCoords hremaining better,
      MNoisy.bestInSetWeight_eq_reflMallowsBestInSetWeight_centerCoords hremaining worse]
    have himage : (remaining.image (rankOf MAcc.center)).Nonempty :=
      Finset.image_nonempty.mpr hremaining
    have hbetter_image :
        rankOf MAcc.center better ∈ remaining.image (rankOf MAcc.center) :=
      Finset.mem_image.mpr ⟨better, hbetter, rfl⟩
    have hworse_image :
        rankOf MAcc.center worse ∈ remaining.image (rankOf MAcc.center) :=
      Finset.mem_image.mpr ⟨worse, hworse, rfl⟩
    simpa [hcenter] using
      (reflMallowsBestInSetWeightMLR_one MAcc.q_pos hq_lt
        himage hbetter_image hworse_image hcenter_order)
  have hnormalize :
      (MAcc.bestInSetWeight remaining better / MAcc.partition) *
            (MNoisy.bestInSetWeight remaining worse / MNoisy.partition) -
          (MAcc.bestInSetWeight remaining worse / MAcc.partition) *
            (MNoisy.bestInSetWeight remaining better / MNoisy.partition) =
        (MAcc.bestInSetWeight remaining better *
              MNoisy.bestInSetWeight remaining worse -
            MAcc.bestInSetWeight remaining worse *
              MNoisy.bestInSetWeight remaining better) /
          (MAcc.partition * MNoisy.partition) := by
    field_simp [MAcc.partition_ne_zero, MNoisy.partition_ne_zero]
  rw [hnormalize]
  exact div_nonneg hraw (mul_nonneg MAcc.partition_pos.le MNoisy.partition_pos.le)

/--
Normalized strict best-in-set Mallows MLR in the three-candidate universe,
with an arbitrary common center.  The positive finite partitions preserve the
strict raw-fiber comparison.
-/
theorem mallowsBestInSetProbabilityMLR_three_candidates_strict
    {MAcc MNoisy : MallowsSpec 1}
    (hcenter : MAcc.center = MNoisy.center)
    (hq_lt : MAcc.q < MNoisy.q)
    {remaining : Finset (Candidate 1)} (hremaining : remaining.Nonempty)
    {better worse : Candidate 1}
    (hbetter : better ∈ remaining) (hworse : worse ∈ remaining)
    (hcenter_order : rankOf MAcc.center better < rankOf MAcc.center worse) :
    0 <
      pmfProb MAcc.law (fun pi => better = bestInSet pi remaining) *
          pmfProb MNoisy.law (fun pi => worse = bestInSet pi remaining) -
        pmfProb MAcc.law (fun pi => worse = bestInSet pi remaining) *
          pmfProb MNoisy.law (fun pi => better = bestInSet pi remaining) := by
  rw [MAcc.bestInSetProbability_eq_weight_div_partition,
    MNoisy.bestInSetProbability_eq_weight_div_partition,
    MAcc.bestInSetProbability_eq_weight_div_partition,
    MNoisy.bestInSetProbability_eq_weight_div_partition]
  classical
  have hraw :
      0 <
        MAcc.bestInSetWeight remaining better *
            MNoisy.bestInSetWeight remaining worse -
          MAcc.bestInSetWeight remaining worse *
            MNoisy.bestInSetWeight remaining better := by
    rw [MAcc.bestInSetWeight_eq_reflMallowsBestInSetWeight_centerCoords hremaining better,
      MAcc.bestInSetWeight_eq_reflMallowsBestInSetWeight_centerCoords hremaining worse,
      MNoisy.bestInSetWeight_eq_reflMallowsBestInSetWeight_centerCoords hremaining better,
      MNoisy.bestInSetWeight_eq_reflMallowsBestInSetWeight_centerCoords hremaining worse]
    have himage : (remaining.image (rankOf MAcc.center)).Nonempty :=
      Finset.image_nonempty.mpr hremaining
    have hbetter_image :
        rankOf MAcc.center better ∈ remaining.image (rankOf MAcc.center) :=
      Finset.mem_image.mpr ⟨better, hbetter, rfl⟩
    have hworse_image :
        rankOf MAcc.center worse ∈ remaining.image (rankOf MAcc.center) :=
      Finset.mem_image.mpr ⟨worse, hworse, rfl⟩
    simpa [hcenter] using
      (reflMallowsBestInSetWeightMLR_one_strict MAcc.q_pos hq_lt
        himage hbetter_image hworse_image hcenter_order)
  have hnormalize :
      (MAcc.bestInSetWeight remaining better / MAcc.partition) *
            (MNoisy.bestInSetWeight remaining worse / MNoisy.partition) -
          (MAcc.bestInSetWeight remaining worse / MAcc.partition) *
            (MNoisy.bestInSetWeight remaining better / MNoisy.partition) =
        (MAcc.bestInSetWeight remaining better *
              MNoisy.bestInSetWeight remaining worse -
            MAcc.bestInSetWeight remaining worse *
              MNoisy.bestInSetWeight remaining better) /
          (MAcc.partition * MNoisy.partition) := by
    field_simp [MAcc.partition_ne_zero, MNoisy.partition_ne_zero]
  rw [hnormalize]
  exact div_pos hraw (mul_pos MAcc.partition_pos MNoisy.partition_pos)

/-- Center-convex remaining sets satisfy the identity-center best-in-set fiber
MLR target.  The proof deletes absent extremes until the interval is the full
candidate set, where the statement reduces to first-choice fiber MLR. -/
theorem reflMallowsBestInSetWeight_cross_nonneg_centerConvex
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) (hconv : CenterConvex remaining)
    {c d : Candidate n} (hc : c ∈ remaining) (hd : d ∈ remaining)
    (hcd : c < d) :
    0 ≤
      reflMallowsBestInSetWeight n qMore remaining c *
          reflMallowsBestInSetWeight n qLess remaining d -
        reflMallowsBestInSetWeight n qMore remaining d *
          reflMallowsBestInSetWeight n qLess remaining c := by
  classical
  induction n with
  | zero =>
      exact
        (reflMallowsBestInSetWeightMLR_zero (le_of_lt hq_lt))
          hremaining hc hd hcd
  | succ n ih =>
      by_cases hzero : (0 : Candidate (n + 1)) ∈ remaining
      · by_cases hlast : reflLastCandidate (n + 1) ∈ remaining
        · have hremaining_univ : remaining = Finset.univ :=
            centerConvex_eq_univ_of_zero_last_mem hconv hzero hlast
          subst remaining
          exact reflMallowsBestInSetWeight_univ_cross_nonneg
            (n + 1) hqMore_pos hq_lt hcd
        · have hc_ne_last : c ≠ reflLastCandidate (n + 1) := by
            intro h
            exact hlast (by simpa [h] using hc)
          have hd_ne_last : d ≠ reflLastCandidate (n + 1) := by
            intro h
            exact hlast (by simpa [h] using hd)
          rcases Fin.eq_castSucc_of_ne_last
              (x := c) (by simpa [reflLastCandidate] using hc_ne_last)
              with ⟨ctail, hc_eq⟩
          rcases Fin.eq_castSucc_of_ne_last
              (x := d) (by simpa [reflLastCandidate] using hd_ne_last)
              with ⟨dtail, hd_eq⟩
          subst c
          subst d
          have hinit :
              (initRemainingOf remaining).Nonempty :=
            initRemainingOf_nonempty_of_nonempty_of_last_not_mem
              hremaining hlast
          have hc_init : ctail ∈ initRemainingOf remaining :=
            (mem_initRemainingOf (remaining := remaining)
              (c := ctail)).mpr hc
          have hd_init : dtail ∈ initRemainingOf remaining :=
            (mem_initRemainingOf (remaining := remaining)
              (c := dtail)).mpr hd
          have hcd_init : ctail < dtail :=
            Fin.castSucc_lt_castSucc_iff.mp hcd
          have hinit_cross :
              0 ≤
                reflMallowsBestInSetWeight n qMore
                    (initRemainingOf remaining) ctail *
                  reflMallowsBestInSetWeight n qLess
                    (initRemainingOf remaining) dtail -
                reflMallowsBestInSetWeight n qMore
                    (initRemainingOf remaining) dtail *
                  reflMallowsBestInSetWeight n qLess
                    (initRemainingOf remaining) ctail :=
            ih hinit (centerConvex_initRemainingOf hconv)
              hc_init hd_init hcd_init
          exact
            reflMallowsBestInSetWeight_cross_nonneg_castSucc_of_last_not_mem
              hqMore_pos hq_lt hremaining hlast hinit_cross
      · cases c using Fin.cases with
        | zero =>
            exact False.elim (hzero hc)
        | succ ctail =>
            cases d using Fin.cases with
            | zero =>
                exact False.elim (hzero hd)
            | succ dtail =>
                have htail :
                    (tailRemainingOf remaining).Nonempty :=
                  tailRemainingOf_nonempty_of_nonempty_of_zero_not_mem
                    hremaining hzero
                have hc_tail : ctail ∈ tailRemainingOf remaining :=
                  (mem_tailRemainingOf (remaining := remaining)
                    (c := ctail)).mpr hc
                have hd_tail : dtail ∈ tailRemainingOf remaining :=
                  (mem_tailRemainingOf (remaining := remaining)
                    (c := dtail)).mpr hd
                have hcd_tail : ctail < dtail := by
                  rw [Fin.lt_def] at hcd ⊢
                  simpa [Fin.val_succ] using
                    (Nat.succ_lt_succ_iff.mp hcd)
                have htail_cross :
                    0 ≤
                      reflMallowsBestInSetWeight n qMore
                          (tailRemainingOf remaining) ctail *
                        reflMallowsBestInSetWeight n qLess
                          (tailRemainingOf remaining) dtail -
                      reflMallowsBestInSetWeight n qMore
                          (tailRemainingOf remaining) dtail *
                        reflMallowsBestInSetWeight n qLess
                          (tailRemainingOf remaining) ctail :=
                  ih htail (centerConvex_tailRemainingOf hconv)
                    hc_tail hd_tail hcd_tail
                exact
                  reflMallowsBestInSetWeight_cross_nonneg_succ_of_zero_not_mem
                    hqMore_pos hq_lt hremaining hzero htail_cross

/--
Arbitrary-center expected best-in-set dominance from the identity-center fiber
MLR target.

Once `ReflMallowsBestInSetWeightMLR n Mmore.q Mless.q` is proved for the
common center coordinates, the existing candidatewise weighted-average bridge
closes the remaining-set utility comparison.
-/
theorem expectedBestInSet_le_of_mallows_bestInSetWeightMLR
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (hmlr : ReflMallowsBestInSetWeightMLR n Mmore.q Mless.q)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining := by
  classical
  refine expectedBestInSet_le_of_bestInSetWeight_cross remaining hvalue ?_
  intro c d hcd
  by_cases hc : c ∈ remaining
  · by_cases hd : d ∈ remaining
    · rw [
        Mmore.bestInSetWeight_eq_reflMallowsBestInSetWeight_centerCoords
          hremaining c,
        Mmore.bestInSetWeight_eq_reflMallowsBestInSetWeight_centerCoords
          hremaining d,
        Mless.bestInSetWeight_eq_reflMallowsBestInSetWeight_centerCoords
          hremaining c,
        Mless.bestInSetWeight_eq_reflMallowsBestInSetWeight_centerCoords
          hremaining d]
      have hc_coords :
          rankOf Mmore.center c ∈
            remaining.image (rankOf Mmore.center) :=
        Finset.mem_image.mpr ⟨c, hc, rfl⟩
      have hd_coords :
          rankOf Mmore.center d ∈
            remaining.image (rankOf Mmore.center) :=
        Finset.mem_image.mpr ⟨d, hd, rfl⟩
      have hcd_coords :
          rankOf Mmore.center c < rankOf Mmore.center d := hcd
      simpa [hcenter] using
        hmlr (Finset.image_nonempty.mpr hremaining)
          hc_coords hd_coords hcd_coords
    · have hmore_d :
          Mmore.bestInSetWeight remaining d = 0 :=
        Mmore.bestInSetWeight_eq_zero_of_not_mem hremaining hd
      have hless_d :
          Mless.bestInSetWeight remaining d = 0 :=
        Mless.bestInSetWeight_eq_zero_of_not_mem hremaining hd
      rw [hmore_d, hless_d]
      ring_nf
      exact le_rfl
  · have hmore_c :
        Mmore.bestInSetWeight remaining c = 0 :=
      Mmore.bestInSetWeight_eq_zero_of_not_mem hremaining hc
    have hless_c :
        Mless.bestInSetWeight remaining c = 0 :=
      Mless.bestInSetWeight_eq_zero_of_not_mem hremaining hc
    rw [hmore_c, hless_c]
    ring_nf
    exact le_rfl

/--
Alternative Theorem-4 bridge in the identity-center payoff-sum coordinates.
This is the target shape for the insertion-decomposition proof of the remaining
Mallows stochastic-dominance step.
-/
theorem expectedBestInSet_le_of_reflMallowsPayoffSum_cross
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (remaining : Finset (Candidate n)) (hremaining : remaining.Nonempty)
    (value : Candidate n → ℝ)
    (hcross :
      0 ≤
        Mless.partition *
          reflMallowsPayoffSum n Mmore.q
            (fun τ : Ranking n =>
              value (Mmore.center
                (bestInSet τ (remaining.image (rankOf Mmore.center))))) -
        Mmore.partition *
          reflMallowsPayoffSum n Mless.q
            (fun τ : Ranking n =>
              value (Mmore.center
                (bestInSet τ (remaining.image (rankOf Mmore.center)))))) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining := by
  classical
  let F : Ranking n → ℝ := fun τ =>
    value (Mmore.center
      (bestInSet τ (remaining.image (rankOf Mmore.center))))
  have hmore_eq :
      expectedBestInSet Mmore.law value remaining =
        reflMallowsPayoffSum n Mmore.q F / Mmore.partition := by
    simpa [F] using
      (Mmore.expectedBestInSet_eq_reflMallowsPayoffSum_centerCoords
        value hremaining)
  have hless_eq :
      expectedBestInSet Mless.law value remaining =
        reflMallowsPayoffSum n Mless.q F / Mless.partition := by
    have h :=
      Mless.expectedBestInSet_eq_reflMallowsPayoffSum_centerCoords
        value hremaining
    simpa [F, hcenter] using h
  rw [hless_eq, hmore_eq]
  exact AppliedModelingLib.PositiveDenominator.div_le_div_of_cross_mul_le
    Mless.partition_pos Mmore.partition_pos (by
      linarith)

/--
Strict identity-center payoff-sum bridge for expected best-in-set utility.
-/
theorem expectedBestInSet_lt_of_reflMallowsPayoffSum_cross
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (remaining : Finset (Candidate n)) (hremaining : remaining.Nonempty)
    (value : Candidate n → ℝ)
    (hcross :
      0 <
        Mless.partition *
          reflMallowsPayoffSum n Mmore.q
            (fun τ : Ranking n =>
              value (Mmore.center
                (bestInSet τ (remaining.image (rankOf Mmore.center))))) -
        Mmore.partition *
          reflMallowsPayoffSum n Mless.q
            (fun τ : Ranking n =>
              value (Mmore.center
                (bestInSet τ (remaining.image (rankOf Mmore.center)))))) :
    expectedBestInSet Mless.law value remaining <
      expectedBestInSet Mmore.law value remaining := by
  classical
  let F : Ranking n → ℝ := fun τ =>
    value (Mmore.center
      (bestInSet τ (remaining.image (rankOf Mmore.center))))
  have hmore_eq :
      expectedBestInSet Mmore.law value remaining =
        reflMallowsPayoffSum n Mmore.q F / Mmore.partition := by
    simpa [F] using
      (Mmore.expectedBestInSet_eq_reflMallowsPayoffSum_centerCoords
        value hremaining)
  have hless_eq :
      expectedBestInSet Mless.law value remaining =
        reflMallowsPayoffSum n Mless.q F / Mless.partition := by
    have h :=
      Mless.expectedBestInSet_eq_reflMallowsPayoffSum_centerCoords
        value hremaining
    simpa [F, hcenter] using h
  rw [hless_eq, hmore_eq]
  exact AppliedModelingLib.PositiveDenominator.div_lt_div_of_cross_mul_lt
    Mless.partition_pos Mmore.partition_pos (by
      linarith)

/-- Identity-center first-choice payoff dominance under the Mallows parameter
order, phrased through `bestInSet` on the full candidate set. -/
theorem reflMallowsPayoffSum_cross_bestInSet_univ_of_q_lt
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {value : Candidate n → ℝ}
    (hvalue : WeaklyOrderedBy (Equiv.refl (Candidate n)) value) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate n)) *
          reflMallowsPayoffSum n qMore
            (fun τ : Ranking n => value (bestInSet τ Finset.univ)) -
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          reflMallowsPayoffSum n qLess
            (fun τ : Ranking n => value (bestInSet τ Finset.univ)) :=
    reflMallowsPayoffSum_cross_of_swapImprovesOn_univ
      n hqMore_pos hq_lt
      (fun τ : Ranking n => value (bestInSet τ Finset.univ))
      (swapImprovesOn_bestInSet_value
        (Equiv.refl (Candidate n)) Finset.univ hvalue)

/-- Singleton remaining sets have equal best-in-set payoff under every Mallows parameter. -/
theorem reflMallowsPayoffSum_cross_bestInSet_singleton
    (n : ℕ) (qMore qLess : ℝ)
    {value : Candidate n → ℝ} (c : Candidate n) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate n)) *
          reflMallowsPayoffSum n qMore
            (fun τ : Ranking n => value (bestInSet τ ({c} : Finset (Candidate n)))) -
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          reflMallowsPayoffSum n qLess
            (fun τ : Ranking n => value (bestInSet τ ({c} : Finset (Candidate n)))) := by
  classical
  have hMore :
      reflMallowsPayoffSum n qMore
          (fun τ : Ranking n =>
            value (bestInSet τ ({c} : Finset (Candidate n)))) =
        mallowsPartition qMore (Equiv.refl (Candidate n)) * value c := by
    simpa using reflMallowsPayoffSum_const n qMore (value c)
  have hLess :
      reflMallowsPayoffSum n qLess
          (fun τ : Ranking n =>
            value (bestInSet τ ({c} : Finset (Candidate n)))) =
        mallowsPartition qLess (Equiv.refl (Candidate n)) * value c := by
    simpa using reflMallowsPayoffSum_const n qLess (value c)
  rw [hMore, hLess]
  ring_nf
  exact le_rfl

/--
Identity-center Mallows best-in-set dominance for center-convex remaining sets.

This closes interval-shaped histories by repeatedly deleting unavailable
center-extreme candidates, reducing to the full-set MLR theorem.
-/
theorem reflMallowsPayoffSum_cross_bestInSet_centerConvex
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {value : Candidate n → ℝ}
    (hvalue : WeaklyOrderedBy (Equiv.refl (Candidate n)) value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty)
    (hconv : CenterConvex remaining) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate n)) *
          reflMallowsPayoffSum n qMore
            (fun τ : Ranking n => value (bestInSet τ remaining)) -
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          reflMallowsPayoffSum n qLess
            (fun τ : Ranking n => value (bestInSet τ remaining)) := by
  classical
  induction n with
  | zero =>
      by_cases hzero : (0 : Candidate 0) ∈ remaining
      · by_cases hone : (1 : Candidate 0) ∈ remaining
        · have hlast : reflLastCandidate 0 ∈ remaining := by
            simpa [reflLastCandidate] using hone
          have hrem : remaining = Finset.univ :=
            centerConvex_eq_univ_of_zero_last_mem hconv hzero hlast
          subst remaining
          exact reflMallowsPayoffSum_cross_bestInSet_univ_of_q_lt
            0 hqMore_pos hq_lt hvalue
        · have hrem : remaining = ({(0 : Candidate 0)} : Finset (Candidate 0)) := by
            ext c
            fin_cases c <;> simp [hzero, hone]
          subst remaining
          exact reflMallowsPayoffSum_cross_bestInSet_singleton
            0 qMore qLess (value := value) (0 : Candidate 0)
      · by_cases hone : (1 : Candidate 0) ∈ remaining
        · have hrem : remaining = ({(1 : Candidate 0)} : Finset (Candidate 0)) := by
            ext c
            fin_cases c <;> simp [hzero, hone]
          subst remaining
          exact reflMallowsPayoffSum_cross_bestInSet_singleton
            0 qMore qLess (value := value) (1 : Candidate 0)
        · rcases hremaining with ⟨c, hc⟩
          fin_cases c <;> contradiction
  | succ n ih =>
      by_cases hzero : (0 : Candidate (n + 1)) ∈ remaining
      · by_cases hlast : reflLastCandidate (n + 1) ∈ remaining
        · have hrem : remaining = Finset.univ :=
            centerConvex_eq_univ_of_zero_last_mem hconv hzero hlast
          subst remaining
          exact reflMallowsPayoffSum_cross_bestInSet_univ_of_q_lt
            (n + 1) hqMore_pos hq_lt hvalue
        · refine
            reflMallowsPayoffSum_cross_bestInSet_of_last_not_mem
              hqMore_pos hq_lt hremaining hlast ?_
          exact ih
            (hvalue := weaklyOrderedBy_castSucc hvalue)
            (hremaining :=
              initRemainingOf_nonempty_of_nonempty_of_last_not_mem
                hremaining hlast)
            (hconv := centerConvex_initRemainingOf hconv)
      · refine
          reflMallowsPayoffSum_cross_bestInSet_of_zero_not_mem
            hqMore_pos hq_lt hremaining hzero ?_
        exact ih
          (hvalue := weaklyOrderedBy_succ hvalue)
          (hremaining :=
            tailRemainingOf_nonempty_of_nonempty_of_zero_not_mem
              hremaining hzero)
          (hconv := centerConvex_tailRemainingOf hconv)

/--
Cut-prefix first-hit dominance for center-convex remaining sets.

This is the prefix-event specialization of
`reflMallowsPayoffSum_cross_bestInSet_centerConvex`, using the cut indicator as
the center-ordered payoff.
-/
theorem reflMallowsBestInSetPrefixCutSum_cross_centerConvex
    (n : ℕ) {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty)
    (hconv : CenterConvex remaining) (cut : ℕ) :
    0 ≤
      mallowsPartition qLess (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixCutSum n qMore remaining cut -
        mallowsPartition qMore (Equiv.refl (Candidate n)) *
          reflMallowsBestInSetPrefixCutSum n qLess remaining cut := by
  have hcross :=
    reflMallowsPayoffSum_cross_bestInSet_centerConvex
      n hqMore_pos hq_lt
      (weaklyOrderedBy_centerPrefixCutValue cut)
      (hremaining := hremaining) (hconv := hconv)
  simpa [reflMallowsBestInSetPrefixCutSum, bestInSetPrefixCutIndicator,
    centerPrefixCutValue] using hcross

/-- Equal Mallows center and parameter give the same expected best-in-set
utility, regardless of the concrete `PMF` package used for the specification. -/
theorem expectedBestInSet_eq_of_mallows_center_q_eq
    {n : ℕ} {M₁ M₂ : MallowsSpec n}
    (hcenter : M₁.center = M₂.center) (hq : M₁.q = M₂.q)
    (remaining : Finset (Candidate n)) (value : Candidate n → ℝ) :
    expectedBestInSet M₁.law value remaining =
      expectedBestInSet M₂.law value remaining := by
  classical
  have hpartition : M₁.partition = M₂.partition := by
    rw [M₁.partition_eq_sum, M₂.partition_eq_sum, hcenter, hq]
  unfold expectedBestInSet pmfExp
  refine Finset.sum_congr rfl ?_
  intro π _
  rw [M₁.law_apply_toReal, M₂.law_apply_toReal]
  simp [hcenter, hq, hpartition]

theorem mallowsPartition_eq_refl
    {n : ℕ} (q : ℝ) (ρ : Ranking n) :
    mallowsPartition q ρ =
      mallowsPartition q (Equiv.refl (Candidate n)) := by
  classical
  unfold mallowsPartition mallowsWeight
  calc
    (∑ π : Ranking n, q ^ kendallTau ρ π)
        =
      ∑ τ : Ranking n, q ^ kendallTau ρ (τ.trans ρ) := by
        simpa using
          (Equiv.sum_comp (rankingRightTransEquiv ρ)
            (fun π : Ranking n => q ^ kendallTau ρ π)).symm
    _ = ∑ τ : Ranking n,
          q ^ kendallTau (Equiv.refl (Candidate n)) τ := by
        refine Finset.sum_congr rfl ?_
        intro τ _
        rw [kendallTau_center_trans]

/--
Arbitrary-center expected-utility bridge from identity-center prefix first-hit
dominance.

The prefix premise is stated after relabeling candidates by the common Mallows
center.  It is the exact remaining Mallows stochastic-dominance target for the
non-convex histories in Theorem 4.
-/
theorem expectedBestInSet_le_of_mallows_prefix
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty)
    (hprefix :
      ∀ k : Fin (n + 1),
        0 ≤
          mallowsPartition Mless.q (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixSum n Mmore.q
                (remaining.image (rankOf Mmore.center)) k -
            mallowsPartition Mmore.q (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixSum n Mless.q
                (remaining.image (rankOf Mmore.center)) k) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining := by
  classical
  refine
    expectedBestInSet_le_of_reflMallowsPayoffSum_cross
      hcenter remaining hremaining value ?_
  have hvalue_coords :
      WeaklyOrderedBy (Equiv.refl (Candidate n))
        (fun c : Candidate n => value (Mmore.center c)) := by
    intro c d hcd
    exact hvalue (by simpa [rankOf] using hcd)
  have hcross :=
    reflMallowsPayoffSum_cross_bestInSet_of_prefix
      n hvalue_coords (remaining.image (rankOf Mmore.center)) hprefix
  rw [Mless.partition_eq_sum, Mmore.partition_eq_sum,
    mallowsPartition_eq_refl Mless.q Mless.center,
    mallowsPartition_eq_refl Mmore.q Mmore.center]
  exact hcross

/--
Strict arbitrary-center expected-utility bridge from prefix first-hit
dominance.  The strict input is existential because trivial prefix cuts can
have zero difference.
-/
theorem expectedBestInSet_lt_of_mallows_prefix
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty)
    (hprefix_nonneg :
      ∀ k : Fin (n + 1),
        0 ≤
          mallowsPartition Mless.q (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixSum n Mmore.q
                (remaining.image (rankOf Mmore.center)) k -
            mallowsPartition Mmore.q (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixSum n Mless.q
                (remaining.image (rankOf Mmore.center)) k)
    (hprefix_pos :
      ∃ k : Fin (n + 1),
        0 <
          mallowsPartition Mless.q (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixSum n Mmore.q
                (remaining.image (rankOf Mmore.center)) k -
            mallowsPartition Mmore.q (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixSum n Mless.q
                (remaining.image (rankOf Mmore.center)) k) :
    expectedBestInSet Mless.law value remaining <
      expectedBestInSet Mmore.law value remaining := by
  classical
  refine
    expectedBestInSet_lt_of_reflMallowsPayoffSum_cross
      hcenter remaining hremaining value ?_
  have hvalue_coords :
      StrictlyOrderedBy (Equiv.refl (Candidate n))
        (fun c : Candidate n => value (Mmore.center c)) := by
    intro c d hcd
    exact hvalue (by simpa [rankOf] using hcd)
  have hcross :=
    reflMallowsPayoffSum_cross_bestInSet_pos_of_prefix
      n hvalue_coords (remaining.image (rankOf Mmore.center))
      hprefix_nonneg hprefix_pos
  rw [Mless.partition_eq_sum, Mmore.partition_eq_sum,
    mallowsPartition_eq_refl Mless.q Mless.center,
    mallowsPartition_eq_refl Mmore.q Mmore.center]
  exact hcross

/--
Arbitrary-center expected-utility bridge from aggregate first-choice bracket
sums at every recursive identity-center size.
-/
theorem expectedBestInSet_le_of_mallows_firstChoiceBracketSums
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (hq_lt : Mmore.q < Mless.q)
    (hbracket :
      ∀ m : ℕ,
        ReflMallowsBestInSetPrefixCutFirstChoiceBracketSum
          m Mmore.q Mless.q)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining :=
    expectedBestInSet_le_of_mallows_prefix
      hcenter hvalue hremaining
      (fun k =>
        reflMallowsBestInSetPrefixSum_cross_of_firstChoiceBracketSums
          n Mmore.q_pos hq_lt hbracket
          (Finset.image_nonempty.mpr hremaining) k)

/--
Arbitrary-center expected-utility bridge from weighted first-choice targets at
every recursive identity-center size.
-/
theorem expectedBestInSet_le_of_mallows_firstChoiceWeighted
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (hq_lt : Mmore.q < Mless.q)
    (hweighted :
      ∀ m : ℕ,
        ReflMallowsBestInSetPrefixCutFirstChoiceWeighted
          m Mmore.q Mless.q)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining :=
    expectedBestInSet_le_of_mallows_prefix
      hcenter hvalue hremaining
      (fun k =>
        reflMallowsBestInSetPrefixSum_cross_of_firstChoiceWeighted
          n Mmore.q_pos hq_lt hweighted
          (Finset.image_nonempty.mpr hremaining) k)

/--
Arbitrary-center expected-utility bridge from the reduced extreme weighted
first-choice target.

The successor proof deletes absent center extremes and trivial cuts before
using this same-size weighted target, so this is the narrowest currently
exposed theorem needed for arbitrary remaining-set Mallows dominance.
-/
theorem expectedBestInSet_le_of_mallows_extremeWeighted
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (hq_lt : Mmore.q < Mless.q)
    (hweighted :
      ∀ m : ℕ,
        ReflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes
          m Mmore.q Mless.q)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining :=
    expectedBestInSet_le_of_mallows_prefix
      hcenter hvalue hremaining
      (fun k =>
        reflMallowsBestInSetPrefixSum_cross_of_extremeWeighted
          n Mmore.q_pos hq_lt hweighted
          (Finset.image_nonempty.mpr hremaining) k)

theorem expectedBestInSet_lt_of_mallows_q_lt_card_gt_one
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (hq_lt : Mmore.q < Mless.q)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) (hcard : 1 < remaining.card) :
    expectedBestInSet Mless.law value remaining <
      expectedBestInSet Mmore.law value remaining := by
  classical
  refine
    expectedBestInSet_lt_of_mallows_prefix
      hcenter hvalue hremaining ?hprefix_nonneg ?hprefix_pos
  · intro k
    exact
      reflMallowsBestInSetPrefixSum_cross_of_extremeWeighted
        n Mmore.q_pos hq_lt
        (fun m =>
          reflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes_of_q_lt
            m Mmore.q_pos hq_lt)
        (Finset.image_nonempty.mpr hremaining) k
  · have himage_card :
        1 < (remaining.image (rankOf Mmore.center)).card := by
      rw [Finset.card_image_of_injective]
      · exact hcard
      · intro a b hab
        simpa [rankOf] using congrArg Mmore.center hab
    exact
      reflMallowsBestInSetPrefixSum_cross_exists_pos_of_q_lt
        n Mmore.q_pos hq_lt
        (Finset.image_nonempty.mpr hremaining) himage_card

/--
Arbitrary-center expected-utility bridge from a generic adjacent-swap
stochastic-dominance theorem for identity-center Mallows laws.

The only remaining non-convex Theorem 4 task is to prove this adjacent
stochastic-dominance interface from the Mallows weights themselves.
-/
theorem expectedBestInSet_le_of_mallows_adjacentStochasticDominance
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (hadj : ReflMallowsAdjacentStochasticDominance n Mmore.q Mless.q)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining := by
  refine
    expectedBestInSet_le_of_mallows_prefix
      hcenter hvalue hremaining ?_
  intro k
  exact
    reflMallowsBestInSetPrefixSum_cross_of_adjacentStochasticDominance
      hadj (Finset.image_nonempty.mpr hremaining) k

/--
Common-center Mallows expected best-in-set dominance for center-convex remaining
sets.  The convexity hypothesis is stated in center-rank coordinates.
-/
theorem expectedBestInSet_le_of_mallows_centerConvex_q_le
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (hq_le : Mmore.q ≤ Mless.q)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty)
    (hconv : CenterConvex (remaining.image (rankOf Mmore.center))) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining := by
  classical
  by_cases hq_lt : Mmore.q < Mless.q
  · refine
      expectedBestInSet_le_of_reflMallowsPayoffSum_cross
        hcenter remaining hremaining value ?_
    have hremaining_coords :
        (remaining.image (rankOf Mmore.center)).Nonempty :=
      Finset.image_nonempty.mpr hremaining
    have hvalue_coords :
        WeaklyOrderedBy (Equiv.refl (Candidate n))
          (fun c : Candidate n => value (Mmore.center c)) := by
      intro c d hcd
      exact hvalue (by simpa [rankOf] using hcd)
    have hcross :=
      reflMallowsPayoffSum_cross_bestInSet_centerConvex
        n Mmore.q_pos hq_lt hvalue_coords
        (hremaining := hremaining_coords) (hconv := hconv)
    rw [Mless.partition_eq_sum, Mmore.partition_eq_sum,
      mallowsPartition_eq_refl Mless.q Mless.center,
      mallowsPartition_eq_refl Mmore.q Mmore.center]
    exact hcross
  · have hq : Mmore.q = Mless.q :=
      le_antisymm hq_le (le_of_not_gt hq_lt)
    exact le_of_eq
      (expectedBestInSet_eq_of_mallows_center_q_eq
        hcenter hq remaining value).symm

/-- The fixed-order multi-firm model used by the sequential Theorem 4 layer. -/
structure SequentialModel (n : ℕ) where
  algorithmRanking : PMF (Ranking n)
  humanRanking : PMF (Ranking n)
  value : Candidate n → ℝ

namespace SequentialModel

variable {n : ℕ} (M : SequentialModel n)

/-- Ranking law used by a strategy in the sequential model. -/
def rankingDist : Strategy → PMF (Ranking n)
  | .algorithm => M.algorithmRanking
  | .human => M.humanRanking

/-- Candidates not yet hired after a finite history. -/
def remainingAfter (hired : Finset (Candidate n)) : Finset (Candidate n) := Finset.univ \ hired

/-- A feasible nonterminal history leaves at least one candidate available. -/
theorem remainingAfter_nonempty_of_card_lt
    {hired : Finset (Candidate n)}
    (hcard : hired.card < Fintype.card (Candidate n)) :
    (remainingAfter (n := n) hired).Nonempty := by
  classical
  have hnot_univ : hired ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ] at hcard
    exact (lt_irrefl _) hcard
  obtain ⟨c, hc⟩ : ∃ c : Candidate n, c ∉ hired := by
    by_contra h
    push Not at h
    exact hnot_univ (Finset.eq_univ_iff_forall.mpr h)
  exact ⟨c, by simp [remainingAfter, hc]⟩

theorem remainingAfter_card_eq
    (hired : Finset (Candidate n)) :
    (remainingAfter (n := n) hired).card =
      Fintype.card (Candidate n) - hired.card := by
  classical
  unfold remainingAfter
  rw [Finset.card_sdiff_of_subset]
  · simp
  · intro c _
    simp

theorem remainingAfter_card_gt_one_of_card_succ_lt
    {hired : Finset (Candidate n)}
    (hcard : hired.card + 1 < Fintype.card (Candidate n)) :
    1 < (remainingAfter (n := n) hired).card := by
  rw [remainingAfter_card_eq]
  omega

/-- Utility of the next mover using strategy `s` after the hires in `hired`. -/
noncomputable def stepUtility (s : Strategy)
    (hired : Finset (Candidate n)) : ℝ :=
  expectedBestInSet (M.rankingDist s) M.value
    (remainingAfter (n := n) hired)

/-- A length-`k` strategy sequence. -/
abbrev StrategySequence (k : ℕ) := Fin k → Strategy

/-- The all-human strategy sequence. -/
def allHumanSequence (k : ℕ) : StrategySequence k := fun _ => Strategy.human

/--
A sequence is sequentially optimal if, at every feasible history length, its
prescribed strategy is a best response for every history of that length.
-/
def IsSequentialBestResponseSequence (k : ℕ) (seq : StrategySequence k) : Prop :=
  ∀ i : Fin k, i.val < Fintype.card (Candidate n) →
    ∀ hired : Finset (Candidate n), hired.card = i.val →
      ∀ s : Strategy, M.stepUtility s hired ≤ M.stepUtility (seq i) hired

/--
At every feasible history in the first `k` moves, `H` weakly dominates `A`.
-/
def HumanWeaklyDominatesAtAllHistories (k : ℕ) : Prop :=
  ∀ i : Fin k, i.val < Fintype.card (Candidate n) →
    ∀ hired : Finset (Candidate n), hired.card = i.val →
      M.stepUtility Strategy.algorithm hired ≤ M.stepUtility Strategy.human hired

/--
At every nonterminal history in the first `k` moves, `H` strictly dominates `A`.
The `i.val + 1 < card` guard says at least two candidates remain, which is the
condition under which strict uniqueness is meaningful.
-/
def HumanStrictlyDominatesAtAllNonterminalHistories (k : ℕ) : Prop :=
  ∀ i : Fin k, i.val + 1 < Fintype.card (Candidate n) →
    ∀ hired : Finset (Candidate n), hired.card = i.val →
      M.stepUtility Strategy.algorithm hired < M.stepUtility Strategy.human hired

/--
At every nonterminal history, the only strategy that can be a best response is
`H`.
-/
def HumanUniquelyOptimalAtAllNonterminalHistories (k : ℕ) : Prop :=
  ∀ i : Fin k, i.val + 1 < Fintype.card (Candidate n) →
    ∀ hired : Finset (Candidate n), hired.card = i.val →
      ∀ s : Strategy,
        (∀ t : Strategy, M.stepUtility t hired ≤ M.stepUtility s hired) →
          s = Strategy.human

/-- Stepwise weak dominance proves that the all-human sequence is optimal. -/
theorem allHumanSequence_isSequentialBestResponse_of_human_weaklyDominates
    {k : ℕ} (hdom : M.HumanWeaklyDominatesAtAllHistories k) :
    M.IsSequentialBestResponseSequence k (allHumanSequence k) := by
  intro i hi hired hhired s
  cases s with
  | algorithm =>
      simpa [allHumanSequence] using hdom i hi hired hhired
  | human =>
      simp [allHumanSequence]

/--
A remaining-set expected-utility comparison supplies stepwise weak dominance at
every feasible history.
-/
theorem humanWeaklyDominatesAtAllHistories_of_remaining_dominance
    {k : ℕ}
    (hdom :
      ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet M.algorithmRanking M.value remaining ≤
          expectedBestInSet M.humanRanking M.value remaining) :
    M.HumanWeaklyDominatesAtAllHistories k := by
  intro i hi hired hhired
  exact hdom (remainingAfter (n := n) hired)
    (remainingAfter_nonempty_of_card_lt (n := n)
      (by simpa [hhired] using hi))

theorem humanStrictlyDominatesAtAllNonterminalHistories_of_remaining_dominance
    {k : ℕ}
    (hdom :
      ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        1 < remaining.card →
          expectedBestInSet M.algorithmRanking M.value remaining <
            expectedBestInSet M.humanRanking M.value remaining) :
    M.HumanStrictlyDominatesAtAllNonterminalHistories k := by
  intro i hi hired hhired
  have hlt_card : hired.card < Fintype.card (Candidate n) := by
    have hi' : i.val < Fintype.card (Candidate n) := by omega
    simpa [hhired] using hi'
  have hsucc_card : hired.card + 1 < Fintype.card (Candidate n) := by
    simpa [hhired] using hi
  simpa [stepUtility] using
    hdom (remainingAfter (n := n) hired)
      (remainingAfter_nonempty_of_card_lt (n := n) hlt_card)
      (remainingAfter_card_gt_one_of_card_succ_lt (n := n) hsucc_card)

/-- Stepwise strict dominance makes `H` the unique best response at every
nonterminal history. -/
theorem human_uniqueOptimal_of_human_strictlyDominates
    {k : ℕ} (hdom : M.HumanStrictlyDominatesAtAllNonterminalHistories k) :
    M.HumanUniquelyOptimalAtAllNonterminalHistories k := by
  intro i hi hired hhired s hbest
  cases s with
  | human =>
      rfl
  | algorithm =>
      have hle : M.stepUtility Strategy.human hired ≤
          M.stepUtility Strategy.algorithm hired :=
        hbest Strategy.human
      have hlt : M.stepUtility Strategy.algorithm hired <
          M.stepUtility Strategy.human hired :=
        hdom i hi hired hhired
      linarith

/-- Sequential model induced by two Mallows specifications. -/
noncomputable def ofMallows {n : ℕ}
    (algorithm human : MallowsSpec n) (value : Candidate n → ℝ) :
    SequentialModel n where
  algorithmRanking := algorithm.law
  humanRanking := human.law
  value := value

end SequentialModel

/--
Pairwise weak dominance of one Mallows law over another in the common center
order.
-/
def PairwiseWeaklyMoreAccurate {n : ℕ}
    (more less : MallowsSpec n) : Prop :=
  ∀ c d : Candidate n, rankOf more.center c < rankOf more.center d →
    less.pairCorrectProb c d ≤ more.pairCorrectProb c d

theorem expectedBestInSet_pair_le_of_pairwiseWeaklyMoreAccurate
    {n : ℕ} {more less : MallowsSpec n}
    (hcenter : more.center = less.center)
    (hpair : PairwiseWeaklyMoreAccurate more less)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy more.center value)
    {c d : Candidate n} (hcd : rankOf more.center c < rankOf more.center d) :
    expectedBestInSet less.law value ({c, d} : Finset (Candidate n)) ≤
      expectedBestInSet more.law value ({c, d} : Finset (Candidate n)) :=
  MallowsSpec.expectedBestInSet_pair_le_of_pairCorrectProb_le
    hcenter hcd hvalue (hpair c d hcd)

theorem expectedBestInSet_le_of_pairwiseWeaklyMoreAccurate_card_le_two
    {n : ℕ} {more less : MallowsSpec n}
    (hcenter : more.center = less.center)
    (hpair : PairwiseWeaklyMoreAccurate more less)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy more.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) (hcard : remaining.card ≤ 2) :
    expectedBestInSet less.law value remaining ≤
      expectedBestInSet more.law value remaining := by
  classical
  have hcard_pos : 0 < remaining.card := Finset.card_pos.mpr hremaining
  have hcases : remaining.card = 1 ∨ remaining.card = 2 := by omega
  rcases hcases with hcard_one | hcard_two
  · rcases Finset.card_eq_one.mp hcard_one with ⟨c, hc⟩
    subst remaining
    simp
  · rcases Finset.card_eq_two.mp hcard_two with ⟨c, d, hcd_ne, hremaining_eq⟩
    subst remaining
    have hrank_ne :
        rankOf more.center c ≠ rankOf more.center d := by
      intro hrank
      exact hcd_ne (by
        simpa [rankOf] using congrArg more.center hrank)
    rcases lt_or_gt_of_ne hrank_ne with hcd | hdc
    · exact
        expectedBestInSet_pair_le_of_pairwiseWeaklyMoreAccurate
          hcenter hpair hvalue hcd
    · rw [Finset.pair_comm c d]
      exact
        expectedBestInSet_pair_le_of_pairwiseWeaklyMoreAccurate
          hcenter hpair hvalue hdc

/--
Pairwise strict dominance of one Mallows law over another in the common center
order.
-/
def PairwiseStrictlyMoreAccurate {n : ℕ}
    (more less : MallowsSpec n) : Prop :=
  ∀ c d : Candidate n, rankOf more.center c < rankOf more.center d →
    less.pairCorrectProb c d < more.pairCorrectProb c d

theorem expectedBestInSet_pair_lt_of_pairwiseStrictlyMoreAccurate
    {n : ℕ} {more less : MallowsSpec n}
    (hcenter : more.center = less.center)
    (hpair : PairwiseStrictlyMoreAccurate more less)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy more.center value)
    {c d : Candidate n} (hcd : rankOf more.center c < rankOf more.center d) :
    expectedBestInSet less.law value ({c, d} : Finset (Candidate n)) <
      expectedBestInSet more.law value ({c, d} : Finset (Candidate n)) :=
  MallowsSpec.expectedBestInSet_pair_lt_of_pairCorrectProb_lt
    hcenter hcd hvalue (hpair c d hcd)

/-- Equal common-center Mallows parameters give equal pairwise probabilities. -/
theorem mallows_pairCorrectProb_eq_of_center_eq_q_eq
    {n : ℕ} {M₁ M₂ : MallowsSpec n} (hcenter : M₁.center = M₂.center)
    (hq : M₁.q = M₂.q) (c d : Candidate n) :
    M₁.pairCorrectProb c d = M₂.pairCorrectProb c d := by
  have hpart : M₁.partition = M₂.partition := by
    calc
      M₁.partition = mallowsPartition M₁.q M₁.center := M₁.partition_eq_sum
      _ = mallowsPartition M₂.q M₂.center := by simp [hcenter, hq]
      _ = M₂.partition := M₂.partition_eq_sum.symm
  have hweight : M₁.pairCorrectWeight c d = M₂.pairCorrectWeight c d := by
    unfold MallowsSpec.pairCorrectWeight
    simp [hcenter, hq, mallowsWeight]
  rw [M₁.pairCorrectProb_eq_pairCorrectWeight_div_partition,
    M₂.pairCorrectProb_eq_pairCorrectWeight_div_partition,
    hweight, hpart]

/--
Lemma 8 in reusable strict common-center form: lower inverse Mallows parameter
means strictly larger pairwise correct-ranking probability.
-/
theorem mallows_pairCorrectProb_lt_of_center_eq_q_lt
    {n : ℕ} {Mmore Mless : MallowsSpec n} {c d : Candidate n}
    (hcenter : Mmore.center = Mless.center)
    (hcd_more : rankOf Mmore.center c < rankOf Mmore.center d)
    (hq_lt : Mmore.q < Mless.q) :
    Mless.pairCorrectProb c d < Mmore.pairCorrectProb c d := by
  let m : ℕ :=
    (rankOf Mmore.center d : ℕ) - (rankOf Mmore.center c : ℕ) - 1
  have hcd_less : rankOf Mless.center c < rankOf Mless.center d := by
    simpa [← hcenter] using hcd_more
  have red_more : PairPositionReduction Mmore c d m := by
    simpa [m] using Mmore.pairPositionReduction_of_center_lt hcd_more
  have red_less : PairPositionReduction Mless c d m := by
    simpa [m, ← hcenter] using
      Mless.pairPositionReduction_of_center_lt hcd_less
  exact pairCorrectProb_lt_of_pairPositionReduction
    hcd_more hcd_less red_more red_less hq_lt

/--
Weak pairwise dominance from `q_more ≤ q_less`; the equality case is discharged
from the normalized finite Mallows weights, while the strict case is Lemma 8.
-/
theorem pairwiseWeaklyMoreAccurate_of_center_eq_q_le
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center) (hq_le : Mmore.q ≤ Mless.q) :
    PairwiseWeaklyMoreAccurate Mmore Mless := by
  intro c d hcd
  by_cases hlt : Mmore.q < Mless.q
  · exact le_of_lt
      (mallows_pairCorrectProb_lt_of_center_eq_q_lt
        hcenter hcd hlt)
  · have hq : Mmore.q = Mless.q := le_antisymm hq_le (le_of_not_gt hlt)
    exact le_of_eq
      (mallows_pairCorrectProb_eq_of_center_eq_q_eq
        hcenter hq c d).symm

/-- Strict pairwise dominance from strict inverse-parameter improvement. -/
theorem pairwiseStrictlyMoreAccurate_of_center_eq_q_lt
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center) (hq_lt : Mmore.q < Mless.q) :
    PairwiseStrictlyMoreAccurate Mmore Mless := by
  intro c d hcd
  exact mallows_pairCorrectProb_lt_of_center_eq_q_lt
    hcenter hcd hq_lt

end KR21Monoculture
