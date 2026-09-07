import AppliedModelingLib.Foundations.Probability.WithoutReplacement
import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import Mathlib.Logic.Equiv.Fintype

/-!
# Pick-Anchor sampling model

The source samples `min((n / n') log(2 / δ), n)` arms without replacement.
This file records the executable natural rounding and an exact finite uniform
without-replacement PMF.  The top-set hitting inequality is intentionally a
separate theorem obligation.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib

/--
Natural executable form of Pick-Anchor's sample size.  The source prints a
real-valued expression; this formalization rounds it up before capping at the
number of arms.
-/
noncomputable def pickAnchorSampleCount (armCount cutoff : ℕ) (delta : ℝ) : ℕ :=
  min armCount ⌈(armCount : ℝ) / (cutoff : ℝ) * Real.log (2 / delta)⌉₊

/-- Pick-Anchor never asks for more arms than are available. -/
theorem pickAnchorSampleCount_le_armCount (armCount cutoff : ℕ) (delta : ℝ) :
    pickAnchorSampleCount armCount cutoff delta ≤ armCount :=
  Nat.min_le_left _ _

/--
The capped integral Pick-Anchor sample size is strictly below its real source
formula plus one.  This keeps the source ceiling correction visible for later
finite resource bounds.
-/
theorem pickAnchorSampleCount_real_lt_sourceFormula_add_one
    (armCount cutoff : ℕ) (delta : ℝ)
    (harmCount : 0 < armCount) (hcutoff : 0 < cutoff)
    (hdeltaPos : 0 < delta) (hdeltaLe : delta ≤ 1) :
    (pickAnchorSampleCount armCount cutoff delta : ℝ) <
      (armCount : ℝ) / (cutoff : ℝ) * Real.log (2 / delta) + 1 := by
  have hrawNonnegative : 0 ≤
      (armCount : ℝ) / (cutoff : ℝ) * Real.log (2 / delta) := by
    have hratio : 1 ≤ 2 / delta := by
      apply (le_div_iff₀ hdeltaPos).mpr
      nlinarith
    apply mul_nonneg
    · exact div_nonneg (by exact_mod_cast Nat.le_of_lt harmCount)
        (by exact_mod_cast Nat.le_of_lt hcutoff)
    · exact Real.log_nonneg hratio
  have hceiling : (⌈(armCount : ℝ) / (cutoff : ℝ) * Real.log (2 / delta)⌉₊ : ℝ) <
      (armCount : ℝ) / (cutoff : ℝ) * Real.log (2 / delta) + 1 :=
    Nat.ceil_lt_add_one (ha := hrawNonnegative)
  have hsample : pickAnchorSampleCount armCount cutoff delta ≤
      ⌈(armCount : ℝ) / (cutoff : ℝ) * Real.log (2 / delta)⌉₊ :=
    Nat.min_le_right _ _
  have hsampleReal : (pickAnchorSampleCount armCount cutoff delta : ℝ) ≤
      (⌈(armCount : ℝ) / (cutoff : ℝ) * Real.log (2 / delta)⌉₊ : ℝ) := by
    exact_mod_cast hsample
  exact hsampleReal.trans_lt hceiling

/-- Under the source's positive size and confidence regime, Pick-Anchor samples at least one arm. -/
theorem pickAnchorSampleCount_pos
    (armCount cutoff : ℕ) (delta : ℝ)
    (harmCount : 0 < armCount) (hcutoff : 0 < cutoff)
    (hdeltaPos : 0 < delta) (hdeltaLe : delta ≤ 1) :
    0 < pickAnchorSampleCount armCount cutoff delta := by
  unfold pickAnchorSampleCount
  rw [lt_min_iff]
  constructor
  · exact harmCount
  · apply Nat.ceil_pos.mpr
    have hratioGtOne : 1 < 2 / delta := by
      rw [lt_div_iff₀ hdeltaPos]
      nlinarith
    have hlogPos : 0 < Real.log (2 / delta) := Real.log_pos hratioGtOne
    exact mul_pos
      (div_pos (by exact_mod_cast harmCount) (by exact_mod_cast hcutoff)) hlogPos

/-- The capped Pick-Anchor sample is the full arm set once its raw ceiling reaches that size. -/
theorem pickAnchorSampleCount_eq_armCount_of_armCount_le_rawCeiling
    (armCount cutoff : ℕ) (delta : ℝ)
    (hraw : armCount ≤ ⌈(armCount : ℝ) / (cutoff : ℝ) * Real.log (2 / delta)⌉₊) :
    pickAnchorSampleCount armCount cutoff delta = armCount := by
  unfold pickAnchorSampleCount
  exact Nat.min_eq_left hraw

/-- A canonical fresh sample used only to witness nonemptiness of the finite sample space. -/
noncomputable def pickAnchorCanonicalSample {Arm : Type*} [Fintype Arm]
    (count : ℕ) (hcount : count ≤ Fintype.card Arm) :
    finiteFreshList Arm count ∅ := by
  let enumeration : Arm ≃ Fin (Fintype.card Arm) := Fintype.equivFin Arm
  refine ⟨fun slot => enumeration.symm ⟨slot.val, lt_of_lt_of_le slot.isLt hcount⟩, ?_, ?_⟩
  · intro first second hequal
    have hindexed :
        (⟨first.val, lt_of_lt_of_le first.isLt hcount⟩ : Fin (Fintype.card Arm)) =
          ⟨second.val, lt_of_lt_of_le second.isLt hcount⟩ :=
      enumeration.symm.injective hequal
    exact Fin.ext (congrArg (fun index : Fin (Fintype.card Arm) => index.val) hindexed)
  · intro slot
    simp

/--
The exact ordered uniform-without-replacement law used for a Pick-Anchor
sample.  Its finite sample space prevents duplicate selected arms by
construction.
-/
noncomputable def pickAnchorUniformSampleLaw {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (count : ℕ) (hcount : count ≤ Fintype.card Arm) :
    PMF (finiteFreshList Arm count ∅) :=
  finiteWithoutReplacementPMF (fun _ : Arm => (1 : ℝ))
    (by intro _; norm_num)
    (by
      intro forbidden hcard
      exact finiteAvailableWeight_pos_of_full_support_of_card_lt
        (fun _ : Arm => (1 : ℝ)) forbidden
        (by intro _; norm_num) (by intro _; norm_num) hcard)
    count ∅ (by simpa using hcount)

/-- The unordered selected set underlying an ordered Pick-Anchor sample. -/
noncomputable def pickAnchorSampleSet {Arm : Type*} [DecidableEq Arm]
    {count : ℕ} (sample : finiteFreshList Arm count ∅) : Finset Arm :=
  finiteFreshListPrefixSet count sample

/-- A Pick-Anchor sample contains exactly its requested number of distinct arms. -/
theorem pickAnchorSampleSet_card {Arm : Type*} [DecidableEq Arm]
    {count : ℕ} (sample : finiteFreshList Arm count ∅) :
    (pickAnchorSampleSet sample).card = count := by
  classical
  unfold pickAnchorSampleSet
  have hset : finiteFreshListPrefixSet count sample =
      (Finset.univ : Finset (Fin count)).image sample.1 := by
    ext arm
    constructor
    · intro hmem
      rcases (finiteFreshList_mem_prefixSet_iff sample arm).1 hmem with
        ⟨slot, _hslot, hvalue⟩
      exact Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, hvalue⟩
    · intro hmem
      rcases Finset.mem_image.mp hmem with ⟨slot, _hslot, hvalue⟩
      exact (finiteFreshList_mem_prefixSet_iff sample arm).2
        ⟨slot, slot.isLt, hvalue⟩
  calc
    (finiteFreshListPrefixSet count sample).card =
        ((Finset.univ : Finset (Fin count)).image sample.1).card := by rw [hset]
    _ = (Finset.univ : Finset (Fin count)).card :=
      Finset.card_image_of_injective _ sample.2.1
    _ = count := by simp

/-- A fresh ordered sample whose size is the population size is exactly the full arm set. -/
theorem pickAnchorSampleSet_eq_univ_of_card_eq {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm] {count : ℕ}
    (sample : finiteFreshList Arm count ∅) (hcount : count = Fintype.card Arm) :
    pickAnchorSampleSet sample = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [pickAnchorSampleSet_card, hcount]
  simp

/-- A fresh ordered sample of full population size is exactly the full arm set. -/
theorem pickAnchorSampleSet_eq_univ_of_fullSample {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (sample : finiteFreshList Arm (Fintype.card Arm) ∅) :
    pickAnchorSampleSet sample = Finset.univ :=
  pickAnchorSampleSet_eq_univ_of_card_eq sample rfl

/-- Splitting a fresh list into its available head and its fresh tail. -/
noncomputable def freshListSuccEquiv {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    {count : ℕ} (forbidden : Finset Arm) :
    finiteFreshList Arm (count + 1) forbidden ≃
      Sigma (fun head : {arm // arm ∉ forbidden} =>
        finiteFreshList Arm count (insert head.1 forbidden)) := by
  classical
  symm
  apply Equiv.ofBijective (fun pair => finiteFreshListCons pair.1 pair.2)
  constructor
  · rintro ⟨firstHead, firstTail⟩ ⟨secondHead, secondTail⟩ hsame
    have hheadValue : firstHead.1 = secondHead.1 := by
      have hzero := congrArg (fun sample : finiteFreshList Arm (count + 1) forbidden =>
        sample.1 ⟨0, Nat.succ_pos count⟩) hsame
      simpa using hzero
    have hhead : firstHead = secondHead := Subtype.ext hheadValue
    subst secondHead
    change finiteFreshListCons firstHead firstTail =
      finiteFreshListCons firstHead secondTail at hsame
    have htail : firstTail = secondTail := by
      apply Subtype.ext
      funext slot
      have hslot := congrArg (fun sample : finiteFreshList Arm (count + 1) forbidden =>
        sample.1 slot.succ) hsame
      simpa using hslot
    subst secondTail
    rfl
  · intro sample
    let head : {arm // arm ∉ forbidden} :=
      ⟨sample.1 ⟨0, Nat.succ_pos count⟩, sample.2.2 ⟨0, Nat.succ_pos count⟩⟩
    refine ⟨⟨head, finiteFreshListTailOfHead sample head rfl⟩, ?_⟩
    exact finiteFreshListCons_tailOfHead sample head rfl

/--
The number of ordered fresh lists is the falling factorial of the number of
available arms.  This is the finite combinatorial core of Pick-Anchor's
without-replacement calculation.
-/
theorem finiteFreshList_card_eq_descFactorial
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (count : ℕ) (forbidden : Finset Arm) :
    Fintype.card (finiteFreshList Arm count forbidden) =
      (Fintype.card Arm - forbidden.card).descFactorial count := by
  induction count generalizing forbidden with
  | zero =>
      letI : Unique (finiteFreshList Arm 0 forbidden) := {
        default := finiteFreshListNil Arm forbidden
        uniq := by
          intro sample
          apply Subtype.ext
          funext slot
          exact Fin.elim0 slot }
      simp [Fintype.card_unique]
  | succ count ih =>
      have havailableCard : Fintype.card {arm : Arm // arm ∉ forbidden} =
          Fintype.card Arm - forbidden.card := by
        calc
          Fintype.card {arm : Arm // arm ∉ forbidden} =
              Fintype.card Arm - Fintype.card {arm : Arm // arm ∈ forbidden} := by
                simp only [Fintype.card_subtype_compl]
          _ = Fintype.card Arm - forbidden.card := by
                rw [Fintype.card_of_subtype forbidden (by intro arm; simp)]
      calc
        Fintype.card (finiteFreshList Arm (count + 1) forbidden) =
            Fintype.card (Sigma (fun head : {arm // arm ∉ forbidden} =>
              finiteFreshList Arm count (insert head.1 forbidden))) :=
          Fintype.card_congr (freshListSuccEquiv forbidden)
        _ = ∑ head : {arm // arm ∉ forbidden},
            Fintype.card (finiteFreshList Arm count (insert head.1 forbidden)) :=
          Fintype.card_sigma
        _ = ∑ head : {arm // arm ∉ forbidden},
            (Fintype.card Arm - (insert head.1 forbidden).card).descFactorial count := by
          apply Finset.sum_congr rfl
          intro head _
          exact ih (insert head.1 forbidden)
        _ = ∑ _head : {arm // arm ∉ forbidden},
            (Fintype.card Arm - forbidden.card - 1).descFactorial count := by
          apply Finset.sum_congr rfl
          intro head _
          rw [Finset.card_insert_of_notMem head.2, ← Nat.sub_sub]
        _ = Fintype.card {arm : Arm // arm ∉ forbidden} *
            (Fintype.card Arm - forbidden.card - 1).descFactorial count := by
          simp
        _ = (Fintype.card Arm - forbidden.card) *
            (Fintype.card Arm - forbidden.card - 1).descFactorial count := by
          rw [havailableCard]
        _ = (Fintype.card Arm - forbidden.card).descFactorial (count + 1) := by
          cases hremaining : Fintype.card Arm - forbidden.card with
          | zero => simp
          | succ remaining =>
              simpa using (Nat.succ_descFactorial_succ remaining count).symm

/-- A fresh Pick-Anchor sample avoids a top set when none of its entries is in that set. -/
def pickAnchorAvoidsTop {Arm : Type*} [DecidableEq Arm]
    {count : ℕ} (top : Finset Arm) (sample : finiteFreshList Arm count ∅) : Prop :=
  ∀ slot, sample.1 slot ∉ top

/-- The entrywise and selected-set formulations of a top-set miss agree. -/
theorem pickAnchorAvoidsTop_iff_noHit {Arm : Type*} [DecidableEq Arm]
    {count : ℕ} (top : Finset Arm) (sample : finiteFreshList Arm count ∅) :
    pickAnchorAvoidsTop top sample ↔
      ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample := by
  constructor
  · intro havoid hhit
    rcases hhit with ⟨pivot, hpivotTop, hpivotSample⟩
    rcases (finiteFreshList_mem_prefixSet_iff sample pivot).1 hpivotSample with
      ⟨slot, _hslot, hvalue⟩
    exact havoid slot (by simpa [hvalue] using hpivotTop)
  · intro hnoHit slot hslotTop
    apply hnoHit
    refine ⟨sample.1 slot, hslotTop, ?_⟩
    exact (finiteFreshList_mem_prefixSet_iff sample (sample.1 slot)).2
      ⟨slot, slot.isLt, rfl⟩

/--
Ordered fresh samples that avoid `top` are exactly fresh samples drawn from
the population with `top` initially forbidden.
-/
noncomputable def pickAnchorAvoidingFreshListEquiv
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    {count : ℕ} (top : Finset Arm) :
    {sample : finiteFreshList Arm count ∅ // pickAnchorAvoidsTop top sample} ≃
      finiteFreshList Arm count top where
  toFun := fun sample =>
    ⟨sample.1.1, sample.1.2.1, fun slot htop => sample.2 slot htop⟩
  invFun := fun sample =>
    ⟨⟨sample.1, sample.2.1, fun slot hempty => by simp at hempty⟩,
      fun slot htop => sample.2.2 slot htop⟩
  left_inv := by
    intro sample
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro sample
    apply Subtype.ext
    rfl

/--
When Pick-Anchor's ceiling-and-cap sample size reaches the full arm set, every
nonempty top set is hit deterministically.  This covers the capped branch of
the source's without-replacement sampling argument.
-/
theorem pickAnchor_topSet_hit_of_fullSample {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    {count : ℕ} (sample : finiteFreshList Arm count ∅) (top : Finset Arm)
    (hcount : count = Fintype.card Arm) (htop : top.Nonempty) :
    ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample := by
  have hsampleUniv : pickAnchorSampleSet sample = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [pickAnchorSampleSet_card, hcount]
    simp
  rcases htop with ⟨pivot, hpivot⟩
  exact ⟨pivot, hpivot, by simp [hsampleUniv]⟩

/--
A deterministic without-replacement hit criterion.  A sample whose cardinality
plus the top-set cardinal exceeds the population cardinal cannot avoid that
top set.  The full-sample endpoint is its special case, but this form also
covers every near-full capped sample.
-/
theorem pickAnchor_topSet_hit_of_card_add_gt_armCount {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    {count : ℕ} (sample : finiteFreshList Arm count ∅) (top : Finset Arm)
    (hcapacity : Fintype.card Arm < count + top.card) :
    ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample := by
  by_contra hnoHit
  have hdisjoint : Disjoint (pickAnchorSampleSet sample) top := by
    refine Finset.disjoint_left.mpr ?_
    intro arm hsample htop
    exact hnoHit ⟨arm, htop, hsample⟩
  have hunionCard : (pickAnchorSampleSet sample ∪ top).card =
      (pickAnchorSampleSet sample).card + top.card :=
    Finset.card_union_of_disjoint hdisjoint
  have hunionBound : (pickAnchorSampleSet sample ∪ top).card ≤ Fintype.card Arm := by
    apply Finset.card_le_card
    exact Finset.subset_univ _
  rw [hunionCard, pickAnchorSampleSet_card] at hunionBound
  omega

/--
Every ordered fresh sample of a fixed length has the same atom probability
under `pickAnchorUniformSampleLaw`.  This checks that the recursive sampler is
exchangeable over the exact without-replacement sample space, rather than just
being a full-support weighted draw.
-/
theorem pickAnchorUniformSampleLaw_atom_exchangeable {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (count : ℕ) (hcount : count ≤ Fintype.card Arm)
    (first second : finiteFreshList Arm count ∅) :
    ((pickAnchorUniformSampleLaw count hcount) first).toReal =
      ((pickAnchorUniformSampleLaw count hcount) second).toReal := by
  classical
  obtain ⟨permutation, hpermutation⟩ := Equiv.Perm.exists_extending_pair
    first.1 second.1 first.2.1 second.2.1
  have htransport :
      finiteFreshListRelabelEquiv permutation (fun arm => by simp) first = second := by
    apply Subtype.ext
    funext slot
    simpa [finiteFreshListRelabelEquiv] using hpermutation slot
  have hatom :
      finiteFreshListAtomWeight (fun _ : Arm => (1 : ℝ)) ∅
          (finiteFreshListRelabelEquiv permutation (fun arm => by simp) first) =
        finiteFreshListAtomWeight (fun _ : Arm => (1 : ℝ)) ∅ first := by
    exact finiteFreshListAtomWeight_congr_equiv
      (fun _ : Arm => (1 : ℝ)) (fun _ : Arm => (1 : ℝ)) permutation
      (fun _ => rfl) (fun arm => by simp) first
  rw [htransport] at hatom
  change
    ((finiteWithoutReplacementPMF (fun _ : Arm => (1 : ℝ)) _ _ count ∅ _) first).toReal =
      ((finiteWithoutReplacementPMF (fun _ : Arm => (1 : ℝ)) _ _ count ∅ _) second).toReal
  rw [finiteWithoutReplacementPMF_atom_toReal,
    finiteWithoutReplacementPMF_atom_toReal]
  exact hatom.symm

/--
With unit base weights, Pick-Anchor's recursive sampler is exactly uniform on
the finite type of ordered fresh samples.  This bridges the executable
without-replacement PMF to finite combinatorial probability calculations.
-/
noncomputable def pickAnchorUniformFreshSamplePMF {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (count : ℕ) (hcount : count ≤ Fintype.card Arm) :
    PMF (finiteFreshList Arm count ∅) := by
  classical
  letI : Nonempty (finiteFreshList Arm count ∅) :=
    ⟨pickAnchorCanonicalSample count hcount⟩
  exact uniformPMF (finiteFreshList Arm count ∅)

theorem pickAnchorUniformSampleLaw_eq_uniformPMF {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (count : ℕ) (hcount : count ≤ Fintype.card Arm) :
    pickAnchorUniformSampleLaw count hcount =
      pickAnchorUniformFreshSamplePMF count hcount := by
  classical
  letI : Nonempty (finiteFreshList Arm count ∅) :=
    ⟨pickAnchorCanonicalSample count hcount⟩
  let μ : PMF (finiteFreshList Arm count ∅) := pickAnchorUniformSampleLaw count hcount
  let reference : finiteFreshList Arm count ∅ := pickAnchorCanonicalSample count hcount
  have hconstant : ∀ sample : finiteFreshList Arm count ∅,
      (μ sample).toReal = (μ reference).toReal := by
    intro sample
    exact pickAnchorUniformSampleLaw_atom_exchangeable count hcount sample reference
  have hsum : ∑ sample : finiteFreshList Arm count ∅, (μ sample).toReal = 1 :=
    pmfToRealSum μ
  have hsumConst :
      (∑ _sample : finiteFreshList Arm count ∅, (μ reference).toReal) =
        (Fintype.card (finiteFreshList Arm count ∅) : ℝ) * (μ reference).toReal := by
    simp [nsmul_eq_mul]
  have hmass : (Fintype.card (finiteFreshList Arm count ∅) : ℝ) *
      (μ reference).toReal = 1 := by
    calc
      (Fintype.card (finiteFreshList Arm count ∅) : ℝ) * (μ reference).toReal =
          ∑ _sample : finiteFreshList Arm count ∅, (μ reference).toReal := hsumConst.symm
      _ = ∑ sample : finiteFreshList Arm count ∅, (μ sample).toReal := by
        apply Finset.sum_congr rfl
        intro sample _
        exact (hconstant sample).symm
      _ = 1 := hsum
  have hcardPos : 0 < (Fintype.card (finiteFreshList Arm count ∅) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hmassValue : (μ reference).toReal =
      (Fintype.card (finiteFreshList Arm count ∅) : ℝ)⁻¹ := by
    rw [inv_eq_one_div]
    apply (eq_div_iff (ne_of_gt hcardPos)).mpr
    nlinarith [hmass]
  change μ = uniformPMF (finiteFreshList Arm count ∅)
  apply PMF.ext
  intro sample
  apply (ENNReal.toReal_eq_toReal_iff'
    (ne_of_lt (lt_of_le_of_lt (PMF.coe_le_one μ sample) ENNReal.one_lt_top))
    (ne_of_lt (lt_of_le_of_lt
      (PMF.coe_le_one (uniformPMF (finiteFreshList Arm count ∅)) sample)
      ENNReal.one_lt_top))).mp
  rw [hconstant sample, hmassValue, uniformPMF_apply_toReal]

end FalahatgarEtAl2017MaxingRanking
