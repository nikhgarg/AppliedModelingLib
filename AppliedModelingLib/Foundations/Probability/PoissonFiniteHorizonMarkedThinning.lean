import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import AppliedModelingLib.Foundations.Probability.PoissonProcess
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Tactic

/-!
# Finite-horizon marked Poisson count thinning

This module gives a literal count-and-mark construction, rather than only a
Poisson-thinning likelihood certificate.  A sample consists of a Poisson total
count and an actual finite vector of Boolean marks indexed by `Fin count`.
Conditional on the total count, the marks have the finite iid product law
`pmfProduct (Fin count) Bool (PMF.bernoulli p hp)`.

The construction concerns the finite-horizon total count and its marks only.
It does not construct a marked point-process path or establish Palm/PASTA
properties.
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace AppliedModelingLib.Probability
namespace FiniteHorizonMarkedPoisson

noncomputable section

/-- A finite Poisson-count sample with one Boolean mark for each arrival. -/
structure Sample where
  count : ℕ
  marks : Fin count → Bool
deriving Countable

/-- The count-and-mark sample space is discrete. -/
instance : MeasurableSpace Sample := ⊤

/-- The actual iid product PMF for the mark vector conditional on `n` arrivals. -/
def iidMarks (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) : PMF (Fin n → Bool) :=
  AppliedModelingLib.pmfProduct (Fin n) Bool (PMF.bernoulli p hp)

/-- The joint PMF: first sample a Poisson count, then a finite iid Bernoulli
mark vector of exactly that length. -/
def jointPMF (mean p : ℝ≥0) (hp : p ≤ 1) : PMF Sample :=
  (poissonMeasure mean).toPMF.bind fun n =>
    (iidMarks p hp n).map (fun marks => ⟨n, marks⟩)

/-- The unthinned total-arrival count. -/
def total : Sample → ℕ := Sample.count

/-- The number of `true` marks in a finite mark vector. -/
def keptInMarks {n : ℕ} (marks : Fin n → Bool) : ℕ :=
  (successIndexSet (fun b : Bool => b = true) marks).card

/-- The retained-arrival count of a marked sample. -/
def kept : Sample → ℕ := fun z => keptInMarks z.2

/-- The number of `false` marks in a finite mark vector. -/
def discardedInMarks {n : ℕ} (marks : Fin n → Bool) : ℕ :=
  n - keptInMarks marks

/-- The discarded-arrival count of a marked sample. -/
def discarded : Sample → ℕ := fun z => discardedInMarks z.2

/-- The retained and discarded counts of a marked sample. -/
def splitCounts : Sample → ℕ × ℕ := fun z => (kept z, discarded z)

/-- The number of retained Boolean marks is the finite sum of their indicator
functions. -/
theorem keptInMarks_eq_sum_indicator {n : ℕ} (marks : Fin n → Bool) :
    keptInMarks marks = ∑ i : Fin n, if marks i = true then 1 else 0 := by
  unfold keptInMarks AppliedModelingLib.successIndexSet
  rw [Finset.card_filter]

/-- Retained marks add under concatenation of two finite event blocks. -/
theorem keptInMarks_append {m n : ℕ}
    (firstBlock : Fin m → Bool) (secondBlock : Fin n → Bool) :
    keptInMarks (Fin.append firstBlock secondBlock) =
      keptInMarks firstBlock + keptInMarks secondBlock := by
  rw [keptInMarks_eq_sum_indicator, keptInMarks_eq_sum_indicator,
    keptInMarks_eq_sum_indicator]
  rw [Fin.sum_univ_add]
  simp

/-- The retained marks in a trailing block are the retained marks in the full
concatenation after removing those in the leading block. -/
theorem keptInMarks_secondBlock_eq_sub {m n : ℕ}
    (firstBlock : Fin m → Bool) (secondBlock : Fin n → Bool) :
    keptInMarks secondBlock =
      keptInMarks (Fin.append firstBlock secondBlock) - keptInMarks firstBlock := by
  rw [keptInMarks_append]
  omega

/-- Discarded Boolean marks add under concatenation of two finite event
blocks. -/
theorem discardedInMarks_append {m n : ℕ}
    (firstBlock : Fin m → Bool) (secondBlock : Fin n → Bool) :
    discardedInMarks (Fin.append firstBlock secondBlock) =
      discardedInMarks firstBlock + discardedInMarks secondBlock := by
  have hfirst : keptInMarks firstBlock ≤ m := by
    unfold keptInMarks
    simpa using Finset.card_le_card
      (Finset.subset_univ (successIndexSet (fun b : Bool => b = true) firstBlock))
  have hsecond : keptInMarks secondBlock ≤ n := by
    unfold keptInMarks
    simpa using Finset.card_le_card
      (Finset.subset_univ (successIndexSet (fun b : Bool => b = true) secondBlock))
  unfold discardedInMarks
  rw [keptInMarks_append]
  omega

/-- The discarded marks in a trailing block are the discarded marks in the
full concatenation after removing those in the leading block. -/
theorem discardedInMarks_secondBlock_eq_sub {m n : ℕ}
    (firstBlock : Fin m → Bool) (secondBlock : Fin n → Bool) :
    discardedInMarks secondBlock =
      discardedInMarks (Fin.append firstBlock secondBlock) -
        discardedInMarks firstBlock := by
  rw [discardedInMarks_append]
  omega

/-- For a finite Boolean vector indexed by a concatenated index set, the
retained marks in the tail are the full retained count minus the prefix
retained count. -/
theorem keptInMarks_tail_eq_sub {m n : ℕ} (marks : Fin (m + n) → Bool) :
    keptInMarks (fun i : Fin n => marks (Fin.natAdd m i)) =
      keptInMarks marks -
        keptInMarks (fun i : Fin m => marks (Fin.castAdd n i)) := by
  have hsplit :
      Fin.append (fun i : Fin m => marks (Fin.castAdd n i))
        (fun i : Fin n => marks (Fin.natAdd m i)) = marks :=
    Fin.append_castAdd_natAdd
  rw [← hsplit]
  simpa only [Fin.append_left, Fin.append_right] using
    (keptInMarks_secondBlock_eq_sub
      (fun i : Fin m => marks (Fin.castAdd n i))
      (fun i : Fin n => marks (Fin.natAdd m i)))

/-- For a finite Boolean vector indexed by a concatenated index set, the
discarded marks in the tail are the full discarded count minus the prefix
discarded count. -/
theorem discardedInMarks_tail_eq_sub {m n : ℕ} (marks : Fin (m + n) → Bool) :
    discardedInMarks (fun i : Fin n => marks (Fin.natAdd m i)) =
      discardedInMarks marks -
        discardedInMarks (fun i : Fin m => marks (Fin.castAdd n i)) := by
  have hsplit :
      Fin.append (fun i : Fin m => marks (Fin.castAdd n i))
        (fun i : Fin n => marks (Fin.natAdd m i)) = marks :=
    Fin.append_castAdd_natAdd
  rw [← hsplit]
  simpa only [Fin.append_left, Fin.append_right] using
    (discardedInMarks_secondBlock_eq_sub
      (fun i : Fin m => marks (Fin.castAdd n i))
      (fun i : Fin n => marks (Fin.natAdd m i)))

/-- The embedding of a fixed-length mark vector preserves its atom mass. -/
private theorem iidMarks_map_embed_apply
    (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) (marks : Fin n → Bool) :
    ((iidMarks p hp n).map (fun x => Sample.mk n x))
      (Sample.mk n marks) =
      iidMarks p hp n marks := by
  rw [PMF.map_apply]
  rw [tsum_eq_single marks (by
    intro b hb
    have hne : Sample.mk n marks ≠ Sample.mk n b := by
      intro h
      cases h
      exact hb rfl
    simp [hne])]
  simp

/-- An embedded mark vector cannot have a different total count. -/
private theorem iidMarks_map_embed_apply_of_ne
    (p : ℝ≥0) (hp : p ≤ 1) {n m : ℕ} (hnm : n ≠ m)
    (marks : Fin m → Bool) :
    ((iidMarks p hp n).map (fun x => Sample.mk n x))
      (Sample.mk m marks) = 0 := by
  rw [PMF.map_apply]
  rw [ENNReal.tsum_eq_zero]
  intro x
  have hne : Sample.mk m marks ≠ Sample.mk n x := by
    intro h
    exact hnm (congrArg Sample.count h).symm
  simp [hne]

/-- Exact joint atom factorization.  This is the conditional iid-mark witness:
given `n`, the mark-vector factor is precisely `iidMarks p hp n`. -/
theorem jointPMF_apply
    (mean p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) (marks : Fin n → Bool) :
    jointPMF mean p hp (Sample.mk n marks) =
      (poissonMeasure mean).toPMF n * iidMarks p hp n marks := by
  rw [jointPMF, PMF.bind_apply]
  rw [tsum_eq_single n (by
    intro m hmn
    rw [iidMarks_map_embed_apply_of_ne p hp hmn]
    simp)]
  rw [iidMarks_map_embed_apply]

private theorem bernoulli_pmfProb_true
    (p : ℝ≥0) (hp : p ≤ 1) :
    pmfProb (PMF.bernoulli p hp) (fun b : Bool => b = true) = (p : ℝ) := by
  simp [pmfProb, pmfExp, PMF.bernoulli_apply]

private theorem bernoulli_pmfProb_not_true
    (p : ℝ≥0) (hp : p ≤ 1) :
    pmfProb (PMF.bernoulli p hp) (fun b : Bool => ¬ b = true) = 1 - (p : ℝ) := by
  simp [pmfProb, pmfExp, PMF.bernoulli_apply, NNReal.coe_sub hp]

/-- A finite-domain PMF map to `ℕ` has the expected atom/event-probability
identity, without requiring the codomain to be finite. -/
private theorem finitePmf_mapNat_apply_toReal_eq_pmfProb_preimage
    {α : Type*} [Fintype α] [DecidableEq α]
    (ν : PMF α) (f : α → ℕ) (k : ℕ) :
    ((ν.map f) k).toReal = pmfProb ν (fun a => f a = k) := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  unfold pmfProb pmfExp
  rw [ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl ?_
    intro a _
    by_cases h : f a = k
    · simp [h]
    · have h' : k ≠ f a := Ne.symm h
      simp [h, h']
  · intro a _
    split_ifs <;> simp [ν.apply_ne_top a]

/-- Conditional on `n` arrivals, the actual iid Bernoulli mark count has the
usual binomial thinning mass. -/
theorem iidMarks_kept_mass_toReal
    (p : ℝ≥0) (hp : p ≤ 1) (n k : ℕ) :
    (((iidMarks p hp n).map keptInMarks) k).toReal =
      PoissonProcess.binomialThinningMass (p : ℝ) n k := by
  rw [finitePmf_mapNat_apply_toReal_eq_pmfProb_preimage]
  change pmfProb (pmfProduct (Fin n) Bool (PMF.bernoulli p hp))
      (fun sample => (successIndexSet (fun b : Bool => b = true) sample).card = k) = _
  rw [pmfProduct_prob_successIndexSet_card_eq,
    bernoulli_pmfProb_true, bernoulli_pmfProb_not_true]
  by_cases h : k ≤ n
  · rw [PoissonProcess.binomialThinningMass_eq_of_le h]
    simp
  · have hlt : n < k := Nat.lt_of_not_ge h
    rw [PoissonProcess.binomialThinningMass_eq_zero_of_lt hlt]
    simp [Nat.choose_eq_zero_of_lt hlt]

private theorem poissonMeasure_toPMF_apply_toReal
    (mean : ℝ≥0) (n : ℕ) :
    ((poissonMeasure mean).toPMF n).toReal =
      PoissonProcess.countLikelihood 1 (mean : ℝ) n := by
  change (poissonMeasure mean).real {n} = _
  rw [poissonMeasure_real_singleton]
  simp [PoissonProcess.countLikelihood]

/-- Mapping the joint construction to retained count is exactly its Poisson
count mixture of actual finite iid mark-count PMFs. -/
theorem jointPMF_map_kept
    (mean p : ℝ≥0) (hp : p ≤ 1) :
    (jointPMF mean p hp).map kept =
      (poissonMeasure mean).toPMF.bind fun n =>
        (iidMarks p hp n).map keptInMarks := by
  rw [jointPMF, PMF.map_bind]
  simp_rw [PMF.map_comp]
  rfl

private theorem keptInMarks_le_length {n : ℕ} (marks : Fin n → Bool) :
    keptInMarks marks ≤ n := by
  unfold keptInMarks
  simpa using Finset.card_le_card
    (Finset.subset_univ (successIndexSet (fun b : Bool => b = true) marks))

private theorem splitMarks_eq_iff {n k d : ℕ} (marks : Fin n → Bool) :
    (keptInMarks marks, discardedInMarks marks) = (k, d) ↔
      keptInMarks marks = k ∧ n = k + d := by
  constructor
  · rintro h
    have hk : keptInMarks marks = k := congrArg Prod.fst h
    have hd : n - keptInMarks marks = d := congrArg Prod.snd h
    refine ⟨hk, ?_⟩
    have hle := keptInMarks_le_length marks
    omega
  · rintro ⟨hk, hn⟩
    apply Prod.ext
    · exact hk
    · unfold discardedInMarks
      omega

private theorem iidMarks_map_split_apply
    (p : ℝ≥0) (hp : p ≤ 1) (n k d : ℕ) :
    ((iidMarks p hp n).map
      (fun marks => (keptInMarks marks, discardedInMarks marks))) (k, d) =
      if n = k + d then ((iidMarks p hp n).map keptInMarks) k else 0 := by
  classical
  rw [PMF.map_apply, PMF.map_apply]
  by_cases h : n = k + d
  · rw [if_pos h]
    apply tsum_congr
    intro marks
    by_cases hpair : (k, d) = (keptInMarks marks, discardedInMarks marks)
    · have hp := (splitMarks_eq_iff marks).mp hpair.symm
      simp [hpair, hp.1]
    · have hmark : ¬ k = keptInMarks marks := by
        intro hk
        have hp : (keptInMarks marks, discardedInMarks marks) = (k, d) :=
          (splitMarks_eq_iff marks).mpr ⟨hk.symm, h⟩
        exact hpair hp.symm
      simp [hpair, hmark]
  · rw [if_neg h]
    apply ENNReal.tsum_eq_zero.mpr
    intro marks
    by_cases hpair : (k, d) = (keptInMarks marks, discardedInMarks marks)
    · have hp := (splitMarks_eq_iff marks).mp hpair.symm
      exact (h hp.2).elim
    · simp [hpair]

/-- Mapping the literal marked construction to its retained/discarded pair is
the corresponding Poisson mixture of finite iid mark-pair PMFs. -/
theorem jointPMF_map_splitCounts
    (mean p : ℝ≥0) (hp : p ≤ 1) :
    (jointPMF mean p hp).map splitCounts =
      (poissonMeasure mean).toPMF.bind fun n =>
        (iidMarks p hp n).map
          (fun marks => (keptInMarks marks, discardedInMarks marks)) := by
  rw [jointPMF, PMF.map_bind]
  simp_rw [PMF.map_comp]
  rfl

private theorem jointPMF_kept_mass_toReal
    (mean p : ℝ≥0) (hp : p ≤ 1) (k : ℕ) :
    (((jointPMF mean p hp).map kept) k).toReal =
      ∑' n : ℕ,
        PoissonProcess.countLikelihood 1 (mean : ℝ) n *
          PoissonProcess.binomialThinningMass (p : ℝ) n k := by
  rw [jointPMF_map_kept, PMF.bind_apply, ENNReal.tsum_toReal_eq]
  · simp_rw [ENNReal.toReal_mul, poissonMeasure_toPMF_apply_toReal,
      iidMarks_kept_mass_toReal]
  · intro n
    exact ENNReal.mul_ne_top
      ((poissonMeasure mean).toPMF.apply_ne_top n)
      (((iidMarks p hp n).map keptInMarks).apply_ne_top k)

/-- The retained-count PMF in the genuine marked construction is Poisson with
the thinned mean. -/
theorem jointPMF_map_kept_eq_poisson
    (mean p : ℝ≥0) (hp : p ≤ 1) :
    (jointPMF mean p hp).map kept =
      (poissonMeasure (mean * p)).toPMF := by
  apply PMF.ext
  intro k
  apply (ENNReal.toReal_eq_toReal_iff'
    (((jointPMF mean p hp).map kept).apply_ne_top k)
    ((poissonMeasure (mean * p)).toPMF.apply_ne_top k)).mp
  calc
    (((jointPMF mean p hp).map kept) k).toReal =
        ∑' n : ℕ,
          PoissonProcess.countLikelihood 1 (mean : ℝ) n *
            PoissonProcess.binomialThinningMass (p : ℝ) n k :=
      jointPMF_kept_mass_toReal mean p hp k
    _ = PoissonProcess.countLikelihood 1 ((mean : ℝ) * (p : ℝ)) k :=
      PoissonProcess.tsum_countLikelihood_mul_binomialThinningMass
        (mean : ℝ) (p : ℝ) k
    _ = PoissonProcess.countLikelihood 1 ((mean * p : ℝ≥0) : ℝ) k := by
      norm_cast
    _ = ((poissonMeasure (mean * p)).toPMF k).toReal :=
      (poissonMeasure_toPMF_apply_toReal (mean * p) k).symm

/-- Under the literal marked sample-space measure, the retained count has the
thinned Poisson law. -/
theorem kept_hasLaw
    (mean p : ℝ≥0) (hp : p ≤ 1) :
    HasLaw kept (poissonMeasure (mean * p))
      (jointPMF mean p hp).toMeasure := by
  refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
  rw [PMF.toMeasure_map kept (jointPMF mean p hp)
    (measurable_of_countable _), jointPMF_map_kept_eq_poisson]
  exact Measure.toPMF_toMeasure _

private theorem jointPMF_split_mass_toReal
    (mean p : ℝ≥0) (hp : p ≤ 1) (k d : ℕ) :
    (((jointPMF mean p hp).map splitCounts) (k, d)).toReal =
      PoissonProcess.countLikelihood 1 (mean : ℝ) (k + d) *
        PoissonProcess.binomialThinningMass (p : ℝ) (k + d) k := by
  rw [jointPMF_map_splitCounts, PMF.bind_apply, ENNReal.tsum_toReal_eq]
  · have hterm (n : ℕ) :
      ((((poissonMeasure mean).toPMF n) *
        (((iidMarks p hp n).map
          (fun marks => (keptInMarks marks, discardedInMarks marks))) (k, d))).toReal) =
        (if n = k + d then
          PoissonProcess.countLikelihood 1 (mean : ℝ) (k + d) *
            PoissonProcess.binomialThinningMass (p : ℝ) (k + d) k
        else 0) := by
      rw [ENNReal.toReal_mul, poissonMeasure_toPMF_apply_toReal,
        iidMarks_map_split_apply]
      split_ifs with hn
      · subst n
        rw [iidMarks_kept_mass_toReal]
      · simp
    simp_rw [hterm]
    simp
  · intro n
    exact ENNReal.mul_ne_top
      ((poissonMeasure mean).toPMF.apply_ne_top n)
      (((iidMarks p hp n).map
        (fun marks => (keptInMarks marks, discardedInMarks marks))).apply_ne_top (k, d))

private theorem jointPMF_split_mass_toReal_factor
    (mean p : ℝ≥0) (hp : p ≤ 1) (k d : ℕ) :
    (((jointPMF mean p hp).map splitCounts) (k, d)).toReal =
      PoissonProcess.countLikelihood 1 ((mean : ℝ) * (p : ℝ)) k *
        PoissonProcess.countLikelihood 1 ((mean : ℝ) * (1 - (p : ℝ))) d := by
  calc
    (((jointPMF mean p hp).map splitCounts) (k, d)).toReal =
        PoissonProcess.countLikelihood 1 (mean : ℝ) (k + d) *
          PoissonProcess.binomialThinningMass (p : ℝ) (k + d) k :=
      jointPMF_split_mass_toReal mean p hp k d
    _ = (Real.exp (-(mean : ℝ)) * ((mean : ℝ) * (p : ℝ)) ^ k /
          (k.factorial : ℝ)) *
        (((mean : ℝ) * (1 - (p : ℝ))) ^ d / (d.factorial : ℝ)) :=
      PoissonProcess.countLikelihood_mul_binomialThinningMass_add_eq
        (mean : ℝ) (p : ℝ) k d
    _ = PoissonProcess.countLikelihood 1 ((mean : ℝ) * (p : ℝ)) k *
        PoissonProcess.countLikelihood 1 ((mean : ℝ) * (1 - (p : ℝ))) d := by
      simp only [PoissonProcess.countLikelihood, one_mul]
      have hExp : Real.exp (-(mean : ℝ)) =
          Real.exp (-((mean : ℝ) * (p : ℝ))) *
            Real.exp (-((mean : ℝ) * (1 - (p : ℝ)))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hExp]
      ring

private theorem jointPMF_split_mass_toReal_poisson_product
    (mean p : ℝ≥0) (hp : p ≤ 1) (k d : ℕ) :
    (((jointPMF mean p hp).map splitCounts) (k, d)).toReal =
      (((poissonMeasure (mean * p)).toPMF k).toReal) *
        (((poissonMeasure (mean * (1 - p))).toPMF d).toReal) := by
  rw [jointPMF_split_mass_toReal_factor mean p hp k d,
    poissonMeasure_toPMF_apply_toReal,
    poissonMeasure_toPMF_apply_toReal]
  simp only [NNReal.coe_mul, NNReal.coe_sub hp, NNReal.coe_one]

/-- Under the literal finite marked construction, the retained and discarded
counts are independent Poisson variables with means `mean * p` and
`mean * (1 - p)`, respectively.  This is a finite-horizon count law; it does
not construct a point process or assert Palm/PASTA semantics. -/
theorem splitCounts_hasLaw
    (mean p : ℝ≥0) (hp : p ≤ 1) :
    HasLaw splitCounts
      ((poissonMeasure (mean * p)).prod (poissonMeasure (mean * (1 - p))))
      (jointPMF mean p hp).toMeasure := by
  refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
  rw [PMF.toMeasure_map splitCounts (jointPMF mean p hp)
    (measurable_of_countable _)]
  apply Measure.ext_of_singleton
  rintro ⟨k, d⟩
  rw [PMF.toMeasure_apply_singleton ((jointPMF mean p hp).map splitCounts)
      (k, d) (measurableSet_singleton _),
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    ← Measure.toPMF_toMeasure (poissonMeasure (mean * p)),
    ← Measure.toPMF_toMeasure (poissonMeasure (mean * (1 - p))),
    PMF.toMeasure_apply_singleton (poissonMeasure (mean * p)).toPMF k
      (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton (poissonMeasure (mean * (1 - p))).toPMF d
      (measurableSet_singleton _)]
  apply (ENNReal.toReal_eq_toReal_iff'
    (((jointPMF mean p hp).map splitCounts).apply_ne_top (k, d))
    (ENNReal.mul_ne_top
      ((poissonMeasure (mean * p)).toPMF.apply_ne_top k)
      ((poissonMeasure (mean * (1 - p))).toPMF.apply_ne_top d))).mp
  rw [ENNReal.toReal_mul]
  exact jointPMF_split_mass_toReal_poisson_product mean p hp k d

/-- Under the literal finite marked construction, the discarded (`false`-mark)
count is Poisson with the complementary thinned mean. -/
theorem discarded_hasLaw
    (mean p : ℝ≥0) (hp : p ≤ 1) :
    HasLaw discarded (poissonMeasure (mean * (1 - p)))
      (jointPMF mean p hp).toMeasure := by
  letI : IsProbabilityMeasure (poissonMeasure (mean * p)) := by
    infer_instance
  have hsnd : HasLaw Prod.snd (poissonMeasure (mean * (1 - p)))
      ((poissonMeasure (mean * p)).prod
        (poissonMeasure (mean * (1 - p)))) := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  simpa [discarded, splitCounts, Function.comp_def] using
    hsnd.comp (splitCounts_hasLaw mean p hp)

/-- Forgetting the mark vector from the joint construction leaves the original
Poisson total-count PMF. -/
theorem jointPMF_map_total
    (mean p : ℝ≥0) (hp : p ≤ 1) :
    (jointPMF mean p hp).map total =
      (poissonMeasure mean).toPMF := by
  rw [jointPMF, PMF.map_bind]
  simp_rw [PMF.map_comp]
  change (poissonMeasure mean).toPMF.bind (fun n =>
    (iidMarks p hp n).map (Function.const (Fin n → Bool) n)) = _
  simp_rw [PMF.map_const]
  exact PMF.bind_pure _

/-- Under the literal marked sample-space measure, the total count has its
original Poisson law. -/
theorem total_hasLaw
    (mean p : ℝ≥0) (hp : p ≤ 1) :
    HasLaw total (poissonMeasure mean)
      (jointPMF mean p hp).toMeasure := by
  refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
  rw [PMF.toMeasure_map total (jointPMF mean p hp)
    (measurable_of_countable _), jointPMF_map_total]
  exact Measure.toPMF_toMeasure _

/-- The finite-horizon specialization with mean `rate * exposure`. -/
def ofRateExposure
    (rate exposure : ℝ) (hmean : 0 ≤ rate * exposure)
    (p : ℝ≥0) (hp : p ≤ 1) : PMF Sample :=
  jointPMF (PoissonProcess.rateExposureParam rate exposure hmean) p hp

/-- The total count in the rate-exposure specialization is Poisson with mean
`rate * exposure`, represented as an `ℝ≥0`. -/
theorem ofRateExposure_total_hasLaw
    (rate exposure : ℝ) (hmean : 0 ≤ rate * exposure)
    (p : ℝ≥0) (hp : p ≤ 1) :
    HasLaw total
      (poissonMeasure (PoissonProcess.rateExposureParam rate exposure hmean))
      (ofRateExposure rate exposure hmean p hp).toMeasure := by
  simpa [ofRateExposure] using
    total_hasLaw (PoissonProcess.rateExposureParam rate exposure hmean) p hp

/-- The retained count in the rate-exposure specialization is Poisson with
mean `(rate * exposure) * p`. -/
theorem ofRateExposure_kept_hasLaw
    (rate exposure : ℝ) (hmean : 0 ≤ rate * exposure)
    (p : ℝ≥0) (hp : p ≤ 1) :
    HasLaw kept
      (poissonMeasure (PoissonProcess.rateExposureParam rate exposure hmean * p))
      (ofRateExposure rate exposure hmean p hp).toMeasure := by
  simpa [ofRateExposure] using
    kept_hasLaw (PoissonProcess.rateExposureParam rate exposure hmean) p hp

/-- The retained and discarded finite-horizon counts in the rate-exposure
specialization have the corresponding independent Poisson product law. -/
theorem ofRateExposure_splitCounts_hasLaw
    (rate exposure : ℝ) (hmean : 0 ≤ rate * exposure)
    (p : ℝ≥0) (hp : p ≤ 1) :
    HasLaw splitCounts
      ((poissonMeasure (PoissonProcess.rateExposureParam rate exposure hmean * p)).prod
        (poissonMeasure
          (PoissonProcess.rateExposureParam rate exposure hmean * (1 - p))))
      (ofRateExposure rate exposure hmean p hp).toMeasure := by
  simpa [ofRateExposure] using
    splitCounts_hasLaw (PoissonProcess.rateExposureParam rate exposure hmean) p hp

end
end FiniteHorizonMarkedPoisson
end AppliedModelingLib.Probability
