import AL16SupplyDemandMatching.ContinuumExistence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.UniformOn

/-!
# Concrete PG23 Continuum Model

This module starts from the literal PG23 carrier: a finite strict ranking and
an unbounded real-valued score at every college.  The upstream AL16 continuum
development uses scores in `[0, 1]`; `pg23ScoreNormalize` is an explicit
strictly increasing coordinate change, not a replacement of the source score
semantics.  No market-clearing, lattice, or equal-cutoff conclusion is stored
as model data here.

Source anchors: `source_tex/model.tex:1-20` defines the applicant type,
matching, and stability; `:22-44` defines cutoff affordability, demand, and
clearing; `:48-65` gives the monoculture and polyculture score laws.
-/

namespace PG23MonocultureMatching

open Filter MeasureTheory Set
open AppliedModelingLib.Matching
open AL16SupplyDemandMatching

universe v

variable {College : Type v} [Fintype College]

/-- PG23 strict preference rankings are finite permutations of the colleges. -/
abbrev PG23Ranking (College : Type v) [Fintype College] :=
  AL16Ranking College

/-- A literal PG23 applicant type: a strict ranking and one real score per college. -/
abbrev PG23ApplicantType (College : Type v) [Fintype College] :=
  PG23Ranking College × (College -> ℝ)

/--
The source says a real law has connected support when its smallest closed
full-measure set is an interval.  On `ℝ`, the formal reading used here is that
the measure support is preconnected; the probability-measure premise supplies
nonemptiness separately where needed.
-/
def pg23ConnectedSupport (law : Measure ℝ) : Prop :=
  IsPreconnected law.support

/-- The source's real-valued estimated score coordinate. -/
def pg23SourceScore (theta : PG23ApplicantType College) (c : College) : ℝ :=
  theta.2 c

/-- The numerical rank underlying the source's strict preference ordering. -/
def pg23SourceRank (theta : PG23ApplicantType College) (c : College) : Nat :=
  (theta.1 c).val

/-- All colleges are strictly preferred to the outside option, as in the source model. -/
abbrev pg23SourcePrefers :
    PG23ApplicantType College -> Option College -> Option College -> Prop :=
  al16RankPrefers pg23SourceRank

/-- Relabel a strict ranking after a permutation of college names. -/
def pg23RelabelRanking (sigma : Equiv.Perm College) (ranking : PG23Ranking College) :
    PG23Ranking College :=
  sigma.symm.trans ranking

/-- Relabel a raw cutoff vector after a permutation of college names. -/
def pg23RelabelCutoff (sigma : Equiv.Perm College) (P : College -> ℝ) : College -> ℝ :=
  fun c => P (sigma.symm c)

/-- Relabel a literal PG23 applicant while preserving ranks and raw scores. -/
def pg23RelabelApplicant (sigma : Equiv.Perm College)
    (theta : PG23ApplicantType College) : PG23ApplicantType College :=
  ⟨pg23RelabelRanking sigma theta.1, fun c => theta.2 (sigma.symm c)⟩

/-- Relabel an iid coordinate-noise sample after a permutation of college names. -/
def pg23RelabelNoise (sigma : Equiv.Perm College) (noise : College -> ℝ) : College -> ℝ :=
  fun c => noise (sigma.symm c)

/-- The ranking relabeling is an equivalence, with inverse relabeling by `sigma.symm`. -/
theorem pg23RelabelRanking_symm_relabel (sigma : Equiv.Perm College)
    (ranking : PG23Ranking College) :
    pg23RelabelRanking sigma.symm (pg23RelabelRanking sigma ranking) = ranking := by
  ext c
  simp [pg23RelabelRanking]

/-- The inverse ranking relabeling cancels on the other side as well. -/
theorem pg23RelabelRanking_relabel_symm (sigma : Equiv.Perm College)
    (ranking : PG23Ranking College) :
    pg23RelabelRanking sigma (pg23RelabelRanking sigma.symm ranking) = ranking := by
  ext c
  simp [pg23RelabelRanking]

/-- The concrete ranking relabeling viewed as a finite carrier equivalence. -/
def pg23RelabelRankingEquiv (sigma : Equiv.Perm College) :
    PG23Ranking College ≃ PG23Ranking College where
  toFun := pg23RelabelRanking sigma
  invFun := pg23RelabelRanking sigma.symm
  left_inv := pg23RelabelRanking_symm_relabel sigma
  right_inv := pg23RelabelRanking_relabel_symm sigma

/-- Relabel a finite active-application set after a permutation of college names. -/
noncomputable def pg23RelabelActiveSet
    (sigma : Equiv.Perm College) (active : Finset College) : Finset College := by
  classical
  exact active.image sigma

@[simp]
theorem pg23RelabelActiveSet_mem
    (sigma : Equiv.Perm College) (active : Finset College) (c : College) :
    c ∈ pg23RelabelActiveSet sigma active ↔ sigma.symm c ∈ active := by
  classical
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨d, hd, rfl⟩
    simpa using hd
  · intro hc
    exact Finset.mem_image.mpr ⟨sigma.symm c, hc, by simp⟩

/--
The differential-access strategy profile used in PG23: the active colleges are
exactly the `k` best-ranked colleges, with Lean's zero-based ranks.
-/
noncomputable def pg23TopKApplicationSet (k : ℕ) (ranking : PG23Ranking College) :
    Finset College := by
  classical
  exact Finset.univ.filter fun c => (ranking c).val < k

@[simp]
theorem pg23TopKApplicationSet_mem (k : ℕ) (ranking : PG23Ranking College)
    (c : College) :
    c ∈ pg23TopKApplicationSet k ranking ↔ (ranking c).val < k := by
  classical
  simp [pg23TopKApplicationSet]

/-- Applying to more colleges expands the source top-k active set. -/
theorem pg23TopKApplicationSet_mono
    {k l : ℕ} (hkl : k ≤ l) (ranking : PG23Ranking College) :
    pg23TopKApplicationSet k ranking ⊆ pg23TopKApplicationSet l ranking := by
  classical
  intro c hc
  rw [pg23TopKApplicationSet_mem] at hc ⊢
  exact lt_of_lt_of_le hc hkl

/-- The first-ranked college is active whenever the applicant can apply somewhere. -/
theorem pg23TopKApplicationSet_top_mem
    [Nonempty College] (ranking : PG23Ranking College) {k : ℕ} (hk : 0 < k) :
    ranking.symm ⟨0, Fintype.card_pos⟩ ∈ pg23TopKApplicationSet k ranking := by
  classical
  rw [pg23TopKApplicationSet_mem]
  simpa using hk

/-- If `k` is at least the number of colleges, the top-k active set is all colleges. -/
theorem pg23TopKApplicationSet_eq_univ_of_card_le
    (ranking : PG23Ranking College) {k : ℕ}
    (hcard : Fintype.card College ≤ k) :
    pg23TopKApplicationSet k ranking = Finset.univ := by
  classical
  ext c
  simp [pg23TopKApplicationSet, lt_of_lt_of_le (ranking c).is_lt hcard]

/-- Relabeling a ranking relabels top-k active-set membership. -/
theorem pg23TopKApplicationSet_relabel_mem
    (sigma : Equiv.Perm College) (ranking : PG23Ranking College) (k : ℕ) :
    ∀ c : College,
      c ∈ pg23TopKApplicationSet k (pg23RelabelRanking sigma ranking) ↔
        sigma.symm c ∈ pg23TopKApplicationSet k ranking := by
  classical
  intro c
  simp [pg23TopKApplicationSet, pg23RelabelRanking]

/-- Relabeling a ranking relabels the top-k active set exactly. -/
theorem pg23TopKApplicationSet_relabel
    (sigma : Equiv.Perm College) (ranking : PG23Ranking College) (k : ℕ) :
    pg23TopKApplicationSet k (pg23RelabelRanking sigma ranking) =
      pg23RelabelActiveSet sigma (pg23TopKApplicationSet k ranking) := by
  classical
  ext c
  rw [pg23TopKApplicationSet_relabel_mem, pg23RelabelActiveSet_mem]

/--
Any college outside the top-`k` set is weakly lower utility than any college
inside it, provided utility is monotone with the applicant's strict ranking.
-/
theorem pg23TopKApplicationSet_utility_ge_complement
    (k : ℕ) (ranking : PG23Ranking College) (utility : College -> ℝ)
    (hrank_utility :
      ∀ c d : College, (ranking c).val < (ranking d).val ->
        utility d ≤ utility c) :
    ∀ c ∈ pg23TopKApplicationSet k ranking,
      ∀ d, d ∉ pg23TopKApplicationSet k ranking -> utility d ≤ utility c := by
  intro c hc d hd
  rw [pg23TopKApplicationSet_mem] at hc
  rw [pg23TopKApplicationSet_mem] at hd
  exact hrank_utility c d (lt_of_lt_of_le hc (le_of_not_gt hd))

/-- Coordinate relabeling of iid noise as Mathlib's measurable pi equivalence. -/
def pg23RelabelNoiseEquiv (sigma : Equiv.Perm College) :
    (College -> ℝ) ≃ᵐ (College -> ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : College => ℝ) sigma

@[simp]
theorem pg23RelabelCutoff_apply (sigma : Equiv.Perm College)
    (P : College -> ℝ) (c : College) :
    pg23RelabelCutoff sigma P c = P (sigma.symm c) :=
  rfl

/-- Pointwise order on literal raw cutoff vectors. -/
def pg23RawCutoffLe (P Q : College -> ℝ) : Prop :=
  ∀ c : College, P c ≤ Q c

/-- Coordinatewise supremum of a set of literal raw cutoff vectors. -/
noncomputable def pg23RawCutoffSup (Z : Set (College -> ℝ)) : College -> ℝ :=
  fun c => sSup ((fun P : College -> ℝ => P c) '' Z)

/-- Coordinatewise infimum of a set of literal raw cutoff vectors. -/
noncomputable def pg23RawCutoffInf (Z : Set (College -> ℝ)) : College -> ℝ :=
  fun c => sInf ((fun P : College -> ℝ => P c) '' Z)

/--
A greatest element of a relabeling-invariant family of raw cutoffs is fixed by
every college permutation.  The order premise is explicit pointwise order on
raw cutoff coordinates.
-/
theorem pg23RelabelCutoff_eq_of_greatest
    (valid : (College -> ℝ) -> Prop)
    (top : College -> ℝ)
    (htop : valid top ∧ ∀ P : College -> ℝ, valid P -> pg23RawCutoffLe P top)
    (hrelabel : ∀ (sigma : Equiv.Perm College) (P : College -> ℝ),
      valid P -> valid (pg23RelabelCutoff sigma P))
    (sigma : Equiv.Perm College) :
    pg23RelabelCutoff sigma top = top := by
  have hforward : pg23RawCutoffLe (pg23RelabelCutoff sigma top) top :=
    htop.2 _ (hrelabel sigma top htop.1)
  have hinverse : pg23RawCutoffLe (pg23RelabelCutoff sigma.symm top) top :=
    htop.2 _ (hrelabel sigma.symm top htop.1)
  funext c
  apply le_antisymm
  · exact hforward c
  · simpa [pg23RelabelCutoff] using hinverse (sigma.symm c)

/--
A least element of a relabeling-invariant family of raw cutoffs is fixed by
every college permutation.
-/
theorem pg23RelabelCutoff_eq_of_least
    (valid : (College -> ℝ) -> Prop)
    (bot : College -> ℝ)
    (hbot : valid bot ∧ ∀ P : College -> ℝ, valid P -> pg23RawCutoffLe bot P)
    (hrelabel : ∀ (sigma : Equiv.Perm College) (P : College -> ℝ),
      valid P -> valid (pg23RelabelCutoff sigma P))
    (sigma : Equiv.Perm College) :
    pg23RelabelCutoff sigma bot = bot := by
  have hforward : pg23RawCutoffLe bot (pg23RelabelCutoff sigma bot) :=
    hbot.2 _ (hrelabel sigma bot hbot.1)
  have hinverse : pg23RawCutoffLe bot (pg23RelabelCutoff sigma.symm bot) :=
    hbot.2 _ (hrelabel sigma.symm bot hbot.1)
  funext c
  apply le_antisymm
  · simpa [pg23RelabelCutoff] using hinverse (sigma.symm c)
  · exact hforward c

/-- A raw cutoff fixed by every college permutation has one common coordinate. -/
theorem pg23RawCutoff_constant_of_relabel_fixed
    [Nonempty College] (P : College -> ℝ)
    (hfixed : ∀ sigma : Equiv.Perm College, pg23RelabelCutoff sigma P = P) :
    ∃ p : ℝ, ∀ c : College, P c = p := by
  classical
  let c0 : College := Classical.choice inferInstance
  refine ⟨P c0, ?_⟩
  intro c
  have hswap := congrFun (hfixed (Equiv.swap c c0)) c
  simpa [pg23RelabelCutoff, c0] using hswap.symm

@[simp]
theorem pg23RelabelApplicant_score (sigma : Equiv.Perm College)
    (theta : PG23ApplicantType College) (c : College) :
    pg23SourceScore (pg23RelabelApplicant sigma theta) c =
      pg23SourceScore theta (sigma.symm c) :=
  rfl

@[simp]
theorem pg23RelabelApplicant_rank (sigma : Equiv.Perm College)
    (theta : PG23ApplicantType College) (c : College) :
    pg23SourceRank (pg23RelabelApplicant sigma theta) c =
      pg23SourceRank theta (sigma.symm c) := by
  simp [pg23RelabelApplicant, pg23RelabelRanking, pg23SourceRank]

/-- Literal applicant relabeling is measurable on the finite-ranking/raw-score carrier. -/
theorem pg23RelabelApplicant_measurable (sigma : Equiv.Perm College) :
    Measurable (pg23RelabelApplicant sigma :
      PG23ApplicantType College -> PG23ApplicantType College) := by
  unfold pg23RelabelApplicant pg23RelabelRanking
  fun_prop

/-- Strict preference is invariant under a simultaneous college relabeling. -/
theorem pg23SourcePrefers_relabel_iff (sigma : Equiv.Perm College)
    (theta : PG23ApplicantType College) (a b : Option College) :
    pg23SourcePrefers (pg23RelabelApplicant sigma theta)
        (Option.map sigma a) (Option.map sigma b) ↔
      pg23SourcePrefers theta a b := by
  cases a <;> cases b <;>
    simp [pg23SourcePrefers, al16RankPrefers]

/--
An explicit order embedding of raw source scores into the closed unit interval.
The score is always interior, but the closed codomain matches the AL16 cutoff
carrier and preserves every raw score/cutoff comparison.
-/
noncomputable def pg23ScoreNormalize (x : ℝ) : Set.Icc (0 : ℝ) 1 := by
  refine ⟨(Real.arctan x + Real.pi / 2) / Real.pi, ?_, ?_⟩
  · have hpos : 0 < Real.arctan x + Real.pi / 2 := by
      linarith [Real.neg_pi_div_two_lt_arctan x]
    exact (div_pos hpos Real.pi_pos).le
  · have hlt : Real.arctan x + Real.pi / 2 < Real.pi := by
      linarith [Real.arctan_lt_pi_div_two x]
    exact (div_le_one₀ Real.pi_pos).2 hlt.le

/-- The normalization preserves strict order of source scores. -/
theorem pg23ScoreNormalize_strictMono : StrictMono pg23ScoreNormalize := by
  intro x y hxy
  change (Real.arctan x + Real.pi / 2) / Real.pi <
    (Real.arctan y + Real.pi / 2) / Real.pi
  apply (div_lt_div_iff₀ Real.pi_pos Real.pi_pos).2
  exact mul_lt_mul_of_pos_right (by
    linarith [Real.arctan_strictMono hxy]) Real.pi_pos

/-- The normalization preserves and reflects weak source score comparisons. -/
theorem pg23ScoreNormalize_le_iff (x y : ℝ) :
    pg23ScoreNormalize x ≤ pg23ScoreNormalize y ↔ x ≤ y :=
  pg23ScoreNormalize_strictMono.le_iff_le

/-- The normalization preserves and reflects strict source score comparisons. -/
theorem pg23ScoreNormalize_lt_iff (x y : ℝ) :
    pg23ScoreNormalize x < pg23ScoreNormalize y ↔ x < y :=
  pg23ScoreNormalize_strictMono.lt_iff_lt

/-- Normalized real scores are strictly above the inactive sentinel `0`. -/
theorem pg23ScoreNormalize_pos (x : ℝ) :
    0 < (pg23ScoreNormalize x : ℝ) := by
  change 0 < (Real.arctan x + Real.pi / 2) / Real.pi
  have hpos : 0 < Real.arctan x + Real.pi / 2 := by
    linarith [Real.neg_pi_div_two_lt_arctan x]
  exact div_pos hpos Real.pi_pos

/-- Normalized real scores are strictly below the unit cutoff `1`. -/
theorem pg23ScoreNormalize_lt_one (x : ℝ) :
    (pg23ScoreNormalize x : ℝ) < 1 := by
  change (Real.arctan x + Real.pi / 2) / Real.pi < 1
  have hlt : Real.arctan x + Real.pi / 2 < Real.pi := by
    linarith [Real.arctan_lt_pi_div_two x]
  have hdiv :
      (Real.arctan x + Real.pi / 2) / Real.pi < Real.pi / Real.pi := by
    apply (div_lt_div_iff₀ Real.pi_pos Real.pi_pos).2
    nlinarith [hlt, Real.pi_pos]
  simpa [div_self (ne_of_gt Real.pi_pos)] using hdiv

/-- The AL16-form score vector induced by a literal PG23 applicant type. -/
noncomputable def pg23NormalizedScore (theta : PG23ApplicantType College) (c : College) :
    Set.Icc (0 : ℝ) 1 :=
  pg23ScoreNormalize (pg23SourceScore theta c)

/-- The literal PG23 type viewed through the AL16 source carrier. -/
noncomputable def pg23NormalizedStudent (theta : PG23ApplicantType College) :
    AL16SourceStudent College :=
  ⟨theta.1, pg23NormalizedScore theta⟩

/-- The raw-to-unit-interval applicant map is measurable. -/
theorem pg23NormalizedStudent_measurable :
    Measurable (pg23NormalizedStudent (College := College)) := by
  unfold pg23NormalizedStudent pg23NormalizedScore
  refine measurable_fst.prodMk ?_
  apply measurable_pi_lambda
  intro c
  apply Measurable.subtype_mk
  change Measurable (fun theta : PG23ApplicantType College =>
    ((Real.arctan (theta.2 c) + Real.pi / 2) / Real.pi : ℝ))
  fun_prop (disch := exact Real.continuous_arctan.measurable)

/-- The normalized A-L type law induced by a literal raw-score PG23 type law. -/
noncomputable def pg23NormalizedTypeLaw
    (typeLaw : Measure (PG23ApplicantType College)) :
    Measure (AL16SourceStudent College) :=
  Measure.map pg23NormalizedStudent typeLaw

/-- Normalizing a probability type law preserves total probability. -/
theorem pg23NormalizedTypeLaw_isProbabilityMeasure
    (typeLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure typeLaw] :
    IsProbabilityMeasure (pg23NormalizedTypeLaw typeLaw) := by
  unfold pg23NormalizedTypeLaw
  exact Measure.isProbabilityMeasure_map pg23NormalizedStudent_measurable.aemeasurable

/-- A raw PG23 cutoff vector transported into AL16's cutoff cube. -/
noncomputable def pg23NormalizedCutoff (P : College -> ℝ) : AL16Cutoff College :=
  fun c => pg23ScoreNormalize (P c)

/-- Relabel a normalized A-L cutoff vector by the same college permutation. -/
noncomputable def pg23RelabelNormalizedCutoff
    (sigma : Equiv.Perm College) (Q : AL16Cutoff College) : AL16Cutoff College :=
  fun c => Q (sigma.symm c)

/-- Normalization commutes with relabeling raw cutoff coordinates. -/
theorem pg23NormalizedCutoff_relabel (sigma : Equiv.Perm College) (P : College -> ℝ) :
    pg23NormalizedCutoff (pg23RelabelCutoff sigma P) =
      pg23RelabelNormalizedCutoff sigma (pg23NormalizedCutoff P) := by
  rfl

/-- Normalized relabeling is inverted by relabeling with the inverse permutation. -/
theorem pg23RelabelNormalizedCutoff_symm_relabel
    (sigma : Equiv.Perm College) (Q : AL16Cutoff College) :
    pg23RelabelNormalizedCutoff sigma.symm
      (pg23RelabelNormalizedCutoff sigma Q) = Q := by
  funext c
  simp [pg23RelabelNormalizedCutoff]

/--
Any greatest element of a relabeling-invariant family of normalized cutoffs is
fixed by every college permutation.  The order is the concrete A-L
coordinatewise order, not an assumed equal-cutoff conclusion.
-/
theorem pg23RelabelNormalizedCutoff_eq_of_greatest
    (valid : AL16Cutoff College -> Prop)
    (top : AL16Cutoff College)
    (htop : valid top ∧ ∀ P : AL16Cutoff College, valid P -> al16CutoffLe P top)
    (hrelabel : ∀ (sigma : Equiv.Perm College) (P : AL16Cutoff College),
      valid P -> valid (pg23RelabelNormalizedCutoff sigma P))
    (sigma : Equiv.Perm College) :
    pg23RelabelNormalizedCutoff sigma top = top := by
  have hforward : al16CutoffLe (pg23RelabelNormalizedCutoff sigma top) top :=
    htop.2 _ (hrelabel sigma top htop.1)
  have hinverse : al16CutoffLe (pg23RelabelNormalizedCutoff sigma.symm top) top :=
    htop.2 _ (hrelabel sigma.symm top htop.1)
  funext c
  apply Subtype.ext
  apply le_antisymm
  · exact hforward c
  · simpa [pg23RelabelNormalizedCutoff, al16CutoffValue] using hinverse (sigma.symm c)

/-- A least relabeling-invariant normalized cutoff is fixed by every relabeling. -/
theorem pg23RelabelNormalizedCutoff_eq_of_least
    (valid : AL16Cutoff College -> Prop)
    (bot : AL16Cutoff College)
    (hbot : valid bot ∧ ∀ P : AL16Cutoff College, valid P -> al16CutoffLe bot P)
    (hrelabel : ∀ (sigma : Equiv.Perm College) (P : AL16Cutoff College),
      valid P -> valid (pg23RelabelNormalizedCutoff sigma P))
    (sigma : Equiv.Perm College) :
    pg23RelabelNormalizedCutoff sigma bot = bot := by
  have hforward : al16CutoffLe bot (pg23RelabelNormalizedCutoff sigma bot) :=
    hbot.2 _ (hrelabel sigma bot hbot.1)
  have hinverse : al16CutoffLe bot (pg23RelabelNormalizedCutoff sigma.symm bot) :=
    hbot.2 _ (hrelabel sigma.symm bot hbot.1)
  funext c
  apply Subtype.ext
  apply le_antisymm
  · simpa [pg23RelabelNormalizedCutoff, al16CutoffValue] using
      hinverse (sigma.symm c)
  · exact hforward c

/-- A normalized cutoff fixed by every college permutation has one common coordinate. -/
theorem pg23NormalizedCutoff_constant_of_relabel_fixed
    [Nonempty College] (Q : AL16Cutoff College)
    (hfixed : ∀ sigma : Equiv.Perm College,
      pg23RelabelNormalizedCutoff sigma Q = Q) :
    ∃ q : ℝ, ∀ c : College, al16CutoffValue Q c = q := by
  classical
  let c0 : College := Classical.choice inferInstance
  refine ⟨al16CutoffValue Q c0, ?_⟩
  intro c
  have hswap := congrFun (hfixed (Equiv.swap c c0)) c
  have hswapval := congrArg Subtype.val hswap
  change (Q c : ℝ) = (Q c0 : ℝ)
  simpa [pg23RelabelNormalizedCutoff, c0] using hswapval.symm

/-- A college is affordable in PG23 exactly when its raw score meets the raw cutoff. -/
def pg23Affordable (P : College -> ℝ) (theta : PG23ApplicantType College)
    (c : College) : Prop :=
  P c ≤ pg23SourceScore theta c

/-- Colleges that are both active and affordable for a literal applicant. -/
noncomputable def pg23ActiveAffordableSet
    (active : Finset College) (P : College -> ℝ)
    (theta : PG23ApplicantType College) : Finset College := by
  classical
  exact active.filter fun c => pg23Affordable P theta c

@[simp]
theorem pg23ActiveAffordableSet_mem
    (active : Finset College) (P : College -> ℝ)
    (theta : PG23ApplicantType College) (c : College) :
    c ∈ pg23ActiveAffordableSet active P theta ↔
      c ∈ active ∧ pg23Affordable P theta c := by
  classical
  simp [pg23ActiveAffordableSet]

/--
The active-set version of PG23 favorite-affordable choice: choose the
best-ranked college among active affordable colleges, if any.
-/
noncomputable def pg23ActiveSourceChoice
    (active : Finset College) (P : College -> ℝ) :
    PG23ApplicantType College -> Option College :=
  fun theta =>
    if hfeasible : (pg23ActiveAffordableSet active P theta).Nonempty then
      some (Classical.choose
        (Finset.exists_min_image
          (pg23ActiveAffordableSet active P theta)
          (pg23SourceRank theta) hfeasible))
    else
      none

/-- Any active-source choice is active and affordable. -/
theorem pg23ActiveSourceChoice_some_active_affordable
    {active : Finset College} {P : College -> ℝ}
    {theta : PG23ApplicantType College} {c : College}
    (hchoice : pg23ActiveSourceChoice active P theta = some c) :
    c ∈ active ∧ pg23Affordable P theta c := by
  classical
  by_cases hfeasible : (pg23ActiveAffordableSet active P theta).Nonempty
  · have hc :
        c =
          Classical.choose
            (Finset.exists_min_image
              (pg23ActiveAffordableSet active P theta)
              (pg23SourceRank theta) hfeasible) := by
      simpa [pg23ActiveSourceChoice, hfeasible] using hchoice.symm
    subst c
    have hmem :=
      (Classical.choose_spec
        (Finset.exists_min_image
          (pg23ActiveAffordableSet active P theta)
          (pg23SourceRank theta) hfeasible)).1
    simpa [pg23ActiveAffordableSet_mem] using hmem
  · simp [pg23ActiveSourceChoice, hfeasible] at hchoice

/-- Any active-source choice has weakly best rank among active affordable colleges. -/
theorem pg23ActiveSourceChoice_rank_le_of_active_affordable
    {active : Finset College} {P : College -> ℝ}
    {theta : PG23ApplicantType College} {c d : College}
    (hchoice : pg23ActiveSourceChoice active P theta = some c)
    (hd_active : d ∈ active) (hd_affordable : pg23Affordable P theta d) :
    pg23SourceRank theta c ≤ pg23SourceRank theta d := by
  classical
  by_cases hfeasible : (pg23ActiveAffordableSet active P theta).Nonempty
  · have hc :
        c =
          Classical.choose
            (Finset.exists_min_image
              (pg23ActiveAffordableSet active P theta)
              (pg23SourceRank theta) hfeasible) := by
      simpa [pg23ActiveSourceChoice, hfeasible] using hchoice.symm
    subst c
    exact
      (Classical.choose_spec
        (Finset.exists_min_image
          (pg23ActiveAffordableSet active P theta)
          (pg23SourceRank theta) hfeasible)).2 d (by
            rw [pg23ActiveAffordableSet_mem]
            exact ⟨hd_active, hd_affordable⟩)
  · simp [pg23ActiveSourceChoice, hfeasible] at hchoice

/-- The raw active-set favorite-affordable choice specification. -/
def pg23ActiveDemandChoiceSemantics
    (choice :
      Finset College -> (College -> ℝ) ->
        PG23ApplicantType College -> Option College) : Prop :=
  ∀ active P theta,
    match choice active P theta with
    | none =>
        ∀ c : College, c ∈ active -> pg23SourceScore theta c < P c
    | some c =>
        c ∈ active ∧ pg23Affordable P theta c ∧
          ∀ d : College, d ∈ active -> pg23Affordable P theta d ->
            ¬ pg23SourcePrefers theta (some d) (some c)

/-- The active-choice implementation satisfies the raw active-set source rule. -/
theorem pg23ActiveSourceChoice_semantics :
    pg23ActiveDemandChoiceSemantics (College := College) pg23ActiveSourceChoice := by
  classical
  intro active P theta
  by_cases hfeasible : (pg23ActiveAffordableSet active P theta).Nonempty
  · simp only [pg23ActiveSourceChoice, hfeasible, dif_pos]
    let selected : College :=
      Classical.choose
        (Finset.exists_min_image
          (pg23ActiveAffordableSet active P theta)
          (pg23SourceRank theta) hfeasible)
    have hselected_mem :
        selected ∈ pg23ActiveAffordableSet active P theta :=
      (Classical.choose_spec
        (Finset.exists_min_image
          (pg23ActiveAffordableSet active P theta)
          (pg23SourceRank theta) hfeasible)).1
    have hselected_min :
        ∀ d : College,
          d ∈ pg23ActiveAffordableSet active P theta ->
            pg23SourceRank theta selected ≤ pg23SourceRank theta d :=
      (Classical.choose_spec
        (Finset.exists_min_image
          (pg23ActiveAffordableSet active P theta)
          (pg23SourceRank theta) hfeasible)).2
    have hselected_active_affordable :
        selected ∈ active ∧ pg23Affordable P theta selected := by
      simpa [selected, pg23ActiveAffordableSet_mem] using hselected_mem
    refine ⟨hselected_active_affordable.1, hselected_active_affordable.2, ?_⟩
    intro d hd_active hd_affordable
    have hd_mem : d ∈ pg23ActiveAffordableSet active P theta := by
      rw [pg23ActiveAffordableSet_mem]
      exact ⟨hd_active, hd_affordable⟩
    change ¬ pg23SourceRank theta d < pg23SourceRank theta selected
    exact not_lt_of_ge (hselected_min d hd_mem)
  · simp only [pg23ActiveSourceChoice, hfeasible]
    intro c hc_active
    by_contra hnot
    have hc_affordable : pg23Affordable P theta c := by
      unfold pg23Affordable
      exact le_of_not_gt hnot
    exact hfeasible ⟨c, by
      rw [pg23ActiveAffordableSet_mem]
      exact ⟨hc_active, hc_affordable⟩⟩

/-- Exact active-source choice fiber characterization. -/
theorem pg23ActiveSourceChoice_eq_some_iff
    (active : Finset College) (P : College -> ℝ)
    (theta : PG23ApplicantType College) (c : College) :
    pg23ActiveSourceChoice active P theta = some c ↔
      c ∈ active ∧ pg23Affordable P theta c ∧
        ∀ d : College, d ∈ active -> pg23Affordable P theta d ->
          ¬ pg23SourcePrefers theta (some d) (some c) := by
  constructor
  · intro hchoice
    have hsem := pg23ActiveSourceChoice_semantics
      (College := College) active P theta
    rw [hchoice] at hsem
    exact hsem
  · intro hc
    cases hchoice : pg23ActiveSourceChoice active P theta with
    | none =>
        have hsem := pg23ActiveSourceChoice_semantics
          (College := College) active P theta
        rw [hchoice] at hsem
        exact False.elim ((not_lt_of_ge hc.2.1) (hsem c hc.1))
    | some d =>
        have hdsem := pg23ActiveSourceChoice_semantics
          (College := College) active P theta
        rw [hchoice] at hdsem
        have hnot_dc := hc.2.2 d hdsem.1 hdsem.2.1
        have hnot_cd := hdsem.2.2 c hc.1 hc.2.1
        have hc_le_d :
            pg23SourceRank theta c ≤ pg23SourceRank theta d := by
          change ¬ pg23SourceRank theta d < pg23SourceRank theta c at hnot_dc
          exact le_of_not_gt hnot_dc
        have hd_le_c :
            pg23SourceRank theta d ≤ pg23SourceRank theta c := by
          change ¬ pg23SourceRank theta c < pg23SourceRank theta d at hnot_cd
          exact le_of_not_gt hnot_cd
        have hd_eq_c : d = c :=
          theta.1.injective (Fin.ext (le_antisymm hd_le_c hc_le_d))
        simpa [hd_eq_c] using hchoice

/-- Active-source choice is defined exactly when some active college is affordable. -/
theorem pg23ActiveSourceChoice_some_iff_exists_active_affordable
    (active : Finset College) (P : College -> ℝ)
    (theta : PG23ApplicantType College) :
    (∃ c : College, pg23ActiveSourceChoice active P theta = some c) ↔
      ∃ c : College, c ∈ active ∧ pg23Affordable P theta c := by
  classical
  constructor
  · rintro ⟨c, hchoice⟩
    exact ⟨c, pg23ActiveSourceChoice_some_active_affordable hchoice⟩
  · rintro ⟨c, hc_active, hc_affordable⟩
    have hfeasible : (pg23ActiveAffordableSet active P theta).Nonempty := by
      refine ⟨c, ?_⟩
      rw [pg23ActiveAffordableSet_mem]
      exact ⟨hc_active, hc_affordable⟩
    refine ⟨Classical.choose
      (Finset.exists_min_image
        (pg23ActiveAffordableSet active P theta)
        (pg23SourceRank theta) hfeasible), ?_⟩
    simp [pg23ActiveSourceChoice, hfeasible]

/--
If one active set is contained in another, existence of an active-source match
is preserved.
-/
theorem pg23ActiveSourceChoice_exists_mono_active
    {active larger : Finset College} {P : College -> ℝ}
    {theta : PG23ApplicantType College}
    (hsubset : active ⊆ larger)
    (hmatched :
      ∃ c : College, pg23ActiveSourceChoice active P theta = some c) :
    ∃ c : College, pg23ActiveSourceChoice larger P theta = some c := by
  rcases
    (pg23ActiveSourceChoice_some_iff_exists_active_affordable active P theta).mp
      hmatched with ⟨c, hc_active, hc_affordable⟩
  exact
    (pg23ActiveSourceChoice_some_iff_exists_active_affordable larger P theta).mpr
      ⟨c, hsubset hc_active, hc_affordable⟩

/-- Applying to more top-ranked colleges preserves existence of an active match. -/
theorem pg23ActiveSourceChoice_topK_exists_mono_applications
    {k l : ℕ} (hkl : k ≤ l) (ranking : PG23Ranking College)
    {P : College -> ℝ} {theta : PG23ApplicantType College}
    (hmatched :
      ∃ c : College,
        pg23ActiveSourceChoice (pg23TopKApplicationSet k ranking) P theta =
          some c) :
    ∃ c : College,
      pg23ActiveSourceChoice (pg23TopKApplicationSet l ranking) P theta =
        some c :=
  pg23ActiveSourceChoice_exists_mono_active
    (pg23TopKApplicationSet_mono hkl ranking) hmatched

/-- Raw affordability is invariant under a simultaneous college relabeling. -/
theorem pg23Affordable_relabel_iff (sigma : Equiv.Perm College)
    (P : College -> ℝ) (theta : PG23ApplicantType College) (c : College) :
    pg23Affordable (pg23RelabelCutoff sigma P) (pg23RelabelApplicant sigma theta)
        (sigma c) ↔
      pg23Affordable P theta c := by
  simp [pg23Affordable]

/-- Simultaneous relabeling transports the active-affordable feasible set. -/
theorem pg23ActiveAffordableSet_relabel
    (sigma : Equiv.Perm College) (active : Finset College)
    (P : College -> ℝ) (theta : PG23ApplicantType College) :
    pg23ActiveAffordableSet
        (pg23RelabelActiveSet sigma active) (pg23RelabelCutoff sigma P)
        (pg23RelabelApplicant sigma theta) =
      pg23RelabelActiveSet sigma (pg23ActiveAffordableSet active P theta) := by
  classical
  ext c
  simp [pg23ActiveAffordableSet, pg23RelabelActiveSet, pg23Affordable]
  constructor
  · rintro ⟨⟨a, ha_active, hsig⟩, haff⟩
    refine ⟨a, ⟨ha_active, ?_⟩, hsig⟩
    have hc : sigma.symm c = a := by
      rw [← hsig]
      simp
    simpa [hc] using haff
  · rintro ⟨a, ⟨ha_active, haff⟩, hsig⟩
    refine ⟨⟨a, ha_active, hsig⟩, ?_⟩
    have hc : sigma.symm c = a := by
      rw [← hsig]
      simp
    simpa [hc] using haff

/--
Active-source choice is equivariant under simultaneous relabeling of colleges,
active applications, raw cutoffs, and applicant types.
-/
theorem pg23ActiveSourceChoice_relabel
    (sigma : Equiv.Perm College) (active : Finset College)
    (P : College -> ℝ) (theta : PG23ApplicantType College) :
    pg23ActiveSourceChoice
        (pg23RelabelActiveSet sigma active) (pg23RelabelCutoff sigma P)
        (pg23RelabelApplicant sigma theta) =
      Option.map sigma (pg23ActiveSourceChoice active P theta) := by
  classical
  have horiginal_sem := pg23ActiveSourceChoice_semantics
    (College := College) active P theta
  have hrel_sem := pg23ActiveSourceChoice_semantics
    (College := College) (pg23RelabelActiveSet sigma active)
    (pg23RelabelCutoff sigma P) (pg23RelabelApplicant sigma theta)
  cases horiginal : pg23ActiveSourceChoice active P theta with
  | none =>
      simp only [Option.map_none]
      cases hrel :
          pg23ActiveSourceChoice
            (pg23RelabelActiveSet sigma active) (pg23RelabelCutoff sigma P)
            (pg23RelabelApplicant sigma theta) with
      | none => rfl
      | some d =>
          exfalso
          rw [horiginal] at horiginal_sem
          rw [hrel] at hrel_sem
          have hd_active : sigma.symm d ∈ active := by
            have hd_active_rel := hrel_sem.1
            rwa [pg23RelabelActiveSet_mem] at hd_active_rel
          have hd_affordable : pg23Affordable P theta (sigma.symm d) := by
            simpa using
              (pg23Affordable_relabel_iff sigma P theta (sigma.symm d)).mp
                (by simpa using hrel_sem.2.1)
          have hd_lt := horiginal_sem (sigma.symm d) hd_active
          exact (not_lt_of_ge hd_affordable) hd_lt
  | some c =>
      simp only [Option.map_some]
      cases hrel :
          pg23ActiveSourceChoice
            (pg23RelabelActiveSet sigma active) (pg23RelabelCutoff sigma P)
            (pg23RelabelApplicant sigma theta) with
      | none =>
          exfalso
          rw [horiginal] at horiginal_sem
          rw [hrel] at hrel_sem
          have hc_active : sigma c ∈ pg23RelabelActiveSet sigma active := by
            rw [pg23RelabelActiveSet_mem]
            simp [horiginal_sem.1]
          have hc_affordable :
              pg23Affordable (pg23RelabelCutoff sigma P)
                (pg23RelabelApplicant sigma theta) (sigma c) :=
            (pg23Affordable_relabel_iff sigma P theta c).mpr
              horiginal_sem.2.1
          have hc_lt := hrel_sem (sigma c) hc_active
          exact (not_lt_of_ge hc_affordable) hc_lt
      | some d =>
          rw [horiginal] at horiginal_sem
          rw [hrel] at hrel_sem
          have hd_active : sigma.symm d ∈ active := by
            have hd_active_rel := hrel_sem.1
            rwa [pg23RelabelActiveSet_mem] at hd_active_rel
          have hd_affordable : pg23Affordable P theta (sigma.symm d) := by
            simpa using
              (pg23Affordable_relabel_iff sigma P theta (sigma.symm d)).mp
                (by simpa using hrel_sem.2.1)
          have hc_active_rel : sigma c ∈ pg23RelabelActiveSet sigma active := by
            rw [pg23RelabelActiveSet_mem]
            simp [horiginal_sem.1]
          have hc_affordable_rel :
              pg23Affordable (pg23RelabelCutoff sigma P)
                (pg23RelabelApplicant sigma theta) (sigma c) :=
            (pg23Affordable_relabel_iff sigma P theta c).mpr
              horiginal_sem.2.1
          have hnot_orig :=
            horiginal_sem.2.2 (sigma.symm d) hd_active hd_affordable
          have hnot_rel :=
            hrel_sem.2.2 (sigma c) hc_active_rel hc_affordable_rel
          have hle_c :
              pg23SourceRank theta c ≤
                pg23SourceRank theta (sigma.symm d) := by
            change ¬ pg23SourceRank theta (sigma.symm d) <
              pg23SourceRank theta c at hnot_orig
            exact le_of_not_gt hnot_orig
          have hle_d :
              pg23SourceRank theta (sigma.symm d) ≤
                pg23SourceRank theta c := by
            change ¬
              pg23SourceRank (pg23RelabelApplicant sigma theta) (sigma c) <
                pg23SourceRank (pg23RelabelApplicant sigma theta) d at hnot_rel
            have hnot :
                ¬ pg23SourceRank theta c <
                  pg23SourceRank theta (sigma.symm d) := by
              simpa using hnot_rel
            exact le_of_not_gt hnot
          have hrank :
              pg23SourceRank theta c =
                pg23SourceRank theta (sigma.symm d) :=
            le_antisymm hle_c hle_d
          have hc_eq : c = sigma.symm d :=
            theta.1.injective (Fin.ext hrank)
          have hd_eq : d = sigma c := by
            calc
            d = sigma (sigma.symm d) := by simp
            _ = sigma c := by rw [← hc_eq]
          rw [hd_eq]

/--
Set-level active-choice transport under applicant relabeling.  This is the
preimage form used by aggregate-demand relabeling proofs.
-/
theorem pg23ActiveSourceChoice_relabel_preimage
    (sigma : Equiv.Perm College)
    (active : PG23ApplicantType College -> Finset College)
    (P : College -> ℝ) (c : College)
    (hactive :
      ∀ theta : PG23ApplicantType College,
        active (pg23RelabelApplicant sigma theta) =
          pg23RelabelActiveSet sigma (active theta)) :
    (pg23RelabelApplicant sigma) ⁻¹'
        {theta' : PG23ApplicantType College |
          pg23ActiveSourceChoice (active theta') (pg23RelabelCutoff sigma P)
            theta' = some (sigma c)} =
      {theta : PG23ApplicantType College |
        pg23ActiveSourceChoice (active theta) P theta = some c} := by
  ext theta
  rw [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_setOf_eq, hactive theta,
    pg23ActiveSourceChoice_relabel sigma (active theta) P theta]
  cases hchoice : pg23ActiveSourceChoice (active theta) P theta with
  | none =>
      simp
  | some d =>
      simp [sigma.apply_eq_iff_eq]

/-- Top-k active-choice transport under applicant relabeling. -/
theorem pg23TopKActiveSourceChoice_relabel_preimage
    (sigma : Equiv.Perm College) (k : ℕ)
    (P : College -> ℝ) (c : College) :
    (pg23RelabelApplicant sigma) ⁻¹'
        {theta' : PG23ApplicantType College |
          pg23ActiveSourceChoice (pg23TopKApplicationSet k theta'.1)
            (pg23RelabelCutoff sigma P) theta' = some (sigma c)} =
      {theta : PG23ApplicantType College |
        pg23ActiveSourceChoice (pg23TopKApplicationSet k theta.1) P theta =
          some c} :=
  pg23ActiveSourceChoice_relabel_preimage sigma
    (fun theta : PG23ApplicantType College => pg23TopKApplicationSet k theta.1)
    P c (by
      intro theta
      exact pg23TopKApplicationSet_relabel sigma theta.1 k)

/--
The literal PG23 favorite-affordable demand choice, implemented through the
order-equivalent AL16 selector.  The following theorem exposes the raw
affordability semantics, so the normalized representation is not visible as a
source-model premise.
-/
noncomputable def pg23SourceChoice (P : College -> ℝ) :
    PG23ApplicantType College -> Option College :=
  fun theta =>
    al16SourceChoice (pg23NormalizedCutoff P) (pg23NormalizedStudent theta)

/-- Raw PG23 affordability agrees exactly with the normalized AL16 comparison. -/
theorem pg23Affordable_iff_al16Affordable
    (P : College -> ℝ) (theta : PG23ApplicantType College) (c : College) :
    pg23Affordable P theta c ↔
      al16Affordable al16SourceScore (pg23NormalizedCutoff P)
        (pg23NormalizedStudent theta) c := by
  change P c ≤ pg23SourceScore theta c ↔
    pg23ScoreNormalize (P c) ≤ pg23ScoreNormalize (pg23SourceScore theta c)
  exact (pg23ScoreNormalize_le_iff (P c) (pg23SourceScore theta c)).symm

/--
Bounded active score for PG23 application restrictions. Active colleges keep
their normalized raw score; inactive colleges receive the sentinel score `0`.
-/
noncomputable def pg23ActiveNormalizedScore
    (active : PG23ApplicantType College -> Finset College)
    (theta : PG23ApplicantType College) (c : College) : Set.Icc (0 : ℝ) 1 := by
  classical
  exact if c ∈ active theta then pg23NormalizedScore theta c else
    ⟨0, by norm_num, by norm_num⟩

/-- Favorite-affordable choice for the bounded active-score representation. -/
noncomputable def pg23ActiveNormalizedChoice
    (active : PG23ApplicantType College -> Finset College)
    (Q : AL16Cutoff College) : PG23ApplicantType College -> Option College :=
  al16FavoriteAffordableChoice (pg23ActiveNormalizedScore active) pg23SourceRank Q

/--
At normalized raw cutoffs, bounded active-score affordability is exactly
source active affordability. Inactive colleges are excluded because every
normalized raw cutoff is strictly positive.
-/
theorem pg23ActiveNormalizedAffordable_iff
    (active : PG23ApplicantType College -> Finset College)
    (P : College -> ℝ) (theta : PG23ApplicantType College) (c : College) :
    al16Affordable (pg23ActiveNormalizedScore active) (pg23NormalizedCutoff P)
        theta c ↔
      c ∈ active theta ∧ pg23Affordable P theta c := by
  constructor
  · intro haff
    have hc_active : c ∈ active theta := by
      by_contra hc
      have hle_zero : (pg23ScoreNormalize (P c) : ℝ) ≤ 0 := by
        simpa [al16Affordable, al16CutoffValue, al16ScoreValue,
          pg23ActiveNormalizedScore, pg23NormalizedCutoff, hc] using haff
      exact (not_lt_of_ge hle_zero) (pg23ScoreNormalize_pos (P c))
    have hnorm :
        pg23ScoreNormalize (P c) ≤
          pg23ScoreNormalize (pg23SourceScore theta c) := by
      simpa [al16Affordable, al16CutoffValue, al16ScoreValue,
        pg23ActiveNormalizedScore, pg23NormalizedCutoff, pg23NormalizedScore,
        hc_active] using haff
    exact ⟨hc_active,
      (pg23ScoreNormalize_le_iff (P c) (pg23SourceScore theta c)).mp hnorm⟩
  · rintro ⟨hc_active, hraw⟩
    have hnorm :
        pg23ScoreNormalize (P c) ≤
          pg23ScoreNormalize (pg23SourceScore theta c) :=
      (pg23ScoreNormalize_le_iff (P c) (pg23SourceScore theta c)).mpr hraw
    simpa [al16Affordable, al16CutoffValue, al16ScoreValue,
      pg23ActiveNormalizedScore, pg23NormalizedCutoff, pg23NormalizedScore,
      hc_active] using hnorm

/--
The bounded active-score selector agrees with PG23's source active selector at
the normalized image of any finite raw cutoff.
-/
theorem pg23ActiveNormalizedChoice_normalizedCutoff_eq
    (active : PG23ApplicantType College -> Finset College)
    (P : College -> ℝ) (theta : PG23ApplicantType College) :
    pg23ActiveNormalizedChoice active (pg23NormalizedCutoff P) theta =
      pg23ActiveSourceChoice (active theta) P theta := by
  classical
  unfold pg23ActiveNormalizedChoice
  have hsem := al16FavoriteAffordableChoice_semantics
    (score := pg23ActiveNormalizedScore active) (rank := pg23SourceRank)
    (P := pg23NormalizedCutoff P) (theta := theta)
  cases hchoice :
      al16FavoriteAffordableChoice (pg23ActiveNormalizedScore active)
        pg23SourceRank (pg23NormalizedCutoff P) theta with
  | none =>
      rw [hchoice] at hsem
      cases hactive_choice : pg23ActiveSourceChoice (active theta) P theta with
      | none => rfl
      | some c =>
          have hc := pg23ActiveSourceChoice_some_active_affordable hactive_choice
          have haff :
              al16Affordable (pg23ActiveNormalizedScore active)
                (pg23NormalizedCutoff P) theta c :=
            (pg23ActiveNormalizedAffordable_iff active P theta c).mpr hc
          exact False.elim ((not_le_of_gt (hsem c)) haff)
  | some c =>
      rw [hchoice] at hsem
      have hc_active_affordable :
          c ∈ active theta ∧ pg23Affordable P theta c :=
        (pg23ActiveNormalizedAffordable_iff active P theta c).mp hsem.1
      have hno_better :
          ∀ d : College, d ∈ active theta -> pg23Affordable P theta d ->
            ¬ pg23SourcePrefers theta (some d) (some c) := by
        intro d hd_active hd_affordable
        have hd_norm :
            al16Affordable (pg23ActiveNormalizedScore active)
              (pg23NormalizedCutoff P) theta d :=
          (pg23ActiveNormalizedAffordable_iff active P theta d).mpr
            ⟨hd_active, hd_affordable⟩
        exact hsem.2 d hd_norm
      have hactive_choice :
          pg23ActiveSourceChoice (active theta) P theta = some c :=
        (pg23ActiveSourceChoice_eq_some_iff (active theta) P theta c).mpr
          ⟨hc_active_affordable.1, hc_active_affordable.2, hno_better⟩
      simp [hactive_choice]

/-- The monoculture type law shares one noisy score across all colleges. -/
def pg23MonocultureType (value noise : ℝ) (ranking : PG23Ranking College) :
    PG23ApplicantType College :=
  ⟨ranking, fun _ => value + noise⟩

/-- The polyculture type law draws one noisy score independently for each college. -/
def pg23PolycultureType (value : ℝ) (ranking : PG23Ranking College)
    (noise : College -> ℝ) : PG23ApplicantType College :=
  ⟨ranking, fun c => value + noise c⟩

/-- The monoculture score formula is literally `v + X` at every college. -/
@[simp]
theorem pg23MonocultureType_score
    (value noise : ℝ) (ranking : PG23Ranking College) (c : College) :
    pg23SourceScore (pg23MonocultureType value noise ranking) c = value + noise :=
  rfl

/-- The polyculture score formula is literally `v + X_c` at each college. -/
@[simp]
theorem pg23PolycultureType_score
    (value : ℝ) (ranking : PG23Ranking College) (noise : College -> ℝ)
    (c : College) :
    pg23SourceScore (pg23PolycultureType value ranking noise) c = value + noise c :=
  rfl

/-- The source's uniform distribution over finite strict preference rankings. -/
noncomputable def pg23UniformRankingLaw : Measure (PG23Ranking College) :=
  ProbabilityTheory.uniformOn Set.univ

/-- The finite-ranking law used by both PG23 economies is a probability measure. -/
theorem pg23UniformRankingLaw_isProbabilityMeasure :
    IsProbabilityMeasure (pg23UniformRankingLaw (College := College)) := by
  classical
  letI : Nonempty (PG23Ranking College) := ⟨Fintype.equivFin College⟩
  change IsProbabilityMeasure (ProbabilityTheory.uniformOn Set.univ)
  infer_instance

/-- The source's uniform finite-ranking law is invariant under every college relabeling. -/
theorem pg23UniformRankingLaw_relabel (sigma : Equiv.Perm College) :
    Measure.map (pg23RelabelRanking sigma) (pg23UniformRankingLaw (College := College)) =
      pg23UniformRankingLaw (College := College) := by
  classical
  ext s hs
  rw [Measure.map_apply (Measurable.of_discrete) hs]
  rw [pg23UniformRankingLaw, ProbabilityTheory.uniformOn_univ,
    ProbabilityTheory.uniformOn_univ]
  rw [Measure.count_apply (MeasurableSet.of_discrete), Measure.count_apply hs]
  congr 1
  simpa [pg23RelabelRankingEquiv] using
    (Set.encard_preimage_of_bijective (pg23RelabelRankingEquiv sigma).bijective s)

/-- College relabeling preserves the concrete uniform-ranking law. -/
theorem pg23UniformRankingLaw_relabel_preserving (sigma : Equiv.Perm College) :
    MeasurePreserving (pg23RelabelRanking sigma)
      (pg23UniformRankingLaw (College := College))
      (pg23UniformRankingLaw (College := College)) :=
  ⟨Measurable.of_discrete, pg23UniformRankingLaw_relabel sigma⟩

/-- Independent value, preference-ranking, and common-noise sample space. -/
abbrev PG23MonocultureSample (College : Type v) [Fintype College] :=
  (ℝ × PG23Ranking College) × ℝ

/-- Independent value, preference-ranking, and coordinate-noise sample space. -/
abbrev PG23PolycultureSample (College : Type v) [Fintype College] :=
  (ℝ × PG23Ranking College) × (College -> ℝ)

/-- The source map from a monoculture sample to its applicant type. -/
def pg23MonocultureSampleToType :
    PG23MonocultureSample College -> PG23ApplicantType College :=
  fun sample => pg23MonocultureType sample.1.1 sample.2 sample.1.2

/-- The source map from a polyculture sample to its applicant type. -/
def pg23PolycultureSampleToType :
    PG23PolycultureSample College -> PG23ApplicantType College :=
  fun sample => pg23PolycultureType sample.1.1 sample.1.2 sample.2

/-- The monoculture source type map is measurable. -/
theorem pg23MonocultureSampleToType_measurable :
    Measurable (pg23MonocultureSampleToType (College := College)) := by
  unfold pg23MonocultureSampleToType pg23MonocultureType
  fun_prop

/-- The polyculture source type map is measurable. -/
theorem pg23PolycultureSampleToType_measurable :
    Measurable (pg23PolycultureSampleToType (College := College)) := by
  unfold pg23PolycultureSampleToType pg23PolycultureType
  fun_prop

/--
The induced monoculture type law.  It is the pushforward of independent value,
uniform ranking, and one common noise draw, matching `model.tex:51-55`.
-/
noncomputable def pg23MonocultureTypeLaw
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw] :
    Measure (PG23ApplicantType College) :=
  Measure.map pg23MonocultureSampleToType
    ((valueLaw.prod (pg23UniformRankingLaw (College := College))).prod noiseLaw)

/--
The induced polyculture type law.  It is the pushforward of independent value,
uniform ranking, and an iid coordinate-noise vector, matching `model.tex:57-61`.
-/
noncomputable def pg23PolycultureTypeLaw
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw] :
    Measure (PG23ApplicantType College) :=
  Measure.map pg23PolycultureSampleToType
    ((valueLaw.prod (pg23UniformRankingLaw (College := College))).prod
      (Measure.pi fun _ : College => noiseLaw))

/-- The source construction preserves total probability in the monoculture case. -/
theorem pg23MonocultureTypeLaw_isProbabilityMeasure
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw] :
    IsProbabilityMeasure
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) := by
  letI : IsProbabilityMeasure (pg23UniformRankingLaw (College := College)) :=
    pg23UniformRankingLaw_isProbabilityMeasure
  unfold pg23MonocultureTypeLaw
  exact Measure.isProbabilityMeasure_map
    pg23MonocultureSampleToType_measurable.aemeasurable

/-- The source construction preserves total probability in the polyculture case. -/
theorem pg23PolycultureTypeLaw_isProbabilityMeasure
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw] :
    IsProbabilityMeasure
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw) := by
  letI : IsProbabilityMeasure (pg23UniformRankingLaw (College := College)) :=
    pg23UniformRankingLaw_isProbabilityMeasure
  unfold pg23PolycultureTypeLaw
  exact Measure.isProbabilityMeasure_map
    pg23PolycultureSampleToType_measurable.aemeasurable

/-- Simultaneous value/ranking/noise relabeling of a monoculture source sample. -/
def pg23RelabelMonocultureSample (sigma : Equiv.Perm College) :
    PG23MonocultureSample College -> PG23MonocultureSample College :=
  Prod.map (Prod.map id (pg23RelabelRanking sigma)) id

/-- Simultaneous value/ranking/noise relabeling of a polyculture source sample. -/
def pg23RelabelPolycultureSample (sigma : Equiv.Perm College) :
    PG23PolycultureSample College -> PG23PolycultureSample College :=
  Prod.map (Prod.map id (pg23RelabelRanking sigma)) (pg23RelabelNoise sigma)

/-- Iid coordinate noise is invariant under the literal coordinate relabeling. -/
theorem pg23IidNoiseLaw_relabel_preserving (sigma : Equiv.Perm College)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] :
    MeasurePreserving (pg23RelabelNoise sigma)
      (Measure.pi fun _ : College => noiseLaw)
      (Measure.pi fun _ : College => noiseLaw) := by
  have hfun : (pg23RelabelNoiseEquiv sigma :
      (College -> ℝ) -> (College -> ℝ)) = pg23RelabelNoise sigma := by
    funext noise c
    obtain ⟨d, rfl⟩ := sigma.surjective c
    change (MeasurableEquiv.piCongrLeft (fun _ : College => ℝ) sigma) noise (sigma d) =
      noise (sigma.symm (sigma d))
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    simp
  rw [← hfun]
  exact MeasureTheory.measurePreserving_piCongrLeft
    (α := fun _ : College => ℝ) (μ := fun _ : College => noiseLaw) sigma

/-- The product law of a monoculture sample is invariant under college relabeling. -/
theorem pg23MonocultureSampleLaw_relabel_preserving (sigma : Equiv.Perm College)
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw] :
    MeasurePreserving (pg23RelabelMonocultureSample sigma)
      ((valueLaw.prod (pg23UniformRankingLaw (College := College))).prod noiseLaw)
      ((valueLaw.prod (pg23UniformRankingLaw (College := College))).prod noiseLaw) := by
  letI : IsProbabilityMeasure (pg23UniformRankingLaw (College := College)) :=
    pg23UniformRankingLaw_isProbabilityMeasure
  unfold pg23RelabelMonocultureSample
  simpa using
    ((MeasurePreserving.id valueLaw).prod
      (pg23UniformRankingLaw_relabel_preserving sigma) |>.prod
        (MeasurePreserving.id noiseLaw))

/-- The product law of a polyculture sample is invariant under college relabeling. -/
theorem pg23PolycultureSampleLaw_relabel_preserving (sigma : Equiv.Perm College)
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw] :
    MeasurePreserving (pg23RelabelPolycultureSample sigma)
      ((valueLaw.prod (pg23UniformRankingLaw (College := College))).prod
        (Measure.pi fun _ : College => noiseLaw))
      ((valueLaw.prod (pg23UniformRankingLaw (College := College))).prod
        (Measure.pi fun _ : College => noiseLaw)) := by
  letI : IsProbabilityMeasure (pg23UniformRankingLaw (College := College)) :=
    pg23UniformRankingLaw_isProbabilityMeasure
  unfold pg23RelabelPolycultureSample
  simpa using
    ((MeasurePreserving.id valueLaw).prod
      (pg23UniformRankingLaw_relabel_preserving sigma) |>.prod
        (pg23IidNoiseLaw_relabel_preserving sigma noiseLaw))

/-- The literal monoculture type map commutes with simultaneous relabeling. -/
theorem pg23RelabelApplicant_monocultureSampleToType (sigma : Equiv.Perm College)
    (sample : PG23MonocultureSample College) :
    pg23RelabelApplicant sigma (pg23MonocultureSampleToType sample) =
      pg23MonocultureSampleToType (pg23RelabelMonocultureSample sigma sample) :=
  rfl

/-- The literal polyculture type map commutes with simultaneous relabeling. -/
theorem pg23RelabelApplicant_polycultureSampleToType (sigma : Equiv.Perm College)
    (sample : PG23PolycultureSample College) :
    pg23RelabelApplicant sigma (pg23PolycultureSampleToType sample) =
      pg23PolycultureSampleToType (pg23RelabelPolycultureSample sigma sample) :=
  rfl

/-- The monoculture type law is invariant under every permutation of college names. -/
theorem pg23MonocultureTypeLaw_relabel (sigma : Equiv.Perm College)
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw] :
    Measure.map (pg23RelabelApplicant sigma)
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) =
      pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw := by
  unfold pg23MonocultureTypeLaw
  letI : IsProbabilityMeasure (pg23UniformRankingLaw (College := College)) :=
    pg23UniformRankingLaw_isProbabilityMeasure
  have hsample := pg23MonocultureSampleLaw_relabel_preserving sigma valueLaw noiseLaw
  calc
    Measure.map (pg23RelabelApplicant sigma)
        (Measure.map pg23MonocultureSampleToType
          ((valueLaw.prod (pg23UniformRankingLaw (College := College))).prod noiseLaw)) =
        Measure.map (pg23RelabelApplicant sigma ∘ pg23MonocultureSampleToType)
          ((valueLaw.prod (pg23UniformRankingLaw (College := College))).prod noiseLaw) :=
      Measure.map_map (pg23RelabelApplicant_measurable sigma)
        pg23MonocultureSampleToType_measurable
    _ = Measure.map (pg23MonocultureSampleToType ∘ pg23RelabelMonocultureSample sigma)
          ((valueLaw.prod (pg23UniformRankingLaw (College := College))).prod noiseLaw) := by
      congr 1
    _ = Measure.map pg23MonocultureSampleToType
          (Measure.map (pg23RelabelMonocultureSample sigma)
            ((valueLaw.prod (pg23UniformRankingLaw (College := College))).prod noiseLaw)) :=
      (Measure.map_map pg23MonocultureSampleToType_measurable hsample.measurable).symm
    _ = Measure.map pg23MonocultureSampleToType
          ((valueLaw.prod (pg23UniformRankingLaw (College := College))).prod noiseLaw) := by
      rw [hsample.map_eq]

/-- The polyculture type law is invariant under every permutation of college names. -/
theorem pg23PolycultureTypeLaw_relabel (sigma : Equiv.Perm College)
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw] :
    Measure.map (pg23RelabelApplicant sigma)
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw) =
      pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw := by
  unfold pg23PolycultureTypeLaw
  letI : IsProbabilityMeasure (pg23UniformRankingLaw (College := College)) :=
    pg23UniformRankingLaw_isProbabilityMeasure
  have hsample := pg23PolycultureSampleLaw_relabel_preserving sigma valueLaw noiseLaw
  calc
    Measure.map (pg23RelabelApplicant sigma)
        (Measure.map pg23PolycultureSampleToType
          ((valueLaw.prod (pg23UniformRankingLaw (College := College))).prod
            (Measure.pi fun _ : College => noiseLaw))) =
        Measure.map (pg23RelabelApplicant sigma ∘ pg23PolycultureSampleToType)
          ((valueLaw.prod (pg23UniformRankingLaw (College := College))).prod
            (Measure.pi fun _ : College => noiseLaw)) :=
      Measure.map_map (pg23RelabelApplicant_measurable sigma)
        pg23PolycultureSampleToType_measurable
    _ = Measure.map (pg23PolycultureSampleToType ∘ pg23RelabelPolycultureSample sigma)
          ((valueLaw.prod (pg23UniformRankingLaw (College := College))).prod
            (Measure.pi fun _ : College => noiseLaw)) := by
      congr 1
    _ = Measure.map pg23PolycultureSampleToType
          (Measure.map (pg23RelabelPolycultureSample sigma)
            ((valueLaw.prod (pg23UniformRankingLaw (College := College))).prod
              (Measure.pi fun _ : College => noiseLaw))) :=
      (Measure.map_map pg23PolycultureSampleToType_measurable hsample.measurable).symm
    _ = Measure.map pg23PolycultureSampleToType
          ((valueLaw.prod (pg23UniformRankingLaw (College := College))).prod
            (Measure.pi fun _ : College => noiseLaw)) := by
      rw [hsample.map_eq]

/--
The score-level-null regularity used by the continuum supply-and-demand
argument.  PG23's connected-support prose does not imply this condition: a
connected-support law can have atoms.  It remains a visible remediation
premise until derived from a documented stronger source distribution class.
-/
def pg23SourceScoreLevelNull
    (typeLaw : Measure (PG23ApplicantType College)) : Prop :=
  ∀ c : College, ∀ x : ℝ,
    typeLaw {theta | pg23SourceScore theta c = x} = 0

/--
Raw score-level nullity transports to A-L's normalized strict-preferences
condition.  The proof does not infer nullity from connected support.
-/
theorem pg23NormalizedTypeLaw_strictPreferences_of_raw
    (typeLaw : Measure (PG23ApplicantType College))
    (hlevel : pg23SourceScoreLevelNull typeLaw) :
    al16SourceStrictPreferences (pg23NormalizedTypeLaw typeLaw) := by
  intro c y
  let s : Set (AL16SourceStudent College) :=
    {student | al16ScoreValue al16SourceScore student c = y}
  have hs : MeasurableSet s := by
    change MeasurableSet
      ((fun student : AL16SourceStudent College =>
        al16ScoreValue al16SourceScore student c) ⁻¹' ({y} : Set ℝ))
    exact MeasurableSet.preimage (MeasurableSet.singleton y)
      (al16SourceScore_measurable c)
  change Measure.map pg23NormalizedStudent typeLaw s = 0
  rw [Measure.map_apply pg23NormalizedStudent_measurable hs]
  by_cases hnonempty : ((pg23NormalizedStudent (College := College)) ⁻¹' s).Nonempty
  · rcases hnonempty with ⟨theta0, htheta0⟩
    let x := pg23SourceScore theta0 c
    have hsubset : (pg23NormalizedStudent (College := College)) ⁻¹' s ⊆
        {theta | pg23SourceScore theta c = x} := by
      intro theta htheta
      change pg23ScoreNormalize (pg23SourceScore theta c) = y at htheta
      change pg23ScoreNormalize (pg23SourceScore theta0 c) = y at htheta0
      apply pg23ScoreNormalize_strictMono.injective
      apply Subtype.ext
      simpa [x] using htheta.trans htheta0.symm
    exact measure_mono_null hsubset (hlevel c x)
  · rw [Set.not_nonempty_iff_eq_empty.mp hnonempty]
    simp

/-- Every literal PG23 ranking is injective, hence induces a strict college order. -/
theorem pg23SourceRank_injective :
    ∀ theta : PG23ApplicantType College,
      Function.Injective (pg23SourceRank theta) := by
  intro theta c d h
  apply theta.1.injective
  exact Fin.ext h

/-- Normalized raw source-score coordinates are measurable on the literal carrier. -/
theorem pg23NormalizedSourceScore_measurable (c : College) :
    Measurable (fun theta : PG23ApplicantType College =>
      al16ScoreValue al16SourceScore (pg23NormalizedStudent theta) c) := by
  change Measurable (fun theta : PG23ApplicantType College =>
    ((Real.arctan (theta.2 c) + Real.pi / 2) / Real.pi : ℝ))
  fun_prop (disch := exact Real.continuous_arctan.measurable)

/-- Raw source-score coordinates are measurable on the literal carrier. -/
theorem pg23SourceScore_measurable (c : College) :
    Measurable (fun theta : PG23ApplicantType College => pg23SourceScore theta c) := by
  unfold pg23SourceScore
  exact (measurable_pi_apply c).comp measurable_snd

/--
In the monoculture primitive law, a nonatomic value distribution makes every
raw score level null.  This is stronger than PG23's printed connected-support
premise, but it derives the regularity condition rather than exposing
score-level nullity as a theorem-facing assumption.
-/
theorem pg23MonocultureTypeLaw_scoreLevelNull_of_noAtoms_value
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    [NoAtoms valueLaw] :
    pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) := by
  letI : IsProbabilityMeasure (pg23UniformRankingLaw (College := College)) :=
    pg23UniformRankingLaw_isProbabilityMeasure
  intro c score
  have htarget :
      MeasurableSet
        {theta : PG23ApplicantType College | pg23SourceScore theta c = score} := by
    change MeasurableSet
      ((fun theta : PG23ApplicantType College => pg23SourceScore theta c) ⁻¹'
        ({score} : Set ℝ))
    exact (MeasurableSet.singleton score).preimage (pg23SourceScore_measurable c)
  have hraw_meas :
      MeasurableSet
        {sample : PG23MonocultureSample College | sample.1.1 + sample.2 = score} := by
    change MeasurableSet
      ((fun sample : PG23MonocultureSample College => sample.1.1 + sample.2) ⁻¹'
        ({score} : Set ℝ))
    exact (MeasurableSet.singleton score).preimage (by fun_prop)
  have hsection_zero : ∀ z : ℝ,
      (valueLaw.prod (pg23UniformRankingLaw (College := College)))
        {sample : ℝ × PG23Ranking College | sample.1 + z = score} = 0 := by
    intro z
    apply measure_mono_null
      (t := ({score - z} : Set ℝ) ×ˢ (Set.univ : Set (PG23Ranking College)))
    · intro sample hsample
      constructor
      · change sample.1 = score - z
        change sample.1 + z = score at hsample
        linarith [hsample]
      · trivial
    · simp
  have hraw_zero :
      ((valueLaw.prod (pg23UniformRankingLaw (College := College))).prod noiseLaw)
        {sample : PG23MonocultureSample College | sample.1.1 + sample.2 = score} = 0 := by
    rw [Measure.prod_apply_symm hraw_meas]
    exact (lintegral_eq_zero_iff
      (measurable_measure_prodMk_right hraw_meas)).mpr
      (Filter.Eventually.of_forall hsection_zero)
  unfold pg23MonocultureTypeLaw
  rw [Measure.map_apply pg23MonocultureSampleToType_measurable htarget]
  simpa [pg23MonocultureSampleToType, pg23MonocultureType, pg23SourceScore]
    using hraw_zero

/-- Raw-ranking coordinates are measurable because rankings have the discrete sigma algebra. -/
theorem pg23SourceRank_measurable (c : College) :
    Measurable (fun theta : PG23ApplicantType College => pg23SourceRank theta c) := by
  unfold pg23SourceRank
  exact (Measurable.of_discrete :
    Measurable (fun ranking : PG23Ranking College => (ranking c).val)).comp measurable_fst

/-- Active top-choice fibers are measurable when active-set membership is measurable. -/
theorem pg23ActiveSourceChoice_fiber_measurable
    (active : PG23ApplicantType College -> Finset College)
    (hactive_meas : ∀ c : College, MeasurableSet {theta | c ∈ active theta})
    (P : College -> ℝ) (c : College) :
    MeasurableSet
      {theta : PG23ApplicantType College |
        pg23ActiveSourceChoice (active theta) P theta = some c} := by
  classical
  have haffordable : ∀ d : College,
      MeasurableSet {theta : PG23ApplicantType College | pg23Affordable P theta d} := by
    intro d
    unfold pg23Affordable
    exact measurableSet_le measurable_const (pg23SourceScore_measurable d)
  have hnotPref : ∀ d : College,
      MeasurableSet
        {theta : PG23ApplicantType College |
          ¬ pg23SourcePrefers theta (some d) (some c)} := by
    intro d
    have hle :
        MeasurableSet
          {theta : PG23ApplicantType College |
            pg23SourceRank theta c ≤ pg23SourceRank theta d} :=
      measurableSet_le (pg23SourceRank_measurable c) (pg23SourceRank_measurable d)
    convert hle using 1
    ext theta
    simp [pg23SourcePrefers, al16RankPrefers, not_lt]
  have hbetter : ∀ d : College,
      MeasurableSet
        {theta : PG23ApplicantType College |
          d ∈ active theta -> pg23Affordable P theta d ->
            ¬ pg23SourcePrefers theta (some d) (some c)} := by
    intro d
    convert
      ((hactive_meas d).compl.union (haffordable d).compl).union (hnotPref d)
        using 1
    ext theta
    by_cases hd_active : d ∈ active theta
    · by_cases hd_affordable : pg23Affordable P theta d
      · simp [hd_active, hd_affordable]
      · simp [hd_active, hd_affordable]
    · simp [hd_active]
  have htarget :
      {theta : PG23ApplicantType College |
        pg23ActiveSourceChoice (active theta) P theta = some c} =
        {theta : PG23ApplicantType College | c ∈ active theta} ∩
          {theta : PG23ApplicantType College | pg23Affordable P theta c} ∩
            {theta : PG23ApplicantType College |
              ∀ d : College, d ∈ active theta -> pg23Affordable P theta d ->
                ¬ pg23SourcePrefers theta (some d) (some c)} := by
    ext theta
    simp [pg23ActiveSourceChoice_eq_some_iff, and_assoc]
  have hforall :
      MeasurableSet
        {theta : PG23ApplicantType College |
          ∀ d : College, d ∈ active theta -> pg23Affordable P theta d ->
            ¬ pg23SourcePrefers theta (some d) (some c)} := by
    convert MeasurableSet.iInter hbetter using 1
    ext theta
    simp
  rw [htarget]
  exact ((hactive_meas c).inter (haffordable c)).inter hforall

/-- Source top-k active-choice fibers are measurable. -/
theorem pg23TopKActiveSourceChoice_fiber_measurable
    (k : ℕ) (P : College -> ℝ) (c : College) :
    MeasurableSet
      {theta : PG23ApplicantType College |
        pg23ActiveSourceChoice (pg23TopKApplicationSet k theta.1) P theta = some c} := by
  classical
  refine pg23ActiveSourceChoice_fiber_measurable
    (fun theta : PG23ApplicantType College => pg23TopKApplicationSet k theta.1) ?_ P c
  intro d
  have hlt :
      MeasurableSet
        {theta : PG23ApplicantType College | pg23SourceRank theta d < k} :=
    measurableSet_lt (pg23SourceRank_measurable d) measurable_const
  convert hlt using 1
  ext theta
  simp [pg23TopKApplicationSet_mem, pg23SourceRank]

/-- The measurable event that a college is ranked first by a literal PG23 applicant. -/
def pg23TopRankSet (c : College) : Set (PG23ApplicantType College) :=
  {theta | pg23SourceRank theta c = 0}

/-- First-rank events are measurable on the source applicant carrier. -/
theorem pg23TopRankSet_measurable (c : College) :
    MeasurableSet (pg23TopRankSet (College := College) c) := by
  exact MeasurableSet.preimage (MeasurableSet.singleton 0) (pg23SourceRank_measurable c)

/-- Distinct colleges cannot both be first in the same strict ranking. -/
theorem pg23TopRankSet_pairwiseDisjoint :
    Pairwise (fun c d => Disjoint (pg23TopRankSet (College := College) c)
      (pg23TopRankSet d)) := by
  intro c d hcd
  rw [Set.disjoint_left]
  intro theta htheta_c htheta_d
  apply hcd
  apply pg23SourceRank_injective theta
  exact htheta_c.trans htheta_d.symm

/-- Every strict finite ranking has exactly one first-ranked college. -/
theorem pg23_iUnion_topRankSet [Nonempty College] :
    (⋃ c : College, pg23TopRankSet c) = Set.univ := by
  ext theta
  simp only [Set.mem_iUnion, pg23TopRankSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  let c : College := theta.1.symm ⟨0, Fintype.card_pos⟩
  refine ⟨c, ?_⟩
  change (theta.1 c).val = 0
  simp [c]

/-- Relabeling takes the first-rank event for `c` to that for `sigma c`. -/
theorem pg23TopRankSet_relabel_preimage (sigma : Equiv.Perm College) (c : College) :
    (pg23RelabelApplicant sigma) ⁻¹' pg23TopRankSet (sigma c) = pg23TopRankSet c := by
  ext theta
  simp [pg23TopRankSet]

/-- An invariant type law gives equal mass to relabeled first-rank events. -/
theorem pg23TopRankSet_measure_relabel
    (typeLaw : Measure (PG23ApplicantType College))
    (sigma : Equiv.Perm College) (c : College)
    (hlaw : Measure.map (pg23RelabelApplicant sigma) typeLaw = typeLaw) :
    typeLaw.real (pg23TopRankSet (sigma c)) = typeLaw.real (pg23TopRankSet c) := by
  have h := congrArg (fun law : Measure (PG23ApplicantType College) =>
    law.real (pg23TopRankSet (sigma c))) hlaw
  change (Measure.map (pg23RelabelApplicant sigma) typeLaw).real
      (pg23TopRankSet (sigma c)) = typeLaw.real (pg23TopRankSet (sigma c)) at h
  rw [map_measureReal_apply (pg23RelabelApplicant_measurable sigma)
    (pg23TopRankSet_measurable (sigma c))] at h
  simpa [pg23TopRankSet_relabel_preimage] using h.symm

/--
Uniformity over strict rankings follows from permutation invariance and the
finite partition into first-rank events.  This is a derived law fact, not an
extra symmetry assumption on the source model.
-/
theorem pg23TopRankSet_measure_eq_one_div_card
    (typeLaw : Measure (PG23ApplicantType College)) [Nonempty College]
    [IsProbabilityMeasure typeLaw]
    (hlaw : ∀ sigma : Equiv.Perm College,
      Measure.map (pg23RelabelApplicant sigma) typeLaw = typeLaw)
    (c : College) :
    typeLaw.real (pg23TopRankSet c) = 1 / Fintype.card College := by
  classical
  have hconst : ∀ d : College,
      typeLaw.real (pg23TopRankSet d) = typeLaw.real (pg23TopRankSet c) := by
    intro d
    have hswap := pg23TopRankSet_measure_relabel typeLaw (Equiv.swap c d) c
      (hlaw (Equiv.swap c d))
    simpa using hswap
  have hsum : (∑ d : College, typeLaw.real (pg23TopRankSet d)) = 1 := by
    rw [← measureReal_iUnion_fintype pg23TopRankSet_pairwiseDisjoint
      pg23TopRankSet_measurable]
    simp [pg23_iUnion_topRankSet]
  have hsum_const : (Fintype.card College : ℝ) *
      typeLaw.real (pg23TopRankSet c) = 1 := by
    simpa [hconst, Finset.sum_const, nsmul_eq_mul] using hsum
  apply (eq_div_iff (by exact_mod_cast Fintype.card_ne_zero)).2
  simpa [mul_comm] using hsum_const

/-- The literal monoculture source law puts mass `1 / |C|` on every first-rank event. -/
theorem pg23MonocultureTopRankSet_measure_eq_one_div_card
    (valueLaw noiseLaw : Measure ℝ) [Nonempty College]
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (c : College) :
    (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw).real
      (pg23TopRankSet c) = 1 / Fintype.card College := by
  letI : IsProbabilityMeasure
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) :=
    pg23MonocultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  exact pg23TopRankSet_measure_eq_one_div_card _
    (fun sigma => pg23MonocultureTypeLaw_relabel sigma valueLaw noiseLaw) c

/-- The literal polyculture source law puts mass `1 / |C|` on every first-rank event. -/
theorem pg23PolycultureTopRankSet_measure_eq_one_div_card
    (valueLaw noiseLaw : Measure ℝ) [Nonempty College]
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (c : College) :
    (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw).real
      (pg23TopRankSet c) = 1 / Fintype.card College := by
  letI : IsProbabilityMeasure
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw) :=
    pg23PolycultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  exact pg23TopRankSet_measure_eq_one_div_card _
    (fun sigma => pg23PolycultureTypeLaw_relabel sigma valueLaw noiseLaw) c

/-- Every normalized literal score is nonnegative because it lies in the A-L cutoff cube. -/
theorem pg23NormalizedScore_nonneg
    (theta : PG23ApplicantType College) (c : College) :
    0 ≤ al16ScoreValue al16SourceScore (pg23NormalizedStudent theta) c := by
  change 0 ≤ (pg23ScoreNormalize (pg23SourceScore theta c) : ℝ)
  exact (pg23ScoreNormalize (pg23SourceScore theta c)).property.1

/--
At a zero normalized cutoff, an applicant who ranks that college first chooses
it.  This is a pointwise selector fact over the literal raw-score carrier.
-/
theorem pg23NormalizedStudent_topRank_choice
    (Q : AL16Cutoff College) (c : College)
    (hQzero : al16CutoffValue Q c = 0)
    (theta : PG23ApplicantType College)
    (htop : theta ∈ pg23TopRankSet c) :
    al16SourceChoice Q (pg23NormalizedStudent theta) = some c := by
  change al16FavoriteAffordableChoice al16SourceScore al16SourceRank Q
    (pg23NormalizedStudent theta) = some c
  apply al16FavoriteAffordableChoice_eq_some_of_no_better
  · exact al16SourceRank_injective _
  · rw [show al16Affordable al16SourceScore Q (pg23NormalizedStudent theta) c ↔
        al16CutoffValue Q c ≤
          al16ScoreValue al16SourceScore (pg23NormalizedStudent theta) c by rfl]
    rw [hQzero]
    exact pg23NormalizedScore_nonneg theta c
  · intro d _ hbetter
    have htoprank : al16SourceRank (pg23NormalizedStudent theta) c = 0 := by
      simpa [pg23TopRankSet] using htop
    rw [htoprank] at hbetter
    exact Nat.not_lt_zero _ hbetter

/--
At a zero normalized cutoff, aggregate demand contains the full first-rank
event after transporting the literal applicant law to the A-L carrier.
-/
theorem pg23NormalizedAggregateDemand_ge_topRankMass
    (typeLaw : Measure (PG23ApplicantType College)) [IsFiniteMeasure typeLaw]
    (Q : AL16Cutoff College) (c : College)
    (hQzero : al16CutoffValue Q c = 0) :
    typeLaw.real (pg23TopRankSet c) ≤
      al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw) Q c := by
  unfold pg23NormalizedTypeLaw al16SourceAggregateDemand
  rw [map_measureReal_apply pg23NormalizedStudent_measurable]
  · refine measureReal_mono ?_ (by finiteness)
    intro theta htheta
    change al16SourceChoice Q (pg23NormalizedStudent theta) = some c
    exact pg23NormalizedStudent_topRank_choice Q c hQzero theta htheta
  · change MeasurableSet ((al16SourceChoice Q) ⁻¹' ({some c} : Set (Option College)))
    exact al16SourceChoice_fiber_measurable Q (some c)

/--
Equal capacity strictly below the first-rank mass rules out zero coordinates
of an A-L clearing cutoff for the transported literal PG23 model.
-/
theorem pg23NormalizedMarketClearing_cutoff_pos
    (typeLaw : Measure (PG23ApplicantType College)) [Nonempty College]
    [IsProbabilityMeasure typeLaw]
    (htop : ∀ c : College,
      typeLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (S : ℝ) (hSlt : S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ))
    (Q : AL16Cutoff College)
    (hQ : al16SourceMarketClearing
      (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw)) capacity Q)
    (c : College) :
    0 < al16CutoffValue Q c := by
  have hcardpos : (0 : ℝ) < Fintype.card College := by
    exact_mod_cast Fintype.card_pos
  have hmass := pg23NormalizedAggregateDemand_ge_topRankMass typeLaw Q c
  have hupper := hQ.1 c
  rw [htop c] at hmass
  rw [hcapacity c] at hupper
  by_contra hnot
  have hzero : al16CutoffValue Q c = 0 :=
    le_antisymm (le_of_not_gt hnot) (Q c).property.1
  specialize hmass hzero
  have hstrict : S / (Fintype.card College : ℝ) <
      1 / (Fintype.card College : ℝ) := by
    exact (div_lt_div_iff₀ hcardpos hcardpos).2 (by nlinarith)
  exact (not_le_of_gt hstrict) (hmass.trans hupper)

/--
Raw score-level nullity and positive capacity rule out unit coordinates of an
A-L clearing cutoff after the explicit score normalization.
-/
theorem pg23NormalizedMarketClearing_cutoff_lt_one
    (typeLaw : Measure (PG23ApplicantType College))
    (hlevel : pg23SourceScoreLevelNull typeLaw)
    (capacity : College -> ℝ)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (Q : AL16Cutoff College)
    (hQ : al16SourceMarketClearing
      (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw)) capacity Q)
    (c : College) :
    al16CutoffValue Q c < 1 := by
  rcases lt_or_eq_of_le (Q c).property.2 with hlt | hone
  · exact hlt
  · have hstrict := pg23NormalizedTypeLaw_strictPreferences_of_raw typeLaw hlevel
    have hzero := al16SourceAggregateDemand_eq_zero_of_cutoff_eq_one
      (pg23NormalizedTypeLaw typeLaw) hstrict Q c hone
    have hpos : 0 < al16CutoffValue Q c := by
      change 0 < (Q c : ℝ)
      rw [hone]
      norm_num
    have heq := hQ.2 c hpos
    rw [hzero] at heq
    linarith [hcapacity_pos c]

/--
For the literal source model with `0 < S < 1` and equal capacity, every A-L
clearing cutoff is strictly inside the normalized interval.  Both endpoint
arguments remain explicit because this is what permits a finite raw cutoff
representation later; it does not establish raw matching stability.
-/
theorem pg23NormalizedMarketClearing_cutoff_interior
    (typeLaw : Measure (PG23ApplicantType College)) [Nonempty College]
    [IsProbabilityMeasure typeLaw]
    (hlevel : pg23SourceScoreLevelNull typeLaw)
    (htop : ∀ c : College,
      typeLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (S : ℝ) (hS : 0 < S ∧ S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ))
    (Q : AL16Cutoff College)
    (hQ : al16SourceMarketClearing
      (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw)) capacity Q) :
    ∀ c : College,
      0 < al16CutoffValue Q c ∧ al16CutoffValue Q c < 1 := by
  intro c
  constructor
  · exact pg23NormalizedMarketClearing_cutoff_pos typeLaw htop S hS.2
      capacity hcapacity Q hQ c
  · apply pg23NormalizedMarketClearing_cutoff_lt_one typeLaw hlevel capacity _ Q hQ c
    intro d
    rw [hcapacity d]
    have hcardpos : (0 : ℝ) < Fintype.card College := by
      exact_mod_cast Fintype.card_pos
    exact div_pos hS.1 hcardpos

/-- The endpoint-interiority result specialized to the literal monoculture source law. -/
theorem pg23MonocultureNormalizedMarketClearing_cutoff_interior
    (valueLaw noiseLaw : Measure ℝ) [Nonempty College]
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ))
    (Q : AL16Cutoff College)
    (hQ : al16SourceMarketClearing
      (al16SourceAggregateDemand
        (pg23NormalizedTypeLaw
          (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))) capacity Q) :
    ∀ c : College,
      0 < al16CutoffValue Q c ∧ al16CutoffValue Q c < 1 := by
  letI : IsProbabilityMeasure
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) :=
    pg23MonocultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  exact pg23NormalizedMarketClearing_cutoff_interior _ hlevel
    (pg23MonocultureTopRankSet_measure_eq_one_div_card valueLaw noiseLaw)
    S hS capacity hcapacity Q hQ

/-- The endpoint-interiority result specialized to the literal polyculture source law. -/
theorem pg23PolycultureNormalizedMarketClearing_cutoff_interior
    (valueLaw noiseLaw : Measure ℝ) [Nonempty College]
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hlevel : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ))
    (Q : AL16Cutoff College)
    (hQ : al16SourceMarketClearing
      (al16SourceAggregateDemand
        (pg23NormalizedTypeLaw
          (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))) capacity Q) :
    ∀ c : College,
      0 < al16CutoffValue Q c ∧ al16CutoffValue Q c < 1 := by
  letI : IsProbabilityMeasure
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw) :=
    pg23PolycultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  exact pg23NormalizedMarketClearing_cutoff_interior _ hlevel
    (pg23PolycultureTopRankSet_measure_eq_one_div_card valueLaw noiseLaw)
    S hS capacity hcapacity Q hQ

/-- The inverse real coordinate of `pg23ScoreNormalize` on the open unit interval. -/
noncomputable def pg23ScoreDenormalize (y : ℝ) : ℝ :=
  Real.tan (Real.pi * y - Real.pi / 2)

/-- The score normalization is inverted exactly at every interior unit-interval value. -/
theorem pg23ScoreNormalize_denormalize
    (y : Set.Icc (0 : ℝ) 1) (hy0 : 0 < (y : ℝ)) (hy1 : (y : ℝ) < 1) :
    pg23ScoreNormalize (pg23ScoreDenormalize y) = y := by
  apply Subtype.ext
  change (Real.arctan (Real.tan (Real.pi * (y : ℝ) - Real.pi / 2)) +
    Real.pi / 2) / Real.pi = (y : ℝ)
  have hleft : -(Real.pi / 2) < Real.pi * (y : ℝ) - Real.pi / 2 := by
    nlinarith [mul_pos Real.pi_pos hy0]
  have hright : Real.pi * (y : ℝ) - Real.pi / 2 < Real.pi / 2 := by
    nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hy1)]
  rw [Real.arctan_tan hleft hright]
  field_simp
  ring

/-- Denormalizing a normalized raw score returns the original raw score. -/
theorem pg23ScoreDenormalize_normalize (x : ℝ) :
    pg23ScoreDenormalize (pg23ScoreNormalize x) = x := by
  unfold pg23ScoreDenormalize pg23ScoreNormalize
  change Real.tan (Real.pi * ((Real.arctan x + Real.pi / 2) / Real.pi) -
      Real.pi / 2) = x
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]
  have hangle : (Real.arctan x * 2 + Real.pi - Real.pi) / 2 = Real.arctan x := by
    ring
  rw [hangle]
  rw [Real.tan_arctan]

/-- Coordinatewise raw cutoff obtained by inverting an interior normalized cutoff. -/
noncomputable def pg23DenormalizedCutoff (Q : AL16Cutoff College) : College -> ℝ :=
  fun c => pg23ScoreDenormalize (al16CutoffValue Q c)

/-- An interior normalized cutoff is exactly the normalization of its raw inverse. -/
theorem pg23NormalizedCutoff_denormalized_eq
    (Q : AL16Cutoff College)
    (hinterior : ∀ c : College,
      0 < al16CutoffValue Q c ∧ al16CutoffValue Q c < 1) :
    pg23NormalizedCutoff (pg23DenormalizedCutoff Q) = Q := by
  funext c
  apply pg23ScoreNormalize_denormalize (Q c)
  · simpa [al16CutoffValue] using (hinterior c).1
  · simpa [al16CutoffValue] using (hinterior c).2

/-- Every literal favorite-affordable college-choice fiber is measurable. -/
theorem pg23SourceChoice_fiber_measurable
    (P : College -> ℝ) (o : Option College) :
    MeasurableSet ((pg23SourceChoice P) ⁻¹' ({o} : Set (Option College))) := by
  unfold pg23SourceChoice
  apply al16FavoriteAffordableChoice_fiber_measurable
  · exact pg23NormalizedSourceScore_measurable
  · exact pg23SourceRank_measurable
  · exact pg23SourceRank_injective

/-- The source's literal favorite-affordable choice specification over raw scores. -/
def pg23DemandChoiceSemantics
    (choice : (College -> ℝ) -> PG23ApplicantType College -> Option College) : Prop :=
  ∀ P theta,
    match choice P theta with
    | none =>
        ∀ c : College, pg23SourceScore theta c < P c
    | some c =>
        pg23Affordable P theta c ∧
          ∀ d : College, pg23Affordable P theta d ->
            ¬ pg23SourcePrefers theta (some d) (some c)

/--
The normalized implementation satisfies the raw PG23 favorite-affordable rule
exactly.  In particular, `none` means no score reaches its raw cutoff.
-/
theorem pg23SourceChoice_semantics :
    pg23DemandChoiceSemantics (College := College) pg23SourceChoice := by
  intro P theta
  have h := al16SourceChoice_semantics (College := College)
  unfold al16DemandChoiceSemantics at h
  change
    match al16SourceChoice (pg23NormalizedCutoff P) (pg23NormalizedStudent theta) with
    | none => ∀ c : College, pg23SourceScore theta c < P c
    | some c =>
        pg23Affordable P theta c ∧
          ∀ d : College, pg23Affordable P theta d ->
            ¬ pg23SourcePrefers theta (some d) (some c)
  cases hchoice : al16SourceChoice (pg23NormalizedCutoff P)
      (pg23NormalizedStudent theta) with
  | none =>
      have hnone := h (pg23NormalizedCutoff P) (pg23NormalizedStudent theta)
      rw [hchoice] at hnone
      intro c
      have hnorm :
          pg23ScoreNormalize (pg23SourceScore theta c) < pg23ScoreNormalize (P c) := by
        simpa [pg23NormalizedScore, pg23NormalizedCutoff, pg23SourceScore,
          al16SourceScore, al16CutoffValue] using hnone c
      exact (pg23ScoreNormalize_lt_iff _ _).mp hnorm
  | some c =>
      have hsome := h (pg23NormalizedCutoff P) (pg23NormalizedStudent theta)
      rw [hchoice] at hsome
      rcases hsome with ⟨haffordable, hno_better⟩
      constructor
      · have hnorm :
            pg23ScoreNormalize (P c) ≤ pg23ScoreNormalize (pg23SourceScore theta c) := by
          simpa [pg23NormalizedScore, pg23NormalizedCutoff, pg23SourceScore,
            al16SourceScore, al16CutoffValue] using haffordable
        exact (pg23ScoreNormalize_le_iff _ _).mp hnorm
      · intro d hd
        apply hno_better d
        have hnorm :
            pg23ScoreNormalize (P d) ≤ pg23ScoreNormalize (pg23SourceScore theta d) :=
          (pg23ScoreNormalize_le_iff _ _).mpr hd
        simpa [pg23NormalizedScore, pg23NormalizedCutoff, pg23SourceScore,
          al16SourceScore, al16CutoffValue] using hnorm

/-- An applicant is matched exactly when at least one raw score reaches its cutoff. -/
theorem pg23SourceChoice_some_iff
    (P : College -> ℝ) (theta : PG23ApplicantType College) :
    (∃ c : College, pg23SourceChoice P theta = some c) ↔
      ∃ c : College, pg23Affordable P theta c := by
  constructor
  · rintro ⟨c, hchoice⟩
    have hsem := pg23SourceChoice_semantics (College := College) P theta
    rw [hchoice] at hsem
    exact ⟨c, hsem.1⟩
  · rintro ⟨c, haffordable⟩
    cases hchoice : pg23SourceChoice P theta with
    | none =>
        have hsem := pg23SourceChoice_semantics (College := College) P theta
        rw [hchoice] at hsem
        exact False.elim ((not_lt_of_ge haffordable) (hsem c))
    | some d => exact ⟨d, rfl⟩

/--
Favorite-affordable choice is equivariant under a permutation of college
labels.  This is a pointwise raw-score statement; no distributional symmetry
or market-clearing conclusion is used.
-/
theorem pg23SourceChoice_relabel (sigma : Equiv.Perm College)
    (P : College -> ℝ) (theta : PG23ApplicantType College) :
    pg23SourceChoice (pg23RelabelCutoff sigma P) (pg23RelabelApplicant sigma theta) =
      Option.map sigma (pg23SourceChoice P theta) := by
  classical
  cases hchoice : pg23SourceChoice P theta with
  | none =>
      simp only [Option.map_none]
      cases hrel : pg23SourceChoice (pg23RelabelCutoff sigma P)
          (pg23RelabelApplicant sigma theta) with
      | none => rfl
      | some d =>
          exfalso
          rcases (pg23SourceChoice_some_iff (College := College)
            (pg23RelabelCutoff sigma P) (pg23RelabelApplicant sigma theta)).mp
              ⟨d, hrel⟩ with ⟨e, he⟩
          have he_original : pg23Affordable P theta (sigma.symm e) := by
            simpa [pg23Affordable] using he
          have hnone := pg23SourceChoice_semantics (College := College) P theta
          rw [hchoice] at hnone
          exact (not_lt_of_ge he_original) (hnone (sigma.symm e))
  | some c =>
      simp only [Option.map_some]
      cases hrel : pg23SourceChoice (pg23RelabelCutoff sigma P)
          (pg23RelabelApplicant sigma theta) with
      | none =>
          exfalso
          have horiginal := pg23SourceChoice_semantics (College := College) P theta
          rw [hchoice] at horiginal
          have hc_relabel :
              pg23Affordable (pg23RelabelCutoff sigma P)
                (pg23RelabelApplicant sigma theta) (sigma c) :=
            (pg23Affordable_relabel_iff sigma P theta c).mpr horiginal.1
          have hnone := pg23SourceChoice_semantics (College := College)
            (pg23RelabelCutoff sigma P) (pg23RelabelApplicant sigma theta)
          rw [hrel] at hnone
          exact (not_lt_of_ge hc_relabel) (hnone (sigma c))
      | some d =>
          have horiginal := pg23SourceChoice_semantics (College := College) P theta
          rw [hchoice] at horiginal
          have hrelabeled := pg23SourceChoice_semantics (College := College)
            (pg23RelabelCutoff sigma P) (pg23RelabelApplicant sigma theta)
          rw [hrel] at hrelabeled
          have hd_original : pg23Affordable P theta (sigma.symm d) := by
            simpa [pg23Affordable] using hrelabeled.1
          have hc_relabel :
              pg23Affordable (pg23RelabelCutoff sigma P)
                (pg23RelabelApplicant sigma theta) (sigma c) :=
            (pg23Affordable_relabel_iff sigma P theta c).mpr horiginal.1
          have hle_left :
              pg23SourceRank theta c ≤ pg23SourceRank theta (sigma.symm d) := by
            apply Nat.le_of_not_gt
            simpa [pg23SourcePrefers, al16RankPrefers] using
              (horiginal.2 (sigma.symm d) hd_original)
          have hle_right_relabel :
              pg23SourceRank (pg23RelabelApplicant sigma theta) d ≤
                pg23SourceRank (pg23RelabelApplicant sigma theta) (sigma c) := by
            apply Nat.le_of_not_gt
            simpa [pg23SourcePrefers, al16RankPrefers] using
              (hrelabeled.2 (sigma c) hc_relabel)
          have hle_right :
              pg23SourceRank theta (sigma.symm d) ≤ pg23SourceRank theta c := by
            simpa using hle_right_relabel
          have hrank :
              pg23SourceRank theta c = pg23SourceRank theta (sigma.symm d) :=
            Nat.le_antisymm hle_left hle_right
          have hcsymmd : c = sigma.symm d :=
            pg23SourceRank_injective (College := College) theta hrank
          have hdc : d = sigma c :=
            (sigma.apply_symm_apply d).symm.trans (congrArg sigma hcsymmd.symm)
          simpa [hdc]

/--
At a shared raw cutoff, monoculture matching is the weak event `P ≤ v + X`.
The source's strict probability formula requires its separately visible
zero-boundary-mass bridge.
-/
theorem pg23Monoculture_sharedCutoff_matched_iff
    [Nonempty College] (value noise P : ℝ) (ranking : PG23Ranking College) :
    (∃ c : College,
      pg23SourceChoice (fun _ : College => P)
        (pg23MonocultureType value noise ranking) = some c) ↔
      P ≤ value + noise := by
  constructor
  · intro hmatched
    rcases (pg23SourceChoice_some_iff (College := College)
      (fun _ : College => P) (pg23MonocultureType value noise ranking)).1 hmatched with
      ⟨c, hc⟩
    simpa [pg23Affordable] using hc
  · intro hscore
    apply (pg23SourceChoice_some_iff (College := College)
      (fun _ : College => P) (pg23MonocultureType value noise ranking)).2
    refine ⟨Classical.choice inferInstance, ?_⟩
    simpa [pg23Affordable] using hscore

/--
At a shared raw cutoff, polyculture matching is the weak event that some
coordinate score reaches the cutoff.  This is the semantic precursor to the
paper's maximum-order-statistic formula.
-/
theorem pg23Polyculture_sharedCutoff_matched_iff
    (value P : ℝ) (ranking : PG23Ranking College) (noise : College -> ℝ) :
    (∃ c : College,
      pg23SourceChoice (fun _ : College => P)
        (pg23PolycultureType value ranking noise) = some c) ↔
      ∃ c : College, P ≤ value + noise c := by
  simpa only [pg23PolycultureType_score] using
    (pg23SourceChoice_some_iff (College := College)
      (fun _ : College => P) (pg23PolycultureType value ranking noise))

/-- Relabeling preserves the monoculture score realization exactly. -/
theorem pg23RelabelApplicant_monocultureType (sigma : Equiv.Perm College)
    (value noise : ℝ) (ranking : PG23Ranking College) :
    pg23RelabelApplicant sigma (pg23MonocultureType value noise ranking) =
      pg23MonocultureType value noise (pg23RelabelRanking sigma ranking) :=
  rfl

/-- Relabeling preserves the polyculture score realization by reindexing iid noise. -/
theorem pg23RelabelApplicant_polycultureType (sigma : Equiv.Perm College)
    (value : ℝ) (ranking : PG23Ranking College) (noise : College -> ℝ) :
    pg23RelabelApplicant sigma (pg23PolycultureType value ranking noise) =
      pg23PolycultureType value (pg23RelabelRanking sigma ranking)
        (pg23RelabelNoise sigma noise) :=
  rfl

/-- A source matching maps each literal applicant type to a college or the outside option. -/
abbrev PG23Matching (College : Type v) [Fintype College] :=
  PG23ApplicantType College -> Option College

/-- The literal source fiber of applicants matched to one college. -/
def pg23MatchingCollegeSet (matching : PG23Matching College) (c : College) :
    Set (PG23ApplicantType College) :=
  {theta | matching theta = some c}

/--
PG23's matching regularity conditions: exact capacity fill, measurable college
fibers, and openness of every set of types that prefers a college to its
assigned outcome (`model.tex:12-16`).
-/
def pg23SourceMatchingFeasible
    (typeLaw : Measure (PG23ApplicantType College)) (capacity : College -> ℝ)
    (matching : PG23Matching College) : Prop := by
  letI : TopologicalSpace (PG23Ranking College) := ⊥
  exact
    (∀ c : College,
      typeLaw.real (pg23MatchingCollegeSet matching c) = capacity c) ∧
    (∀ c : College, MeasurableSet (pg23MatchingCollegeSet matching c)) ∧
    ∀ c : College,
      IsOpen {theta : PG23ApplicantType College |
        pg23SourcePrefers theta (some c) (matching theta)}

/-- A literal source blocking pair, using the paper's strict score comparison. -/
def pg23SourceMatchingBlocks
    (matching : PG23Matching College)
    (theta : PG23ApplicantType College) (c : College) : Prop :=
  pg23SourcePrefers theta (some c) (matching theta) ∧
    ∃ theta' : PG23ApplicantType College,
      matching theta' = some c ∧
        pg23SourceScore theta' c < pg23SourceScore theta c

/-- A stable PG23 matching is feasible and has no literal source blocking pair. -/
def pg23SourceStableMatching
    (typeLaw : Measure (PG23ApplicantType College)) (capacity : College -> ℝ)
    (matching : PG23Matching College) : Prop :=
  pg23SourceMatchingFeasible typeLaw capacity matching ∧
    ∀ theta : PG23ApplicantType College, ∀ c : College,
      ¬ pg23SourceMatchingBlocks matching theta c

/-- Aggregate demand is the type-law mass of applicants demanding a college. -/
def pg23SourceAggregateDemand
    (typeLaw : Measure (PG23ApplicantType College)) (P : College -> ℝ)
    (c : College) : ℝ :=
  typeLaw.real (pg23MatchingCollegeSet (pg23SourceChoice P) c)

/-- Active-source matching induced by a type-dependent active application set. -/
noncomputable def pg23ActiveSourceMatching
    (active : PG23ApplicantType College -> Finset College) (P : College -> ℝ) :
    PG23Matching College :=
  fun theta => pg23ActiveSourceChoice (active theta) P theta

/-- Aggregate demand induced by active-source choice. -/
noncomputable def pg23ActiveSourceAggregateDemand
    (typeLaw : Measure (PG23ApplicantType College))
    (active : PG23ApplicantType College -> Finset College)
    (P : College -> ℝ) (c : College) : ℝ :=
  typeLaw.real (pg23MatchingCollegeSet (pg23ActiveSourceMatching active P) c)

/--
Relabeling an invariant literal type law transports active-source aggregate
demand, provided the active-set rule is equivariant and the relabeled fiber is
measurable.
-/
theorem pg23ActiveSourceAggregateDemand_relabel_of_typeLaw_relabel
    (typeLaw : Measure (PG23ApplicantType College))
    (active : PG23ApplicantType College -> Finset College)
    (sigma : Equiv.Perm College) (P : College -> ℝ) (c : College)
    (hactive :
      ∀ theta : PG23ApplicantType College,
        active (pg23RelabelApplicant sigma theta) =
          pg23RelabelActiveSet sigma (active theta))
    (hlaw : Measure.map (pg23RelabelApplicant sigma) typeLaw = typeLaw)
    (hmeas :
      MeasurableSet
        (pg23MatchingCollegeSet
          (pg23ActiveSourceMatching active (pg23RelabelCutoff sigma P))
          (sigma c))) :
    pg23ActiveSourceAggregateDemand typeLaw active
        (pg23RelabelCutoff sigma P) (sigma c) =
      pg23ActiveSourceAggregateDemand typeLaw active P c := by
  unfold pg23ActiveSourceAggregateDemand pg23ActiveSourceMatching
  calc
    typeLaw.real
        (pg23MatchingCollegeSet
          (fun theta : PG23ApplicantType College =>
            pg23ActiveSourceChoice (active theta) (pg23RelabelCutoff sigma P) theta)
          (sigma c)) =
        (Measure.map (pg23RelabelApplicant sigma) typeLaw).real
          (pg23MatchingCollegeSet
            (fun theta : PG23ApplicantType College =>
              pg23ActiveSourceChoice (active theta) (pg23RelabelCutoff sigma P) theta)
            (sigma c)) := by
      rw [hlaw]
    _ = typeLaw.real
          ((pg23RelabelApplicant sigma) ⁻¹'
            pg23MatchingCollegeSet
              (fun theta : PG23ApplicantType College =>
                pg23ActiveSourceChoice (active theta) (pg23RelabelCutoff sigma P) theta)
              (sigma c)) :=
      map_measureReal_apply (pg23RelabelApplicant_measurable sigma) hmeas
    _ = typeLaw.real
          (pg23MatchingCollegeSet
            (fun theta : PG23ApplicantType College =>
              pg23ActiveSourceChoice (active theta) P theta) c) := by
      congr 1
      exact pg23ActiveSourceChoice_relabel_preimage sigma active P c hactive

/--
Differential-access applicant type: the first coordinate is the realized
positive application count `k.val + 1`, and the second coordinate is the
underlying PG23 value/ranking/score type.
-/
abbrev PG23DifferentialApplicantType
    (College : Type v) [Fintype College] (n : ℕ) :=
  Fin n × PG23ApplicantType College

/-- Relabel a differential-access applicant without changing application access. -/
def pg23DifferentialRelabelApplicant {n : ℕ} (sigma : Equiv.Perm College) :
    PG23DifferentialApplicantType College n ->
      PG23DifferentialApplicantType College n :=
  fun theta => (theta.1, pg23RelabelApplicant sigma theta.2)

/-- Differential-applicant relabeling is measurable. -/
theorem pg23DifferentialRelabelApplicant_measurable {n : ℕ}
    (sigma : Equiv.Perm College) :
    Measurable (pg23DifferentialRelabelApplicant (College := College) (n := n) sigma) := by
  unfold pg23DifferentialRelabelApplicant
  exact measurable_fst.prodMk ((pg23RelabelApplicant_measurable sigma).comp measurable_snd)

/--
The differential-access type law is an independent product of application
access and an underlying PG23 applicant type law.
-/
noncomputable def pg23DifferentialTypeLaw {n : ℕ}
    (accessLaw : Measure (Fin n))
    (baseLaw : Measure (PG23ApplicantType College)) :
    Measure (PG23DifferentialApplicantType College n) :=
  accessLaw.prod baseLaw

/-- Producting with an access-count law preserves total probability. -/
theorem pg23DifferentialTypeLaw_isProbabilityMeasure {n : ℕ}
    (accessLaw : Measure (Fin n))
    (baseLaw : Measure (PG23ApplicantType College))
    [IsProbabilityMeasure accessLaw] [IsProbabilityMeasure baseLaw] :
    IsProbabilityMeasure
      (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw) := by
  unfold pg23DifferentialTypeLaw
  infer_instance

/-- Relabel invariance lifts from the underlying PG23 type law to differential access. -/
theorem pg23DifferentialTypeLaw_relabel {n : ℕ}
    (accessLaw : Measure (Fin n))
    (baseLaw : Measure (PG23ApplicantType College))
    [IsProbabilityMeasure accessLaw] [IsProbabilityMeasure baseLaw]
    (sigma : Equiv.Perm College)
    (hbase :
      Measure.map (pg23RelabelApplicant sigma) baseLaw = baseLaw) :
    Measure.map (pg23DifferentialRelabelApplicant (College := College) (n := n) sigma)
        (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw) =
      pg23DifferentialTypeLaw (College := College) accessLaw baseLaw := by
  let hbase_mp : MeasurePreserving (pg23RelabelApplicant sigma) baseLaw baseLaw :=
    ⟨pg23RelabelApplicant_measurable sigma, hbase⟩
  have hprod :
      MeasurePreserving
        (Prod.map id (pg23RelabelApplicant sigma))
        (accessLaw.prod baseLaw) (accessLaw.prod baseLaw) :=
    (MeasurePreserving.id accessLaw).prod hbase_mp
  simpa [pg23DifferentialTypeLaw, pg23DifferentialRelabelApplicant] using hprod.map_eq

/-- Monoculture differential-access type law. -/
noncomputable def pg23MonocultureDifferentialTypeLaw {n : ℕ}
    (accessLaw : Measure (Fin n)) (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw] :
    Measure (PG23DifferentialApplicantType College n) :=
  pg23DifferentialTypeLaw (College := College) accessLaw
    (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw)

/-- Polyculture differential-access type law. -/
noncomputable def pg23PolycultureDifferentialTypeLaw {n : ℕ}
    (accessLaw : Measure (Fin n)) (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw] :
    Measure (PG23DifferentialApplicantType College n) :=
  pg23DifferentialTypeLaw (College := College) accessLaw
    (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw)

/-- Monoculture differential-access source law is relabel-invariant. -/
theorem pg23MonocultureDifferentialTypeLaw_relabel {n : ℕ}
    (accessLaw : Measure (Fin n)) (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure accessLaw]
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (sigma : Equiv.Perm College) :
    Measure.map (pg23DifferentialRelabelApplicant (College := College) (n := n) sigma)
        (pg23MonocultureDifferentialTypeLaw
          (College := College) accessLaw valueLaw noiseLaw) =
      pg23MonocultureDifferentialTypeLaw
        (College := College) accessLaw valueLaw noiseLaw := by
  letI : IsProbabilityMeasure
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) :=
    pg23MonocultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  unfold pg23MonocultureDifferentialTypeLaw
  exact pg23DifferentialTypeLaw_relabel accessLaw
    (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) sigma
    (pg23MonocultureTypeLaw_relabel sigma valueLaw noiseLaw)

/-- Polyculture differential-access source law is relabel-invariant. -/
theorem pg23PolycultureDifferentialTypeLaw_relabel {n : ℕ}
    (accessLaw : Measure (Fin n)) (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure accessLaw]
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (sigma : Equiv.Perm College) :
    Measure.map (pg23DifferentialRelabelApplicant (College := College) (n := n) sigma)
        (pg23PolycultureDifferentialTypeLaw
          (College := College) accessLaw valueLaw noiseLaw) =
      pg23PolycultureDifferentialTypeLaw
        (College := College) accessLaw valueLaw noiseLaw := by
  letI : IsProbabilityMeasure
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw) :=
    pg23PolycultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  unfold pg23PolycultureDifferentialTypeLaw
  exact pg23DifferentialTypeLaw_relabel accessLaw
    (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw) sigma
    (pg23PolycultureTypeLaw_relabel sigma valueLaw noiseLaw)

/-- The source top-k active set for a differential-access applicant. -/
noncomputable def pg23DifferentialActiveSet {n : ℕ}
    (theta : PG23DifferentialApplicantType College n) : Finset College :=
  pg23TopKApplicationSet (theta.1.val + 1) theta.2.1

/-- Differential active sets relabel with college names. -/
theorem pg23DifferentialActiveSet_relabel {n : ℕ}
    (sigma : Equiv.Perm College)
    (theta : PG23DifferentialApplicantType College n) :
    pg23DifferentialActiveSet
        (pg23DifferentialRelabelApplicant (College := College) sigma theta) =
      pg23RelabelActiveSet sigma (pg23DifferentialActiveSet theta) := by
  unfold pg23DifferentialActiveSet pg23DifferentialRelabelApplicant
  exact pg23TopKApplicationSet_relabel sigma theta.2.1 (theta.1.val + 1)

/-- Differential-access favorite-affordable choice at a raw cutoff. -/
noncomputable def pg23DifferentialSourceChoice {n : ℕ} (P : College -> ℝ) :
    PG23DifferentialApplicantType College n -> Option College :=
  fun theta => pg23ActiveSourceChoice (pg23DifferentialActiveSet theta) P theta.2

/-- Differential applicant ranking, ignoring the access-count coordinate. -/
def pg23DifferentialSourceRank {n : ℕ}
    (theta : PG23DifferentialApplicantType College n) (c : College) : Nat :=
  pg23SourceRank theta.2 c

/--
Bounded normalized score for differential access. Active colleges keep their
normalized raw score; inactive colleges receive the sentinel score `0`.
-/
noncomputable def pg23DifferentialNormalizedScore {n : ℕ}
    (theta : PG23DifferentialApplicantType College n) (c : College) :
    Set.Icc (0 : ℝ) 1 := by
  classical
  exact if c ∈ pg23DifferentialActiveSet theta then pg23NormalizedScore theta.2 c
    else ⟨0, by norm_num, by norm_num⟩

/-- Differential normalized scores are strictly below the unit cutoff `1`. -/
theorem pg23DifferentialNormalizedScore_lt_one {n : ℕ}
    (theta : PG23DifferentialApplicantType College n) (c : College) :
    al16ScoreValue
      (pg23DifferentialNormalizedScore (College := College)) theta c < 1 := by
  classical
  by_cases hc : c ∈ pg23DifferentialActiveSet theta
  · simpa [pg23DifferentialNormalizedScore, hc, al16ScoreValue,
      pg23NormalizedScore] using
      pg23ScoreNormalize_lt_one (pg23SourceScore theta.2 c)
  · simp [pg23DifferentialNormalizedScore, hc, al16ScoreValue]

/-- Favorite-affordable choice for the bounded differential-access score. -/
noncomputable def pg23DifferentialNormalizedSourceChoice {n : ℕ}
    (Q : AL16Cutoff College) :
    PG23DifferentialApplicantType College n -> Option College :=
  al16FavoriteAffordableChoice
    (pg23DifferentialNormalizedScore (College := College))
    pg23DifferentialSourceRank Q

/-- Differential-access aggregate demand. -/
noncomputable def pg23DifferentialSourceAggregateDemand {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    (P : College -> ℝ) (c : College) : ℝ :=
  typeLaw.real {theta : PG23DifferentialApplicantType College n |
    pg23DifferentialSourceChoice P theta = some c}

/-- Differential-access exact market-clearing condition. -/
def pg23DifferentialSourceMarketClearing
    (demand : (College -> ℝ) -> College -> ℝ) (capacity : College -> ℝ)
    (P : College -> ℝ) : Prop :=
  ∀ c : College, demand P c = capacity c

/-- Aggregate demand for the bounded normalized differential-access score. -/
noncomputable def pg23DifferentialNormalizedSourceAggregateDemand {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    (Q : AL16Cutoff College) (c : College) : ℝ :=
  typeLaw.real
    (al16DemandChoiceSet
      (pg23DifferentialNormalizedSourceChoice (College := College)) Q c)

/-- If a college's bounded cutoff is `1`, no differential applicant can demand it. -/
theorem pg23DifferentialNormalizedSourceAggregateDemand_eq_zero_of_cutoff_eq_one {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    (Q : AL16Cutoff College) (c : College)
    (hQ : al16CutoffValue Q c = 1) :
    pg23DifferentialNormalizedSourceAggregateDemand typeLaw Q c = 0 := by
  have hsubset :
      al16DemandChoiceSet
          (pg23DifferentialNormalizedSourceChoice (College := College)) Q c ⊆
        (∅ : Set (PG23DifferentialApplicantType College n)) := by
    intro theta htheta
    change pg23DifferentialNormalizedSourceChoice
      (College := College) Q theta = some c at htheta
    have hsemantics := al16FavoriteAffordableChoice_semantics
      (pg23DifferentialNormalizedScore (College := College))
      pg23DifferentialSourceRank Q theta
    have hchosen :
        al16FavoriteAffordableChoice
            (pg23DifferentialNormalizedScore (College := College))
            pg23DifferentialSourceRank Q theta = some c := by
      simpa [pg23DifferentialNormalizedSourceChoice] using htheta
    rw [hchosen] at hsemantics
    have hle : (1 : ℝ) ≤
        al16ScoreValue
          (pg23DifferentialNormalizedScore (College := College)) theta c := by
      simpa [hQ] using hsemantics.1
    exact False.elim
      ((not_le_of_gt (pg23DifferentialNormalizedScore_lt_one theta c)) hle)
  have hzero :
      typeLaw
          (al16DemandChoiceSet
            (pg23DifferentialNormalizedSourceChoice (College := College)) Q c) = 0 :=
    measure_mono_null hsubset measure_empty
  rw [pg23DifferentialNormalizedSourceAggregateDemand, measureReal_def, hzero]
  rfl

/-- Outside-option mass for the bounded normalized differential-access score. -/
noncomputable def pg23DifferentialNormalizedOutsideDemand {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    (Q : AL16Cutoff College) : ℝ :=
  typeLaw.real
    (al16OutsideChoiceSet
      (pg23DifferentialNormalizedSourceChoice (College := College)) Q)

/-- Differential rankings are injective because the underlying PG23 ranking is. -/
theorem pg23DifferentialSourceRank_injective {n : ℕ} :
    ∀ theta : PG23DifferentialApplicantType College n,
      Function.Injective (pg23DifferentialSourceRank theta) := by
  intro theta
  exact pg23SourceRank_injective theta.2

/-- Raising only other colleges' bounded differential cutoffs weakly raises own demand. -/
theorem pg23DifferentialNormalizedAggregateDemand_le_of_le_same_coordinate {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    {P Q : AL16Cutoff College} {c : College}
    (hPQ : P ≤ Q)
    (hcoordinate : al16CutoffValue P c = al16CutoffValue Q c) :
    pg23DifferentialNormalizedSourceAggregateDemand typeLaw P c ≤
      pg23DifferentialNormalizedSourceAggregateDemand typeLaw Q c := by
  have htotal :
      ∀ theta : PG23DifferentialApplicantType College n, ∀ a b : College,
        a = b ∨
          al16RankPrefers pg23DifferentialSourceRank theta (some a) (some b) ∨
          al16RankPrefers pg23DifferentialSourceRank theta (some b) (some a) :=
    al16RankPrefers_total pg23DifferentialSourceRank
      pg23DifferentialSourceRank_injective
  have hcomp := al16AggregateDemand_le_sup_of_choice_semantics
    (demand := pg23DifferentialNormalizedSourceAggregateDemand typeLaw)
    (mass := typeLaw.real)
    (score := pg23DifferentialNormalizedScore (College := College))
    (prefers := al16RankPrefers pg23DifferentialSourceRank)
    (choice := pg23DifferentialNormalizedSourceChoice (College := College))
    (fun {A B} hAB => al16MeasureMass_mono typeLaw hAB)
    (fun _ _ => rfl)
    (al16FavoriteAffordableChoice_semantics
      (pg23DifferentialNormalizedScore (College := College))
      pg23DifferentialSourceRank)
    htotal
    (P := Q) (Q := P) (c := c) hcoordinate.ge
  have hsup : Q ⊔ P = Q := sup_eq_left.mpr hPQ
  simpa only [hsup] using hcomp

/-- Differential ranking coordinates are measurable. -/
theorem pg23DifferentialSourceRank_measurable {n : ℕ} (c : College) :
    Measurable
      (fun theta : PG23DifferentialApplicantType College n =>
        pg23DifferentialSourceRank theta c) := by
  unfold pg23DifferentialSourceRank
  exact (pg23SourceRank_measurable c).comp measurable_snd

/-- Membership in a differential top-k active set is measurable. -/
theorem pg23DifferentialActiveSet_mem_measurable {n : ℕ} (c : College) :
    MeasurableSet
      {theta : PG23DifferentialApplicantType College n |
        c ∈ pg23DifferentialActiveSet theta} := by
  have hleft :
      Measurable
        (fun theta : PG23DifferentialApplicantType College n =>
          pg23SourceRank theta.2 c) :=
    (pg23SourceRank_measurable c).comp measurable_snd
  have hright :
      Measurable
        (fun theta : PG23DifferentialApplicantType College n =>
          theta.1.val + 1) :=
    (Measurable.of_discrete :
      Measurable (fun k : Fin n => k.val + 1)).comp measurable_fst
  have hlt :
      MeasurableSet
        {theta : PG23DifferentialApplicantType College n |
          pg23SourceRank theta.2 c < theta.1.val + 1} :=
    measurableSet_lt hleft hright
  convert hlt using 1
  ext theta
  simp [pg23DifferentialActiveSet, pg23TopKApplicationSet_mem, pg23SourceRank]

/-- Differential normalized active-score coordinates are measurable. -/
theorem pg23DifferentialNormalizedScore_measurable {n : ℕ} (c : College) :
    Measurable
      (fun theta : PG23DifferentialApplicantType College n =>
        al16ScoreValue
          (pg23DifferentialNormalizedScore (College := College)) theta c) := by
  classical
  unfold al16ScoreValue pg23DifferentialNormalizedScore
  dsimp
  have hscore :
      Measurable
        (fun theta : PG23DifferentialApplicantType College n =>
          (pg23NormalizedScore theta.2 c : ℝ)) := by
    change Measurable
      (fun theta : PG23DifferentialApplicantType College n =>
        al16ScoreValue al16SourceScore (pg23NormalizedStudent theta.2) c)
    exact (pg23NormalizedSourceScore_measurable c).comp measurable_snd
  have hite :
      Measurable
        (fun theta : PG23DifferentialApplicantType College n =>
          if c ∈ pg23DifferentialActiveSet theta then
            (pg23NormalizedScore theta.2 c : ℝ) else 0) :=
    Measurable.ite (pg23DifferentialActiveSet_mem_measurable c)
      hscore measurable_const
  convert hite using 1
  funext theta
  by_cases hc : c ∈ pg23DifferentialActiveSet theta <;> simp [hc]

/--
Positive score-level nullity for the bounded differential score.  The level
`0` is intentionally excluded because inactive applications are encoded by the
sentinel score `0`.
-/
def pg23DifferentialPositiveNormalizedScoreLevelNull {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n)) : Prop :=
  ∀ c : College, ∀ x : ℝ, 0 < x ->
    typeLaw {theta : PG23DifferentialApplicantType College n |
      al16ScoreValue
        (pg23DifferentialNormalizedScore (College := College)) theta c = x} = 0

/--
Raw score-level nullity of the base PG23 type law implies positive normalized
score-level nullity for the differential product law.  The proof excludes only
the inactive sentinel level `0`; positive levels project to raw score levels on
the base applicant coordinate.
-/
theorem pg23DifferentialPositiveNormalizedScoreLevelNull_of_raw {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College))
    [IsProbabilityMeasure baseLaw]
    (hbase : pg23SourceScoreLevelNull baseLaw) :
    pg23DifferentialPositiveNormalizedScoreLevelNull
      (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw) := by
  intro c y hy
  let t : Set (PG23ApplicantType College) :=
    {eta | al16ScoreValue al16SourceScore (pg23NormalizedStudent eta) c = y}
  have ht_meas : MeasurableSet t := by
    change MeasurableSet
      ((fun eta : PG23ApplicantType College =>
        al16ScoreValue al16SourceScore (pg23NormalizedStudent eta) c) ⁻¹'
          ({y} : Set ℝ))
    exact MeasurableSet.preimage (MeasurableSet.singleton y)
      (pg23NormalizedSourceScore_measurable c)
  have ht_zero : baseLaw t = 0 := by
    by_cases hnonempty : t.Nonempty
    · rcases hnonempty with ⟨eta0, heta0⟩
      let x := pg23SourceScore eta0 c
      have hsubset_t : t ⊆ {eta : PG23ApplicantType College |
          pg23SourceScore eta c = x} := by
        intro eta heta
        change pg23ScoreNormalize (pg23SourceScore eta c) = y at heta
        change pg23ScoreNormalize (pg23SourceScore eta0 c) = y at heta0
        apply pg23ScoreNormalize_strictMono.injective
        apply Subtype.ext
        simpa [x] using heta.trans heta0.symm
      exact measure_mono_null hsubset_t (hbase c x)
    · rw [Set.not_nonempty_iff_eq_empty.mp hnonempty]
      simp
  have hprod_zero :
      (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw)
        (Prod.snd ⁻¹' t) = 0 := by
    change (accessLaw.prod baseLaw) (Prod.snd ⁻¹' t) = 0
    have hmap : Measure.map Prod.snd (accessLaw.prod baseLaw) = baseLaw := by
      simpa using (Measure.map_snd_prod (μ := accessLaw) (ν := baseLaw))
    calc
      (accessLaw.prod baseLaw) (Prod.snd ⁻¹' t) =
          Measure.map Prod.snd (accessLaw.prod baseLaw) t := by
        rw [Measure.map_apply measurable_snd ht_meas]
      _ = baseLaw t := by rw [hmap]
      _ = 0 := ht_zero
  have hsubset :
      {theta : PG23DifferentialApplicantType College n |
        al16ScoreValue
          (pg23DifferentialNormalizedScore (College := College)) theta c = y} ⊆
        Prod.snd ⁻¹' t := by
    intro theta htheta
    by_cases hc : c ∈ pg23DifferentialActiveSet theta
    · simpa [t, pg23DifferentialNormalizedScore, hc, al16ScoreValue,
        pg23NormalizedStudent, pg23NormalizedScore] using htheta
    · have hzero : (0 : ℝ) = y := by
        simpa [pg23DifferentialNormalizedScore, hc, al16ScoreValue] using htheta
      have hnot : ¬ (0 : ℝ) < y := by
        rw [← hzero]
        exact lt_irrefl 0
      exact False.elim (hnot hy)
  exact measure_mono_null hsubset hprod_zero

/--
At a zero bounded cutoff, a differential applicant whose underlying first
choice is `c` chooses `c`.  The zero cutoff makes its bounded score affordable,
and no strictly better college exists.
-/
theorem pg23DifferentialNormalizedStudent_topRank_choice {n : ℕ}
    [Nonempty College]
    (Q : AL16Cutoff College) (c : College)
    (hQzero : al16CutoffValue Q c = 0)
    (theta : PG23DifferentialApplicantType College n)
    (htop : theta.2 ∈ pg23TopRankSet c) :
    pg23DifferentialNormalizedSourceChoice (College := College) Q theta =
      some c := by
  unfold pg23DifferentialNormalizedSourceChoice
  apply al16FavoriteAffordableChoice_eq_some_of_no_better
  · exact pg23DifferentialSourceRank_injective theta
  · rw [show
        al16Affordable
          (pg23DifferentialNormalizedScore (College := College)) Q theta c ↔
          al16CutoffValue Q c ≤
            al16ScoreValue
              (pg23DifferentialNormalizedScore (College := College)) theta c by rfl]
    rw [hQzero]
    exact (pg23DifferentialNormalizedScore (College := College) theta c).property.1
  · intro d _ hbetter
    have htoprank : pg23DifferentialSourceRank theta c = 0 := by
      simpa [pg23DifferentialSourceRank, pg23TopRankSet] using htop
    rw [htoprank] at hbetter
    exact Nat.not_lt_zero _ hbetter

/--
At a zero bounded cutoff, differential aggregate demand for `c` contains the
event that the underlying applicant ranks `c` first.
-/
theorem pg23DifferentialNormalizedAggregateDemand_ge_topRankMass {n : ℕ}
    [Nonempty College]
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsFiniteMeasure typeLaw]
    (Q : AL16Cutoff College) (c : College)
    (hQzero : al16CutoffValue Q c = 0) :
    typeLaw.real
        {theta : PG23DifferentialApplicantType College n |
          theta.2 ∈ pg23TopRankSet c} ≤
      pg23DifferentialNormalizedSourceAggregateDemand typeLaw Q c := by
  unfold pg23DifferentialNormalizedSourceAggregateDemand
  refine measureReal_mono ?_ (by finiteness)
  intro theta htheta
  change pg23DifferentialNormalizedSourceChoice
      (College := College) Q theta = some c
  exact pg23DifferentialNormalizedStudent_topRank_choice Q c hQzero theta htheta

/-- A first-ranked college is active under every differential access count. -/
theorem pg23DifferentialActiveSet_mem_of_topRank {n : ℕ}
    (theta : PG23DifferentialApplicantType College n) (c : College)
    (htop : theta.2 ∈ pg23TopRankSet c) :
    c ∈ pg23DifferentialActiveSet theta := by
  rw [pg23DifferentialActiveSet, pg23TopKApplicationSet_mem]
  change pg23SourceRank theta.2 c < theta.1.val + 1
  rw [show pg23SourceRank theta.2 c = 0 by
    simpa [pg23TopRankSet] using htop]
  omega

/-- On the first-rank event, the bounded differential score is strictly above the sentinel. -/
theorem pg23DifferentialNormalizedScore_pos_of_topRank {n : ℕ}
    (theta : PG23DifferentialApplicantType College n) (c : College)
    (htop : theta.2 ∈ pg23TopRankSet c) :
    0 < al16ScoreValue
      (pg23DifferentialNormalizedScore (College := College)) theta c := by
  have hc : c ∈ pg23DifferentialActiveSet theta :=
    pg23DifferentialActiveSet_mem_of_topRank theta c htop
  simpa [pg23DifferentialNormalizedScore, hc, al16ScoreValue,
    pg23NormalizedScore] using pg23ScoreNormalize_pos (pg23SourceScore theta.2 c)

/--
If a first-ranked college is affordable at an arbitrary bounded differential
cutoff, favorite-affordable demand chooses it.
-/
theorem pg23DifferentialNormalizedStudent_topRank_choice_of_affordable {n : ℕ}
    (Q : AL16Cutoff College) (c : College)
    (theta : PG23DifferentialApplicantType College n)
    (htop : theta.2 ∈ pg23TopRankSet c)
    (haff :
      al16CutoffValue Q c ≤
        al16ScoreValue
          (pg23DifferentialNormalizedScore (College := College)) theta c) :
    pg23DifferentialNormalizedSourceChoice (College := College) Q theta =
      some c := by
  unfold pg23DifferentialNormalizedSourceChoice
  apply al16FavoriteAffordableChoice_eq_some_of_no_better
  · exact pg23DifferentialSourceRank_injective theta
  · exact haff
  · intro d _ hbetter
    have htoprank : pg23DifferentialSourceRank theta c = 0 := by
      simpa [pg23DifferentialSourceRank, pg23TopRankSet] using htop
    rw [htoprank] at hbetter
    exact Nat.not_lt_zero _ hbetter

/--
At any bounded differential cutoff, demand for a college contains the first-rank
types whose bounded score clears that college's cutoff.
-/
theorem pg23DifferentialNormalizedAggregateDemand_ge_topRankThresholdMass {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsFiniteMeasure typeLaw]
    (Q : AL16Cutoff College) (c : College) :
    typeLaw.real
        {theta : PG23DifferentialApplicantType College n |
          theta.2 ∈ pg23TopRankSet c ∧
            al16CutoffValue Q c ≤
              al16ScoreValue
                (pg23DifferentialNormalizedScore (College := College)) theta c} ≤
      pg23DifferentialNormalizedSourceAggregateDemand typeLaw Q c := by
  unfold pg23DifferentialNormalizedSourceAggregateDemand
  refine measureReal_mono ?_ (by finiteness)
  intro theta htheta
  change pg23DifferentialNormalizedSourceChoice
      (College := College) Q theta = some c
  exact pg23DifferentialNormalizedStudent_topRank_choice_of_affordable
    Q c theta htheta.1 htheta.2

/--
As a positive threshold decreases to the inactive sentinel, the first-rank types
whose bounded score exceeds the threshold converge in mass to the whole
first-rank event.  This uses only finite measure and strict positivity of
normalized raw scores on first-ranked active colleges.
-/
theorem pg23DifferentialTopRankThresholdMass_tendsto_zero {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsFiniteMeasure typeLaw] (c : College) :
    Tendsto
      (fun m : ℕ =>
        typeLaw.real
          {theta : PG23DifferentialApplicantType College n |
            theta.2 ∈ pg23TopRankSet c ∧
              (1 : ℝ) / ((m : ℝ) + 1) ≤
                al16ScoreValue
                  (pg23DifferentialNormalizedScore (College := College)) theta c})
      atTop
      (nhds (typeLaw.real
        {theta : PG23DifferentialApplicantType College n |
          theta.2 ∈ pg23TopRankSet c})) := by
  let A : Set (PG23DifferentialApplicantType College n) :=
    {theta | theta.2 ∈ pg23TopRankSet c}
  let Aseq : ℕ -> Set (PG23DifferentialApplicantType College n) := fun m =>
    {theta | theta.2 ∈ pg23TopRankSet c ∧
      (1 : ℝ) / ((m : ℝ) + 1) ≤
        al16ScoreValue
          (pg23DifferentialNormalizedScore (College := College)) theta c}
  have hA_meas : MeasurableSet A := by
    change MeasurableSet (Prod.snd ⁻¹' pg23TopRankSet c)
    exact MeasurableSet.preimage (pg23TopRankSet_measurable c) measurable_snd
  have hAseq_meas : ∀ m : ℕ, MeasurableSet (Aseq m) := by
    intro m
    have hthreshold :
        MeasurableSet
          {theta : PG23DifferentialApplicantType College n |
            (1 : ℝ) / ((m : ℝ) + 1) ≤
              al16ScoreValue
                (pg23DifferentialNormalizedScore (College := College)) theta c} :=
      measurableSet_le measurable_const
        (pg23DifferentialNormalizedScore_measurable (College := College) c)
    exact hA_meas.inter hthreshold
  have hmembership : ∀ theta : PG23DifferentialApplicantType College n,
      ∀ᶠ m in atTop, theta ∈ Aseq m ↔ theta ∈ A := by
    intro theta
    by_cases htop : theta.2 ∈ pg23TopRankSet c
    · have hscore_pos :
          0 <
            al16ScoreValue
              (pg23DifferentialNormalizedScore (College := College)) theta c :=
        pg23DifferentialNormalizedScore_pos_of_topRank theta c htop
      have hthreshold_tendsto :
          Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hthreshold : ∀ᶠ (m : ℕ) in atTop,
          (1 : ℝ) / ((m : ℝ) + 1) <
            al16ScoreValue
              (pg23DifferentialNormalizedScore (College := College)) theta c :=
        hthreshold_tendsto.eventually_lt_const hscore_pos
      filter_upwards [hthreshold] with m hm
      constructor
      · intro _h
        exact htop
      · intro _h
        exact ⟨htop, le_of_lt hm⟩
    · exact Filter.Eventually.of_forall fun m => by
        constructor
        · intro h
          exact False.elim (htop h.1)
        · intro h
          exact False.elim (htop h)
  have hmeasure :
      Tendsto (fun m : ℕ => typeLaw (Aseq m)) atTop (nhds (typeLaw A)) :=
    MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      (L := atTop) (μ := typeLaw) (A := A) (As := Aseq)
      hA_meas hAseq_meas (ae_of_all typeLaw hmembership)
  have hreal :=
    (ENNReal.tendsto_toReal (measure_ne_top typeLaw A)).comp hmeasure
  simpa [A, Aseq, measureReal_def] using hreal

/--
Equal capacity strictly below the first-rank mass rules out zero coordinates of
a bounded differential normalized clearing cutoff.
-/
theorem pg23DifferentialNormalizedMarketClearing_cutoff_pos {n : ℕ}
    [Nonempty College]
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    (htop : ∀ c : College,
      typeLaw.real
        {theta : PG23DifferentialApplicantType College n |
          theta.2 ∈ pg23TopRankSet c} =
        1 / (Fintype.card College : ℝ))
    (S : ℝ) (hSlt : S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ))
    (Q : AL16Cutoff College)
    (hQ :
      al16SourceMarketClearing
        (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity Q)
    (c : College) :
    0 < al16CutoffValue Q c := by
  have hcardpos : (0 : ℝ) < Fintype.card College := by
    exact_mod_cast Fintype.card_pos
  have hmass := pg23DifferentialNormalizedAggregateDemand_ge_topRankMass
    typeLaw Q c
  have hupper := hQ.1 c
  rw [htop c] at hmass
  rw [hcapacity c] at hupper
  by_contra hnot
  have hzero : al16CutoffValue Q c = 0 :=
    le_antisymm (le_of_not_gt hnot) (Q c).property.1
  specialize hmass hzero
  have hstrict : S / (Fintype.card College : ℝ) <
      1 / (Fintype.card College : ℝ) := by
    exact (div_lt_div_iff₀ hcardpos hcardpos).2 (by nlinarith)
  exact (not_le_of_gt hstrict) (hmass.trans hupper)

/-- The differential product law inherits first-rank event mass from its base law. -/
theorem pg23DifferentialTypeLaw_topRankMass_eq_base {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (c : College) :
    (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw).real
        {theta : PG23DifferentialApplicantType College n |
          theta.2 ∈ pg23TopRankSet c} =
      baseLaw.real (pg23TopRankSet c) := by
  have hmap :
      Measure.map Prod.snd (accessLaw.prod baseLaw) = baseLaw := by
    simpa using (Measure.map_snd_prod (μ := accessLaw) (ν := baseLaw))
  have h := congrArg (fun law : Measure (PG23ApplicantType College) =>
      law.real (pg23TopRankSet c)) hmap
  change (Measure.map Prod.snd (accessLaw.prod baseLaw)).real
      (pg23TopRankSet c) = baseLaw.real (pg23TopRankSet c) at h
  rw [map_measureReal_apply measurable_snd (pg23TopRankSet_measurable c)] at h
  simpa [pg23DifferentialTypeLaw] using h

/--
For a differential product law, base first-rank mass `1 / |C|` and equal
capacity `S / |C|` with `S < 1` force every bounded clearing cutoff coordinate
above the inactive sentinel `0`.
-/
theorem pg23DifferentialNormalizedMarketClearing_cutoff_pos_of_base {n : ℕ}
    [Nonempty College]
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (htop : ∀ c : College,
      baseLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (S : ℝ) (hSlt : S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ))
    (Q : AL16Cutoff College)
    (hQ :
      al16SourceMarketClearing
        (pg23DifferentialNormalizedSourceAggregateDemand
          (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
        capacity Q) :
    ∀ c : College, 0 < al16CutoffValue Q c := by
  letI : IsProbabilityMeasure
      (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw) :=
    pg23DifferentialTypeLaw_isProbabilityMeasure accessLaw baseLaw
  intro c
  apply pg23DifferentialNormalizedMarketClearing_cutoff_pos
    (typeLaw := pg23DifferentialTypeLaw (College := College) accessLaw baseLaw)
    (S := S) (capacity := capacity) (Q := Q)
  · intro d
    rw [pg23DifferentialTypeLaw_topRankMass_eq_base accessLaw baseLaw d,
      htop d]
  · exact hSlt
  · exact hcapacity
  · exact hQ

/-- Positive capacities rule out unit coordinates of a bounded differential clearing cutoff. -/
theorem pg23DifferentialNormalizedMarketClearing_cutoff_lt_one {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    (capacity : College -> ℝ)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (Q : AL16Cutoff College)
    (hQ :
      al16SourceMarketClearing
        (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity Q)
    (c : College) :
    al16CutoffValue Q c < 1 := by
  rcases lt_or_eq_of_le (Q c).property.2 with hlt | hone
  · exact hlt
  · have hzero :=
      pg23DifferentialNormalizedSourceAggregateDemand_eq_zero_of_cutoff_eq_one
        typeLaw Q c hone
    have hpos : 0 < al16CutoffValue Q c := by
      change 0 < (Q c : ℝ)
      rw [hone]
      norm_num
    have heq := hQ.2 c hpos
    rw [hzero] at heq
    linarith [hcapacity_pos c]

/--
For a differential product law with equal capacity `0 < S < 1`, every bounded
normalized clearing cutoff is in the open unit interval coordinatewise.
-/
theorem pg23DifferentialNormalizedMarketClearing_cutoff_interior_of_base {n : ℕ}
    [Nonempty College]
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (htop : ∀ c : College,
      baseLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (S : ℝ) (hSpos : 0 < S) (hSlt : S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ))
    (Q : AL16Cutoff College)
    (hQ :
      al16SourceMarketClearing
        (pg23DifferentialNormalizedSourceAggregateDemand
          (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
        capacity Q) :
    ∀ c : College, 0 < al16CutoffValue Q c ∧ al16CutoffValue Q c < 1 := by
  let typeLaw :=
    pg23DifferentialTypeLaw (College := College) accessLaw baseLaw
  letI : IsProbabilityMeasure typeLaw :=
    pg23DifferentialTypeLaw_isProbabilityMeasure accessLaw baseLaw
  have hcapacity_pos : ∀ c : College, 0 < capacity c := by
    intro c
    rw [hcapacity c]
    have hcardpos : (0 : ℝ) < Fintype.card College := by
      exact_mod_cast Fintype.card_pos
    exact div_pos hSpos hcardpos
  intro c
  constructor
  · exact
      pg23DifferentialNormalizedMarketClearing_cutoff_pos_of_base
        accessLaw baseLaw htop S hSlt capacity hcapacity Q hQ c
  · exact
      pg23DifferentialNormalizedMarketClearing_cutoff_lt_one
        typeLaw capacity hcapacity_pos Q hQ c

/--
For a differential product law with equal capacity strictly below first-rank
mass, each college has a positive lower bound shared by all bounded normalized
clearing cutoffs.  This is the endpoint fact needed for infimum closure.
-/
theorem pg23DifferentialNormalizedMarketClearing_cutoff_uniform_pos_of_base {n : ℕ}
    [Nonempty College]
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (htop : ∀ c : College,
      baseLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (S : ℝ) (hSlt : S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ))
    (c : College) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ Q : AL16Cutoff College,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand
            (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
          capacity Q ->
        eps ≤ al16CutoffValue Q c := by
  let typeLaw :=
    pg23DifferentialTypeLaw (College := College) accessLaw baseLaw
  letI : IsProbabilityMeasure typeLaw :=
    pg23DifferentialTypeLaw_isProbabilityMeasure accessLaw baseLaw
  have hcardpos : (0 : ℝ) < Fintype.card College := by
    exact_mod_cast Fintype.card_pos
  have htop_prod :
      typeLaw.real
          {theta : PG23DifferentialApplicantType College n |
            theta.2 ∈ pg23TopRankSet c} =
        1 / (Fintype.card College : ℝ) := by
    change (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw).real
        {theta : PG23DifferentialApplicantType College n |
          theta.2 ∈ pg23TopRankSet c} =
      1 / (Fintype.card College : ℝ)
    rw [pg23DifferentialTypeLaw_topRankMass_eq_base accessLaw baseLaw c, htop c]
  have hcap_lt_top :
      capacity c <
        typeLaw.real
          {theta : PG23DifferentialApplicantType College n |
            theta.2 ∈ pg23TopRankSet c} := by
    rw [hcapacity c, htop_prod]
    exact (div_lt_div_iff₀ hcardpos hcardpos).2 (by nlinarith)
  have hthreshold_tendsto :=
    pg23DifferentialTopRankThresholdMass_tendsto_zero
      (College := College) (n := n) typeLaw c
  have hevent : ∀ᶠ m : ℕ in atTop,
      capacity c <
        typeLaw.real
          {theta : PG23DifferentialApplicantType College n |
            theta.2 ∈ pg23TopRankSet c ∧
              (1 : ℝ) / ((m : ℝ) + 1) ≤
                al16ScoreValue
                  (pg23DifferentialNormalizedScore (College := College)) theta c} :=
    hthreshold_tendsto.eventually_const_lt hcap_lt_top
  rcases hevent.exists with ⟨m, hm⟩
  refine ⟨(1 : ℝ) / ((m : ℝ) + 1), by positivity, ?_⟩
  intro Q hQ
  by_contra hnot
  have hQ_lt :
      al16CutoffValue Q c < (1 : ℝ) / ((m : ℝ) + 1) :=
    lt_of_not_ge hnot
  have hmass_mono :
      typeLaw.real
          {theta : PG23DifferentialApplicantType College n |
            theta.2 ∈ pg23TopRankSet c ∧
              (1 : ℝ) / ((m : ℝ) + 1) ≤
                al16ScoreValue
                  (pg23DifferentialNormalizedScore (College := College)) theta c} ≤
        typeLaw.real
          {theta : PG23DifferentialApplicantType College n |
            theta.2 ∈ pg23TopRankSet c ∧
              al16CutoffValue Q c ≤
                al16ScoreValue
                  (pg23DifferentialNormalizedScore (College := College)) theta c} := by
    refine measureReal_mono ?_ (by finiteness)
    intro theta htheta
    exact ⟨htheta.1, (le_of_lt hQ_lt).trans htheta.2⟩
  have hmass_le_demand :
      typeLaw.real
          {theta : PG23DifferentialApplicantType College n |
            theta.2 ∈ pg23TopRankSet c ∧
              (1 : ℝ) / ((m : ℝ) + 1) ≤
                al16ScoreValue
                  (pg23DifferentialNormalizedScore (College := College)) theta c} ≤
        pg23DifferentialNormalizedSourceAggregateDemand typeLaw Q c :=
    hmass_mono.trans
      (pg23DifferentialNormalizedAggregateDemand_ge_topRankThresholdMass
        typeLaw Q c)
  exact (not_lt_of_ge (hmass_le_demand.trans (hQ.1 c))) hm

/--
For the differential product law, the same first-rank/equal-capacity gap gives a
positive lower bound for any own cutoff that makes a college weakly feasible.
This is the paper-specific input needed to construct the least feasible
best-response threshold away from the inactive sentinel.
-/
theorem pg23DifferentialNormalizedOwnCutoff_uniform_pos_of_base {n : ℕ}
    [Nonempty College]
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (htop : ∀ c : College,
      baseLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (S : ℝ) (hSlt : S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ))
    (c : College) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ (P : AL16Cutoff College) (x : Set.Icc (0 : ℝ) 1),
        pg23DifferentialNormalizedSourceAggregateDemand
            (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw)
            (al16SourceUpdateCutoff P c x) c ≤ capacity c ->
        eps ≤ (x : ℝ) := by
  let typeLaw :=
    pg23DifferentialTypeLaw (College := College) accessLaw baseLaw
  letI : IsProbabilityMeasure typeLaw :=
    pg23DifferentialTypeLaw_isProbabilityMeasure accessLaw baseLaw
  have hcardpos : (0 : ℝ) < Fintype.card College := by
    exact_mod_cast Fintype.card_pos
  have htop_prod :
      typeLaw.real
          {theta : PG23DifferentialApplicantType College n |
            theta.2 ∈ pg23TopRankSet c} =
        1 / (Fintype.card College : ℝ) := by
    change (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw).real
        {theta : PG23DifferentialApplicantType College n |
          theta.2 ∈ pg23TopRankSet c} =
      1 / (Fintype.card College : ℝ)
    rw [pg23DifferentialTypeLaw_topRankMass_eq_base accessLaw baseLaw c, htop c]
  have hcap_lt_top :
      capacity c <
        typeLaw.real
          {theta : PG23DifferentialApplicantType College n |
            theta.2 ∈ pg23TopRankSet c} := by
    rw [hcapacity c, htop_prod]
    exact (div_lt_div_iff₀ hcardpos hcardpos).2 (by nlinarith)
  have hthreshold_tendsto :=
    pg23DifferentialTopRankThresholdMass_tendsto_zero
      (College := College) (n := n) typeLaw c
  have hevent : ∀ᶠ m : ℕ in atTop,
      capacity c <
        typeLaw.real
          {theta : PG23DifferentialApplicantType College n |
            theta.2 ∈ pg23TopRankSet c ∧
              (1 : ℝ) / ((m : ℝ) + 1) ≤
                al16ScoreValue
                  (pg23DifferentialNormalizedScore (College := College)) theta c} :=
    hthreshold_tendsto.eventually_const_lt hcap_lt_top
  rcases hevent.exists with ⟨m, hm⟩
  refine ⟨(1 : ℝ) / ((m : ℝ) + 1), by positivity, ?_⟩
  intro P x hfeasible
  by_contra hnot
  have hx_lt :
      (x : ℝ) < (1 : ℝ) / ((m : ℝ) + 1) :=
    lt_of_not_ge hnot
  have hmass_mono :
      typeLaw.real
          {theta : PG23DifferentialApplicantType College n |
            theta.2 ∈ pg23TopRankSet c ∧
              (1 : ℝ) / ((m : ℝ) + 1) ≤
                al16ScoreValue
                  (pg23DifferentialNormalizedScore (College := College)) theta c} ≤
        typeLaw.real
          {theta : PG23DifferentialApplicantType College n |
            theta.2 ∈ pg23TopRankSet c ∧
              al16CutoffValue (al16SourceUpdateCutoff P c x) c ≤
                al16ScoreValue
                  (pg23DifferentialNormalizedScore (College := College)) theta c} := by
    refine measureReal_mono ?_ (by finiteness)
    intro theta htheta
    have hx_value :
        al16CutoffValue (al16SourceUpdateCutoff P c x) c = (x : ℝ) := by
      simp [al16CutoffValue, al16SourceUpdateCutoff]
    exact ⟨htheta.1, by
      rw [hx_value]
      exact (le_of_lt hx_lt).trans htheta.2⟩
  have hmass_le_demand :
      typeLaw.real
          {theta : PG23DifferentialApplicantType College n |
            theta.2 ∈ pg23TopRankSet c ∧
              (1 : ℝ) / ((m : ℝ) + 1) ≤
                al16ScoreValue
                  (pg23DifferentialNormalizedScore (College := College)) theta c} ≤
        pg23DifferentialNormalizedSourceAggregateDemand typeLaw
          (al16SourceUpdateCutoff P c x) c :=
    hmass_mono.trans
      (pg23DifferentialNormalizedAggregateDemand_ge_topRankThresholdMass
        typeLaw (al16SourceUpdateCutoff P c x) c)
  exact (not_lt_of_ge (hmass_le_demand.trans hfeasible)) hm

/--
At normalized raw cutoffs, bounded differential-score affordability is exactly
source active affordability for the underlying applicant.
-/
theorem pg23DifferentialNormalizedAffordable_iff {n : ℕ}
    (P : College -> ℝ) (theta : PG23DifferentialApplicantType College n)
    (c : College) :
    al16Affordable
        (pg23DifferentialNormalizedScore (College := College))
        (pg23NormalizedCutoff P) theta c ↔
      c ∈ pg23DifferentialActiveSet theta ∧ pg23Affordable P theta.2 c := by
  constructor
  · intro haff
    have hc_active : c ∈ pg23DifferentialActiveSet theta := by
      by_contra hc
      have hle_zero : (pg23ScoreNormalize (P c) : ℝ) ≤ 0 := by
        simpa [al16Affordable, al16CutoffValue, al16ScoreValue,
          pg23DifferentialNormalizedScore, pg23NormalizedCutoff, hc] using haff
      exact (not_lt_of_ge hle_zero) (pg23ScoreNormalize_pos (P c))
    have hnorm :
        pg23ScoreNormalize (P c) ≤
          pg23ScoreNormalize (pg23SourceScore theta.2 c) := by
      simpa [al16Affordable, al16CutoffValue, al16ScoreValue,
        pg23DifferentialNormalizedScore, pg23NormalizedCutoff, pg23NormalizedScore,
        hc_active] using haff
    exact ⟨hc_active,
      (pg23ScoreNormalize_le_iff (P c) (pg23SourceScore theta.2 c)).mp hnorm⟩
  · rintro ⟨hc_active, hraw⟩
    have hnorm :
        pg23ScoreNormalize (P c) ≤
          pg23ScoreNormalize (pg23SourceScore theta.2 c) :=
      (pg23ScoreNormalize_le_iff (P c) (pg23SourceScore theta.2 c)).mpr hraw
    simpa [al16Affordable, al16CutoffValue, al16ScoreValue,
      pg23DifferentialNormalizedScore, pg23NormalizedCutoff, pg23NormalizedScore,
      hc_active] using hnorm

/-- Differential normalized scores are equivariant under relabeling. -/
theorem pg23DifferentialNormalizedScore_relabel {n : ℕ}
    (sigma : Equiv.Perm College)
    (theta : PG23DifferentialApplicantType College n) (c : College) :
    pg23DifferentialNormalizedScore
        (pg23DifferentialRelabelApplicant (College := College) sigma theta)
        (sigma c) =
      pg23DifferentialNormalizedScore theta c := by
  classical
  have hactive :
      sigma c ∈
          pg23DifferentialActiveSet
            (pg23DifferentialRelabelApplicant (College := College) sigma theta) ↔
        c ∈ pg23DifferentialActiveSet theta := by
    rw [pg23DifferentialActiveSet_relabel]
    simpa using
      (pg23RelabelActiveSet_mem sigma (pg23DifferentialActiveSet theta) (sigma c))
  by_cases hc : c ∈ pg23DifferentialActiveSet theta
  · have hsig :
        sigma c ∈
          pg23DifferentialActiveSet
            (pg23DifferentialRelabelApplicant (College := College) sigma theta) :=
      hactive.mpr hc
    have hsig' :
        sigma c ∈
          pg23DifferentialActiveSet (theta.1, pg23RelabelApplicant sigma theta.2) := by
      simpa [pg23DifferentialRelabelApplicant] using hsig
    apply Subtype.ext
    simp [pg23DifferentialNormalizedScore, hsig', hc, pg23NormalizedScore,
      pg23DifferentialRelabelApplicant, pg23RelabelApplicant_score]
  · have hsig :
        sigma c ∉
          pg23DifferentialActiveSet
            (pg23DifferentialRelabelApplicant (College := College) sigma theta) := by
      intro h
      exact hc (hactive.mp h)
    simp [pg23DifferentialNormalizedScore, hsig, hc]

/-- Bounded differential affordability is invariant under simultaneous relabeling. -/
theorem pg23DifferentialNormalizedAffordable_relabel_iff {n : ℕ}
    (sigma : Equiv.Perm College) (Q : AL16Cutoff College)
    (theta : PG23DifferentialApplicantType College n) (c : College) :
    al16Affordable
        (pg23DifferentialNormalizedScore (College := College))
        (pg23RelabelNormalizedCutoff sigma Q)
        (pg23DifferentialRelabelApplicant (College := College) sigma theta)
        (sigma c) ↔
      al16Affordable
        (pg23DifferentialNormalizedScore (College := College)) Q theta c := by
  unfold al16Affordable al16CutoffValue al16ScoreValue
  rw [pg23DifferentialNormalizedScore_relabel]
  simp [pg23RelabelNormalizedCutoff]

/--
The bounded differential-score selector agrees with PG23's source differential
selector at the normalized image of any finite raw cutoff.
-/
theorem pg23DifferentialNormalizedSourceChoice_normalizedCutoff_eq {n : ℕ}
    (P : College -> ℝ) (theta : PG23DifferentialApplicantType College n) :
    pg23DifferentialNormalizedSourceChoice
        (College := College) (pg23NormalizedCutoff P) theta =
      pg23DifferentialSourceChoice P theta := by
  classical
  unfold pg23DifferentialNormalizedSourceChoice
  have hsem := al16FavoriteAffordableChoice_semantics
    (score := pg23DifferentialNormalizedScore (College := College))
    (rank := pg23DifferentialSourceRank)
    (P := pg23NormalizedCutoff P) (theta := theta)
  cases hchoice :
      al16FavoriteAffordableChoice
        (pg23DifferentialNormalizedScore (College := College))
        pg23DifferentialSourceRank (pg23NormalizedCutoff P) theta with
  | none =>
      rw [hchoice] at hsem
      cases hsource_choice : pg23DifferentialSourceChoice P theta with
      | none => rfl
      | some c =>
          have hc :=
            pg23ActiveSourceChoice_some_active_affordable
              (active := pg23DifferentialActiveSet theta)
              (P := P) (theta := theta.2) hsource_choice
          have haff :
              al16Affordable
                (pg23DifferentialNormalizedScore (College := College))
                (pg23NormalizedCutoff P) theta c :=
            (pg23DifferentialNormalizedAffordable_iff P theta c).mpr hc
          exact False.elim ((not_le_of_gt (hsem c)) haff)
  | some c =>
      rw [hchoice] at hsem
      have hc_active_affordable :
          c ∈ pg23DifferentialActiveSet theta ∧ pg23Affordable P theta.2 c :=
        (pg23DifferentialNormalizedAffordable_iff P theta c).mp hsem.1
      have hno_better :
          ∀ d : College, d ∈ pg23DifferentialActiveSet theta ->
            pg23Affordable P theta.2 d ->
              ¬ pg23SourcePrefers theta.2 (some d) (some c) := by
        intro d hd_active hd_affordable
        have hd_norm :
            al16Affordable
              (pg23DifferentialNormalizedScore (College := College))
              (pg23NormalizedCutoff P) theta d :=
          (pg23DifferentialNormalizedAffordable_iff P theta d).mpr
            ⟨hd_active, hd_affordable⟩
        exact hsem.2 d hd_norm
      have hsource_choice :
          pg23DifferentialSourceChoice P theta = some c :=
        (pg23ActiveSourceChoice_eq_some_iff
          (pg23DifferentialActiveSet theta) P theta.2 c).mpr
          ⟨hc_active_affordable.1, hc_active_affordable.2, hno_better⟩
      simp [hsource_choice]

/-- Normalized differential aggregate demand agrees with raw demand on normalized raw cutoffs. -/
theorem pg23DifferentialNormalizedAggregateDemand_normalizedCutoff_eq {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    (P : College -> ℝ) (c : College) :
    pg23DifferentialNormalizedSourceAggregateDemand typeLaw
        (pg23NormalizedCutoff P) c =
      pg23DifferentialSourceAggregateDemand typeLaw P c := by
  unfold pg23DifferentialNormalizedSourceAggregateDemand
    pg23DifferentialSourceAggregateDemand al16DemandChoiceSet
  congr 1
  ext theta
  change
    pg23DifferentialNormalizedSourceChoice
        (College := College) (pg23NormalizedCutoff P) theta = some c ↔
      pg23DifferentialSourceChoice P theta = some c
  rw [pg23DifferentialNormalizedSourceChoice_normalizedCutoff_eq]

/-- Differential bounded-score choice is equivariant under relabeling. -/
theorem pg23DifferentialNormalizedSourceChoice_relabel {n : ℕ}
    (sigma : Equiv.Perm College) (Q : AL16Cutoff College)
    (theta : PG23DifferentialApplicantType College n) :
    pg23DifferentialNormalizedSourceChoice
        (College := College) (pg23RelabelNormalizedCutoff sigma Q)
        (pg23DifferentialRelabelApplicant (College := College) sigma theta) =
      Option.map sigma
        (pg23DifferentialNormalizedSourceChoice (College := College) Q theta) := by
  classical
  unfold pg23DifferentialNormalizedSourceChoice
  have horig_sem := al16FavoriteAffordableChoice_semantics
    (score := pg23DifferentialNormalizedScore (College := College))
    (rank := pg23DifferentialSourceRank)
    (P := Q) (theta := theta)
  cases horig :
      al16FavoriteAffordableChoice
        (pg23DifferentialNormalizedScore (College := College))
        pg23DifferentialSourceRank Q theta with
  | none =>
      rw [horig] at horig_sem
      apply al16FavoriteAffordableChoice_eq_none_of_no_affordable
      intro d hd_affordable
      have hd_original :
          al16Affordable
            (pg23DifferentialNormalizedScore (College := College)) Q theta
            (sigma.symm d) := by
        have hd_affordable' :
            al16Affordable
              (pg23DifferentialNormalizedScore (College := College))
              (pg23RelabelNormalizedCutoff sigma Q)
              (pg23DifferentialRelabelApplicant (College := College) sigma theta)
              (sigma (sigma.symm d)) := by
          simpa using hd_affordable
        simpa using
          (pg23DifferentialNormalizedAffordable_relabel_iff
            (College := College) sigma Q theta (sigma.symm d)).mp
              hd_affordable'
      exact (not_le_of_gt (horig_sem (sigma.symm d))) hd_original
  | some c =>
      rw [horig] at horig_sem
      have hc_affordable :
          al16Affordable
            (pg23DifferentialNormalizedScore (College := College))
            (pg23RelabelNormalizedCutoff sigma Q)
            (pg23DifferentialRelabelApplicant (College := College) sigma theta)
            (sigma c) :=
        (pg23DifferentialNormalizedAffordable_relabel_iff
          (College := College) sigma Q theta c).mpr horig_sem.1
      change
        al16FavoriteAffordableChoice
            (pg23DifferentialNormalizedScore (College := College))
            pg23DifferentialSourceRank
            (pg23RelabelNormalizedCutoff sigma Q)
            (pg23DifferentialRelabelApplicant (College := College) sigma theta) =
          some (sigma c)
      refine al16FavoriteAffordableChoice_eq_some_of_no_better
        (score := pg23DifferentialNormalizedScore (College := College))
        (rank := pg23DifferentialSourceRank)
        (P := pg23RelabelNormalizedCutoff sigma Q)
        (theta := pg23DifferentialRelabelApplicant
          (College := College) sigma theta)
        (c := sigma c)
        (hrank_injective :=
          pg23DifferentialSourceRank_injective
            (pg23DifferentialRelabelApplicant (College := College) sigma theta))
        hc_affordable ?_
      intro d hd_affordable
      have hd_original :
          al16Affordable
            (pg23DifferentialNormalizedScore (College := College)) Q theta
            (sigma.symm d) := by
        have hd_affordable' :
            al16Affordable
              (pg23DifferentialNormalizedScore (College := College))
              (pg23RelabelNormalizedCutoff sigma Q)
              (pg23DifferentialRelabelApplicant (College := College) sigma theta)
              (sigma (sigma.symm d)) := by
          simpa using hd_affordable
        simpa using
          (pg23DifferentialNormalizedAffordable_relabel_iff
            (College := College) sigma Q theta (sigma.symm d)).mp
              hd_affordable'
      have hnot := horig_sem.2 (sigma.symm d) hd_original
      simpa [al16RankPrefers, pg23DifferentialSourceRank,
        pg23DifferentialRelabelApplicant, pg23RelabelApplicant_rank] using hnot

/--
Relabeling an invariant differential-access type law transports bounded
normalized differential aggregate demand.
-/
theorem pg23DifferentialNormalizedSourceAggregateDemand_relabel_of_typeLaw_relabel
    {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    (sigma : Equiv.Perm College) (Q : AL16Cutoff College) (c : College)
    (hlaw :
      Measure.map
        (pg23DifferentialRelabelApplicant (College := College) (n := n) sigma)
        typeLaw = typeLaw) :
    pg23DifferentialNormalizedSourceAggregateDemand typeLaw
        (pg23RelabelNormalizedCutoff sigma Q) (sigma c) =
      pg23DifferentialNormalizedSourceAggregateDemand typeLaw Q c := by
  have hmeas :
      MeasurableSet
        (al16DemandChoiceSet
          (pg23DifferentialNormalizedSourceChoice (College := College) (n := n))
          (pg23RelabelNormalizedCutoff sigma Q) (sigma c)) := by
    change MeasurableSet
      ((al16FavoriteAffordableChoice
        (pg23DifferentialNormalizedScore (College := College))
        pg23DifferentialSourceRank
        (pg23RelabelNormalizedCutoff sigma Q)) ⁻¹'
        ({some (sigma c)} : Set (Option College)))
    exact
      al16FavoriteAffordableChoice_fiber_measurable
        (score := pg23DifferentialNormalizedScore (College := College))
        (rank := pg23DifferentialSourceRank)
        (hscore_measurable :=
          pg23DifferentialNormalizedScore_measurable (College := College))
        (hrank_measurable :=
          pg23DifferentialSourceRank_measurable (College := College))
        (hrank_injective :=
          pg23DifferentialSourceRank_injective (College := College))
        (P := pg23RelabelNormalizedCutoff sigma Q)
        (o := some (sigma c))
  unfold pg23DifferentialNormalizedSourceAggregateDemand
  calc
    typeLaw.real
          (al16DemandChoiceSet
          (pg23DifferentialNormalizedSourceChoice (College := College) (n := n))
          (pg23RelabelNormalizedCutoff sigma Q) (sigma c)) =
        (Measure.map
          (pg23DifferentialRelabelApplicant (College := College) (n := n) sigma)
          typeLaw).real
          (al16DemandChoiceSet
            (pg23DifferentialNormalizedSourceChoice (College := College) (n := n))
            (pg23RelabelNormalizedCutoff sigma Q) (sigma c)) := by
      rw [hlaw]
    _ = typeLaw.real
          ((pg23DifferentialRelabelApplicant
            (College := College) (n := n) sigma) ⁻¹'
            al16DemandChoiceSet
              (pg23DifferentialNormalizedSourceChoice (College := College) (n := n))
              (pg23RelabelNormalizedCutoff sigma Q) (sigma c)) :=
      map_measureReal_apply
        (pg23DifferentialRelabelApplicant_measurable
          (College := College) (n := n) sigma)
        hmeas
    _ = typeLaw.real
          (al16DemandChoiceSet
            (pg23DifferentialNormalizedSourceChoice (College := College) (n := n))
            Q c) := by
      congr 1
      ext theta
      simp only [Set.mem_preimage, al16DemandChoiceSet, Set.mem_setOf_eq]
      rw [pg23DifferentialNormalizedSourceChoice_relabel]
      constructor
      · intro h
        exact Option.map_injective sigma.injective h
      · intro h
        simp [h]

/--
Under type-law and capacity invariance, bounded normalized differential market
clearing is invariant under college relabeling.
-/
theorem pg23DifferentialNormalizedMarketClearing_relabel_of_typeLaw_relabel
    {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    (capacity : College -> ℝ)
    (sigma : Equiv.Perm College) (Q : AL16Cutoff College)
    (hlaw :
      Measure.map
        (pg23DifferentialRelabelApplicant (College := College) (n := n) sigma)
        typeLaw = typeLaw)
    (hcapacity : ∀ c : College, capacity (sigma c) = capacity c)
    (hQ :
      al16SourceMarketClearing
        (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity Q) :
    al16SourceMarketClearing
      (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity
      (pg23RelabelNormalizedCutoff sigma Q) := by
  constructor
  · intro c
    calc
      pg23DifferentialNormalizedSourceAggregateDemand typeLaw
          (pg23RelabelNormalizedCutoff sigma Q) c =
          pg23DifferentialNormalizedSourceAggregateDemand typeLaw Q (sigma.symm c) := by
        simpa using
          pg23DifferentialNormalizedSourceAggregateDemand_relabel_of_typeLaw_relabel
            (typeLaw := typeLaw) sigma Q (sigma.symm c) hlaw
      _ ≤ capacity (sigma.symm c) := hQ.1 (sigma.symm c)
      _ = capacity c := by
        simpa using (hcapacity (sigma.symm c)).symm
  · intro c hpos
    have hpos_original : 0 < al16CutoffValue Q (sigma.symm c) := by
      simpa [pg23RelabelNormalizedCutoff, al16CutoffValue] using hpos
    calc
      pg23DifferentialNormalizedSourceAggregateDemand typeLaw
          (pg23RelabelNormalizedCutoff sigma Q) c =
          pg23DifferentialNormalizedSourceAggregateDemand typeLaw Q (sigma.symm c) := by
        simpa using
          pg23DifferentialNormalizedSourceAggregateDemand_relabel_of_typeLaw_relabel
            (typeLaw := typeLaw) sigma Q (sigma.symm c) hlaw
      _ = capacity (sigma.symm c) := hQ.2 (sigma.symm c) hpos_original
      _ = capacity c := by
        simpa using (hcapacity (sigma.symm c)).symm

/--
The greatest bounded normalized differential-access clearing cutoff is
coordinate-constant whenever the differential law and capacities are invariant
under college relabeling.  This proves the symmetry/extrema step without
assuming existence or uniqueness.
-/
theorem pg23DifferentialNormalizedMarketClearing_greatest_constant_of_typeLaw_relabel
    {n : ℕ} [Nonempty College]
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    (capacity : College -> ℝ)
    (hlaw :
      ∀ sigma : Equiv.Perm College,
        Measure.map
          (pg23DifferentialRelabelApplicant (College := College) (n := n) sigma)
          typeLaw = typeLaw)
    (hcapacity :
      ∀ sigma : Equiv.Perm College, ∀ c : College,
        capacity (sigma c) = capacity c)
    (top : AL16Cutoff College)
    (htop :
      al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity top ∧
        ∀ Q : AL16Cutoff College,
          al16SourceMarketClearing
            (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity Q ->
          al16CutoffLe Q top) :
    ∃ q : ℝ, ∀ c : College, al16CutoffValue top c = q := by
  apply pg23NormalizedCutoff_constant_of_relabel_fixed top
  intro sigma
  apply pg23RelabelNormalizedCutoff_eq_of_greatest
    (fun Q : AL16Cutoff College =>
      al16SourceMarketClearing
        (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity Q)
    top htop
  intro tau Q hQ
  exact pg23DifferentialNormalizedMarketClearing_relabel_of_typeLaw_relabel
    typeLaw capacity tau Q (hlaw tau) (hcapacity tau) hQ

/--
The least bounded normalized differential-access clearing cutoff is
coordinate-constant under the same relabeling invariance assumptions.
-/
theorem pg23DifferentialNormalizedMarketClearing_least_constant_of_typeLaw_relabel
    {n : ℕ} [Nonempty College]
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    (capacity : College -> ℝ)
    (hlaw :
      ∀ sigma : Equiv.Perm College,
        Measure.map
          (pg23DifferentialRelabelApplicant (College := College) (n := n) sigma)
          typeLaw = typeLaw)
    (hcapacity :
      ∀ sigma : Equiv.Perm College, ∀ c : College,
        capacity (sigma c) = capacity c)
    (bot : AL16Cutoff College)
    (hbot :
      al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity bot ∧
        ∀ Q : AL16Cutoff College,
          al16SourceMarketClearing
            (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity Q ->
          al16CutoffLe bot Q) :
    ∃ q : ℝ, ∀ c : College, al16CutoffValue bot c = q := by
  apply pg23NormalizedCutoff_constant_of_relabel_fixed bot
  intro sigma
  apply pg23RelabelNormalizedCutoff_eq_of_least
    (fun Q : AL16Cutoff College =>
      al16SourceMarketClearing
        (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity Q)
    bot hbot
  intro tau Q hQ
  exact pg23DifferentialNormalizedMarketClearing_relabel_of_typeLaw_relabel
    typeLaw capacity tau Q (hlaw tau) (hcapacity tau) hQ

/-- Raw exact differential clearing transports to bounded normalized clearing. -/
theorem pg23DifferentialNormalizedMarketClearing_of_raw {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    (capacity : College -> ℝ) (P : College -> ℝ)
    (hP :
      pg23DifferentialSourceMarketClearing
        (pg23DifferentialSourceAggregateDemand typeLaw) capacity P) :
    al16SourceMarketClearing
      (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity
      (pg23NormalizedCutoff P) := by
  constructor
  · intro c
    rw [pg23DifferentialNormalizedAggregateDemand_normalizedCutoff_eq]
    exact (hP c).le
  · intro c _hc
    rw [pg23DifferentialNormalizedAggregateDemand_normalizedCutoff_eq]
    exact hP c

/--
Interior bounded normalized differential clearing transports back to finite
raw exact clearing.
-/
theorem pg23DifferentialSourceMarketClearing_of_normalized {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    (capacity : College -> ℝ) (Q : AL16Cutoff College)
    (hinterior :
      ∀ c : College, 0 < al16CutoffValue Q c ∧ al16CutoffValue Q c < 1)
    (hQ :
      al16SourceMarketClearing
        (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity Q) :
    pg23DifferentialSourceMarketClearing
      (pg23DifferentialSourceAggregateDemand typeLaw) capacity
      (pg23DenormalizedCutoff Q) := by
  intro c
  have hnormalized_eq :
      pg23NormalizedCutoff (pg23DenormalizedCutoff Q) = Q :=
    pg23NormalizedCutoff_denormalized_eq Q hinterior
  calc
    pg23DifferentialSourceAggregateDemand typeLaw
        (pg23DenormalizedCutoff Q) c =
        pg23DifferentialNormalizedSourceAggregateDemand typeLaw
          (pg23NormalizedCutoff (pg23DenormalizedCutoff Q)) c := by
      rw [pg23DifferentialNormalizedAggregateDemand_normalizedCutoff_eq]
    _ = pg23DifferentialNormalizedSourceAggregateDemand typeLaw Q c := by
      rw [hnormalized_eq]
    _ = capacity c := hQ.2 c (hinterior c).1

/--
The AL complete-lattice theorem applies to the bounded differential-access
score once demand continuity is proved.  The continuity premise is visible
because inactive applications put an atom at the sentinel score `0`, so it is
not the same strict-preferences argument used by the baseline PG23 model.
-/
theorem pg23DifferentialNormalizedMarketClearing_completeLattice_of_continuity {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    (capacity : College -> ℝ)
    (hdemand_continuous :
      ∀ (Pseq : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College),
        al16CoordinatewiseTendsto Pseq Q ->
          ∀ c : College,
            Tendsto
              (fun m => pg23DifferentialNormalizedSourceAggregateDemand typeLaw
                (Pseq m) c)
              atTop
              (nhds (pg23DifferentialNormalizedSourceAggregateDemand typeLaw Q c)))
    (hnonempty : ∃ P : AL16Cutoff College,
      al16SourceMarketClearing
        (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity P) :
    CompleteLatticeOn
      (al16SourceMarketClearing
        (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity)
      al16CutoffLe := by
  apply al16SourceMarketClearing_completeLattice_of_probability_measure_ranked_choice_primitives
    (mu := typeLaw)
    (demand := pg23DifferentialNormalizedSourceAggregateDemand typeLaw)
    (outside := pg23DifferentialNormalizedOutsideDemand typeLaw)
    (capacity := capacity)
    (score := pg23DifferentialNormalizedScore (College := College))
    (rank := pg23DifferentialSourceRank)
  · intro Q c
    rfl
  · intro Q
    rfl
  · exact pg23DifferentialNormalizedScore_measurable
  · exact pg23DifferentialSourceRank_measurable
  · exact pg23DifferentialSourceRank_injective
  · exact hdemand_continuous
  · exact hnonempty

/--
At a strictly positive bounded cutoff vector, differential normalized aggregate
demand is sequentially continuous under positive score-level nullity.  This is
the source-faithful replacement for the baseline global strict-preferences
argument; it deliberately does not claim continuity at the inactive sentinel
level `0`.
-/
theorem pg23DifferentialNormalizedAggregateDemand_tendsto_of_positive_coordinatewiseTendsto
    {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    (hlevel : pg23DifferentialPositiveNormalizedScoreLevelNull typeLaw)
    (Pseq : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College)
    (hQpos : ∀ c : College, 0 < al16CutoffValue Q c)
    (hPQ : al16CoordinatewiseTendsto Pseq Q) (c : College) :
    Tendsto
      (fun m => pg23DifferentialNormalizedSourceAggregateDemand typeLaw
        (Pseq m) c)
      atTop
      (nhds (pg23DifferentialNormalizedSourceAggregateDemand typeLaw Q c)) := by
  unfold pg23DifferentialNormalizedSourceAggregateDemand
  exact al16FavoriteAffordableAggregateDemand_tendsto_of_coordinatewiseTendsto
    (mu := typeLaw)
    (score := pg23DifferentialNormalizedScore (College := College))
    (rank := pg23DifferentialSourceRank)
    (hscore_measurable :=
      pg23DifferentialNormalizedScore_measurable (College := College))
    (hrank_measurable :=
      pg23DifferentialSourceRank_measurable (College := College))
    (hrank_injective :=
      pg23DifferentialSourceRank_injective (College := College))
    (P := Pseq) (Q := Q)
    (hboundary_null := fun d => hlevel d (al16CutoffValue Q d) (hQpos d))
    hPQ c

/--
For the differential product law, raw base score-level nullity gives continuity
at any bounded clearing cutoff with equal capacity `S / |C|` and `S < 1`.  The
positivity of the cutoff coordinates is derived from clearing and first-rank
mass rather than assumed.
-/
theorem pg23DifferentialNormalizedAggregateDemand_tendsto_at_productClearing_of_raw
    {n : ℕ} [Nonempty College]
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (hbase_level : pg23SourceScoreLevelNull baseLaw)
    (htop : ∀ c : College,
      baseLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (S : ℝ) (hSlt : S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ))
    (Pseq : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College)
    (hQ :
      al16SourceMarketClearing
        (pg23DifferentialNormalizedSourceAggregateDemand
          (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
        capacity Q)
    (hPQ : al16CoordinatewiseTendsto Pseq Q) (c : College) :
    Tendsto
      (fun m => pg23DifferentialNormalizedSourceAggregateDemand
        (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw)
        (Pseq m) c)
      atTop
      (nhds (pg23DifferentialNormalizedSourceAggregateDemand
        (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw) Q c)) := by
  letI : IsProbabilityMeasure
      (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw) :=
    pg23DifferentialTypeLaw_isProbabilityMeasure accessLaw baseLaw
  have hQpos : ∀ d : College, 0 < al16CutoffValue Q d :=
    pg23DifferentialNormalizedMarketClearing_cutoff_pos_of_base
      accessLaw baseLaw htop S hSlt capacity hcapacity Q hQ
  exact pg23DifferentialNormalizedAggregateDemand_tendsto_of_positive_coordinatewiseTendsto
    (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw)
    (pg23DifferentialPositiveNormalizedScoreLevelNull_of_raw accessLaw baseLaw
      hbase_level)
    Pseq Q hQpos hPQ c

/--
One-coordinate continuity for bounded differential demand at a positive own
cutoff.  Other cutoff coordinates are fixed, so no score-level nullity is needed
at their possibly-zero sentinel values.
-/
theorem pg23DifferentialNormalizedAggregateDemand_tendsto_of_updateTendsto
    {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    (hlevel : pg23DifferentialPositiveNormalizedScoreLevelNull typeLaw)
    (P : AL16Cutoff College) (c : College)
    (xseq : ℕ -> Set.Icc (0 : ℝ) 1) (x : Set.Icc (0 : ℝ) 1)
    (hxpos : 0 < (x : ℝ))
    (hxseq : Tendsto (fun m => (xseq m : ℝ)) atTop (nhds (x : ℝ))) :
    Tendsto
      (fun m => pg23DifferentialNormalizedSourceAggregateDemand typeLaw
        (al16SourceUpdateCutoff P c (xseq m)) c)
      atTop
      (nhds (pg23DifferentialNormalizedSourceAggregateDemand typeLaw
        (al16SourceUpdateCutoff P c x) c)) := by
  unfold pg23DifferentialNormalizedSourceAggregateDemand
  exact al16FavoriteAffordableAggregateDemand_tendsto_of_updateTendsto
    (mu := typeLaw)
    (score := pg23DifferentialNormalizedScore (College := College))
    (rank := pg23DifferentialSourceRank)
    (hscore_measurable :=
      pg23DifferentialNormalizedScore_measurable (College := College))
    (hrank_measurable :=
      pg23DifferentialSourceRank_measurable (College := College))
    (hrank_injective :=
      pg23DifferentialSourceRank_injective (College := College))
    (P := P) (c := c) (xseq := xseq) (x := x)
    (hboundary_null := hlevel c (x : ℝ) hxpos)
    hxseq

/-- View a cutoff value from `[eps, 1]` as a cutoff value in `[0, 1]`. -/
def pg23LowerBoundUnitCutoff (eps : ℝ) (heps_nonneg : 0 ≤ eps)
    (x : Set.Icc eps 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨(x : ℝ), ⟨le_trans heps_nonneg x.property.1, x.property.2⟩⟩

@[simp]
theorem pg23LowerBoundUnitCutoff_coe
    (eps : ℝ) (heps_nonneg : 0 ≤ eps) (x : Set.Icc eps 1) :
    (pg23LowerBoundUnitCutoff eps heps_nonneg x : ℝ) = (x : ℝ) :=
  rfl

/-- Demand as a function of one positive own cutoff is continuous on `[eps, 1]`. -/
theorem pg23DifferentialNormalizedOwnAggregateDemand_continuous_lowerBound
    {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    (hlevel : pg23DifferentialPositiveNormalizedScoreLevelNull typeLaw)
    (eps : ℝ) (heps_pos : 0 < eps)
    (capacity : College -> ℝ)
    (P : AL16Cutoff College) (c : College) :
    Continuous
      (fun x : Set.Icc eps 1 =>
        pg23DifferentialNormalizedSourceAggregateDemand typeLaw
          (al16SourceUpdateCutoff P c
            (pg23LowerBoundUnitCutoff eps heps_pos.le x)) c) := by
  rw [continuous_iff_seqContinuous]
  intro xseq x hxseq
  have hxreal : Tendsto (fun m => (xseq m : ℝ)) atTop (nhds (x : ℝ)) :=
    (continuous_subtype_val.tendsto x).comp hxseq
  have hxpos :
      0 < (pg23LowerBoundUnitCutoff eps heps_pos.le x : ℝ) :=
    lt_of_lt_of_le heps_pos x.property.1
  exact pg23DifferentialNormalizedAggregateDemand_tendsto_of_updateTendsto
    typeLaw hlevel P c
    (fun m => pg23LowerBoundUnitCutoff eps heps_pos.le (xseq m))
    (pg23LowerBoundUnitCutoff eps heps_pos.le x)
    hxpos
    (by simpa using hxreal)

/-- Own-cutoff values in `[eps, 1]` that make one college weakly feasible. -/
noncomputable def pg23DifferentialNormalizedCapacityFeasibleCutoffsOn {n : ℕ}
    (eps : ℝ) (heps_nonneg : 0 ≤ eps)
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    (capacity : College -> ℝ)
    (P : AL16Cutoff College) (c : College) : Set (Set.Icc eps 1) :=
  {x | pg23DifferentialNormalizedSourceAggregateDemand typeLaw
      (al16SourceUpdateCutoff P c
        (pg23LowerBoundUnitCutoff eps heps_nonneg x)) c ≤ capacity c}

/-- The positive-own-cutoff feasible set is closed inside `[eps, 1]`. -/
theorem pg23DifferentialNormalizedCapacityFeasibleCutoffsOn_closed {n : ℕ}
    (eps : ℝ) (heps_pos : 0 < eps)
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    (hlevel : pg23DifferentialPositiveNormalizedScoreLevelNull typeLaw)
    (capacity : College -> ℝ)
    (P : AL16Cutoff College) (c : College) :
    IsClosed
      (pg23DifferentialNormalizedCapacityFeasibleCutoffsOn
        eps heps_pos.le typeLaw capacity P c) := by
  exact isClosed_le
    (pg23DifferentialNormalizedOwnAggregateDemand_continuous_lowerBound
      typeLaw hlevel eps heps_pos capacity P c)
    continuous_const

/-- Positive capacities make the positive-own-cutoff feasible set nonempty. -/
theorem pg23DifferentialNormalizedCapacityFeasibleCutoffsOn_nonempty {n : ℕ}
    (eps : ℝ) (heps_nonneg : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    (capacity : College -> ℝ)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (P : AL16Cutoff College) (c : College) :
    (pg23DifferentialNormalizedCapacityFeasibleCutoffsOn
      eps heps_nonneg typeLaw capacity P c).Nonempty := by
  refine ⟨⟨1, ⟨heps_le_one, le_rfl⟩⟩, ?_⟩
  change pg23DifferentialNormalizedSourceAggregateDemand typeLaw
      (al16SourceUpdateCutoff P c
        (pg23LowerBoundUnitCutoff eps heps_nonneg ⟨1, ⟨heps_le_one, le_rfl⟩⟩)) c ≤
    capacity c
  rw [pg23DifferentialNormalizedSourceAggregateDemand_eq_zero_of_cutoff_eq_one]
  · exact (hcapacity_pos c).le
  · simp [al16CutoffValue, al16SourceUpdateCutoff, pg23LowerBoundUnitCutoff]

/-- The least feasible own cutoff in a positive lower-bound interval. -/
noncomputable def pg23DifferentialNormalizedCapacityThresholdSubtype {n : ℕ}
    (eps : ℝ) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    (hlevel : pg23DifferentialPositiveNormalizedScoreLevelNull typeLaw)
    (capacity : College -> ℝ)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (P : AL16Cutoff College) (c : College) : Set.Icc eps 1 :=
  ((pg23DifferentialNormalizedCapacityFeasibleCutoffsOn_closed
      eps heps_pos typeLaw hlevel capacity P c).isCompact.exists_isLeast
    (pg23DifferentialNormalizedCapacityFeasibleCutoffsOn_nonempty
      eps heps_pos.le heps_le_one typeLaw capacity hcapacity_pos P c)).choose

/-- The least feasible own cutoff, viewed in the ambient bounded cutoff carrier. -/
noncomputable def pg23DifferentialNormalizedCapacityThresholdOn {n : ℕ}
    (eps : ℝ) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    (hlevel : pg23DifferentialPositiveNormalizedScoreLevelNull typeLaw)
    (capacity : College -> ℝ)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (P : AL16Cutoff College) (c : College) : Set.Icc (0 : ℝ) 1 :=
  pg23LowerBoundUnitCutoff eps heps_pos.le
    (pg23DifferentialNormalizedCapacityThresholdSubtype
      eps heps_pos heps_le_one typeLaw hlevel capacity hcapacity_pos P c)

/-- The threshold subtype is least among feasible own cutoffs on `[eps, 1]`. -/
theorem pg23DifferentialNormalizedCapacityThresholdSubtype_isLeast {n : ℕ}
    (eps : ℝ) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    (hlevel : pg23DifferentialPositiveNormalizedScoreLevelNull typeLaw)
    (capacity : College -> ℝ)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (P : AL16Cutoff College) (c : College) :
    IsLeast
      (pg23DifferentialNormalizedCapacityFeasibleCutoffsOn
        eps heps_pos.le typeLaw capacity P c)
      (pg23DifferentialNormalizedCapacityThresholdSubtype
        eps heps_pos heps_le_one typeLaw hlevel capacity hcapacity_pos P c) := by
  simpa [pg23DifferentialNormalizedCapacityThresholdSubtype] using
    ((pg23DifferentialNormalizedCapacityFeasibleCutoffsOn_closed
        eps heps_pos typeLaw hlevel capacity P c).isCompact.exists_isLeast
      (pg23DifferentialNormalizedCapacityFeasibleCutoffsOn_nonempty
        eps heps_pos.le heps_le_one typeLaw capacity hcapacity_pos P c)).choose_spec

/-- The least feasible own threshold is weakly capacity feasible. -/
theorem pg23DifferentialNormalizedCapacityThresholdOn_feasible {n : ℕ}
    (eps : ℝ) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    (hlevel : pg23DifferentialPositiveNormalizedScoreLevelNull typeLaw)
    (capacity : College -> ℝ)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (P : AL16Cutoff College) (c : College) :
    pg23DifferentialNormalizedSourceAggregateDemand typeLaw
      (al16SourceUpdateCutoff P c
        (pg23DifferentialNormalizedCapacityThresholdOn
          eps heps_pos heps_le_one typeLaw hlevel capacity hcapacity_pos P c)) c ≤
      capacity c := by
  have hleast :=
    pg23DifferentialNormalizedCapacityThresholdSubtype_isLeast
      eps heps_pos heps_le_one typeLaw hlevel capacity hcapacity_pos P c
  simpa [pg23DifferentialNormalizedCapacityFeasibleCutoffsOn,
    pg23DifferentialNormalizedCapacityThresholdOn] using hleast.1

/--
If the least feasible threshold is not the lower endpoint of the compact
interval, then it fills capacity exactly.
-/
theorem pg23DifferentialNormalizedCapacityThresholdOn_eq_capacity_of_lowerEndpoint_lt
    {n : ℕ}
    (eps : ℝ) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    (hlevel : pg23DifferentialPositiveNormalizedScoreLevelNull typeLaw)
    (capacity : College -> ℝ)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (P : AL16Cutoff College) (c : College)
    (hlower_lt :
      eps <
        (pg23DifferentialNormalizedCapacityThresholdSubtype
          eps heps_pos heps_le_one typeLaw hlevel capacity hcapacity_pos P c : ℝ)) :
    pg23DifferentialNormalizedSourceAggregateDemand typeLaw
      (al16SourceUpdateCutoff P c
        (pg23DifferentialNormalizedCapacityThresholdOn
          eps heps_pos heps_le_one typeLaw hlevel capacity hcapacity_pos P c)) c =
      capacity c := by
  let f : Set.Icc eps 1 -> ℝ :=
    fun x => pg23DifferentialNormalizedSourceAggregateDemand typeLaw
      (al16SourceUpdateCutoff P c
        (pg23LowerBoundUnitCutoff eps heps_pos.le x)) c
  have hf : Continuous f :=
    pg23DifferentialNormalizedOwnAggregateDemand_continuous_lowerBound
      typeLaw hlevel eps heps_pos capacity P c
  have hfeasible : f
      (pg23DifferentialNormalizedCapacityThresholdSubtype
        eps heps_pos heps_le_one typeLaw hlevel capacity hcapacity_pos P c) ≤
      capacity c := by
    have hleast :=
      pg23DifferentialNormalizedCapacityThresholdSubtype_isLeast
        eps heps_pos heps_le_one typeLaw hlevel capacity hcapacity_pos P c
    simpa [f, pg23DifferentialNormalizedCapacityFeasibleCutoffsOn] using hleast.1
  apply le_antisymm
  · simpa [f, pg23DifferentialNormalizedCapacityThresholdOn] using hfeasible
  · apply le_of_not_gt
    intro hlt
    have hopen : IsOpen {x : Set.Icc eps 1 | f x < capacity c} :=
      isOpen_lt hf continuous_const
    have hnotmin :
        ¬ IsMin
          (pg23DifferentialNormalizedCapacityThresholdSubtype
            eps heps_pos heps_le_one typeLaw hlevel capacity hcapacity_pos P c) := by
      intro hmin
      let t : Set.Icc eps 1 :=
        pg23DifferentialNormalizedCapacityThresholdSubtype
          eps heps_pos heps_le_one typeLaw hlevel capacity hcapacity_pos P c
      let y : Set.Icc eps 1 :=
        ⟨(eps + (t : ℝ)) / 2, by
          constructor
          · linarith [hlower_lt]
          · exact le_trans (by nlinarith [hlower_lt]) t.property.2⟩
      have hylt : y < t := by
        change (eps + (t : ℝ)) / 2 < (t : ℝ)
        linarith [hlower_lt]
      exact (not_lt_of_ge (hmin (le_of_lt hylt))) hylt
    obtain ⟨x, hxopen, hxlt⟩ :=
      nonempty_nhds_inter_Iio (hopen.mem_nhds hlt) hnotmin
    have hxfeasible :
        x ∈ pg23DifferentialNormalizedCapacityFeasibleCutoffsOn
          eps heps_pos.le typeLaw capacity P c := by
      change f x ≤ capacity c
      exact le_of_lt hxopen
    have hleast :=
      pg23DifferentialNormalizedCapacityThresholdSubtype_isLeast
        eps heps_pos heps_le_one typeLaw hlevel capacity hcapacity_pos P c
    exact (not_lt_of_ge (hleast.2 hxfeasible)) hxlt

/--
Positive-target closure of bounded differential normalized clearing.  This is
the closure statement that remains valid for the differential sentinel model:
the limiting cutoff must be known to stay strictly above `0`.
-/
theorem pg23DifferentialNormalizedMarketClearing_of_positive_coordinatewise_limit
    {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    (hlevel : pg23DifferentialPositiveNormalizedScoreLevelNull typeLaw)
    (capacity : College -> ℝ)
    (Pseq : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College)
    (hQpos : ∀ c : College, 0 < al16CutoffValue Q c)
    (hclear :
      ∀ m : ℕ,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw)
          capacity (Pseq m))
    (hlim : al16CoordinatewiseTendsto Pseq Q) :
    al16SourceMarketClearing
      (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity Q := by
  constructor
  · intro c
    apply le_of_tendsto
      (pg23DifferentialNormalizedAggregateDemand_tendsto_of_positive_coordinatewiseTendsto
        typeLaw hlevel Pseq Q hQpos hlim c)
    exact Filter.Eventually.of_forall fun m => (hclear m).1 c
  · intro c _hc
    have hPpos : ∀ᶠ m in atTop, 0 < al16CutoffValue (Pseq m) c :=
      (tendsto_order.1 (hlim c)).1 0 (hQpos c)
    have hDemandEq : ∀ᶠ m in atTop,
        pg23DifferentialNormalizedSourceAggregateDemand typeLaw (Pseq m) c =
          capacity c :=
      hPpos.mono fun m hm => (hclear m).2 c hm
    apply tendsto_nhds_unique
      (pg23DifferentialNormalizedAggregateDemand_tendsto_of_positive_coordinatewiseTendsto
        typeLaw hlevel Pseq Q hQpos hlim c)
    exact tendsto_const_nhds.congr' (hDemandEq.mono fun _ hm => hm.symm)

/--
Sequential closedness of bounded normalized clearing for differential product
laws.  The proof first derives a positive coordinatewise lower bound for every
clearing cutoff, so the limit lies in the positive region where demand
continuity is available.
-/
theorem pg23DifferentialNormalizedMarketClearing_of_product_coordinatewise_limit_of_raw
    {n : ℕ} [Nonempty College]
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (hbase_level : pg23SourceScoreLevelNull baseLaw)
    (htop : ∀ c : College,
      baseLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (S : ℝ) (hSlt : S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ))
    (Pseq : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College)
    (hclear :
      ∀ m : ℕ,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand
            (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
          capacity (Pseq m))
    (hlim : al16CoordinatewiseTendsto Pseq Q) :
    al16SourceMarketClearing
      (pg23DifferentialNormalizedSourceAggregateDemand
        (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
      capacity Q := by
  let typeLaw :=
    pg23DifferentialTypeLaw (College := College) accessLaw baseLaw
  letI : IsProbabilityMeasure typeLaw :=
    pg23DifferentialTypeLaw_isProbabilityMeasure accessLaw baseLaw
  have hlevel :
      pg23DifferentialPositiveNormalizedScoreLevelNull typeLaw :=
    pg23DifferentialPositiveNormalizedScoreLevelNull_of_raw accessLaw baseLaw
      hbase_level
  have hQpos : ∀ c : College, 0 < al16CutoffValue Q c := by
    intro c
    rcases pg23DifferentialNormalizedMarketClearing_cutoff_uniform_pos_of_base
        accessLaw baseLaw htop S hSlt capacity hcapacity c with
      ⟨eps, heps_pos, heps_le⟩
    have heps_le_Q : eps ≤ al16CutoffValue Q c :=
      ge_of_tendsto (hlim c)
        (Filter.Eventually.of_forall fun m => heps_le (Pseq m) (hclear m))
    exact lt_of_lt_of_le heps_pos heps_le_Q
  exact pg23DifferentialNormalizedMarketClearing_of_positive_coordinatewise_limit
    typeLaw hlevel capacity Pseq Q hQpos hclear hlim

/--
For differential product laws, raw score-level nullity plus the top-rank/equal
capacity gap is enough to recover the bounded normalized clearing lattice.  This
uses local closedness rather than false global continuity at the inactive
sentinel.
-/
theorem pg23DifferentialNormalizedMarketClearing_completeLattice_of_product_raw
    {n : ℕ} [Nonempty College]
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (hbase_level : pg23SourceScoreLevelNull baseLaw)
    (htop : ∀ c : College,
      baseLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (S : ℝ) (hSlt : S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ))
    (hnonempty : ∃ P : AL16Cutoff College,
      al16SourceMarketClearing
        (pg23DifferentialNormalizedSourceAggregateDemand
          (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
        capacity P) :
    CompleteLatticeOn
      (al16SourceMarketClearing
        (pg23DifferentialNormalizedSourceAggregateDemand
          (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
        capacity)
      al16CutoffLe := by
  let typeLaw :=
    pg23DifferentialTypeLaw (College := College) accessLaw baseLaw
  letI : IsProbabilityMeasure typeLaw :=
    pg23DifferentialTypeLaw_isProbabilityMeasure accessLaw baseLaw
  apply
    al16SourceMarketClearing_completeLattice_of_probability_measure_ranked_choice_primitives_of_limit_closed
      (mu := typeLaw)
      (demand := pg23DifferentialNormalizedSourceAggregateDemand typeLaw)
      (outside := pg23DifferentialNormalizedOutsideDemand typeLaw)
      (capacity := capacity)
      (score := pg23DifferentialNormalizedScore (College := College))
      (rank := pg23DifferentialSourceRank)
  · intro Q c
    rfl
  · intro Q
    rfl
  · exact pg23DifferentialNormalizedScore_measurable
  · exact pg23DifferentialSourceRank_measurable
  · exact pg23DifferentialSourceRank_injective
  · intro Pseq Q hclear hlim
    exact pg23DifferentialNormalizedMarketClearing_of_product_coordinatewise_limit_of_raw
      accessLaw baseLaw hbase_level htop S hSlt capacity hcapacity
      Pseq Q hclear hlim
  · exact hnonempty

/--
For differential product laws with `0 < S < 1`, the bounded normalized clearing
set is nonempty.  The proof builds the paper-specific least feasible own-cutoff
operator above a positive sentinel lower bound and applies the generic
Knaster--Tarski best-response shell.
-/
theorem pg23DifferentialNormalizedMarketClearing_nonempty_of_product_raw
    {n : ℕ} [Nonempty College]
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (hbase_level : pg23SourceScoreLevelNull baseLaw)
    (htop : ∀ c : College,
      baseLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (S : ℝ) (hSpos : 0 < S) (hSlt : S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ)) :
    ∃ Q : AL16Cutoff College,
      al16SourceMarketClearing
        (pg23DifferentialNormalizedSourceAggregateDemand
          (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
        capacity Q := by
  let typeLaw :=
    pg23DifferentialTypeLaw (College := College) accessLaw baseLaw
  letI : IsProbabilityMeasure typeLaw :=
    pg23DifferentialTypeLaw_isProbabilityMeasure accessLaw baseLaw
  have hlevel : pg23DifferentialPositiveNormalizedScoreLevelNull typeLaw :=
    pg23DifferentialPositiveNormalizedScoreLevelNull_of_raw accessLaw baseLaw
      hbase_level
  have hcardpos : (0 : ℝ) < Fintype.card College := by
    exact_mod_cast Fintype.card_pos
  have hcapacity_pos : ∀ c : College, 0 < capacity c := by
    intro c
    rw [hcapacity c]
    exact div_pos hSpos hcardpos
  have hown_lower : ∀ c : College,
      ∃ eps : ℝ, 0 < eps ∧
        ∀ (P : AL16Cutoff College) (x : Set.Icc (0 : ℝ) 1),
          pg23DifferentialNormalizedSourceAggregateDemand typeLaw
              (al16SourceUpdateCutoff P c x) c ≤ capacity c ->
          eps ≤ (x : ℝ) := by
    intro c
    exact pg23DifferentialNormalizedOwnCutoff_uniform_pos_of_base
      accessLaw baseLaw htop S hSlt capacity hcapacity c
  let lower : College -> ℝ := fun c => (hown_lower c).choose
  have hlower_pos : ∀ c : College, 0 < lower c := by
    intro c
    exact (hown_lower c).choose_spec.1
  have hlower_feasible : ∀ c : College, ∀ (P : AL16Cutoff College)
      (x : Set.Icc (0 : ℝ) 1),
      pg23DifferentialNormalizedSourceAggregateDemand typeLaw
          (al16SourceUpdateCutoff P c x) c ≤ capacity c ->
      lower c ≤ (x : ℝ) := by
    intro c
    exact (hown_lower c).choose_spec.2
  let zeroCutoff : AL16Cutoff College :=
    fun _ => (0 : Set.Icc (0 : ℝ) 1)
  have hlower_le_one : ∀ c : College, lower c ≤ 1 := by
    intro c
    apply hlower_feasible c zeroCutoff (1 : Set.Icc (0 : ℝ) 1)
    change pg23DifferentialNormalizedSourceAggregateDemand typeLaw
        (al16SourceUpdateCutoff zeroCutoff c (1 : Set.Icc (0 : ℝ) 1)) c ≤
      capacity c
    rw [pg23DifferentialNormalizedSourceAggregateDemand_eq_zero_of_cutoff_eq_one]
    · exact (hcapacity_pos c).le
    · simp [al16CutoffValue, al16SourceUpdateCutoff]
  have heps_pos : ∀ c : College, 0 < lower c / 2 := by
    intro c
    linarith [hlower_pos c]
  have heps_le_one : ∀ c : College, lower c / 2 ≤ 1 := by
    intro c
    linarith [hlower_le_one c]
  let threshold : AL16Cutoff College -> College -> Set.Icc (0 : ℝ) 1 :=
    fun P c =>
      pg23DifferentialNormalizedCapacityThresholdOn
        (lower c / 2) (heps_pos c) (heps_le_one c)
        typeLaw hlevel capacity hcapacity_pos P c
  apply al16SourceMarketClearing_nonempty_of_capacity_threshold_primitives
    (demand := pg23DifferentialNormalizedSourceAggregateDemand typeLaw)
    (capacity := capacity)
    (threshold := threshold)
  · intro P Q hPQ c
    dsimp [threshold]
    have hleast :=
      pg23DifferentialNormalizedCapacityThresholdSubtype_isLeast
        (lower c / 2) (heps_pos c) (heps_le_one c)
        typeLaw hlevel capacity hcapacity_pos P c
    change
      (pg23DifferentialNormalizedCapacityThresholdSubtype
        (lower c / 2) (heps_pos c) (heps_le_one c)
        typeLaw hlevel capacity hcapacity_pos P c : ℝ) ≤
      (pg23DifferentialNormalizedCapacityThresholdSubtype
        (lower c / 2) (heps_pos c) (heps_le_one c)
        typeLaw hlevel capacity hcapacity_pos Q c : ℝ)
    apply hleast.2
    change pg23DifferentialNormalizedSourceAggregateDemand typeLaw
        (al16SourceUpdateCutoff P c
          (pg23DifferentialNormalizedCapacityThresholdOn
            (lower c / 2) (heps_pos c) (heps_le_one c)
            typeLaw hlevel capacity hcapacity_pos Q c)) c ≤
      capacity c
    have hQfeasible :
        pg23DifferentialNormalizedSourceAggregateDemand typeLaw
          (al16SourceUpdateCutoff Q c
            (threshold Q c)) c ≤ capacity c := by
      simpa [threshold] using
        pg23DifferentialNormalizedCapacityThresholdOn_feasible
          (lower c / 2) (heps_pos c) (heps_le_one c)
          typeLaw hlevel capacity hcapacity_pos Q c
    have hupdate :
        al16SourceUpdateCutoff P c (threshold Q c) ≤
          al16SourceUpdateCutoff Q c (threshold Q c) :=
      al16SourceUpdateCutoff_le_of_le hPQ c (threshold Q c)
    have hcoordinate :
        al16CutoffValue (al16SourceUpdateCutoff P c (threshold Q c)) c =
          al16CutoffValue (al16SourceUpdateCutoff Q c (threshold Q c)) c := by
      simp [al16CutoffValue, al16SourceUpdateCutoff]
    exact
      (pg23DifferentialNormalizedAggregateDemand_le_of_le_same_coordinate
        typeLaw hupdate hcoordinate).trans hQfeasible
  · intro P c
    simpa [threshold] using
      pg23DifferentialNormalizedCapacityThresholdOn_feasible
        (lower c / 2) (heps_pos c) (heps_le_one c)
        typeLaw hlevel capacity hcapacity_pos P c
  · intro P c _hpos
    have hfeasible :
        pg23DifferentialNormalizedSourceAggregateDemand typeLaw
          (al16SourceUpdateCutoff P c (threshold P c)) c ≤ capacity c := by
      simpa [threshold] using
        pg23DifferentialNormalizedCapacityThresholdOn_feasible
          (lower c / 2) (heps_pos c) (heps_le_one c)
          typeLaw hlevel capacity hcapacity_pos P c
    have hthreshold_lower : lower c ≤ (threshold P c : ℝ) :=
      hlower_feasible c P (threshold P c) hfeasible
    have hlower_endpoint_lt :
        lower c / 2 <
          (pg23DifferentialNormalizedCapacityThresholdSubtype
            (lower c / 2) (heps_pos c) (heps_le_one c)
            typeLaw hlevel capacity hcapacity_pos P c : ℝ) := by
      have hhalf_lt : lower c / 2 < lower c := by
        linarith [hlower_pos c]
      have hlt_threshold :
          lower c / 2 < (threshold P c : ℝ) :=
        lt_of_lt_of_le hhalf_lt hthreshold_lower
      simpa [threshold, pg23DifferentialNormalizedCapacityThresholdOn] using
        hlt_threshold
    simpa [threshold] using
      pg23DifferentialNormalizedCapacityThresholdOn_eq_capacity_of_lowerEndpoint_lt
        (lower c / 2) (heps_pos c) (heps_le_one c)
        typeLaw hlevel capacity hcapacity_pos P c hlower_endpoint_lt

/--
Least and greatest bounded normalized differential clearing cutoffs are
coordinate-constant when a complete lattice and relabeling symmetry are already
available.
-/
theorem pg23DifferentialNormalizedMarketClearing_extremaConstant_of_completeLattice
    {n : ℕ} [Nonempty College]
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    (capacity : College -> ℝ)
    (hlaw :
      ∀ sigma : Equiv.Perm College,
        Measure.map
          (pg23DifferentialRelabelApplicant (College := College) (n := n) sigma)
          typeLaw = typeLaw)
    (hcapacity :
      ∀ sigma : Equiv.Perm College, ∀ c : College,
        capacity (sigma c) = capacity c)
    (L :
      CompleteLatticeOn
        (al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity)
        al16CutoffLe)
    (hnonempty :
      ∃ Q : AL16Cutoff College,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity Q) :
    ∃ bot top : AL16Cutoff College,
      al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity bot ∧
      (∀ Q : AL16Cutoff College,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity Q ->
        al16CutoffLe bot Q) ∧
      al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity top ∧
      (∀ Q : AL16Cutoff College,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity Q ->
        al16CutoffLe Q top) ∧
      (∃ qbot : ℝ, ∀ c : College, al16CutoffValue bot c = qbot) ∧
      (∃ qtop : ℝ, ∀ c : College, al16CutoffValue top c = qtop) := by
  rcases L.exists_least hnonempty with ⟨bot, hbot⟩
  rcases L.exists_greatest hnonempty with ⟨top, htop⟩
  refine ⟨bot, top, hbot.1, hbot.2, htop.1, htop.2, ?_, ?_⟩
  · exact pg23DifferentialNormalizedMarketClearing_least_constant_of_typeLaw_relabel
      typeLaw capacity hlaw hcapacity bot hbot
  · exact pg23DifferentialNormalizedMarketClearing_greatest_constant_of_typeLaw_relabel
      typeLaw capacity hlaw hcapacity top htop

/--
For differential product laws, the local-closedness lattice plus relabeling
symmetry gives coordinate-constant least and greatest bounded normalized
clearing cutoffs without a global continuity premise or an externally supplied
nonempty-clearing witness.
-/
theorem pg23DifferentialNormalizedMarketClearing_extremaConstant_of_product_raw
    {n : ℕ} [Nonempty College]
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (hbase_level : pg23SourceScoreLevelNull baseLaw)
    (htop : ∀ c : College,
      baseLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (hbase_relabel :
      ∀ sigma : Equiv.Perm College,
        Measure.map (pg23RelabelApplicant (College := College) sigma) baseLaw =
          baseLaw)
    (S : ℝ) (hSpos : 0 < S) (hSlt : S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ)) :
    ∃ bot top : AL16Cutoff College,
      al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand
            (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
          capacity bot ∧
      (∀ Q : AL16Cutoff College,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand
            (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
          capacity Q ->
        al16CutoffLe bot Q) ∧
      al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand
            (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
          capacity top ∧
      (∀ Q : AL16Cutoff College,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand
            (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
          capacity Q ->
        al16CutoffLe Q top) ∧
      (∃ qbot : ℝ, ∀ c : College, al16CutoffValue bot c = qbot) ∧
      (∃ qtop : ℝ, ∀ c : College, al16CutoffValue top c = qtop) := by
  let typeLaw :=
    pg23DifferentialTypeLaw (College := College) accessLaw baseLaw
  letI : IsProbabilityMeasure typeLaw :=
    pg23DifferentialTypeLaw_isProbabilityMeasure accessLaw baseLaw
  have hlaw : ∀ sigma : Equiv.Perm College,
      Measure.map
        (pg23DifferentialRelabelApplicant (College := College) (n := n) sigma)
        typeLaw = typeLaw := by
    intro sigma
    exact pg23DifferentialTypeLaw_relabel accessLaw baseLaw sigma
      (hbase_relabel sigma)
  have hcapacity_perm :
      ∀ sigma : Equiv.Perm College, ∀ c : College,
        capacity (sigma c) = capacity c := by
    intro sigma c
    rw [hcapacity (sigma c), hcapacity c]
  have hnonempty :
      ∃ Q : AL16Cutoff College,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw)
          capacity Q :=
    pg23DifferentialNormalizedMarketClearing_nonempty_of_product_raw
      accessLaw baseLaw hbase_level htop S hSpos hSlt capacity hcapacity
  have L :
      CompleteLatticeOn
        (al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity)
        al16CutoffLe :=
    pg23DifferentialNormalizedMarketClearing_completeLattice_of_product_raw
      accessLaw baseLaw hbase_level htop S hSlt capacity hcapacity hnonempty
  exact pg23DifferentialNormalizedMarketClearing_extremaConstant_of_completeLattice
    typeLaw capacity hlaw hcapacity_perm L hnonempty

/--
For differential product laws, the bounded normalized clearing witness transports
back to a finite raw exact-clearing cutoff.  The endpoint facts are derived from
the first-rank/equal-capacity gap and positive capacity.
-/
theorem pg23DifferentialSourceMarketClearing_nonempty_of_product_raw
    {n : ℕ} [Nonempty College]
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (hbase_level : pg23SourceScoreLevelNull baseLaw)
    (htop : ∀ c : College,
      baseLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (S : ℝ) (hSpos : 0 < S) (hSlt : S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ)) :
    ∃ P : College -> ℝ,
      pg23DifferentialSourceMarketClearing
        (pg23DifferentialSourceAggregateDemand
          (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
        capacity P := by
  let typeLaw :=
    pg23DifferentialTypeLaw (College := College) accessLaw baseLaw
  letI : IsProbabilityMeasure typeLaw :=
    pg23DifferentialTypeLaw_isProbabilityMeasure accessLaw baseLaw
  rcases pg23DifferentialNormalizedMarketClearing_nonempty_of_product_raw
      accessLaw baseLaw hbase_level htop S hSpos hSlt capacity hcapacity with
    ⟨Q, hQ⟩
  have hinterior :
      ∀ c : College, 0 < al16CutoffValue Q c ∧ al16CutoffValue Q c < 1 :=
    pg23DifferentialNormalizedMarketClearing_cutoff_interior_of_base
      accessLaw baseLaw htop S hSpos hSlt capacity hcapacity Q hQ
  exact ⟨pg23DenormalizedCutoff Q,
    pg23DifferentialSourceMarketClearing_of_normalized typeLaw capacity Q
      hinterior hQ⟩

/--
For differential product laws, relabeling symmetry gives a finite raw
exact-clearing cutoff with shared coordinates.
-/
theorem pg23DifferentialSourceMarketClearing_exists_constant_of_product_raw
    {n : ℕ} [Nonempty College]
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (hbase_level : pg23SourceScoreLevelNull baseLaw)
    (htop : ∀ c : College,
      baseLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (hbase_relabel :
      ∀ sigma : Equiv.Perm College,
        Measure.map (pg23RelabelApplicant (College := College) sigma) baseLaw =
          baseLaw)
    (S : ℝ) (hSpos : 0 < S) (hSlt : S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ)) :
    ∃ P : College -> ℝ,
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
          capacity P ∧
        ∃ p : ℝ, ∀ c : College, P c = p := by
  let typeLaw :=
    pg23DifferentialTypeLaw (College := College) accessLaw baseLaw
  letI : IsProbabilityMeasure typeLaw :=
    pg23DifferentialTypeLaw_isProbabilityMeasure accessLaw baseLaw
  rcases pg23DifferentialNormalizedMarketClearing_extremaConstant_of_product_raw
      accessLaw baseLaw hbase_level htop hbase_relabel S hSpos hSlt
      capacity hcapacity with
    ⟨bot, _top, hbot, _hbot_le, _htop, _htop_ge, hbot_const, _htop_const⟩
  have hinterior :
      ∀ c : College, 0 < al16CutoffValue bot c ∧ al16CutoffValue bot c < 1 :=
    pg23DifferentialNormalizedMarketClearing_cutoff_interior_of_base
      accessLaw baseLaw htop S hSpos hSlt capacity hcapacity bot hbot
  rcases hbot_const with ⟨qbot, hqbot⟩
  refine ⟨pg23DenormalizedCutoff bot,
    pg23DifferentialSourceMarketClearing_of_normalized typeLaw capacity bot
      hinterior hbot,
    pg23ScoreDenormalize qbot, ?_⟩
  intro c
  unfold pg23DenormalizedCutoff
  exact congrArg pg23ScoreDenormalize (hqbot c)

/--
For differential product laws, uniqueness of the one-dimensional common-cutoff
clearing equation upgrades the normalized lattice/extrema argument to uniqueness
of every finite raw exact-clearing vector.
-/
theorem pg23DifferentialSourceMarketClearing_unique_of_product_raw_scalar_unique
    {n : ℕ} [Nonempty College]
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (hbase_level : pg23SourceScoreLevelNull baseLaw)
    (htop : ∀ c : College,
      baseLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (hbase_relabel :
      ∀ sigma : Equiv.Perm College,
        Measure.map (pg23RelabelApplicant (College := College) sigma) baseLaw =
          baseLaw)
    (S : ℝ) (hSpos : 0 < S) (hSlt : S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ))
    (hcommon_unique :
      ∀ p q : ℝ,
        pg23DifferentialSourceMarketClearing
            (pg23DifferentialSourceAggregateDemand
              (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
            capacity (fun _ : College => p) ->
        pg23DifferentialSourceMarketClearing
            (pg23DifferentialSourceAggregateDemand
              (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
            capacity (fun _ : College => q) ->
          p = q) :
    ∀ P Q : College -> ℝ,
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
          capacity P ->
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
          capacity Q ->
        P = Q := by
  let typeLaw :=
    pg23DifferentialTypeLaw (College := College) accessLaw baseLaw
  letI : IsProbabilityMeasure typeLaw :=
    pg23DifferentialTypeLaw_isProbabilityMeasure accessLaw baseLaw
  have hnonempty :
      ∃ Q : AL16Cutoff College,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity Q :=
    pg23DifferentialNormalizedMarketClearing_nonempty_of_product_raw
      accessLaw baseLaw hbase_level htop S hSpos hSlt capacity hcapacity
  have L :
      CompleteLatticeOn
        (al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity)
        al16CutoffLe :=
    pg23DifferentialNormalizedMarketClearing_completeLattice_of_product_raw
      accessLaw baseLaw hbase_level htop S hSlt capacity hcapacity hnonempty
  rcases pg23DifferentialNormalizedMarketClearing_extremaConstant_of_product_raw
      accessLaw baseLaw hbase_level htop hbase_relabel S hSpos hSlt
      capacity hcapacity with
    ⟨bot, top, hbot, hbot_le, htop_clear, htop_ge, hbot_const, htop_const⟩
  have hbot_interior :
      ∀ c : College, 0 < al16CutoffValue bot c ∧ al16CutoffValue bot c < 1 :=
    pg23DifferentialNormalizedMarketClearing_cutoff_interior_of_base
      accessLaw baseLaw htop S hSpos hSlt capacity hcapacity bot hbot
  have htop_interior :
      ∀ c : College, 0 < al16CutoffValue top c ∧ al16CutoffValue top c < 1 :=
    pg23DifferentialNormalizedMarketClearing_cutoff_interior_of_base
      accessLaw baseLaw htop S hSpos hSlt capacity hcapacity top htop_clear
  rcases hbot_const with ⟨qbot, hqbot⟩
  rcases htop_const with ⟨qtop, hqtop⟩
  have hbot_denormalized : pg23DenormalizedCutoff bot =
      fun _ : College => pg23ScoreDenormalize qbot := by
    funext c
    unfold pg23DenormalizedCutoff
    exact congrArg pg23ScoreDenormalize (hqbot c)
  have htop_denormalized : pg23DenormalizedCutoff top =
      fun _ : College => pg23ScoreDenormalize qtop := by
    funext c
    unfold pg23DenormalizedCutoff
    exact congrArg pg23ScoreDenormalize (hqtop c)
  have hbot_raw :
      pg23DifferentialSourceMarketClearing
        (pg23DifferentialSourceAggregateDemand typeLaw) capacity
        (fun _ : College => pg23ScoreDenormalize qbot) := by
    have hraw :=
      pg23DifferentialSourceMarketClearing_of_normalized typeLaw capacity bot
        hbot_interior hbot
    rwa [hbot_denormalized] at hraw
  have htop_raw :
      pg23DifferentialSourceMarketClearing
        (pg23DifferentialSourceAggregateDemand typeLaw) capacity
        (fun _ : College => pg23ScoreDenormalize qtop) := by
    have hraw :=
      pg23DifferentialSourceMarketClearing_of_normalized typeLaw capacity top
        htop_interior htop_clear
    rwa [htop_denormalized] at hraw
  have hraw_value_eq :
      pg23ScoreDenormalize qbot = pg23ScoreDenormalize qtop :=
    hcommon_unique (pg23ScoreDenormalize qbot) (pg23ScoreDenormalize qtop)
      hbot_raw htop_raw
  have hraw_cutoff_eq : pg23DenormalizedCutoff bot =
      pg23DenormalizedCutoff top := by
    rw [hbot_denormalized, htop_denormalized, hraw_value_eq]
  have hbot_top : bot = top := by
    calc
      bot = pg23NormalizedCutoff (pg23DenormalizedCutoff bot) :=
        (pg23NormalizedCutoff_denormalized_eq bot hbot_interior).symm
      _ = pg23NormalizedCutoff (pg23DenormalizedCutoff top) := by
        rw [hraw_cutoff_eq]
      _ = top := pg23NormalizedCutoff_denormalized_eq top htop_interior
  have hnormalized_unique :
      ∀ Q R : AL16Cutoff College,
        al16SourceMarketClearing
            (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity Q ->
        al16SourceMarketClearing
            (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity R ->
          Q = R :=
    L.unique_of_least_greatest_eq
      ⟨hbot, hbot_le⟩ ⟨htop_clear, htop_ge⟩ hbot_top
  intro P Q hP hQ
  have hP_norm :
      al16SourceMarketClearing
        (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity
        (pg23NormalizedCutoff P) :=
    pg23DifferentialNormalizedMarketClearing_of_raw typeLaw capacity P hP
  have hQ_norm :
      al16SourceMarketClearing
        (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity
        (pg23NormalizedCutoff Q) :=
    pg23DifferentialNormalizedMarketClearing_of_raw typeLaw capacity Q hQ
  have hnorm :
      pg23NormalizedCutoff P = pg23NormalizedCutoff Q :=
    hnormalized_unique (pg23NormalizedCutoff P) (pg23NormalizedCutoff Q)
      hP_norm hQ_norm
  funext c
  exact pg23ScoreNormalize_strictMono.injective (congrFun hnorm c)

/--
With a visible nonempty-clearing witness and visible demand-continuity premise,
the bounded normalized differential-access clearing set has least and greatest
cutoffs, and relabeling symmetry forces both extrema to be coordinate-constant.
-/
theorem pg23DifferentialNormalizedMarketClearing_extremaConstant_of_lattice_primitives
    {n : ℕ} [Nonempty College]
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    (capacity : College -> ℝ)
    (hlaw :
      ∀ sigma : Equiv.Perm College,
        Measure.map
          (pg23DifferentialRelabelApplicant (College := College) (n := n) sigma)
          typeLaw = typeLaw)
    (hcapacity :
      ∀ sigma : Equiv.Perm College, ∀ c : College,
        capacity (sigma c) = capacity c)
    (hdemand_continuous :
      ∀ (Pseq : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College),
        al16CoordinatewiseTendsto Pseq Q ->
          ∀ c : College,
            Tendsto
              (fun m => pg23DifferentialNormalizedSourceAggregateDemand typeLaw
                (Pseq m) c)
              atTop
              (nhds (pg23DifferentialNormalizedSourceAggregateDemand typeLaw Q c)))
    (hnonempty :
      ∃ Q : AL16Cutoff College,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity Q) :
    ∃ bot top : AL16Cutoff College,
      al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity bot ∧
      (∀ Q : AL16Cutoff College,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity Q ->
        al16CutoffLe bot Q) ∧
      al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity top ∧
      (∀ Q : AL16Cutoff College,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity Q ->
        al16CutoffLe Q top) ∧
      (∃ qbot : ℝ, ∀ c : College, al16CutoffValue bot c = qbot) ∧
      (∃ qtop : ℝ, ∀ c : College, al16CutoffValue top c = qtop) := by
  let valid : AL16Cutoff College -> Prop :=
    al16SourceMarketClearing
      (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity
  let L : CompleteLatticeOn valid al16CutoffLe :=
    pg23DifferentialNormalizedMarketClearing_completeLattice_of_continuity
      typeLaw capacity hdemand_continuous hnonempty
  rcases L.exists_least hnonempty with ⟨bot, hbot⟩
  rcases L.exists_greatest hnonempty with ⟨top, htop⟩
  refine ⟨bot, top, hbot.1, hbot.2, htop.1, htop.2, ?_, ?_⟩
  · exact pg23DifferentialNormalizedMarketClearing_least_constant_of_typeLaw_relabel
      typeLaw capacity hlaw hcapacity bot hbot
  · exact pg23DifferentialNormalizedMarketClearing_greatest_constant_of_typeLaw_relabel
      typeLaw capacity hlaw hcapacity top htop

/-- Differential top-k choice is equivariant under simultaneous relabeling. -/
theorem pg23DifferentialSourceChoice_relabel {n : ℕ}
    (sigma : Equiv.Perm College) (P : College -> ℝ)
    (theta : PG23DifferentialApplicantType College n) :
    pg23DifferentialSourceChoice (pg23RelabelCutoff sigma P)
        (pg23DifferentialRelabelApplicant sigma theta) =
      Option.map sigma (pg23DifferentialSourceChoice P theta) := by
  change
    pg23ActiveSourceChoice
        (pg23TopKApplicationSet (theta.1.val + 1)
          (pg23RelabelRanking sigma theta.2.1))
        (pg23RelabelCutoff sigma P) (pg23RelabelApplicant sigma theta.2) =
      Option.map sigma
        (pg23ActiveSourceChoice
          (pg23TopKApplicationSet (theta.1.val + 1) theta.2.1) P theta.2)
  rw [pg23TopKApplicationSet_relabel]
  exact
    pg23ActiveSourceChoice_relabel sigma
      (pg23TopKApplicationSet (theta.1.val + 1) theta.2.1) P theta.2

/-- Differential top-k choice fibers are measurable. -/
theorem pg23DifferentialSourceChoice_fiber_measurable {n : ℕ}
    (P : College -> ℝ) (c : College) :
    MeasurableSet
      {theta : PG23DifferentialApplicantType College n |
        pg23DifferentialSourceChoice P theta = some c} := by
  classical
  have hslice : ∀ k : Fin n,
      MeasurableSet
        {theta : PG23DifferentialApplicantType College n |
          theta.1 = k ∧
            pg23ActiveSourceChoice
              (pg23TopKApplicationSet (k.val + 1) theta.2.1) P theta.2 = some c} := by
    intro k
    have hfst :
        MeasurableSet
          {theta : PG23DifferentialApplicantType College n | theta.1 = k} := by
      change MeasurableSet
        ((fun theta : PG23DifferentialApplicantType College n => theta.1) ⁻¹'
          ({k} : Set (Fin n)))
      exact MeasurableSet.preimage (MeasurableSet.singleton k) measurable_fst
    have hchoice :
        MeasurableSet
          {theta : PG23DifferentialApplicantType College n |
            pg23ActiveSourceChoice
              (pg23TopKApplicationSet (k.val + 1) theta.2.1) P theta.2 = some c} := by
      change MeasurableSet
        ((fun theta : PG23DifferentialApplicantType College n => theta.2) ⁻¹'
          {eta : PG23ApplicantType College |
            pg23ActiveSourceChoice
              (pg23TopKApplicationSet (k.val + 1) eta.1) P eta = some c})
      exact MeasurableSet.preimage
        (pg23TopKActiveSourceChoice_fiber_measurable
          (College := College) (k.val + 1) P c)
        measurable_snd
    exact hfst.inter hchoice
  have htarget :
      {theta : PG23DifferentialApplicantType College n |
        pg23DifferentialSourceChoice P theta = some c} =
        ⋃ k : Fin n,
          {theta : PG23DifferentialApplicantType College n |
            theta.1 = k ∧
              pg23ActiveSourceChoice
                (pg23TopKApplicationSet (k.val + 1) theta.2.1) P theta.2 = some c} := by
    ext theta
    constructor
    · intro hchoice
      refine Set.mem_iUnion.mpr ⟨theta.1, ?_⟩
      constructor
      · rfl
      · change pg23DifferentialSourceChoice P theta = some c at hchoice
        simpa [pg23DifferentialSourceChoice, pg23DifferentialActiveSet] using hchoice
    · intro hchoice
      rcases Set.mem_iUnion.mp hchoice with ⟨k, hk⟩
      rcases hk with ⟨hfirst, hchoice'⟩
      subst k
      simpa [pg23DifferentialSourceChoice, pg23DifferentialActiveSet] using hchoice'
  rw [htarget]
  exact MeasurableSet.iUnion hslice

/--
Relabeling an invariant differential-access type law transports differential
aggregate demand.
-/
theorem pg23DifferentialSourceAggregateDemand_relabel_of_typeLaw_relabel {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    (sigma : Equiv.Perm College) (P : College -> ℝ) (c : College)
    (hlaw :
      Measure.map (pg23DifferentialRelabelApplicant (College := College) (n := n) sigma)
        typeLaw = typeLaw) :
    pg23DifferentialSourceAggregateDemand typeLaw
        (pg23RelabelCutoff sigma P) (sigma c) =
      pg23DifferentialSourceAggregateDemand typeLaw P c := by
  unfold pg23DifferentialSourceAggregateDemand
  calc
    typeLaw.real {theta : PG23DifferentialApplicantType College n |
        pg23DifferentialSourceChoice (pg23RelabelCutoff sigma P) theta =
          some (sigma c)} =
        (Measure.map
          (pg23DifferentialRelabelApplicant (College := College) (n := n) sigma)
          typeLaw).real {theta : PG23DifferentialApplicantType College n |
            pg23DifferentialSourceChoice (pg23RelabelCutoff sigma P) theta =
              some (sigma c)} := by
      rw [hlaw]
    _ = typeLaw.real
          ((pg23DifferentialRelabelApplicant (College := College) (n := n) sigma) ⁻¹'
            {theta : PG23DifferentialApplicantType College n |
              pg23DifferentialSourceChoice (pg23RelabelCutoff sigma P) theta =
                some (sigma c)}) :=
      map_measureReal_apply
        (pg23DifferentialRelabelApplicant_measurable
          (College := College) (n := n) sigma)
        (pg23DifferentialSourceChoice_fiber_measurable
          (College := College) (pg23RelabelCutoff sigma P) (sigma c))
    _ = typeLaw.real {theta : PG23DifferentialApplicantType College n |
          pg23DifferentialSourceChoice P theta = some c} := by
      congr 1
      ext theta
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rw [pg23DifferentialSourceChoice_relabel]
      constructor
      · intro h
        exact Option.map_injective sigma.injective h
      · intro h
        simp [h]

/--
Under type-law and capacity invariance, a differential-access exact-clearing
cutoff remains exact clearing after relabeling colleges.
-/
theorem pg23DifferentialSourceMarketClearing_relabel_of_typeLaw_relabel {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    (capacity : College -> ℝ)
    (sigma : Equiv.Perm College) (P : College -> ℝ)
    (hlaw :
      Measure.map (pg23DifferentialRelabelApplicant (College := College) (n := n) sigma)
        typeLaw = typeLaw)
    (hcapacity : ∀ c : College, capacity (sigma c) = capacity c)
    (hP :
      pg23DifferentialSourceMarketClearing
        (pg23DifferentialSourceAggregateDemand typeLaw) capacity P) :
    pg23DifferentialSourceMarketClearing
      (pg23DifferentialSourceAggregateDemand typeLaw) capacity
      (pg23RelabelCutoff sigma P) := by
  intro c
  calc
    pg23DifferentialSourceAggregateDemand typeLaw (pg23RelabelCutoff sigma P) c =
        pg23DifferentialSourceAggregateDemand typeLaw P (sigma.symm c) := by
      simpa using
        pg23DifferentialSourceAggregateDemand_relabel_of_typeLaw_relabel
          (typeLaw := typeLaw) sigma P (sigma.symm c) hlaw
    _ = capacity (sigma.symm c) := hP (sigma.symm c)
    _ = capacity c := by
      simpa using (hcapacity (sigma.symm c)).symm

/--
The greatest differential-access exact-clearing raw cutoff is coordinate
constant whenever the differential law and capacities are invariant under
college relabeling.  This is the symmetry half of the differential Equal
Cutoffs Lemma; it does not assume existence or uniqueness.
-/
theorem pg23DifferentialSourceMarketClearing_greatest_constant_of_typeLaw_relabel
    {n : ℕ} [Nonempty College]
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    (capacity : College -> ℝ)
    (hlaw :
      ∀ sigma : Equiv.Perm College,
        Measure.map (pg23DifferentialRelabelApplicant
          (College := College) (n := n) sigma) typeLaw = typeLaw)
    (hcapacity :
      ∀ sigma : Equiv.Perm College, ∀ c : College,
        capacity (sigma c) = capacity c)
    (top : College -> ℝ)
    (htop :
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand typeLaw) capacity top ∧
        ∀ P : College -> ℝ,
          pg23DifferentialSourceMarketClearing
            (pg23DifferentialSourceAggregateDemand typeLaw) capacity P ->
          pg23RawCutoffLe P top) :
    ∃ p : ℝ, ∀ c : College, top c = p := by
  apply pg23RawCutoff_constant_of_relabel_fixed top
  intro sigma
  apply pg23RelabelCutoff_eq_of_greatest
    (fun P : College -> ℝ =>
      pg23DifferentialSourceMarketClearing
        (pg23DifferentialSourceAggregateDemand typeLaw) capacity P)
    top htop
  intro tau P hP
  exact pg23DifferentialSourceMarketClearing_relabel_of_typeLaw_relabel
    typeLaw capacity tau P (hlaw tau) (hcapacity tau) hP

/--
The least differential-access exact-clearing raw cutoff is coordinate constant
under the same relabeling invariance assumptions.
-/
theorem pg23DifferentialSourceMarketClearing_least_constant_of_typeLaw_relabel
    {n : ℕ} [Nonempty College]
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    (capacity : College -> ℝ)
    (hlaw :
      ∀ sigma : Equiv.Perm College,
        Measure.map (pg23DifferentialRelabelApplicant
          (College := College) (n := n) sigma) typeLaw = typeLaw)
    (hcapacity :
      ∀ sigma : Equiv.Perm College, ∀ c : College,
        capacity (sigma c) = capacity c)
    (bot : College -> ℝ)
    (hbot :
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand typeLaw) capacity bot ∧
        ∀ P : College -> ℝ,
          pg23DifferentialSourceMarketClearing
            (pg23DifferentialSourceAggregateDemand typeLaw) capacity P ->
          pg23RawCutoffLe bot P) :
    ∃ p : ℝ, ∀ c : College, bot c = p := by
  apply pg23RawCutoff_constant_of_relabel_fixed bot
  intro sigma
  apply pg23RelabelCutoff_eq_of_least
    (fun P : College -> ℝ =>
      pg23DifferentialSourceMarketClearing
        (pg23DifferentialSourceAggregateDemand typeLaw) capacity P)
    bot hbot
  intro tau P hP
  exact pg23DifferentialSourceMarketClearing_relabel_of_typeLaw_relabel
    typeLaw capacity tau P (hlaw tau) (hcapacity tau) hP

/-- Monoculture differential-access clearing is invariant under relabeling. -/
theorem pg23MonocultureDifferentialSourceMarketClearing_relabel {n : ℕ}
    (accessLaw : Measure (Fin n)) (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure accessLaw]
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (capacity : College -> ℝ)
    (sigma : Equiv.Perm College) (P : College -> ℝ)
    (hcapacity : ∀ c : College, capacity (sigma c) = capacity c)
    (hP :
      pg23DifferentialSourceMarketClearing
        (pg23DifferentialSourceAggregateDemand
          (pg23MonocultureDifferentialTypeLaw
            (College := College) accessLaw valueLaw noiseLaw))
        capacity P) :
    pg23DifferentialSourceMarketClearing
      (pg23DifferentialSourceAggregateDemand
        (pg23MonocultureDifferentialTypeLaw
          (College := College) accessLaw valueLaw noiseLaw))
      capacity (pg23RelabelCutoff sigma P) :=
  pg23DifferentialSourceMarketClearing_relabel_of_typeLaw_relabel
    (typeLaw :=
      pg23MonocultureDifferentialTypeLaw
        (College := College) accessLaw valueLaw noiseLaw)
    capacity sigma P
    (pg23MonocultureDifferentialTypeLaw_relabel
      (College := College) accessLaw valueLaw noiseLaw sigma)
    hcapacity hP

/-- Polyculture differential-access clearing is invariant under relabeling. -/
theorem pg23PolycultureDifferentialSourceMarketClearing_relabel {n : ℕ}
    (accessLaw : Measure (Fin n)) (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure accessLaw]
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (capacity : College -> ℝ)
    (sigma : Equiv.Perm College) (P : College -> ℝ)
    (hcapacity : ∀ c : College, capacity (sigma c) = capacity c)
    (hP :
      pg23DifferentialSourceMarketClearing
        (pg23DifferentialSourceAggregateDemand
          (pg23PolycultureDifferentialTypeLaw
            (College := College) accessLaw valueLaw noiseLaw))
        capacity P) :
    pg23DifferentialSourceMarketClearing
      (pg23DifferentialSourceAggregateDemand
        (pg23PolycultureDifferentialTypeLaw
          (College := College) accessLaw valueLaw noiseLaw))
      capacity (pg23RelabelCutoff sigma P) :=
  pg23DifferentialSourceMarketClearing_relabel_of_typeLaw_relabel
    (typeLaw :=
      pg23PolycultureDifferentialTypeLaw
        (College := College) accessLaw valueLaw noiseLaw)
    capacity sigma P
    (pg23PolycultureDifferentialTypeLaw_relabel
      (College := College) accessLaw valueLaw noiseLaw sigma)
    hcapacity hP

/--
For the concrete monoculture differential-access law, any least and greatest
exact-clearing raw cutoffs supplied by a later existence/lattice argument have
constant coordinates.
-/
theorem pg23MonocultureDifferentialSourceMarketClearing_extrema_constant
    {n : ℕ} [Nonempty College]
    (accessLaw : Measure (Fin n)) (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure accessLaw]
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (capacity : College -> ℝ)
    (hcapacity :
      ∀ sigma : Equiv.Perm College, ∀ c : College,
        capacity (sigma c) = capacity c)
    (bot top : College -> ℝ)
    (hbot :
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23MonocultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw)) capacity bot ∧
        ∀ P : College -> ℝ,
          pg23DifferentialSourceMarketClearing
            (pg23DifferentialSourceAggregateDemand
              (pg23MonocultureDifferentialTypeLaw
                (College := College) accessLaw valueLaw noiseLaw)) capacity P ->
          pg23RawCutoffLe bot P)
    (htop :
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23MonocultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw)) capacity top ∧
        ∀ P : College -> ℝ,
          pg23DifferentialSourceMarketClearing
            (pg23DifferentialSourceAggregateDemand
              (pg23MonocultureDifferentialTypeLaw
                (College := College) accessLaw valueLaw noiseLaw)) capacity P ->
          pg23RawCutoffLe P top) :
    (∃ p : ℝ, ∀ c : College, bot c = p) ∧
      ∃ p : ℝ, ∀ c : College, top c = p := by
  constructor
  · exact pg23DifferentialSourceMarketClearing_least_constant_of_typeLaw_relabel
      (typeLaw :=
        pg23MonocultureDifferentialTypeLaw
          (College := College) accessLaw valueLaw noiseLaw)
      capacity
      (fun sigma =>
        pg23MonocultureDifferentialTypeLaw_relabel
          (College := College) accessLaw valueLaw noiseLaw sigma)
      hcapacity bot hbot
  · exact pg23DifferentialSourceMarketClearing_greatest_constant_of_typeLaw_relabel
      (typeLaw :=
        pg23MonocultureDifferentialTypeLaw
          (College := College) accessLaw valueLaw noiseLaw)
      capacity
      (fun sigma =>
        pg23MonocultureDifferentialTypeLaw_relabel
          (College := College) accessLaw valueLaw noiseLaw sigma)
      hcapacity top htop

/--
For the concrete polyculture differential-access law, any least and greatest
exact-clearing raw cutoffs supplied by a later existence/lattice argument have
constant coordinates.
-/
theorem pg23PolycultureDifferentialSourceMarketClearing_extrema_constant
    {n : ℕ} [Nonempty College]
    (accessLaw : Measure (Fin n)) (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure accessLaw]
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (capacity : College -> ℝ)
    (hcapacity :
      ∀ sigma : Equiv.Perm College, ∀ c : College,
        capacity (sigma c) = capacity c)
    (bot top : College -> ℝ)
    (hbot :
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23PolycultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw)) capacity bot ∧
        ∀ P : College -> ℝ,
          pg23DifferentialSourceMarketClearing
            (pg23DifferentialSourceAggregateDemand
              (pg23PolycultureDifferentialTypeLaw
                (College := College) accessLaw valueLaw noiseLaw)) capacity P ->
          pg23RawCutoffLe bot P)
    (htop :
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23PolycultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw)) capacity top ∧
        ∀ P : College -> ℝ,
          pg23DifferentialSourceMarketClearing
            (pg23DifferentialSourceAggregateDemand
              (pg23PolycultureDifferentialTypeLaw
                (College := College) accessLaw valueLaw noiseLaw)) capacity P ->
          pg23RawCutoffLe P top) :
    (∃ p : ℝ, ∀ c : College, bot c = p) ∧
      ∃ p : ℝ, ∀ c : College, top c = p := by
  constructor
  · exact pg23DifferentialSourceMarketClearing_least_constant_of_typeLaw_relabel
      (typeLaw :=
        pg23PolycultureDifferentialTypeLaw
          (College := College) accessLaw valueLaw noiseLaw)
      capacity
      (fun sigma =>
        pg23PolycultureDifferentialTypeLaw_relabel
          (College := College) accessLaw valueLaw noiseLaw sigma)
      hcapacity bot hbot
  · exact pg23DifferentialSourceMarketClearing_greatest_constant_of_typeLaw_relabel
      (typeLaw :=
        pg23PolycultureDifferentialTypeLaw
          (College := College) accessLaw valueLaw noiseLaw)
      capacity
      (fun sigma =>
        pg23PolycultureDifferentialTypeLaw_relabel
          (College := College) accessLaw valueLaw noiseLaw sigma)
      hcapacity top htop

/--
For every finite raw cutoff, literal PG23 aggregate demand equals aggregate
demand after the explicit normalized-score transport.  This is a one-way
comparison of raw cutoffs with their normalized images.
-/
theorem pg23AggregateDemand_normalized_transport
    (typeLaw : Measure (PG23ApplicantType College))
    (P : College -> ℝ) (c : College) :
    al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw)
      (pg23NormalizedCutoff P) c =
      pg23SourceAggregateDemand typeLaw P c := by
  unfold pg23NormalizedTypeLaw al16SourceAggregateDemand pg23SourceAggregateDemand
  rw [map_measureReal_apply pg23NormalizedStudent_measurable]
  · congr 1
  · change MeasurableSet
      ((al16SourceChoice (pg23NormalizedCutoff P)) ⁻¹' ({some c} : Set (Option College)))
    exact al16SourceChoice_fiber_measurable _ _

/-- The literal PG23 exact market-clearing condition. -/
def pg23SourceMarketClearing
    (demand : (College -> ℝ) -> College -> ℝ) (capacity : College -> ℝ)
    (P : College -> ℝ) : Prop :=
  ∀ c : College, demand P c = capacity c

/--
An exact-clearing finite raw cutoff transports to an A-L market-clearing
normalized cutoff.  This direction does not identify boundary cutoffs with
raw real cutoffs.
-/
theorem pg23NormalizedMarketClearing_of_raw
    (typeLaw : Measure (PG23ApplicantType College)) (capacity : College -> ℝ)
    (P : College -> ℝ)
    (hP : pg23SourceMarketClearing (pg23SourceAggregateDemand typeLaw) capacity P) :
    al16SourceMarketClearing
      (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw)) capacity
      (pg23NormalizedCutoff P) := by
  constructor
  · intro c
    rw [pg23AggregateDemand_normalized_transport]
    exact (hP c).le
  · intro c _
    rw [pg23AggregateDemand_normalized_transport]
    exact hP c

/--
An interior A-L clearing cutoff transports back to an exact finite raw PG23
cutoff.  This is a clearing correspondence only; it does not turn the A-L
matching theorem into a raw PG23 stability or regularity correspondence.
-/
theorem pg23SourceMarketClearing_of_normalized
    (typeLaw : Measure (PG23ApplicantType College)) (capacity : College -> ℝ)
    (Q : AL16Cutoff College)
    (hinterior : ∀ c : College,
      0 < al16CutoffValue Q c ∧ al16CutoffValue Q c < 1)
    (hQ : al16SourceMarketClearing
      (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw)) capacity Q) :
    pg23SourceMarketClearing (pg23SourceAggregateDemand typeLaw) capacity
      (pg23DenormalizedCutoff Q) := by
  intro c
  calc
    pg23SourceAggregateDemand typeLaw (pg23DenormalizedCutoff Q) c =
        al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw)
          (pg23NormalizedCutoff (pg23DenormalizedCutoff Q)) c := by
      rw [pg23AggregateDemand_normalized_transport]
    _ = al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw) Q c := by
      rw [pg23NormalizedCutoff_denormalized_eq Q hinterior]
    _ = capacity c := hQ.2 c (hinterior c).1

/--
The exact ambient coordinatewise supremum of a nonempty family of normalized
PG23 clearing cutoffs clears.  The accompanying ambient and clearing-relative
least-upper-bound facts retain the operation identified by A-L's construction.
-/
theorem pg23NormalizedMarketClearing_pointwiseSup
    (typeLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure typeLaw]
    (hlevel : pg23SourceScoreLevelNull typeLaw)
    (capacity : College -> ℝ)
    (T : Set (AL16Cutoff College))
    (hT : T.Nonempty)
    (hclear : ∀ Q : AL16Cutoff College, T Q →
      al16SourceMarketClearing
        (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw)) capacity Q) :
    al16IsPointwiseLeastUpperBound T (al16PointwiseSup T hT) ∧
      IsLeastUpperBoundOn
        (al16SourceMarketClearing
          (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw)) capacity)
        al16CutoffLe T (al16PointwiseSup T hT) := by
  letI : IsProbabilityMeasure (pg23NormalizedTypeLaw typeLaw) :=
    pg23NormalizedTypeLaw_isProbabilityMeasure typeLaw
  have hstrict : al16SourceStrictPreferences (pg23NormalizedTypeLaw typeLaw) :=
    pg23NormalizedTypeLaw_strictPreferences_of_raw typeLaw hlevel
  apply al16SourceMarketClearing_pointwiseSup_of_continuum_primitives
    (demand := al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw))
    (outside := al16SourceOutsideDemand (pg23NormalizedTypeLaw typeLaw))
    (capacity := capacity)
  · intro R
    simpa [al16SourceOutsideDemand, al16SourceAggregateDemand] using
      (al16UnitMassPartition_of_measure_choice
        (pg23NormalizedTypeLaw typeLaw) al16SourceChoice
        al16SourceChoice_fiber_measurable R)
  · intro P Q
    simpa [sup_comm] using
      al16Outside_le_sup_of_choice_semantics
        (al16SourceOutsideDemand (pg23NormalizedTypeLaw typeLaw))
        (pg23NormalizedTypeLaw typeLaw).real al16SourceScore
        al16SourcePrefers al16SourceChoice
        (fun {A B} hAB =>
          al16MeasureMass_mono (pg23NormalizedTypeLaw typeLaw) hAB)
        (fun _ => rfl) al16SourceChoice_semantics Q P
  · intro P Q c hPQ
    exact al16AggregateDemand_le_sup_of_choice_semantics
      (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw))
      (pg23NormalizedTypeLaw typeLaw).real al16SourceScore
      al16SourcePrefers al16SourceChoice
      (fun {A B} hAB =>
        al16MeasureMass_mono (pg23NormalizedTypeLaw typeLaw) hAB)
      (fun _ _ => rfl) al16SourceChoice_semantics
      (al16RankPrefers_total al16SourceRank al16SourceRank_injective) hPQ
  · intro P Q hPQ c
    exact al16SourceAggregateDemand_tendsto_of_coordinatewiseTendsto
      (pg23NormalizedTypeLaw typeLaw) hstrict P Q hPQ c
  · exact hclear

/--
The exact ambient coordinatewise infimum of a nonempty family of normalized
PG23 clearing cutoffs clears, with its ambient and clearing-relative
greatest-lower-bound properties.
-/
theorem pg23NormalizedMarketClearing_pointwiseInf
    (typeLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure typeLaw]
    (hlevel : pg23SourceScoreLevelNull typeLaw)
    (capacity : College -> ℝ)
    (T : Set (AL16Cutoff College))
    (hT : T.Nonempty)
    (hclear : ∀ Q : AL16Cutoff College, T Q →
      al16SourceMarketClearing
        (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw)) capacity Q) :
    al16IsPointwiseGreatestLowerBound T (al16PointwiseInf T hT) ∧
      IsGreatestLowerBoundOn
        (al16SourceMarketClearing
          (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw)) capacity)
        al16CutoffLe T (al16PointwiseInf T hT) := by
  letI : IsProbabilityMeasure (pg23NormalizedTypeLaw typeLaw) :=
    pg23NormalizedTypeLaw_isProbabilityMeasure typeLaw
  have hstrict : al16SourceStrictPreferences (pg23NormalizedTypeLaw typeLaw) :=
    pg23NormalizedTypeLaw_strictPreferences_of_raw typeLaw hlevel
  apply al16SourceMarketClearing_pointwiseInf_of_continuum_primitives
    (demand := al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw))
    (outside := al16SourceOutsideDemand (pg23NormalizedTypeLaw typeLaw))
    (capacity := capacity)
  · intro R
    simpa [al16SourceOutsideDemand, al16SourceAggregateDemand] using
      (al16UnitMassPartition_of_measure_choice
        (pg23NormalizedTypeLaw typeLaw) al16SourceChoice
        al16SourceChoice_fiber_measurable R)
  · intro P Q
    simpa [sup_comm] using
      al16Outside_le_sup_of_choice_semantics
        (al16SourceOutsideDemand (pg23NormalizedTypeLaw typeLaw))
        (pg23NormalizedTypeLaw typeLaw).real al16SourceScore
        al16SourcePrefers al16SourceChoice
        (fun {A B} hAB =>
          al16MeasureMass_mono (pg23NormalizedTypeLaw typeLaw) hAB)
        (fun _ => rfl) al16SourceChoice_semantics Q P
  · intro P Q c hPQ
    exact al16AggregateDemand_le_sup_of_choice_semantics
      (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw))
      (pg23NormalizedTypeLaw typeLaw).real al16SourceScore
      al16SourcePrefers al16SourceChoice
      (fun {A B} hAB =>
        al16MeasureMass_mono (pg23NormalizedTypeLaw typeLaw) hAB)
      (fun _ _ => rfl) al16SourceChoice_semantics
      (al16RankPrefers_total al16SourceRank al16SourceRank_injective) hPQ
  · intro P Q
    exact al16Outside_inf_le_of_choice_semantics
      (al16SourceOutsideDemand (pg23NormalizedTypeLaw typeLaw))
      (pg23NormalizedTypeLaw typeLaw).real al16SourceScore
      al16SourcePrefers al16SourceChoice
      (fun {A B} hAB =>
        al16MeasureMass_mono (pg23NormalizedTypeLaw typeLaw) hAB)
      (fun _ => rfl) al16SourceChoice_semantics P Q
  · intro P Q c hPQ
    exact al16AggregateDemand_inf_le_of_choice_semantics
      (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw))
      (pg23NormalizedTypeLaw typeLaw).real al16SourceScore
      al16SourcePrefers al16SourceChoice
      (fun {A B} hAB =>
        al16MeasureMass_mono (pg23NormalizedTypeLaw typeLaw) hAB)
      (fun _ _ => rfl) al16SourceChoice_semantics
      (al16RankPrefers_total al16SourceRank al16SourceRank_injective) hPQ
  · intro P Q hPQ c
    exact al16SourceAggregateDemand_tendsto_of_coordinatewiseTendsto
      (pg23NormalizedTypeLaw typeLaw) hstrict P Q hPQ c
  · exact hclear

/--
The raw monoculture clearing correspondence, with the source-law endpoint
conditions proved from uniform rankings, equal capacity, and score nullity.
-/
theorem pg23MonocultureSourceMarketClearing_of_normalized
    (valueLaw noiseLaw : Measure ℝ) [Nonempty College]
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ))
    (Q : AL16Cutoff College)
    (hQ : al16SourceMarketClearing
      (al16SourceAggregateDemand
        (pg23NormalizedTypeLaw
          (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))) capacity Q) :
    pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw)) capacity
      (pg23DenormalizedCutoff Q) := by
  apply pg23SourceMarketClearing_of_normalized _ capacity Q _ hQ
  exact pg23MonocultureNormalizedMarketClearing_cutoff_interior
    valueLaw noiseLaw hlevel S hS capacity hcapacity Q hQ

/--
The raw polyculture clearing correspondence, with the source-law endpoint
conditions proved from uniform rankings, equal capacity, and score nullity.
-/
theorem pg23PolycultureSourceMarketClearing_of_normalized
    (valueLaw noiseLaw : Measure ℝ) [Nonempty College]
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hlevel : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ))
    (Q : AL16Cutoff College)
    (hQ : al16SourceMarketClearing
      (al16SourceAggregateDemand
        (pg23NormalizedTypeLaw
          (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))) capacity Q) :
    pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw)) capacity
      (pg23DenormalizedCutoff Q) := by
  apply pg23SourceMarketClearing_of_normalized _ capacity Q _ hQ
  exact pg23PolycultureNormalizedMarketClearing_cutoff_interior
    valueLaw noiseLaw hlevel S hS capacity hcapacity Q hQ

/--
The literal monoculture model has a finite raw exact-clearing cutoff when
equal capacity lies in `(0, 1)` and every raw score level is null.  The
score-null premise is an explicit remediation condition, not a consequence
of the source's connected-support wording.
-/
theorem pg23MonocultureSourceMarketClearing_nonempty
    (valueLaw noiseLaw : Measure ℝ) [Nonempty College]
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1) :
    ∃ P : College -> ℝ,
      pg23SourceMarketClearing
        (pg23SourceAggregateDemand
          (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
        (fun _ : College => S / (Fintype.card College : ℝ)) P := by
  letI : IsProbabilityMeasure
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) :=
    pg23MonocultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  letI : IsProbabilityMeasure
      (pg23NormalizedTypeLaw
        (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw)) :=
    pg23NormalizedTypeLaw_isProbabilityMeasure _
  have hstrict := pg23NormalizedTypeLaw_strictPreferences_of_raw _ hlevel
  have hcapacity_pos : ∀ c : College,
      0 < S / (Fintype.card College : ℝ) := by
    intro c
    have hcardpos : (0 : ℝ) < Fintype.card College := by
      exact_mod_cast Fintype.card_pos
    exact div_pos hS.1 hcardpos
  rcases al16SourceMarketClearing_nonempty_of_concrete_continuum_primitives
      (pg23NormalizedTypeLaw
        (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
      (fun _ : College => S / (Fintype.card College : ℝ)) hcapacity_pos hstrict with ⟨Q, hQ⟩
  exact ⟨pg23DenormalizedCutoff Q,
    pg23MonocultureSourceMarketClearing_of_normalized valueLaw noiseLaw hlevel S hS
      (fun _ : College => S / (Fintype.card College : ℝ)) (by intro c; rfl) Q hQ⟩

/--
The literal polyculture model has a finite raw exact-clearing cutoff under the
same visible equal-capacity and raw score-level-null conditions.
-/
theorem pg23PolycultureSourceMarketClearing_nonempty
    (valueLaw noiseLaw : Measure ℝ) [Nonempty College]
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hlevel : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1) :
    ∃ P : College -> ℝ,
      pg23SourceMarketClearing
        (pg23SourceAggregateDemand
          (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
        (fun _ : College => S / (Fintype.card College : ℝ)) P := by
  letI : IsProbabilityMeasure
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw) :=
    pg23PolycultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  letI : IsProbabilityMeasure
      (pg23NormalizedTypeLaw
        (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw)) :=
    pg23NormalizedTypeLaw_isProbabilityMeasure _
  have hstrict := pg23NormalizedTypeLaw_strictPreferences_of_raw _ hlevel
  have hcapacity_pos : ∀ c : College,
      0 < S / (Fintype.card College : ℝ) := by
    intro c
    have hcardpos : (0 : ℝ) < Fintype.card College := by
      exact_mod_cast Fintype.card_pos
    exact div_pos hS.1 hcardpos
  rcases al16SourceMarketClearing_nonempty_of_concrete_continuum_primitives
      (pg23NormalizedTypeLaw
        (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
      (fun _ : College => S / (Fintype.card College : ℝ)) hcapacity_pos hstrict with ⟨Q, hQ⟩
  exact ⟨pg23DenormalizedCutoff Q,
    pg23PolycultureSourceMarketClearing_of_normalized valueLaw noiseLaw hlevel S hS
      (fun _ : College => S / (Fintype.card College : ℝ)) (by intro c; rfl) Q hQ⟩

/--
Relabeling an invariant literal type law transports raw aggregate demand to
the correspondingly relabeled college.  This is the distributional symmetry
step used in the source's Equal Cutoffs Lemma proof.
-/
theorem pg23SourceAggregateDemand_relabel_of_typeLaw_relabel
    (typeLaw : Measure (PG23ApplicantType College))
    (sigma : Equiv.Perm College) (P : College -> ℝ) (c : College)
    (hlaw : Measure.map (pg23RelabelApplicant sigma) typeLaw = typeLaw) :
    pg23SourceAggregateDemand typeLaw (pg23RelabelCutoff sigma P) (sigma c) =
      pg23SourceAggregateDemand typeLaw P c := by
  unfold pg23SourceAggregateDemand
  calc
    typeLaw.real
        (pg23MatchingCollegeSet (pg23SourceChoice (pg23RelabelCutoff sigma P)) (sigma c)) =
        (Measure.map (pg23RelabelApplicant sigma) typeLaw).real
          (pg23MatchingCollegeSet (pg23SourceChoice (pg23RelabelCutoff sigma P)) (sigma c)) := by
      rw [hlaw]
    _ = typeLaw.real
          ((pg23RelabelApplicant sigma) ⁻¹'
            pg23MatchingCollegeSet
              (pg23SourceChoice (pg23RelabelCutoff sigma P)) (sigma c)) :=
      map_measureReal_apply (pg23RelabelApplicant_measurable sigma)
        (by
          change MeasurableSet
            ((pg23SourceChoice (pg23RelabelCutoff sigma P)) ⁻¹' ({some (sigma c)} :
              Set (Option College)))
          exact pg23SourceChoice_fiber_measurable _ _)
    _ = typeLaw.real (pg23MatchingCollegeSet (pg23SourceChoice P) c) := by
      congr 1
      ext theta
      simp only [Set.mem_preimage, pg23MatchingCollegeSet, Set.mem_setOf_eq]
      rw [pg23SourceChoice_relabel]
      constructor
      · intro h
        exact Option.map_injective sigma.injective h
      · intro h
        simp [h]

/--
Under capacity invariance, a literal exact-clearing cutoff remains exact
clearing after relabeling colleges.  No lattice, cutoff-existence, or
uniqueness assumption is used here.
-/
theorem pg23SourceMarketClearing_relabel_of_typeLaw_relabel
    (typeLaw : Measure (PG23ApplicantType College)) (capacity : College -> ℝ)
    (sigma : Equiv.Perm College) (P : College -> ℝ)
    (hlaw : Measure.map (pg23RelabelApplicant sigma) typeLaw = typeLaw)
    (hcapacity : ∀ c : College, capacity (sigma c) = capacity c)
    (hP : pg23SourceMarketClearing (pg23SourceAggregateDemand typeLaw) capacity P) :
    pg23SourceMarketClearing (pg23SourceAggregateDemand typeLaw) capacity
      (pg23RelabelCutoff sigma P) := by
  intro c
  calc
    pg23SourceAggregateDemand typeLaw (pg23RelabelCutoff sigma P) c =
        pg23SourceAggregateDemand typeLaw P (sigma.symm c) := by
      simpa using
        pg23SourceAggregateDemand_relabel_of_typeLaw_relabel
          typeLaw sigma P (sigma.symm c) hlaw
    _ = capacity (sigma.symm c) := hP (sigma.symm c)
    _ = capacity c := by
      simpa using (hcapacity (sigma.symm c)).symm

/--
The concrete PG23 cutoff market built from the displayed source definitions.
Unlike the generic `CutoffMarket` input used by the older wrappers, every
field here is a source definition over the literal applicant type and raw
score cutoffs.
-/
noncomputable def pg23SourceCutoffMarket
    (typeLaw : Measure (PG23ApplicantType College)) (capacity : College -> ℝ) :
    CutoffMarket (PG23ApplicantType College) College where
  Cutoff := College -> ℝ
  Matching := PG23Matching College
  demandAt := pg23SourceChoice
  aggregateDemand := pg23SourceAggregateDemand typeLaw
  capacity := capacity
  isStable := pg23SourceStableMatching typeLaw capacity
  marketClearing := pg23SourceMarketClearing (pg23SourceAggregateDemand typeLaw) capacity
  representedByCutoff := fun matching P => matching = pg23SourceChoice P

/-- The concrete monoculture economy from the source's value and noise laws. -/
noncomputable def pg23MonocultureCutoffMarket
    (valueLaw noiseLaw : Measure ℝ) (capacity : College -> ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw] :
    CutoffMarket (PG23ApplicantType College) College :=
  pg23SourceCutoffMarket
    (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) capacity

/-- The concrete polyculture economy from the source's value and iid noise laws. -/
noncomputable def pg23PolycultureCutoffMarket
    (valueLaw noiseLaw : Measure ℝ) (capacity : College -> ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw] :
    CutoffMarket (PG23ApplicantType College) College :=
  pg23SourceCutoffMarket
    (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw) capacity

/--
The displayed monoculture law makes exact clearing invariant under every
capacity-preserving college permutation.
-/
theorem pg23MonocultureMarketClearing_relabel
    (valueLaw noiseLaw : Measure ℝ) (capacity : College -> ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (sigma : Equiv.Perm College) (P : College -> ℝ)
    (hcapacity : ∀ c : College, capacity (sigma c) = capacity c)
    (hP : pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw)) capacity P) :
    pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw)) capacity
      (pg23RelabelCutoff sigma P) :=
  pg23SourceMarketClearing_relabel_of_typeLaw_relabel _ _ sigma P
    (pg23MonocultureTypeLaw_relabel sigma valueLaw noiseLaw) hcapacity hP

/--
The displayed polyculture iid law makes exact clearing invariant under every
capacity-preserving college permutation.
-/
theorem pg23PolycultureMarketClearing_relabel
    (valueLaw noiseLaw : Measure ℝ) (capacity : College -> ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (sigma : Equiv.Perm College) (P : College -> ℝ)
    (hcapacity : ∀ c : College, capacity (sigma c) = capacity c)
    (hP : pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw)) capacity P) :
    pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw)) capacity
      (pg23RelabelCutoff sigma P) :=
  pg23SourceMarketClearing_relabel_of_typeLaw_relabel _ _ sigma P
    (pg23PolycultureTypeLaw_relabel sigma valueLaw noiseLaw) hcapacity hP

/--
For the literal monoculture law, normalized clearing cutoffs are closed under
college relabeling.  The proof transports through the checked finite raw
cutoff inverse and back; it does not assume normalized-law symmetry as an
opaque input.
-/
theorem pg23MonocultureNormalizedMarketClearing_relabel
    (valueLaw noiseLaw : Measure ℝ) [Nonempty College]
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ))
    (sigma : Equiv.Perm College) (Q : AL16Cutoff College)
    (hQ : al16SourceMarketClearing
      (al16SourceAggregateDemand
        (pg23NormalizedTypeLaw
          (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))) capacity Q) :
    al16SourceMarketClearing
      (al16SourceAggregateDemand
        (pg23NormalizedTypeLaw
          (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))) capacity
      (pg23RelabelNormalizedCutoff sigma Q) := by
  let P := pg23DenormalizedCutoff Q
  have hraw := pg23MonocultureSourceMarketClearing_of_normalized
    valueLaw noiseLaw hlevel S hS capacity hcapacity Q hQ
  have hcapacity_invariant : ∀ c : College, capacity (sigma c) = capacity c := by
    intro c
    rw [hcapacity (sigma c), hcapacity c]
  have hraw_relabel := pg23MonocultureMarketClearing_relabel
    valueLaw noiseLaw capacity sigma P hcapacity_invariant (by simpa [P] using hraw)
  have hnormalized := pg23NormalizedMarketClearing_of_raw
    (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) capacity
    (pg23RelabelCutoff sigma P) hraw_relabel
  simpa only [P, pg23NormalizedCutoff_relabel,
    pg23NormalizedCutoff_denormalized_eq Q
      (pg23MonocultureNormalizedMarketClearing_cutoff_interior
        valueLaw noiseLaw hlevel S hS capacity hcapacity Q hQ)] using hnormalized

/--
For the literal polyculture law, normalized clearing cutoffs are closed under
college relabeling by the derived iid-law and raw-clearing equivariance.
-/
theorem pg23PolycultureNormalizedMarketClearing_relabel
    (valueLaw noiseLaw : Measure ℝ) [Nonempty College]
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hlevel : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ))
    (sigma : Equiv.Perm College) (Q : AL16Cutoff College)
    (hQ : al16SourceMarketClearing
      (al16SourceAggregateDemand
        (pg23NormalizedTypeLaw
          (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))) capacity Q) :
    al16SourceMarketClearing
      (al16SourceAggregateDemand
        (pg23NormalizedTypeLaw
          (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))) capacity
      (pg23RelabelNormalizedCutoff sigma Q) := by
  let P := pg23DenormalizedCutoff Q
  have hraw := pg23PolycultureSourceMarketClearing_of_normalized
    valueLaw noiseLaw hlevel S hS capacity hcapacity Q hQ
  have hcapacity_invariant : ∀ c : College, capacity (sigma c) = capacity c := by
    intro c
    rw [hcapacity (sigma c), hcapacity c]
  have hraw_relabel := pg23PolycultureMarketClearing_relabel
    valueLaw noiseLaw capacity sigma P hcapacity_invariant (by simpa [P] using hraw)
  have hnormalized := pg23NormalizedMarketClearing_of_raw
    (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw) capacity
    (pg23RelabelCutoff sigma P) hraw_relabel
  simpa only [P, pg23NormalizedCutoff_relabel,
    pg23NormalizedCutoff_denormalized_eq Q
      (pg23PolycultureNormalizedMarketClearing_cutoff_interior
        valueLaw noiseLaw hlevel S hS capacity hcapacity Q hQ)] using hnormalized

/--
The A-L greatest clearing cutoff is coordinate-constant whenever the concrete
normalized clearing set is permutation invariant.  This proves the lattice
symmetry part of PG23's Equal Cutoffs proof but deliberately does not claim
uniqueness of all clearing cutoffs.
-/
theorem pg23NormalizedMarketClearing_exists_constant_of_relabel
    (typeLaw : Measure (PG23ApplicantType College)) [Nonempty College]
    [IsProbabilityMeasure typeLaw]
    (hlevel : pg23SourceScoreLevelNull typeLaw)
    (S : ℝ) (hS : 0 < S ∧ S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ))
    (hrelabel : ∀ (sigma : Equiv.Perm College) (Q : AL16Cutoff College),
      al16SourceMarketClearing
        (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw)) capacity Q ->
          al16SourceMarketClearing
            (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw)) capacity
            (pg23RelabelNormalizedCutoff sigma Q)) :
    ∃ Q : AL16Cutoff College,
      al16SourceMarketClearing
        (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw)) capacity Q ∧
        ∃ q : ℝ, ∀ c : College, al16CutoffValue Q c = q := by
  letI : IsProbabilityMeasure (pg23NormalizedTypeLaw typeLaw) :=
    pg23NormalizedTypeLaw_isProbabilityMeasure _
  have hstrict := pg23NormalizedTypeLaw_strictPreferences_of_raw _ hlevel
  have hcapacity_pos : ∀ c : College, 0 < capacity c := by
    intro c
    rw [hcapacity c]
    have hcardpos : (0 : ℝ) < Fintype.card College := by
      exact_mod_cast Fintype.card_pos
    exact div_pos hS.1 hcardpos
  have hnonempty := al16SourceMarketClearing_nonempty_of_concrete_continuum_primitives
    (pg23NormalizedTypeLaw typeLaw) capacity hcapacity_pos hstrict
  let L := al16SourceMarketClearing_completeLattice_of_concrete_continuum_primitives
    (pg23NormalizedTypeLaw typeLaw) capacity hstrict hnonempty
  rcases L.exists_greatest hnonempty with ⟨top, htop, hgreatest⟩
  refine ⟨top, htop, ?_⟩
  apply pg23NormalizedCutoff_constant_of_relabel_fixed top
  intro sigma
  apply pg23RelabelNormalizedCutoff_eq_of_greatest _ top ⟨htop, hgreatest⟩ _ sigma
  intro tau P hP
  exact hrelabel tau P hP

/--
The literal monoculture economy admits a shared finite raw exact-clearing
cutoff under the explicit score-null remediation.  This is the symmetry and
lattice-existence half of the source Equal Cutoffs Lemma, not its uniqueness
half.
-/
theorem pg23MonocultureSourceMarketClearing_exists_constant
    (valueLaw noiseLaw : Measure ℝ) [Nonempty College]
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ)) :
    ∃ P : College -> ℝ,
      pg23SourceMarketClearing
        (pg23SourceAggregateDemand
          (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw)) capacity P ∧
        ∃ p : ℝ, ∀ c : College, P c = p := by
  letI : IsProbabilityMeasure
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) :=
    pg23MonocultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  rcases pg23NormalizedMarketClearing_exists_constant_of_relabel
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw)
      hlevel S hS capacity hcapacity (fun sigma Q hQ =>
        pg23MonocultureNormalizedMarketClearing_relabel
          valueLaw noiseLaw hlevel S hS capacity hcapacity sigma Q hQ)
      with ⟨Q, hQ, q, hq⟩
  refine ⟨pg23DenormalizedCutoff Q,
    pg23MonocultureSourceMarketClearing_of_normalized
      valueLaw noiseLaw hlevel S hS capacity hcapacity Q hQ,
    pg23ScoreDenormalize q, ?_⟩
  intro c
  unfold pg23DenormalizedCutoff
  exact congrArg pg23ScoreDenormalize (hq c)

/--
The literal polyculture economy likewise admits a shared finite raw
exact-clearing cutoff, derived from its actual iid-law symmetry.
-/
theorem pg23PolycultureSourceMarketClearing_exists_constant
    (valueLaw noiseLaw : Measure ℝ) [Nonempty College]
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hlevel : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1)
    (capacity : College -> ℝ)
    (hcapacity : ∀ c : College, capacity c = S / (Fintype.card College : ℝ)) :
    ∃ P : College -> ℝ,
      pg23SourceMarketClearing
        (pg23SourceAggregateDemand
          (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw)) capacity P ∧
        ∃ p : ℝ, ∀ c : College, P c = p := by
  letI : IsProbabilityMeasure
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw) :=
    pg23PolycultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  rcases pg23NormalizedMarketClearing_exists_constant_of_relabel
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw)
      hlevel S hS capacity hcapacity (fun sigma Q hQ =>
        pg23PolycultureNormalizedMarketClearing_relabel
          valueLaw noiseLaw hlevel S hS capacity hcapacity sigma Q hQ)
      with ⟨Q, hQ, q, hq⟩
  refine ⟨pg23DenormalizedCutoff Q,
    pg23PolycultureSourceMarketClearing_of_normalized
      valueLaw noiseLaw hlevel S hS capacity hcapacity Q hQ,
    pg23ScoreDenormalize q, ?_⟩
  intro c
  unfold pg23DenormalizedCutoff
  exact congrArg pg23ScoreDenormalize (hq c)

/--
The literal PG23 Supply and Demand Lemma statement for a concrete type law.
This is a proof obligation, not a source-model field: `model.tex:37-42` claims
both directions between stable matchings and exact-clearing cutoff demand.
-/
def pg23SupplyDemandLemmaStatement
    (typeLaw : Measure (PG23ApplicantType College)) (capacity : College -> ℝ) : Prop :=
  ∀ matching : PG23Matching College,
    pg23SourceStableMatching typeLaw capacity matching ↔
      ∃ P : College -> ℝ,
        pg23SourceMarketClearing (pg23SourceAggregateDemand typeLaw) capacity P ∧
          matching = pg23SourceChoice P

/--
The literal Equal Cutoffs Lemma statement for one concrete type law.  The
uniqueness quantifier ranges over every exact-clearing cutoff, not merely over
constant cutoffs; the last conjunct is the paper's shared-coordinate result.
-/
def pg23EqualCutoffsLemmaStatement
    (typeLaw : Measure (PG23ApplicantType College)) (capacity : College -> ℝ) : Prop :=
  ∃ P : College -> ℝ,
    pg23SourceMarketClearing (pg23SourceAggregateDemand typeLaw) capacity P ∧
      (∀ Q : College -> ℝ,
        pg23SourceMarketClearing (pg23SourceAggregateDemand typeLaw) capacity Q ->
          Q = P) ∧
      ∃ p : ℝ, ∀ c : College, P c = p

/-- The source Lemma 1 obligation specialized to the displayed monoculture law. -/
def pg23MonocultureSupplyDemandLemmaStatement
    (valueLaw noiseLaw : Measure ℝ) (capacity : College -> ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw] : Prop :=
  pg23SupplyDemandLemmaStatement
    (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) capacity

/-- The source Lemma 2 obligation specialized to the displayed monoculture law. -/
def pg23MonocultureEqualCutoffsLemmaStatement
    (valueLaw noiseLaw : Measure ℝ) (capacity : College -> ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw] : Prop :=
  pg23EqualCutoffsLemmaStatement
    (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) capacity

/-- The source Lemma 1 obligation specialized to the displayed polyculture law. -/
def pg23PolycultureSupplyDemandLemmaStatement
    (valueLaw noiseLaw : Measure ℝ) (capacity : College -> ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw] : Prop :=
  pg23SupplyDemandLemmaStatement
    (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw) capacity

/-- The source Lemma 2 obligation specialized to the displayed polyculture law. -/
def pg23PolycultureEqualCutoffsLemmaStatement
    (valueLaw noiseLaw : Measure ℝ) (capacity : College -> ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw] : Prop :=
  pg23EqualCutoffsLemmaStatement
    (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw) capacity

end PG23MonocultureMatching
