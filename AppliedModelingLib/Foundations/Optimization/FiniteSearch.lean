import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import AppliedModelingLib.Foundations.Optimization.Certificate

namespace AppliedModelingLib
namespace Optimization

/-!
# Finite Feasible Search

Reusable existence lemmas for optimization over finite feasible regions and
finite encodings of feasible regions.

## Main declarations

- `exists_isMaximizerOn_of_fintype_subtype`
- `exists_isMinimizerOn_of_fintype_subtype`
- `exists_isMaximizerOn_of_finite`
- `exists_isMinimizerOn_of_finite`
- `exists_isMaximizerOn_of_finite_code`
- `exists_isMinimizerOn_of_finite_code`
-/

/-- A real objective has a maximizer over any nonempty finite feasible subtype. -/
theorem exists_isMaximizerOn_of_fintype_subtype
    {α : Type*} (feasible : α → Prop) [Fintype {x : α // feasible x}]
    [Nonempty {x : α // feasible x}] (objective : α → ℝ) :
    ∃ opt : α, IsMaximizerOn feasible objective opt := by
  classical
  let defaultFeasible : {x : α // feasible x} := Classical.choice inferInstance
  have hnonempty : (Finset.univ : Finset {x : α // feasible x}).Nonempty :=
    ⟨defaultFeasible, by simp⟩
  obtain ⟨opt, _hmem, hopt⟩ :=
    Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset {x : α // feasible x}))
      (H := hnonempty) (f := fun x : {x : α // feasible x} => objective x.1)
  refine ⟨opt.1, ?_⟩
  constructor
  · exact opt.2
  · intro y hy
    have hle_sub :
        (fun x : {x : α // feasible x} => objective x.1) ⟨y, hy⟩ ≤
          (Finset.univ : Finset {x : α // feasible x}).sup' hnonempty
            (fun x : {x : α // feasible x} => objective x.1) :=
      Finset.le_sup'
        (s := (Finset.univ : Finset {x : α // feasible x}))
        (f := fun x : {x : α // feasible x} => objective x.1)
        (by simp)
    have hle :
        objective y ≤
          (Finset.univ : Finset {x : α // feasible x}).sup' hnonempty
            (fun x : {x : α // feasible x} => objective x.1) := by
      simpa using hle_sub
    rwa [hopt] at hle

/-- A real objective has a minimizer over any nonempty finite feasible subtype. -/
theorem exists_isMinimizerOn_of_fintype_subtype
    {α : Type*} (feasible : α → Prop) [Fintype {x : α // feasible x}]
    [Nonempty {x : α // feasible x}] (objective : α → ℝ) :
    ∃ opt : α, IsMinimizerOn feasible objective opt := by
  classical
  obtain ⟨opt, hopt⟩ :=
    exists_isMaximizerOn_of_fintype_subtype feasible (fun x => -objective x)
  refine ⟨opt, ?_⟩
  constructor
  · exact hopt.isFeasible
  · intro y hy
    exact neg_le_neg_iff.mp (hopt.le hy)

/-- A real objective has a maximizer over any nonempty decidable finite feasible set. -/
theorem exists_isMaximizerOn_of_finite
    {α : Type*} [Fintype α] (feasible : α → Prop) [DecidablePred feasible]
    (objective : α → ℝ) (hnonempty : ∃ x, feasible x) :
    ∃ opt : α, IsMaximizerOn feasible objective opt := by
  classical
  haveI : Nonempty {x : α // feasible x} :=
    ⟨⟨Classical.choose hnonempty, Classical.choose_spec hnonempty⟩⟩
  exact exists_isMaximizerOn_of_fintype_subtype feasible objective

/-- A real objective has a minimizer over any nonempty decidable finite feasible set. -/
theorem exists_isMinimizerOn_of_finite
    {α : Type*} [Fintype α] (feasible : α → Prop) [DecidablePred feasible]
    (objective : α → ℝ) (hnonempty : ∃ x, feasible x) :
    ∃ opt : α, IsMinimizerOn feasible objective opt := by
  classical
  haveI : Nonempty {x : α // feasible x} :=
    ⟨⟨Classical.choose hnonempty, Classical.choose_spec hnonempty⟩⟩
  exact exists_isMinimizerOn_of_fintype_subtype feasible objective

/--
Finite-code maximizer existence.

Use this when the feasible objects are not themselves convenient finite
data, but every feasible object is represented by a feasible finite code.
-/
theorem exists_isMaximizerOn_of_finite_code
    {Code α : Type*} [Fintype Code]
    (codeFeasible : Code → Prop) [DecidablePred codeFeasible]
    (decode : Code → α) (feasible : α → Prop) (objective : α → ℝ)
    (hdecode_feasible : ∀ c, codeFeasible c → feasible (decode c))
    (hcover : ∀ x, feasible x → ∃ c, codeFeasible c ∧ decode c = x)
    (hnonempty : ∃ x, feasible x) :
    ∃ opt : α, IsMaximizerOn feasible objective opt := by
  classical
  have hcode_nonempty : ∃ c, codeFeasible c := by
    rcases hnonempty with ⟨x, hx⟩
    rcases hcover x hx with ⟨c, hc, _⟩
    exact ⟨c, hc⟩
  obtain ⟨copt, hcopt⟩ :=
    exists_isMaximizerOn_of_finite codeFeasible
      (fun c => objective (decode c)) hcode_nonempty
  refine ⟨decode copt, ?_⟩
  constructor
  · exact hdecode_feasible copt hcopt.isFeasible
  · intro y hy
    rcases hcover y hy with ⟨c, hc, rfl⟩
    exact hcopt.le hc

/--
Finite-code minimizer existence.

This is the minimization analogue of `exists_isMaximizerOn_of_finite_code`.
-/
theorem exists_isMinimizerOn_of_finite_code
    {Code α : Type*} [Fintype Code]
    (codeFeasible : Code → Prop) [DecidablePred codeFeasible]
    (decode : Code → α) (feasible : α → Prop) (objective : α → ℝ)
    (hdecode_feasible : ∀ c, codeFeasible c → feasible (decode c))
    (hcover : ∀ x, feasible x → ∃ c, codeFeasible c ∧ decode c = x)
    (hnonempty : ∃ x, feasible x) :
    ∃ opt : α, IsMinimizerOn feasible objective opt := by
  classical
  have hcode_nonempty : ∃ c, codeFeasible c := by
    rcases hnonempty with ⟨x, hx⟩
    rcases hcover x hx with ⟨c, hc, _⟩
    exact ⟨c, hc⟩
  obtain ⟨copt, hcopt⟩ :=
    exists_isMinimizerOn_of_finite codeFeasible
      (fun c => objective (decode c)) hcode_nonempty
  refine ⟨decode copt, ?_⟩
  constructor
  · exact hdecode_feasible copt hcopt.isFeasible
  · intro y hy
    rcases hcover y hy with ⟨c, hc, rfl⟩
    exact hcopt.le hc

/--
The finite index predicate for a deterministic measurable argmin.  It asks
that a candidate's fixed finite enumeration index be in range and attain the
finite pointwise infimum of the score.

The explicit enumeration makes ties deterministic.  This is important when a
finite optimization routine is used inside a stochastic kernel: an arbitrary
existence choice need not depend measurably on its input state.
-/
noncomputable def finiteArgminIndexProperty
    {State Candidate : Type*} [Fintype Candidate] [Nonempty Candidate]
    (score : Candidate → State → ℝ) (state : State) (index : ℕ) : Prop :=
  if hindex : index < Fintype.card Candidate then
    score ((Fintype.equivFin Candidate).symm ⟨index, hindex⟩) state =
      ⨅ candidate : Candidate, score candidate state
  else False

/-- Every finite score family has an enumerated index attaining its infimum. -/
theorem exists_finiteArgminIndexProperty
    {State Candidate : Type*} [Fintype Candidate] [Nonempty Candidate]
    (score : Candidate → State → ℝ) (state : State) :
    ∃ index, finiteArgminIndexProperty score state index := by
  obtain ⟨candidate, hcandidate⟩ :=
    exists_eq_ciInf_of_finite (f := fun candidate : Candidate => score candidate state)
  refine ⟨(Fintype.equivFin Candidate candidate).val, ?_⟩
  unfold finiteArgminIndexProperty
  split
  · simpa using hcandidate
  · rename_i hnot
    exact False.elim (hnot (Fintype.equivFin Candidate candidate).isLt)

/-- The least enumerated index attaining the finite pointwise infimum. -/
noncomputable def measurableFiniteArgminIndex
    {State Candidate : Type*} [Fintype Candidate] [Nonempty Candidate]
    (score : Candidate → State → ℝ) (state : State) : ℕ :=
  by
    classical
    exact Nat.find (exists_finiteArgminIndexProperty score state)

/-- The deterministic finite argmin obtained from `measurableFiniteArgminIndex`. -/
noncomputable def measurableFiniteArgmin
    {State Candidate : Type*} [Fintype Candidate] [Nonempty Candidate]
  (score : Candidate → State → ℝ) (state : State) : Candidate :=
  (Fintype.equivFin Candidate).symm
    ⟨measurableFiniteArgminIndex score state,
      by
        classical
        have hproperty : finiteArgminIndexProperty score state
            (measurableFiniteArgminIndex score state) := by
          simpa [measurableFiniteArgminIndex] using
            Nat.find_spec (exists_finiteArgminIndexProperty score state)
        by_cases hbound : measurableFiniteArgminIndex score state < Fintype.card Candidate
        · exact hbound
        · rw [finiteArgminIndexProperty, dif_neg hbound] at hproperty
          exact False.elim hproperty⟩

/-- The selected finite index is in the range of the candidate enumeration. -/
theorem measurableFiniteArgminIndex_lt
    {State Candidate : Type*} [Fintype Candidate] [Nonempty Candidate]
    (score : Candidate → State → ℝ) (state : State) :
    measurableFiniteArgminIndex score state < Fintype.card Candidate := by
  classical
  have hproperty : finiteArgminIndexProperty score state
      (measurableFiniteArgminIndex score state) := by
    simpa [measurableFiniteArgminIndex] using
      Nat.find_spec (exists_finiteArgminIndexProperty score state)
  by_contra hbound
  rw [finiteArgminIndexProperty, dif_neg hbound] at hproperty
  exact False.elim hproperty

/-- The deterministic finite argmin attains the pointwise finite infimum. -/
theorem measurableFiniteArgmin_spec
    {State Candidate : Type*} [Fintype Candidate] [Nonempty Candidate]
    (score : Candidate → State → ℝ) (state : State) :
    score (measurableFiniteArgmin score state) state =
      ⨅ candidate : Candidate, score candidate state := by
  classical
  have hproperty : finiteArgminIndexProperty score state
      (measurableFiniteArgminIndex score state) := by
    simpa [measurableFiniteArgminIndex] using
      Nat.find_spec (exists_finiteArgminIndexProperty score state)
  rw [finiteArgminIndexProperty,
    dif_pos (measurableFiniteArgminIndex_lt score state)] at hproperty
  simpa [measurableFiniteArgmin] using hproperty

/-- The deterministic finite argmin has score no larger than every candidate. -/
theorem measurableFiniteArgmin_isMin
    {State Candidate : Type*} [Fintype Candidate] [Nonempty Candidate]
    (score : Candidate → State → ℝ) (state : State) (candidate : Candidate) :
    score (measurableFiniteArgmin score state) state ≤ score candidate state := by
  rw [measurableFiniteArgmin_spec score state]
  exact ciInf_le (Finite.bddBelow_range (fun candidate : Candidate => score candidate state))
    candidate

/-- The finite argmin index predicate is measurable when every score is. -/
theorem measurableSet_finiteArgminIndexProperty
    {State Candidate : Type*} [MeasurableSpace State]
    [Fintype Candidate] [Nonempty Candidate]
    (score : Candidate → State → ℝ) (hscore : ∀ candidate, Measurable (score candidate))
    (index : ℕ) :
    MeasurableSet {state | finiteArgminIndexProperty score state index} := by
  classical
  by_cases hindex : index < Fintype.card Candidate
  · simpa [finiteArgminIndexProperty, hindex] using
      (measurableSet_eq_fun (hscore ((Fintype.equivFin Candidate).symm ⟨index, hindex⟩))
        (Measurable.iInf hscore))
  · simp [finiteArgminIndexProperty, hindex]

/-- The least finite argmin index is measurable in its state. -/
theorem measurable_measurableFiniteArgminIndex
    {State Candidate : Type*} [MeasurableSpace State]
    [Fintype Candidate] [Nonempty Candidate]
    (score : Candidate → State → ℝ) (hscore : ∀ candidate, Measurable (score candidate)) :
    Measurable (measurableFiniteArgminIndex score) := by
  classical
  simpa [measurableFiniteArgminIndex] using
    (measurable_find (fun state => exists_finiteArgminIndexProperty score state)
      (fun index => measurableSet_finiteArgminIndexProperty score hscore index))

/--
The deterministic finite argmin is measurable whenever the finite candidate
space is discrete and each score is measurable in the input state.
-/
theorem measurable_measurableFiniteArgmin
    {State Candidate : Type*} [MeasurableSpace State] [MeasurableSpace Candidate]
    [MeasurableSingletonClass Candidate] [Fintype Candidate] [Nonempty Candidate]
    (score : Candidate → State → ℝ) (hscore : ∀ candidate, Measurable (score candidate)) :
    Measurable (measurableFiniteArgmin score) := by
  classical
  have hindex : Measurable (fun state =>
      (⟨measurableFiniteArgminIndex score state,
        measurableFiniteArgminIndex_lt score state⟩ : Fin (Fintype.card Candidate))) :=
    measurable_to_countable' fun index => by
      have hnat : MeasurableSet {state |
          measurableFiniteArgminIndex score state = index.val} := by
        exact (measurable_measurableFiniteArgminIndex score hscore)
          (measurableSet_singleton index.val)
      convert hnat using 1
      ext state
      constructor
      · intro heq
        exact congrArg Fin.val heq
      · intro heq
        exact Fin.ext heq
  simpa [measurableFiniteArgmin] using
    (measurable_of_finite (Fintype.equivFin Candidate).symm).comp hindex

end Optimization
end AppliedModelingLib
