import LG21TestOptionalPolicies.StrictMonotoneCutoff

/-!
# Semantic binary-action cutoffs

This order-theoretic bridge turns a nontrivial upward-closed Boolean action
set on the real line into the finite cutoff rule it represents, up to its
single boundary point.  It deliberately refers only to the action relation,
not to a policy or function name.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set

/-- A nontrivial upward-closed Boolean action on real types is an upper-tail
rule almost everywhere under any atomless law.  The only possible ambiguity is
the single finite boundary point. -/
theorem lg21_bool_choice_eq_decide_upperTail_ae_of_upperClosed_nontrivial
    (law : Measure ℝ) [NoAtoms law]
    (decision : ℝ -> Bool)
    (hupper : ∀ ⦃low high : ℝ⦄,
      low ≤ high -> decision low = true -> decision high = true)
    (htrue : ∃ value, decision value = true)
    (hfalse : ∃ value, decision value = false) :
    ∃ cutoff : ℝ,
      ∀ᵐ value ∂law, decision value = decide (cutoff ≤ value) := by
  let chosen : Set ℝ := {value | decision value = true}
  rcases htrue with ⟨chosenValue, hchosenValue⟩
  rcases hfalse with ⟨unchosenValue, hunchosenValue⟩
  have hchosenNonempty : chosen.Nonempty := ⟨chosenValue, hchosenValue⟩
  have hbelow : ∀ value ∈ chosen, unchosenValue ≤ value := by
    intro value hvalue
    by_contra hnot
    have hlt : value < unchosenValue := lt_of_not_ge hnot
    have hcontradiction := hupper (le_of_lt hlt) hvalue
    rw [hunchosenValue] at hcontradiction
    simp at hcontradiction
  have hbounded : BddBelow chosen := ⟨unchosenValue, hbelow⟩
  refine ⟨sInf chosen, ?_⟩
  have hbelowCutoff : ∀ value, value < sInf chosen -> decision value = false := by
    intro value hvalue
    cases hdecision : decision value with
    | false => simpa [hdecision]
    | true =>
        have hmember : value ∈ chosen := hdecision
        have hcutoffLe : sInf chosen ≤ value := csInf_le hbounded hmember
        exact False.elim ((not_le_of_gt hvalue) hcutoffLe)
  have haboveCutoff : ∀ value, sInf chosen < value -> decision value = true := by
    intro value hvalue
    obtain ⟨chosenBelow, hmember, hchosenBelow⟩ :=
      exists_lt_of_csInf_lt hchosenNonempty hvalue
    exact hupper (le_of_lt hchosenBelow) hmember
  have hpoint : ∀ value, value ≠ sInf chosen ->
      decision value = decide (sInf chosen ≤ value) := by
    intro value hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hdecision := hbelowCutoff value hlt
      simp [hdecision, not_le_of_gt hlt]
    · have hdecision := haboveCutoff value hgt
      simp [hdecision, le_of_lt hgt]
  exact ae_of_forall_not_mem_null (μ := law) (measure_singleton (sInf chosen))
    (fun value hnotMember => hpoint value (by simpa using hnotMember))

/-- Fibrewise form of the semantic cutoff bridge.  A caller derives the
positive/negative action sides from its actual source law, then this theorem
turns those facts into finite cutoffs on almost every public-base fibre. -/
theorem lg21_ae_base_exists_upperTailCutoff_of_upperClosed_nontrivial
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) (skillKernel : Kernel Base ℝ)
    (decision : Base -> ℝ -> Bool)
    (hupper : ∀ publicBase ⦃low high : ℝ⦄,
      low ≤ high -> decision publicBase low = true ->
        decision publicBase high = true)
    (hnoAtoms : ∀ publicBase, NoAtoms (skillKernel publicBase))
    (hnontrivial : ∀ᵐ publicBase ∂baseLaw,
      (∃ skill, decision publicBase skill = true) ∧
        ∃ skill, decision publicBase skill = false) :
    ∀ᵐ publicBase ∂baseLaw,
      ∃ cutoff : ℝ,
        ∀ᵐ skill ∂skillKernel publicBase,
          decision publicBase skill = decide (cutoff ≤ skill) := by
  filter_upwards [hnontrivial] with publicBase hnontrivial
  letI : NoAtoms (skillKernel publicBase) := hnoAtoms publicBase
  exact lg21_bool_choice_eq_decide_upperTail_ae_of_upperClosed_nontrivial
    (skillKernel publicBase) (decision publicBase)
    (fun low high hle hlow => hupper publicBase hle hlow)
    hnontrivial.1 hnontrivial.2

end

end LG21TestOptionalPolicies
