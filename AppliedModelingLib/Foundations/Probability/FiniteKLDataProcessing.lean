import AppliedModelingLib.Foundations.Probability.FiniteKL
import AppliedModelingLib.Foundations.Probability.Kernel

/-!
# Finite KL data processing

Finite log-sum inequalities and their consequences for the Kullback--Leibler
divergence of probability mass functions.
-/

open scoped BigOperators

namespace AppliedModelingLib

/-- The finite log-sum inequality for nonnegative masses.  The reference
total is positive and the first mass vanishes wherever the reference mass
does, which is the unnormalised form of absolute continuity. -/
theorem finite_log_sum_inequality
    {Atom : Type*} [Fintype Atom]
    (firstMass referenceMass : Atom → ℝ)
    (hfirst_nonneg : ∀ atom, 0 ≤ firstMass atom)
    (href_nonneg : ∀ atom, 0 ≤ referenceMass atom)
    (hcontinuous : ∀ atom, referenceMass atom = 0 → firstMass atom = 0)
    (href_total_pos : 0 < ∑ atom : Atom, referenceMass atom) :
    (∑ atom : Atom, firstMass atom) *
        (Real.log (∑ atom : Atom, firstMass atom) -
          Real.log (∑ atom : Atom, referenceMass atom)) ≤
      ∑ atom : Atom,
        firstMass atom * (Real.log (firstMass atom) - Real.log (referenceMass atom)) := by
  classical
  let firstTotal : ℝ := ∑ atom : Atom, firstMass atom
  let referenceTotal : ℝ := ∑ atom : Atom, referenceMass atom
  let weight : Atom → ℝ := fun atom => referenceMass atom / referenceTotal
  let point : Atom → ℝ := fun atom =>
    if referenceMass atom = 0 then 0 else firstMass atom / referenceMass atom
  have href_total_ne : referenceTotal ≠ 0 := by
    exact (show 0 < referenceTotal by simpa [referenceTotal] using href_total_pos).ne'
  have hweight_nonneg : ∀ atom ∈ (Finset.univ : Finset Atom), 0 ≤ weight atom := by
    intro atom _
    exact div_nonneg (href_nonneg atom)
      (show 0 ≤ referenceTotal by simpa [referenceTotal] using href_total_pos.le)
  have hweight_sum : ∑ atom ∈ (Finset.univ : Finset Atom), weight atom = 1 := by
    change (∑ atom : Atom, referenceMass atom / referenceTotal) = 1
    rw [← Finset.sum_div]
    exact div_self href_total_ne
  have hpoint_nonneg : ∀ atom ∈ (Finset.univ : Finset Atom), point atom ∈ Set.Ici (0 : ℝ) := by
    intro atom _
    unfold point
    split
    · simp
    · exact div_nonneg (hfirst_nonneg atom) (href_nonneg atom)
  have hjensen :
      (fun x : ℝ => x * Real.log x) (∑ atom : Atom, weight atom * point atom) ≤
        ∑ atom : Atom, weight atom * ((fun x : ℝ => x * Real.log x) (point atom)) :=
    Real.convexOn_mul_log.map_sum_le hweight_nonneg hweight_sum hpoint_nonneg
  have hmean : (∑ atom : Atom, weight atom * point atom) = firstTotal / referenceTotal := by
    calc
      (∑ atom : Atom, weight atom * point atom) =
          ∑ atom : Atom, firstMass atom / referenceTotal := by
            refine Finset.sum_congr rfl fun atom _ => ?_
            unfold weight point
            by_cases href_zero : referenceMass atom = 0
            · rw [href_zero, hcontinuous atom href_zero]
              simp
            · rw [if_neg href_zero]
              field_simp [href_zero, href_total_ne]
      _ = firstTotal / referenceTotal := by
        rw [← Finset.sum_div]
  have hright :
      (∑ atom : Atom, weight atom * ((fun x : ℝ => x * Real.log x) (point atom))) =
        (1 / referenceTotal) *
          ∑ atom : Atom,
            firstMass atom * (Real.log (firstMass atom) - Real.log (referenceMass atom)) := by
    calc
      (∑ atom : Atom, weight atom * ((fun x : ℝ => x * Real.log x) (point atom))) =
          ∑ atom : Atom,
            (1 / referenceTotal) *
              (firstMass atom *
                (Real.log (firstMass atom) - Real.log (referenceMass atom))) := by
            refine Finset.sum_congr rfl fun atom _ => ?_
            unfold weight point
            by_cases href_zero : referenceMass atom = 0
            · rw [href_zero, hcontinuous atom href_zero]
              simp
            · rw [if_neg href_zero]
              by_cases hfirst_zero : firstMass atom = 0
              · simp [hfirst_zero]
              · change referenceMass atom / referenceTotal *
                    ((firstMass atom / referenceMass atom) *
                      Real.log (firstMass atom / referenceMass atom)) = _
                rw [Real.log_div hfirst_zero href_zero]
                field_simp [href_zero, href_total_ne]
      _ = (1 / referenceTotal) *
          ∑ atom : Atom,
            firstMass atom * (Real.log (firstMass atom) - Real.log (referenceMass atom)) := by
        rw [Finset.mul_sum]
  rw [hmean, hright] at hjensen
  have hscaled := mul_le_mul_of_nonneg_left hjensen
    (show 0 ≤ referenceTotal by simpa [referenceTotal] using href_total_pos.le)
  have hleft_scale :
      referenceTotal *
          ((firstTotal / referenceTotal) * Real.log (firstTotal / referenceTotal)) =
        firstTotal * Real.log (firstTotal / referenceTotal) := by
    field_simp [href_total_ne]
  have hright_scale :
      referenceTotal *
          ((1 / referenceTotal) *
            ∑ atom : Atom,
              firstMass atom *
                (Real.log (firstMass atom) - Real.log (referenceMass atom))) =
        ∑ atom : Atom,
          firstMass atom *
            (Real.log (firstMass atom) - Real.log (referenceMass atom)) := by
    field_simp [href_total_ne]
  rw [hleft_scale, hright_scale] at hscaled
  have hlog :
      firstTotal * (Real.log firstTotal - Real.log referenceTotal) =
        firstTotal * Real.log (firstTotal / referenceTotal) := by
    by_cases hfirst_total_zero : firstTotal = 0
    · simp [hfirst_total_zero]
    · rw [Real.log_div hfirst_total_zero href_total_ne]
  simpa only [firstTotal, referenceTotal] using hlog.trans_le hscaled

/-- The real mass at an atom of a finite PMF pushforward is the sum of the
real input masses in that atom's fiber. -/
theorem pmfMap_apply_toReal
    {Input Output : Type*} [Fintype Input] [DecidableEq Input]
    [Fintype Output] [DecidableEq Output]
    (law : PMF Input) (map : Input → Output) (output : Output) :
    ((law.map map) output).toReal =
      ∑ input : Input, if output = map input then (law input).toReal else 0 := by
  classical
  have hne_top : ∀ input ∈ (Finset.univ : Finset Input),
      (if output = map input then law input else 0) ≠ ⊤ := by
    intro input _
    split
    · exact law.apply_ne_top input
    · simp
  calc
    ((law.map map) output).toReal =
        (∑ input : Input, if output = map input then law input else 0).toReal := by
          rw [PMF.map_apply, tsum_fintype]
          apply congrArg ENNReal.toReal
          refine Finset.sum_congr rfl fun input _ => ?_
          by_cases hmap : output = map input <;> simp [hmap]
    _ = ∑ input : Input,
        (if output = map input then law input else 0).toReal := by
          exact ENNReal.toReal_sum (s := (Finset.univ : Finset Input))
            (f := fun input : Input => if output = map input then law input else 0) hne_top
    _ = ∑ input : Input, if output = map input then (law input).toReal else 0 := by
      refine Finset.sum_congr rfl fun input _ => ?_
      split <;> simp [*]

/-- Absolute continuity is preserved by deterministic finite
post-processing. -/
theorem PMFAbsoluteContinuous.map
    {Input Output : Type*} [Fintype Input] [DecidableEq Input]
    [Fintype Output] [DecidableEq Output]
    {first second : PMF Input} (hcontinuous : PMFAbsoluteContinuous first second)
    (map : Input → Output) :
    PMFAbsoluteContinuous (first.map map) (second.map map) := by
  intro output hfirst
  rw [pmfMap_apply_toReal] at hfirst ⊢
  by_contra hsecond_not_pos
  have hsecond_zero :
      (∑ input : Input, if output = map input then (second input).toReal else 0) = 0 :=
    le_antisymm (le_of_not_gt hsecond_not_pos)
      (Finset.sum_nonneg fun input _ => by split <;> simp [ENNReal.toReal_nonneg])
  have hfirst_zero :
      (∑ input : Input, if output = map input then (first input).toReal else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro input _
    by_cases hmap : output = map input
    · rw [if_pos hmap]
      have hsecond_atom_zero : (second input).toReal = 0 := by
        have hterm_le : (second input).toReal ≤
            ∑ other : Input, if output = map other then (second other).toReal else 0 := by
          have hsum := Finset.single_le_sum
            (s := (Finset.univ : Finset Input))
            (f := fun other => if output = map other then (second other).toReal else 0)
            (fun other _ => by
              by_cases hother : output = map other <;> simp [hother, ENNReal.toReal_nonneg])
            (Finset.mem_univ input)
          simpa [hmap] using hsum
        rw [hsecond_zero] at hterm_le
        exact le_antisymm hterm_le ENNReal.toReal_nonneg
      have hfirst_atom_not_pos : ¬ 0 < (first input).toReal := by
        intro hfirst_atom
        have hsecond_atom := hcontinuous input hfirst_atom
        rw [hsecond_atom_zero] at hsecond_atom
        exact lt_irrefl _ hsecond_atom
      exact le_antisymm (le_of_not_gt hfirst_atom_not_pos) ENNReal.toReal_nonneg
    · simp [hmap]
  rw [hfirst_zero] at hfirst
  exact lt_irrefl _ hfirst

/-- Deterministic finite post-processing cannot increase KL divergence. -/
theorem finiteKLDivergence_map_le
    {Input Output : Type*} [Fintype Input] [DecidableEq Input]
    [Fintype Output] [DecidableEq Output]
    (first second : PMF Input) (hcontinuous : PMFAbsoluteContinuous first second)
    (map : Input → Output) :
    finiteKLDivergence (first.map map) (second.map map) ≤
      finiteKLDivergence first second := by
  classical
  have hmapContinuous := hcontinuous.map map
  unfold finiteKLDivergence
  calc
    ∑ output : Output,
        ((first.map map) output).toReal *
          (Real.log ((first.map map) output).toReal -
            Real.log ((second.map map) output).toReal) ≤
        ∑ output : Output, ∑ input : Input,
          if output = map input then
            (first input).toReal *
              (Real.log (first input).toReal - Real.log (second input).toReal)
          else 0 := by
      refine Finset.sum_le_sum fun output _ => ?_
      let firstMass : Input → ℝ := fun input =>
        if output = map input then (first input).toReal else 0
      let secondMass : Input → ℝ := fun input =>
        if output = map input then (second input).toReal else 0
      have hfirst_nonneg : ∀ input, 0 ≤ firstMass input := by
        intro input
        unfold firstMass
        split <;> simp [ENNReal.toReal_nonneg]
      have hsecond_nonneg : ∀ input, 0 ≤ secondMass input := by
        intro input
        unfold secondMass
        split <;> simp [ENNReal.toReal_nonneg]
      have hcontinuousMass : ∀ input, secondMass input = 0 → firstMass input = 0 := by
        intro input hsecond
        dsimp [firstMass, secondMass] at hsecond ⊢
        by_cases hmap : output = map input
        · rw [if_pos hmap] at hsecond ⊢
          have hfirst_not_pos : ¬ 0 < (first input).toReal := by
            intro hfirst_pos
            have hsecond_pos := hcontinuous input hfirst_pos
            rw [hsecond] at hsecond_pos
            exact lt_irrefl _ hsecond_pos
          exact le_antisymm (le_of_not_gt hfirst_not_pos) ENNReal.toReal_nonneg
        · simp [hmap]
      have hfirst_total : (∑ input : Input, firstMass input) =
          ((first.map map) output).toReal := by
        rw [pmfMap_apply_toReal]
      have hsecond_total : (∑ input : Input, secondMass input) =
          ((second.map map) output).toReal := by
        rw [pmfMap_apply_toReal]
      have hright :
          (∑ input : Input,
            firstMass input * (Real.log (firstMass input) - Real.log (secondMass input))) =
          ∑ input : Input,
            if output = map input then
              (first input).toReal *
                (Real.log (first input).toReal - Real.log (second input).toReal)
            else 0 := by
        refine Finset.sum_congr rfl fun input _ => ?_
        unfold firstMass secondMass
        by_cases hmap : output = map input <;> simp [hmap]
      rw [← hfirst_total, ← hsecond_total]
      by_cases hsecond_total_pos : 0 < ∑ input : Input, secondMass input
      · rw [← hright]
        exact finite_log_sum_inequality firstMass secondMass hfirst_nonneg hsecond_nonneg
          hcontinuousMass hsecond_total_pos
      · have hfirst_total_zero : (∑ input : Input, firstMass input) = 0 := by
          have hfirst_not_pos : ¬ 0 < ∑ input : Input, firstMass input := by
            intro hfirst_pos
            have hsecond_pos := hmapContinuous output (by simpa [hfirst_total] using hfirst_pos)
            exact hsecond_total_pos (by simpa [hsecond_total] using hsecond_pos)
          exact le_antisymm (le_of_not_gt hfirst_not_pos)
            (Finset.sum_nonneg fun input _ => hfirst_nonneg input)
        have hfirst_mass_zero : ∀ input, firstMass input = 0 := by
          intro input
          have hterm_le : firstMass input ≤ ∑ other : Input, firstMass other :=
            Finset.single_le_sum (fun other _ => hfirst_nonneg other) (Finset.mem_univ input)
          rw [hfirst_total_zero] at hterm_le
          exact le_antisymm hterm_le (hfirst_nonneg input)
        rw [← hright]
        simp [hfirst_mass_zero]
    _ = ∑ input : Input,
        (first input).toReal *
          (Real.log (first input).toReal - Real.log (second input).toReal) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun input _ => ?_
      simp

/-- The real mass at an output atom of a finite PMF bind is the corresponding
finite mixture of the kernel rows. -/
theorem pmfBind_apply_toReal
    {Input Output : Type*} [Fintype Input] [DecidableEq Input]
    [Fintype Output] [DecidableEq Output]
    (distribution : PMF Input) (kernel : Input → PMF Output) (output : Output) :
    ((distribution.bind kernel) output).toReal =
      ∑ input : Input, (distribution input).toReal * (kernel input output).toReal := by
  classical
  have hne_top : ∀ input ∈ (Finset.univ : Finset Input),
      distribution input * kernel input output ≠ ⊤ := by
    intro input _
    exact ENNReal.mul_ne_top (distribution.apply_ne_top input)
      ((kernel input).apply_ne_top output)
  calc
    ((distribution.bind kernel) output).toReal =
        (∑ input : Input, distribution input * kernel input output).toReal := by
          rw [PMF.bind_apply, tsum_fintype]
    _ = ∑ input : Input, (distribution input * kernel input output).toReal := by
          exact ENNReal.toReal_sum (s := (Finset.univ : Finset Input))
            (f := fun input : Input => distribution input * kernel input output) hne_top
    _ = ∑ input : Input, (distribution input).toReal * (kernel input output).toReal := by
          simp [ENNReal.toReal_mul]

/-- Absolute continuity is preserved by arbitrary finite randomized
post-processing. -/
theorem PMFAbsoluteContinuous.bind
    {Input Output : Type*} [Fintype Input] [DecidableEq Input]
    [Fintype Output] [DecidableEq Output]
    {first second : PMF Input} (hcontinuous : PMFAbsoluteContinuous first second)
    (kernel : Input → PMF Output) :
    PMFAbsoluteContinuous (first.bind kernel) (second.bind kernel) := by
  intro output hfirst
  have hfirstENN : 0 < (first.bind kernel) output :=
    (ENNReal.toReal_pos_iff.mp hfirst).1
  have hfirstSupport : output ∈ (first.bind kernel).support :=
    (PMF.mem_support_iff _ _).2 (ne_of_gt hfirstENN)
  rcases (PMF.mem_support_bind_iff first kernel output).mp hfirstSupport with
    ⟨input, hinputFirst, hkernel⟩
  have hinputFirstReal : 0 < (first input).toReal :=
    ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hinputFirst) (first.apply_ne_top input)
  have hinputSecondReal : 0 < (second input).toReal :=
    hcontinuous input hinputFirstReal
  have hinputSecondENN : 0 < second input :=
    (ENNReal.toReal_pos_iff.mp hinputSecondReal).1
  have hsecondSupport : output ∈ (second.bind kernel).support := by
    rw [PMF.mem_support_bind_iff]
    exact ⟨input, (PMF.mem_support_iff _ _).2 (ne_of_gt hinputSecondENN), hkernel⟩
  exact ENNReal.toReal_pos
    ((PMF.mem_support_iff _ _).mp hsecondSupport)
    ((second.bind kernel).apply_ne_top output)

/-- Absolute continuity is also preserved when both a finite input law and
its transition kernel change, provided every matched kernel row is absolutely
continuous. -/
theorem PMFAbsoluteContinuous.bind_of_pointwise
    {Input Output : Type*} [Fintype Input] [DecidableEq Input]
    [Fintype Output] [DecidableEq Output]
    {first second : PMF Input} (hprior : PMFAbsoluteContinuous first second)
    (firstKernel secondKernel : Input → PMF Output)
    (hkernel : ∀ input, PMFAbsoluteContinuous (firstKernel input) (secondKernel input)) :
    PMFAbsoluteContinuous (first.bind firstKernel) (second.bind secondKernel) := by
  intro output hfirst
  have hfirstENN : 0 < (first.bind firstKernel) output :=
    (ENNReal.toReal_pos_iff.mp hfirst).1
  have hfirstSupport : output ∈ (first.bind firstKernel).support :=
    (PMF.mem_support_iff _ _).2 (ne_of_gt hfirstENN)
  rcases (PMF.mem_support_bind_iff first firstKernel output).mp hfirstSupport with
    ⟨input, hinputFirst, hkernelFirst⟩
  have hinputFirstReal : 0 < (first input).toReal :=
    ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hinputFirst) (first.apply_ne_top input)
  have hinputSecondReal : 0 < (second input).toReal := hprior input hinputFirstReal
  have hinputSecondENN : 0 < second input :=
    (ENNReal.toReal_pos_iff.mp hinputSecondReal).1
  have hkernelSecond : output ∈ (secondKernel input).support := by
    apply (PMF.mem_support_iff _ _).2
    have hkernelFirstReal : 0 < (firstKernel input output).toReal :=
      ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hkernelFirst)
        ((firstKernel input).apply_ne_top output)
    exact ne_of_gt (ENNReal.toReal_pos_iff.mp (hkernel input output hkernelFirstReal)).1
  have hsecondSupport : output ∈ (second.bind secondKernel).support := by
    rw [PMF.mem_support_bind_iff]
    exact ⟨input, (PMF.mem_support_iff _ _).2 (ne_of_gt hinputSecondENN), hkernelSecond⟩
  exact ENNReal.toReal_pos
    ((PMF.mem_support_iff _ _).mp hsecondSupport)
    ((second.bind secondKernel).apply_ne_top output)

/-- Arbitrary finite randomized post-processing cannot increase KL
divergence. -/
theorem finiteKLDivergence_bind_le
    {Input Output : Type*} [Fintype Input] [DecidableEq Input]
    [Fintype Output] [DecidableEq Output]
    (first second : PMF Input) (hcontinuous : PMFAbsoluteContinuous first second)
    (kernel : Input → PMF Output) :
    finiteKLDivergence (first.bind kernel) (second.bind kernel) ≤
      finiteKLDivergence first second := by
  classical
  have hbindContinuous := hcontinuous.bind kernel
  unfold finiteKLDivergence
  calc
    ∑ output : Output,
        ((first.bind kernel) output).toReal *
          (Real.log ((first.bind kernel) output).toReal -
            Real.log ((second.bind kernel) output).toReal) ≤
        ∑ output : Output, ∑ input : Input,
          ((first input).toReal * (kernel input output).toReal) *
            (Real.log ((first input).toReal * (kernel input output).toReal) -
              Real.log ((second input).toReal * (kernel input output).toReal)) := by
      refine Finset.sum_le_sum fun output _ => ?_
      let firstMass : Input → ℝ := fun input =>
        (first input).toReal * (kernel input output).toReal
      let secondMass : Input → ℝ := fun input =>
        (second input).toReal * (kernel input output).toReal
      have hfirst_nonneg : ∀ input, 0 ≤ firstMass input := by
        intro input
        exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      have hsecond_nonneg : ∀ input, 0 ≤ secondMass input := by
        intro input
        exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      have hcontinuousMass : ∀ input, secondMass input = 0 → firstMass input = 0 := by
        intro input hsecond
        dsimp [firstMass, secondMass] at hsecond ⊢
        rcases mul_eq_zero.mp hsecond with hsecond_atom | hkernel_zero
        · have hfirst_not_pos : ¬ 0 < (first input).toReal := by
            intro hfirst_pos
            have hsecond_pos := hcontinuous input hfirst_pos
            rw [hsecond_atom] at hsecond_pos
            exact lt_irrefl _ hsecond_pos
          rw [le_antisymm (le_of_not_gt hfirst_not_pos) ENNReal.toReal_nonneg]
          ring
        · rw [hkernel_zero]
          ring
      have hfirst_total : (∑ input : Input, firstMass input) =
          ((first.bind kernel) output).toReal := by
        rw [pmfBind_apply_toReal]
      have hsecond_total : (∑ input : Input, secondMass input) =
          ((second.bind kernel) output).toReal := by
        rw [pmfBind_apply_toReal]
      rw [← hfirst_total, ← hsecond_total]
      by_cases hsecond_total_pos : 0 < ∑ input : Input, secondMass input
      · exact finite_log_sum_inequality firstMass secondMass hfirst_nonneg hsecond_nonneg
          hcontinuousMass hsecond_total_pos
      · have hfirst_total_zero : (∑ input : Input, firstMass input) = 0 := by
          have hfirst_not_pos : ¬ 0 < ∑ input : Input, firstMass input := by
            intro hfirst_pos
            have hsecond_pos := hbindContinuous output (by simpa [hfirst_total] using hfirst_pos)
            exact hsecond_total_pos (by simpa [hsecond_total] using hsecond_pos)
          exact le_antisymm (le_of_not_gt hfirst_not_pos)
            (Finset.sum_nonneg fun input _ => hfirst_nonneg input)
        have hfirst_mass_zero : ∀ input, firstMass input = 0 := by
          intro input
          have hterm_le : firstMass input ≤ ∑ other : Input, firstMass other :=
            Finset.single_le_sum (fun other _ => hfirst_nonneg other) (Finset.mem_univ input)
          rw [hfirst_total_zero] at hterm_le
          exact le_antisymm hterm_le (hfirst_nonneg input)
        have hright_zero :
            (∑ input : Input,
              ((first input).toReal * (kernel input output).toReal) *
                (Real.log ((first input).toReal * (kernel input output).toReal) -
                  Real.log ((second input).toReal * (kernel input output).toReal))) = 0 := by
          apply Finset.sum_eq_zero
          intro input _
          have hmass_zero := hfirst_mass_zero input
          dsimp [firstMass] at hmass_zero
          rw [hmass_zero]
          ring
        rw [hfirst_total_zero, hright_zero]
        norm_num
    _ = ∑ input : Input, ∑ output : Output,
        ((first input).toReal * (kernel input output).toReal) *
          (Real.log ((first input).toReal * (kernel input output).toReal) -
            Real.log ((second input).toReal * (kernel input output).toReal)) := by
      exact Finset.sum_comm
    _ = ∑ input : Input,
        ((first input).toReal *
          (Real.log (first input).toReal - Real.log (second input).toReal)) *
          ∑ output : Output, (kernel input output).toReal := by
      refine Finset.sum_congr rfl fun input _ => ?_
      calc
        ∑ output : Output,
            (first input).toReal * (kernel input output).toReal *
              (Real.log ((first input).toReal * (kernel input output).toReal) -
                Real.log ((second input).toReal * (kernel input output).toReal)) =
            ∑ output : Output,
              ((first input).toReal *
                (Real.log (first input).toReal - Real.log (second input).toReal)) *
                (kernel input output).toReal := by
              refine Finset.sum_congr rfl fun output _ => ?_
              by_cases hkernel_zero : (kernel input output).toReal = 0
              · simp [hkernel_zero]
              · by_cases hfirst_zero : (first input).toReal = 0
                · simp [hfirst_zero]
                · have hfirst_pos : 0 < (first input).toReal :=
                    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hfirst_zero)
                  have hsecond_pos : 0 < (second input).toReal := hcontinuous input hfirst_pos
                  rw [Real.log_mul hfirst_zero hkernel_zero,
                    Real.log_mul hsecond_pos.ne' hkernel_zero]
                  ring
        _ = ((first input).toReal *
            (Real.log (first input).toReal - Real.log (second input).toReal)) *
            ∑ output : Output, (kernel input output).toReal := by
              rw [Finset.mul_sum]
    _ = ∑ input : Input,
        (first input).toReal *
          (Real.log (first input).toReal - Real.log (second input).toReal) := by
      refine Finset.sum_congr rfl fun input _ => ?_
      rw [pmfToRealSum (kernel input)]
      ring

/-- The finite KL chain rule for two joint laws formed from a prior and a
conditional kernel. -/
theorem finiteKLDivergence_kernelJoint_chain_rule
    {Input Output : Type*} [Fintype Input] [DecidableEq Input]
    [Fintype Output] [DecidableEq Output]
    (firstPrior secondPrior : PMF Input)
    (hprior : PMFAbsoluteContinuous firstPrior secondPrior)
    (firstKernel secondKernel : Input → PMF Output)
    (hkernel : ∀ input, PMFAbsoluteContinuous (firstKernel input) (secondKernel input)) :
    finiteKLDivergence (pmfKernelJoint firstPrior firstKernel)
        (pmfKernelJoint secondPrior secondKernel) =
      finiteKLDivergence firstPrior secondPrior +
        pmfExp firstPrior (fun input =>
          finiteKLDivergence (firstKernel input) (secondKernel input)) := by
  classical
  unfold finiteKLDivergence pmfExp
  rw [Fintype.sum_prod_type]
  calc
    ∑ input : Input, ∑ output : Output,
        (pmfKernelJoint firstPrior firstKernel (input, output)).toReal *
          (Real.log (pmfKernelJoint firstPrior firstKernel (input, output)).toReal -
            Real.log (pmfKernelJoint secondPrior secondKernel (input, output)).toReal) =
        ∑ input : Input, ∑ output : Output,
          ((firstPrior input).toReal * (firstKernel input output).toReal) *
            (Real.log ((firstPrior input).toReal * (firstKernel input output).toReal) -
              Real.log ((secondPrior input).toReal * (secondKernel input output).toReal)) := by
          refine Finset.sum_congr rfl fun input _ => ?_
          refine Finset.sum_congr rfl fun output _ => ?_
          simp [pmfKernelJoint_apply, ENNReal.toReal_mul]
    _ = ∑ input : Input, ∑ output : Output,
          (((firstPrior input).toReal *
            (Real.log (firstPrior input).toReal - Real.log (secondPrior input).toReal)) *
              (firstKernel input output).toReal +
            (firstPrior input).toReal *
              ((firstKernel input output).toReal *
                (Real.log (firstKernel input output).toReal -
                  Real.log (secondKernel input output).toReal))) := by
          refine Finset.sum_congr rfl fun input _ => ?_
          refine Finset.sum_congr rfl fun output _ => ?_
          by_cases hprior_zero : (firstPrior input).toReal = 0
          · simp [hprior_zero]
          · by_cases hkernel_zero : (firstKernel input output).toReal = 0
            · simp [hkernel_zero]
            · have hprior_pos : 0 < (firstPrior input).toReal :=
                lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hprior_zero)
              have hsecond_prior_pos : 0 < (secondPrior input).toReal :=
                hprior input hprior_pos
              have hkernel_pos : 0 < (firstKernel input output).toReal :=
                lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hkernel_zero)
              have hsecond_kernel_pos : 0 < (secondKernel input output).toReal :=
                hkernel input output hkernel_pos
              rw [Real.log_mul hprior_zero hkernel_zero,
                Real.log_mul hsecond_prior_pos.ne' hsecond_kernel_pos.ne']
              ring
    _ = ∑ input : Input,
          (((firstPrior input).toReal *
            (Real.log (firstPrior input).toReal - Real.log (secondPrior input).toReal)) *
              ∑ output : Output, (firstKernel input output).toReal +
            (firstPrior input).toReal *
              ∑ output : Output,
                (firstKernel input output).toReal *
                  (Real.log (firstKernel input output).toReal -
                    Real.log (secondKernel input output).toReal)) := by
          refine Finset.sum_congr rfl fun input _ => ?_
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (∑ input : Input,
          (firstPrior input).toReal *
            (Real.log (firstPrior input).toReal - Real.log (secondPrior input).toReal)) +
        ∑ input : Input, (firstPrior input).toReal *
          ∑ output : Output,
            (firstKernel input output).toReal *
              (Real.log (firstKernel input output).toReal -
                Real.log (secondKernel input output).toReal) := by
          rw [Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun input _ => ?_
          rw [pmfToRealSum (firstKernel input)]
          ring
    _ = finiteKLDivergence firstPrior secondPrior +
        pmfExp firstPrior (fun input =>
          finiteKLDivergence (firstKernel input) (secondKernel input)) := by
          rfl

/-- Absolute continuity of a prior and each conditional row gives absolute
continuity of the corresponding finite joint laws. -/
theorem PMFAbsoluteContinuous.kernelJoint
    {Input Output : Type*} [Fintype Input] [DecidableEq Input]
    [Fintype Output] [DecidableEq Output]
    {firstPrior secondPrior : PMF Input}
    (hprior : PMFAbsoluteContinuous firstPrior secondPrior)
    (firstKernel secondKernel : Input → PMF Output)
    (hkernel : ∀ input, PMFAbsoluteContinuous (firstKernel input) (secondKernel input)) :
    PMFAbsoluteContinuous (pmfKernelJoint firstPrior firstKernel)
      (pmfKernelJoint secondPrior secondKernel) := by
  intro pair hfirst
  rw [pmfKernelJoint_apply, ENNReal.toReal_mul] at hfirst ⊢
  have hfirst_prior_pos : 0 < (firstPrior pair.1).toReal := by
    by_contra hnot
    have hzero : (firstPrior pair.1).toReal = 0 :=
      le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
    rw [hzero] at hfirst
    simp at hfirst
  have hfirst_kernel_pos : 0 < (firstKernel pair.1 pair.2).toReal := by
    by_contra hnot
    have hzero : (firstKernel pair.1 pair.2).toReal = 0 :=
      le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
    rw [hzero] at hfirst
    simp at hfirst
  exact mul_pos (hprior pair.1 hfirst_prior_pos)
    (hkernel pair.1 pair.2 hfirst_kernel_pos)

/-- Marginalizing the second coordinate of a finite prior/kernel joint law is
definitionally the ordinary PMF bind by that kernel. -/
theorem pmfKernelSignalMarginal_eq_bind
    {Input Output : Type*} [Fintype Input] [DecidableEq Input]
    [Fintype Output] [DecidableEq Output]
    (prior : PMF Input) (kernel : Input → PMF Output) :
    pmfKernelSignalMarginal prior kernel = prior.bind kernel := by
  apply PMF.ext
  intro output
  apply (ENNReal.toReal_eq_toReal_iff'
    ((pmfKernelSignalMarginal prior kernel).apply_ne_top output)
    ((prior.bind kernel).apply_ne_top output)).mp
  rw [pmfKernelSignalMarginal_apply, pmfBind_apply_toReal]
  have hne_top : ∀ input ∈ (Finset.univ : Finset Input),
      prior input * kernel input output ≠ ⊤ := by
    intro input _
    exact ENNReal.mul_ne_top (prior.apply_ne_top input) ((kernel input).apply_ne_top output)
  simpa [ENNReal.toReal_mul] using
    (ENNReal.toReal_sum (s := (Finset.univ : Finset Input))
      (f := fun input : Input => prior input * kernel input output) hne_top)

/-- When both the input law and the conditional kernel can change, the KL
cost of the output is at most the input KL plus the first-law average of the
conditional KL costs. -/
theorem finiteKLDivergence_bind_le_add_expected
    {Input Output : Type*} [Fintype Input] [DecidableEq Input]
    [Fintype Output] [DecidableEq Output]
    (firstPrior secondPrior : PMF Input)
    (hprior : PMFAbsoluteContinuous firstPrior secondPrior)
    (firstKernel secondKernel : Input → PMF Output)
    (hkernel : ∀ input, PMFAbsoluteContinuous (firstKernel input) (secondKernel input)) :
    finiteKLDivergence (firstPrior.bind firstKernel) (secondPrior.bind secondKernel) ≤
      finiteKLDivergence firstPrior secondPrior +
        pmfExp firstPrior (fun input =>
          finiteKLDivergence (firstKernel input) (secondKernel input)) := by
  have hjointContinuous := hprior.kernelJoint firstKernel secondKernel hkernel
  calc
    finiteKLDivergence (firstPrior.bind firstKernel) (secondPrior.bind secondKernel) =
        finiteKLDivergence
          ((pmfKernelJoint firstPrior firstKernel).map Prod.snd)
          ((pmfKernelJoint secondPrior secondKernel).map Prod.snd) := by
            change finiteKLDivergence (firstPrior.bind firstKernel)
              (secondPrior.bind secondKernel) =
              finiteKLDivergence (pmfKernelSignalMarginal firstPrior firstKernel)
                (pmfKernelSignalMarginal secondPrior secondKernel)
            rw [pmfKernelSignalMarginal_eq_bind, pmfKernelSignalMarginal_eq_bind]
    _ ≤ finiteKLDivergence (pmfKernelJoint firstPrior firstKernel)
          (pmfKernelJoint secondPrior secondKernel) :=
      finiteKLDivergence_map_le _ _ hjointContinuous Prod.snd
    _ = finiteKLDivergence firstPrior secondPrior +
        pmfExp firstPrior (fun input =>
          finiteKLDivergence (firstKernel input) (secondKernel input)) :=
      finiteKLDivergence_kernelJoint_chain_rule firstPrior secondPrior hprior
        firstKernel secondKernel hkernel

end AppliedModelingLib
