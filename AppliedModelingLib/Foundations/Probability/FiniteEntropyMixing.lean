import AppliedModelingLib.Foundations.Probability.FiniteEntropy
import AppliedModelingLib.Foundations.Probability.ExponentialTilt

/-!
# Convexity of finite exponential functional entropy

The entropy tensorization induction needs convexity under a finite mixture.
This module proves the positive-exponential, full-support case by identifying
the convexity gap with a finite mutual-information KL divergence.  The
full-support restriction is explicit; support reduction is a separate bridge.
-/

namespace AppliedModelingLib

open scoped BigOperators

/-- A finite product of full-support PMFs has full support. -/
theorem pmfProd_fullSupport
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (first : PMF α) (second : PMF β)
    (hfirst : PMFFullSupport first) (hsecond : PMFFullSupport second) :
    PMFFullSupport (pmfProd first second) := by
  intro pair
  rw [pmfProd_apply_toReal]
  exact mul_pos (hfirst pair.1) (hsecond pair.2)

/-- Under a finite PMF, an everywhere-positive function has positive
expectation. -/
theorem pmfExp_pos_of_forall_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (law : PMF α) (value : α → ℝ) (hvalue : ∀ outcome, 0 < value outcome) :
    0 < pmfExp law value := by
  letI : Nonempty α := ⟨Classical.choose law.support_nonempty⟩
  exact pmfExp_pos_of_support_forall_pos law value
    (fun outcome _ => hvalue outcome)

/-- The finite entropy of an exponential weight is convex under a finite
mixture.  The proof is the nonnegativity of the KL divergence between the
tilted joint law and the product of its tilted marginals.  Zero-mass atoms
are handled through absolute continuity rather than a full-support premise. -/
theorem pmfFunctionalEntropy_exp_mixture_le
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (first : PMF α) (second : PMF β) (score : α → β → ℝ) :
    pmfFunctionalEntropy first (fun left =>
      pmfExp second (fun right => Real.exp (score left right))) ≤
      pmfExp second (fun right =>
        pmfFunctionalEntropy first (fun left => Real.exp (score left right))) := by
  let leftWeight : α → ℝ := fun left =>
    pmfExp second (fun right => Real.exp (score left right))
  let rightWeight : β → ℝ := fun right =>
    pmfExp first (fun left => Real.exp (score left right))
  let partition : ℝ := pmfExp first leftWeight
  let base : PMF (α × β) := pmfProd first second
  let joint : PMF (α × β) :=
    exponentialTilt base (fun pair => score pair.1 pair.2) 1
  let leftTilt : PMF α := exponentialTilt first (fun left => Real.log (leftWeight left)) 1
  let rightTilt : PMF β := exponentialTilt second (fun right => Real.log (rightWeight right)) 1
  have hleftWeight_pos (left : α) : 0 < leftWeight left := by
    unfold leftWeight
    exact pmfExp_pos_of_forall_pos second _ (fun right => Real.exp_pos _)
  have hrightWeight_pos (right : β) : 0 < rightWeight right := by
    unfold rightWeight
    exact pmfExp_pos_of_forall_pos first _ (fun left => Real.exp_pos _)
  have hpartition_pos : 0 < partition := by
    unfold partition
    exact pmfExp_pos_of_forall_pos first leftWeight hleftWeight_pos
  have hjoint_norm :
      Probability.finiteMGF base (fun pair => score pair.1 pair.2) 1 = partition := by
    unfold Probability.finiteMGF
    change pmfExp base (fun pair => Real.exp (1 * score pair.1 pair.2)) = partition
    unfold partition leftWeight base
    rw [pmfExp_pmfProd_eq_pairExp]
    unfold pmfPairExp
    apply pmfExp_congr
    intro left
    apply pmfExp_congr
    intro right
    simp
  have hleft_norm :
      Probability.finiteMGF first (fun left => Real.log (leftWeight left)) 1 = partition := by
    unfold Probability.finiteMGF partition
    apply pmfExp_congr
    intro left
    rw [one_mul, Real.exp_log (hleftWeight_pos left)]
  have hright_partition :
      pmfExp second rightWeight = partition := by
    change pmfPairExp second first (fun right left => Real.exp (score left right)) =
      pmfPairExp first second (fun left right => Real.exp (score left right))
    rw [pmfPairExp_swap]
  have hright_norm :
      Probability.finiteMGF second (fun right => Real.log (rightWeight right)) 1 = partition := by
    unfold Probability.finiteMGF
    calc
      pmfExp second (fun right => Real.exp (1 * Real.log (rightWeight right))) =
          pmfExp second rightWeight := by
            apply pmfExp_congr
            intro right
            rw [one_mul, Real.exp_log (hrightWeight_pos right)]
      _ = partition := hright_partition
  have hjoint_mass (pair : α × β) :
      (joint pair).toReal =
        (first pair.1).toReal * (second pair.2).toReal *
          Real.exp (score pair.1 pair.2) / partition := by
    unfold joint
    rw [exponentialTilt_apply_toReal, hjoint_norm, one_mul, pmfProd_apply_toReal]
  -- The log-ratio identity is used only after weighting by the base mass.
  -- At a zero-mass atom both sides vanish, while at a positive-mass atom the
  -- pointwise tilt identity is available without a global support hypothesis.
  have hlogratio_weighted :
      pmfExp base (fun pair =>
        Real.exp (score pair.1 pair.2) *
          (Real.log (joint pair).toReal -
            Real.log ((pmfProd leftTilt rightTilt) pair).toReal)) =
        pmfExp base (fun pair =>
          Real.exp (score pair.1 pair.2) *
            (score pair.1 pair.2 - Real.log (leftWeight pair.1) -
              Real.log (rightWeight pair.2) + Real.log partition)) := by
    unfold pmfExp
    apply Finset.sum_congr rfl
    intro pair _
    by_cases hfirst_zero : (first pair.1).toReal = 0
    · have hbase_zero : (base pair).toReal = 0 := by
        change (pmfProd first second pair).toReal = 0
        rw [pmfProd_apply_toReal, hfirst_zero]
        ring
      rw [hbase_zero]
      ring
    by_cases hsecond_zero : (second pair.2).toReal = 0
    · have hbase_zero : (base pair).toReal = 0 := by
        change (pmfProd first second pair).toReal = 0
        rw [pmfProd_apply_toReal, hsecond_zero]
        ring
      rw [hbase_zero]
      ring
    have hfirst_pos : 0 < (first pair.1).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hfirst_zero)
    have hsecond_pos : 0 < (second pair.2).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hsecond_zero)
    have hbase_pos : 0 < (base pair).toReal := by
      change 0 < (pmfProd first second pair).toReal
      rw [pmfProd_apply_toReal]
      exact mul_pos hfirst_pos hsecond_pos
    have hleftTilt_pos : 0 < (leftTilt pair.1).toReal := by
      unfold leftTilt
      rw [exponentialTilt_apply_toReal]
      exact div_pos
        (mul_pos hfirst_pos (Real.exp_pos _))
        (Probability.finiteMGF_pos first _ _)
    have hrightTilt_pos : 0 < (rightTilt pair.2).toReal := by
      unfold rightTilt
      rw [exponentialTilt_apply_toReal]
      exact div_pos
        (mul_pos hsecond_pos (Real.exp_pos _))
        (Probability.finiteMGF_pos second _ _)
    have hjoint_ratio := exponentialTilt_log_ratio_of_pos base
      (fun x => score x.1 x.2) 1 hbase_pos
    have hleft_ratio := exponentialTilt_log_ratio_of_pos first
      (fun left => Real.log (leftWeight left)) 1 hfirst_pos
    have hright_ratio := exponentialTilt_log_ratio_of_pos second
      (fun right => Real.log (rightWeight right)) 1 hsecond_pos
    rw [hjoint_norm] at hjoint_ratio
    rw [hleft_norm] at hleft_ratio
    rw [hright_norm] at hright_ratio
    have hjoint_ratio' :
        Real.log (joint pair).toReal - Real.log (base pair).toReal =
          score pair.1 pair.2 - Real.log partition := by
      simpa only [joint, one_mul] using hjoint_ratio
    have hleft_ratio' :
        Real.log (leftTilt pair.1).toReal - Real.log (first pair.1).toReal =
          Real.log (leftWeight pair.1) - Real.log partition := by
      simpa only [leftTilt, one_mul] using hleft_ratio
    have hright_ratio' :
        Real.log (rightTilt pair.2).toReal - Real.log (second pair.2).toReal =
          Real.log (rightWeight pair.2) - Real.log partition := by
      simpa only [rightTilt, one_mul] using hright_ratio
    have hproduct_log :
        Real.log ((pmfProd leftTilt rightTilt) pair).toReal =
          Real.log (leftTilt pair.1).toReal + Real.log (rightTilt pair.2).toReal := by
      rw [pmfProd_apply_toReal, Real.log_mul
        hleftTilt_pos.ne' hrightTilt_pos.ne']
    have hbase_log :
        Real.log (base pair).toReal =
          Real.log (first pair.1).toReal + Real.log (second pair.2).toReal := by
      change Real.log ((pmfProd first second) pair).toReal = _
      rw [pmfProd_apply_toReal, Real.log_mul hfirst_pos.ne' hsecond_pos.ne']
    have hlogratio :
        Real.log (joint pair).toReal - Real.log ((pmfProd leftTilt rightTilt) pair).toReal =
          score pair.1 pair.2 - Real.log (leftWeight pair.1) -
            Real.log (rightWeight pair.2) + Real.log partition := by
      rw [hproduct_log]
      linarith [hjoint_ratio', hleft_ratio', hright_ratio', hbase_log]
    change (base pair).toReal *
        (Real.exp (score pair.1 pair.2) *
          (Real.log (joint pair).toReal -
            Real.log ((pmfProd leftTilt rightTilt) pair).toReal)) =
      (base pair).toReal *
        (Real.exp (score pair.1 pair.2) *
          (score pair.1 pair.2 - Real.log (leftWeight pair.1) -
            Real.log (rightWeight pair.2) + Real.log partition))
    rw [hlogratio]
  have hchange (statistic : (α × β) → ℝ) :
      partition * pmfExp joint statistic =
        pmfExp base (fun pair => Real.exp (score pair.1 pair.2) * statistic pair) := by
    unfold pmfExp base
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro pair _
    rw [hjoint_mass pair, pmfProd_apply_toReal]
    field_simp [hpartition_pos.ne']
  have hscore_term :
      pmfExp base (fun pair =>
        Real.exp (score pair.1 pair.2) * score pair.1 pair.2) =
        pmfExp second (fun right =>
          pmfExp first (fun left =>
            Real.exp (score left right) * score left right)) := by
    change pmfExp (pmfProd first second) (fun pair =>
      Real.exp (score pair.1 pair.2) * score pair.1 pair.2) =
        pmfPairExp second first (fun right left =>
          Real.exp (score left right) * score left right)
    rw [pmfExp_pmfProd_eq_pairExp, pmfPairExp_swap]
  have hleft_term :
      pmfExp base (fun pair =>
        Real.exp (score pair.1 pair.2) * Real.log (leftWeight pair.1)) =
        pmfExp first (fun left => leftWeight left * Real.log (leftWeight left)) := by
    change pmfExp (pmfProd first second) (fun pair =>
      Real.exp (score pair.1 pair.2) * Real.log (leftWeight pair.1)) = _
    rw [pmfExp_pmfProd_eq_pairExp]
    unfold pmfPairExp
    change pmfExp first (fun left =>
      pmfExp second (fun right =>
        Real.exp (score left right) * Real.log (leftWeight left))) = _
    apply pmfExp_congr
    intro left
    rw [pmfExp_mul_const]
  have hright_term :
      pmfExp base (fun pair =>
        Real.exp (score pair.1 pair.2) * Real.log (rightWeight pair.2)) =
        pmfExp second (fun right => rightWeight right * Real.log (rightWeight right)) := by
    change pmfExp (pmfProd first second) (fun pair =>
      Real.exp (score pair.1 pair.2) * Real.log (rightWeight pair.2)) = _
    rw [pmfExp_pmfProd_eq_pairExp]
    change pmfPairExp first second (fun left right =>
      Real.exp (score left right) * Real.log (rightWeight right)) = _
    rw [pmfPairExp_swap]
    unfold pmfPairExp
    change pmfExp second (fun right =>
      pmfExp first (fun left =>
        Real.exp (score left right) * Real.log (rightWeight right))) = _
    apply pmfExp_congr
    intro right
    rw [pmfExp_mul_const]
  have hpartition_term :
      pmfExp base (fun pair => Real.exp (score pair.1 pair.2)) = partition := by
    change pmfExp (pmfProd first second) (fun pair =>
      Real.exp (score pair.1 pair.2)) =
        pmfPairExp first second (fun left right => Real.exp (score left right))
    rw [pmfExp_pmfProd_eq_pairExp]
  have hkl_identity :
      partition * finiteKLDivergence joint (pmfProd leftTilt rightTilt) =
        (pmfExp second (fun right =>
          pmfFunctionalEntropy first (fun left => Real.exp (score left right))) -
          pmfFunctionalEntropy first leftWeight) := by
    unfold finiteKLDivergence
    change partition * pmfExp joint (fun pair =>
      Real.log (joint pair).toReal - Real.log ((pmfProd leftTilt rightTilt pair).toReal)) = _
    rw [hchange]
    calc
      pmfExp base (fun pair =>
          Real.exp (score pair.1 pair.2) *
            (Real.log (joint pair).toReal -
              Real.log ((pmfProd leftTilt rightTilt) pair).toReal)) =
          pmfExp base (fun pair =>
            Real.exp (score pair.1 pair.2) *
              (score pair.1 pair.2 - Real.log (leftWeight pair.1) -
                Real.log (rightWeight pair.2) + Real.log partition)) :=
            hlogratio_weighted
      _ = pmfExp base (fun pair =>
            Real.exp (score pair.1 pair.2) * score pair.1 pair.2) -
          pmfExp base (fun pair =>
            Real.exp (score pair.1 pair.2) * Real.log (leftWeight pair.1)) -
          pmfExp base (fun pair =>
            Real.exp (score pair.1 pair.2) * Real.log (rightWeight pair.2)) +
          pmfExp base (fun pair =>
            Real.exp (score pair.1 pair.2) * Real.log partition) := by
            calc
              pmfExp base (fun pair =>
                  Real.exp (score pair.1 pair.2) *
                    (score pair.1 pair.2 - Real.log (leftWeight pair.1) -
                      Real.log (rightWeight pair.2) + Real.log partition)) =
                  pmfExp base (fun pair =>
                    (Real.exp (score pair.1 pair.2) * score pair.1 pair.2 -
                      Real.exp (score pair.1 pair.2) * Real.log (leftWeight pair.1) -
                        Real.exp (score pair.1 pair.2) * Real.log (rightWeight pair.2)) +
                      Real.exp (score pair.1 pair.2) * Real.log partition) := by
                    apply pmfExp_congr
                    intro pair
                    ring
              _ = pmfExp base (fun pair =>
                    Real.exp (score pair.1 pair.2) * score pair.1 pair.2 -
                      Real.exp (score pair.1 pair.2) * Real.log (leftWeight pair.1) -
                        Real.exp (score pair.1 pair.2) * Real.log (rightWeight pair.2)) +
                  pmfExp base (fun pair =>
                    Real.exp (score pair.1 pair.2) * Real.log partition) := by
                    rw [pmfExp_add]
              _ = (pmfExp base (fun pair =>
                    Real.exp (score pair.1 pair.2) * score pair.1 pair.2 -
                      Real.exp (score pair.1 pair.2) * Real.log (leftWeight pair.1)) -
                    pmfExp base (fun pair =>
                      Real.exp (score pair.1 pair.2) * Real.log (rightWeight pair.2))) +
                  pmfExp base (fun pair =>
                    Real.exp (score pair.1 pair.2) * Real.log partition) := by
                    rw [pmfExp_sub]
              _ = (pmfExp base (fun pair =>
                    Real.exp (score pair.1 pair.2) * score pair.1 pair.2) -
                  pmfExp base (fun pair =>
                    Real.exp (score pair.1 pair.2) * Real.log (leftWeight pair.1)) -
                  pmfExp base (fun pair =>
                    Real.exp (score pair.1 pair.2) * Real.log (rightWeight pair.2))) +
                  pmfExp base (fun pair =>
                    Real.exp (score pair.1 pair.2) * Real.log partition) := by
                    rw [pmfExp_sub]
              _ = _ := by ring
      _ = pmfExp second (fun right =>
            pmfExp first (fun left =>
              Real.exp (score left right) * score left right)) -
          pmfExp first (fun left => leftWeight left * Real.log (leftWeight left)) -
          pmfExp second (fun right => rightWeight right * Real.log (rightWeight right)) +
          partition * Real.log partition := by
            rw [hscore_term, hleft_term, hright_term, pmfExp_mul_const,
              hpartition_term]
      _ = (pmfExp second (fun right =>
            pmfFunctionalEntropy first (fun left => Real.exp (score left right))) -
            pmfFunctionalEntropy first leftWeight) := by
            have hright_entropy :
                pmfExp second (fun right =>
                  pmfFunctionalEntropy first (fun left =>
                    Real.exp (score left right))) =
                    pmfExp second (fun right =>
                      pmfExp first (fun left =>
                        Real.exp (score left right) * score left right) -
                      rightWeight right * Real.log (rightWeight right)) := by
              unfold pmfFunctionalEntropy
              apply pmfExp_congr
              intro right
              simp_rw [Real.log_exp]
              simp only [rightWeight]
            have hright_entropy_expanded :
                pmfExp second (fun right =>
                  pmfFunctionalEntropy first (fun left =>
                    Real.exp (score left right))) =
                    pmfExp second (fun right =>
                      pmfExp first (fun left =>
                        Real.exp (score left right) * score left right)) -
                    pmfExp second (fun right =>
                      rightWeight right * Real.log (rightWeight right)) := by
              rw [hright_entropy, pmfExp_sub]
            have hleft_entropy :
                pmfFunctionalEntropy first leftWeight =
                  pmfExp first (fun left => leftWeight left * Real.log (leftWeight left)) -
                    partition * Real.log partition := by
              unfold pmfFunctionalEntropy partition
              rfl
            rw [hright_entropy_expanded, hleft_entropy]
            ring
  have hproduct_continuous :
      PMFAbsoluteContinuous joint (pmfProd leftTilt rightTilt) := by
    intro pair hjoint_pos
    have hbase_pos : 0 < (base pair).toReal := by
      by_contra hnot
      have hbase_zero : (base pair).toReal = 0 :=
        le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
      change 0 < (exponentialTilt base (fun x => score x.1 x.2) 1 pair).toReal at hjoint_pos
      rw [exponentialTilt_apply_toReal, hbase_zero] at hjoint_pos
      simp at hjoint_pos
    have hbase_product_pos :
        0 < (first pair.1).toReal * (second pair.2).toReal := by
      change 0 < (pmfProd first second pair).toReal at hbase_pos
      rwa [pmfProd_apply_toReal] at hbase_pos
    rcases (mul_pos_iff.mp hbase_product_pos) with hpositive | hnegative
    · have hleft_tilt_pos : 0 < (leftTilt pair.1).toReal := by
        unfold leftTilt
        rw [exponentialTilt_apply_toReal]
        exact div_pos
          (mul_pos hpositive.1 (Real.exp_pos _))
          (Probability.finiteMGF_pos first _ _)
      have hright_tilt_pos : 0 < (rightTilt pair.2).toReal := by
        unfold rightTilt
        rw [exponentialTilt_apply_toReal]
        exact div_pos
          (mul_pos hpositive.2 (Real.exp_pos _))
          (Probability.finiteMGF_pos second _ _)
      rw [pmfProd_apply_toReal]
      exact mul_pos hleft_tilt_pos hright_tilt_pos
    · exact False.elim ((not_lt_of_ge ENNReal.toReal_nonneg) hnegative.1)
  have hkl_nonneg : 0 ≤ finiteKLDivergence joint (pmfProd leftTilt rightTilt) :=
    finiteKLDivergence_nonneg_of_absoluteContinuous joint
      (pmfProd leftTilt rightTilt) hproduct_continuous
  have hgap_nonneg :
      0 ≤ pmfExp second (fun right =>
        pmfFunctionalEntropy first (fun left => Real.exp (score left right))) -
          pmfFunctionalEntropy first leftWeight := by
    rw [← hkl_identity]
    exact mul_nonneg hpartition_pos.le hkl_nonneg
  exact sub_nonneg.mp hgap_nonneg

end AppliedModelingLib
