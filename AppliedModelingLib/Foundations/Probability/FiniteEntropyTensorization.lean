import AppliedModelingLib.Foundations.Probability.FiniteEntropyMixing

/-!
# Finite-product entropy tensorization for exponential weights

This module develops the finite, iid product form of the entropy
tensorization step used by the self-bounding concentration proof.  It is
stated for exponential weights, the only case needed by the Herbst argument;
this keeps the analytic domain explicit.
-/

namespace AppliedModelingLib

open scoped BigOperators

/-- The entropy tensorization inequality for exponential weights on a finite
iid product with an arbitrary finite coordinate index type. -/
def FiniteProductEntropyTensorizesExp
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (law : PMF α) : Prop :=
  ∀ score : (ι → α) → ℝ,
    pmfFunctionalEntropy (pmfProduct ι α law) (fun sample => Real.exp (score sample)) ≤
      pmfExp (pmfProduct ι α law) (fun sample =>
        ∑ coordinate : ι,
          pmfFunctionalEntropy law (fun value =>
            Real.exp (score (Function.update sample coordinate value))))

/-- Reindexing iid coordinates by an equivalence preserves functional entropy. -/
theorem pmfFunctionalEntropy_pmfProduct_equiv
    {ι κ α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype α] [DecidableEq α]
    (e : ι ≃ κ) (law : PMF α) (weight : (κ → α) → ℝ) :
    pmfFunctionalEntropy (pmfProduct ι α law)
        (fun sample => weight (fun coordinate => sample (e.symm coordinate))) =
      pmfFunctionalEntropy (pmfProduct κ α law) weight := by
  unfold pmfFunctionalEntropy
  rw [pmfExp_pmfProduct_equiv e law (fun sample =>
    weight sample * Real.log (weight sample)),
    pmfExp_pmfProduct_equiv e law weight]

/-- Tensorization transfers along a coordinate equivalence. -/
theorem finiteProductEntropyTensorizesExp_equiv
    {ι κ α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype α] [DecidableEq α]
    (e : ι ≃ κ) (law : PMF α)
    (htensor : FiniteProductEntropyTensorizesExp (ι := ι) law) :
    FiniteProductEntropyTensorizesExp (ι := κ) law := by
  intro score
  let reindexedScore : (ι → α) → ℝ := fun sample =>
    score (fun coordinate => sample (e.symm coordinate))
  let rightKappa : (κ → α) → ℝ := fun sample =>
    ∑ coordinate : κ,
      pmfFunctionalEntropy law (fun value =>
        Real.exp (score (Function.update sample coordinate value)))
  have hleft :
      pmfFunctionalEntropy (pmfProduct ι α law)
          (fun sample => Real.exp (reindexedScore sample)) =
        pmfFunctionalEntropy (pmfProduct κ α law)
          (fun sample => Real.exp (score sample)) := by
    simpa only [reindexedScore] using
      pmfFunctionalEntropy_pmfProduct_equiv e law
        (fun sample => Real.exp (score sample))
  have hright :
      pmfExp (pmfProduct ι α law) (fun sample =>
        ∑ coordinate : ι,
          pmfFunctionalEntropy law (fun value =>
            Real.exp (reindexedScore (Function.update sample coordinate value)))) =
        pmfExp (pmfProduct κ α law) rightKappa := by
    rw [← pmfExp_pmfProduct_equiv e law rightKappa]
    apply pmfExp_congr
    intro sample
    unfold rightKappa reindexedScore
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro coordinate _
    congr 1
    funext value
    congr 1
    congr 1
    funext target
    by_cases htarget : target = e coordinate
    · subst target
      rw [e.symm_apply_apply]
      simp
    · have hinverse : e.symm target ≠ coordinate := by
        intro heq
        apply htarget
        rw [← heq]
        simp
      simp [Function.update_of_ne, htarget, hinverse]
  have hsource := htensor reindexedScore
  rw [hleft, hright] at hsource
  exact hsource

/-- The empty iid product tensorizes. -/
theorem finiteProductEntropyTensorizesExp_empty
    {α : Type*} [Fintype α] [DecidableEq α] (law : PMF α) :
    FiniteProductEntropyTensorizesExp (ι := Fin 0) law := by
  intro score
  let weight : (Fin 0 → α) → ℝ := fun sample => Real.exp (score sample)
  have hweight : ∀ sample : Fin 0 → α, weight sample = weight Fin.elim0 := by
    intro sample
    congr
    exact Subsingleton.elim _ _
  have hfirst :
      pmfExp (pmfProduct (Fin 0) α law)
          (fun sample => weight sample * Real.log (weight sample)) =
        weight Fin.elim0 * Real.log (weight Fin.elim0) := by
    calc
      pmfExp (pmfProduct (Fin 0) α law)
          (fun sample => weight sample * Real.log (weight sample)) =
          pmfExp (pmfProduct (Fin 0) α law)
            (fun _sample => weight Fin.elim0 * Real.log (weight Fin.elim0)) := by
              apply pmfExp_congr
              intro sample
              rw [hweight sample]
      _ = weight Fin.elim0 * Real.log (weight Fin.elim0) := pmfExp_const _ _
  have hmean : pmfExp (pmfProduct (Fin 0) α law) weight = weight Fin.elim0 := by
    calc
      pmfExp (pmfProduct (Fin 0) α law) weight =
          pmfExp (pmfProduct (Fin 0) α law) (fun _sample => weight Fin.elim0) := by
            apply pmfExp_congr
            intro sample
            exact hweight sample
      _ = weight Fin.elim0 := pmfExp_const _ _
  change pmfFunctionalEntropy (pmfProduct (Fin 0) α law) weight ≤ _
  unfold pmfFunctionalEntropy
  rw [hfirst, hmean]
  simp

/-- Tensorization for an iid coordinate family extends by one distinguished
coordinate.  The first part is controlled by the induction hypothesis and
finite entropy mixing; the second is the literal entropy of the new draw. -/
theorem finiteProductEntropyTensorizesExp_option
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (law : PMF α) (htensor : FiniteProductEntropyTensorizesExp (ι := ι) law) :
    FiniteProductEntropyTensorizesExp (ι := Option ι) law := by
  intro score
  let weight : (Option ι → α) → ℝ := fun sample => Real.exp (score sample)
  let averagedScore : (ι → α) → ℝ := fun oldSample =>
    Real.log (pmfExp law (fun newValue => weight (extendDraw oldSample newValue)))
  let noneTerm : (ι → α) → ℝ := fun oldSample =>
    pmfFunctionalEntropy law (fun value => weight (extendDraw oldSample value))
  let someTerm : (ι → α) → ι → ℝ := fun oldSample coordinate =>
    pmfExp law (fun newValue =>
      pmfFunctionalEntropy law (fun value =>
        weight (extendDraw (Function.update oldSample coordinate value) newValue)))
  have hmean_pos (oldSample : ι → α) :
      0 < pmfExp law (fun newValue => weight (extendDraw oldSample newValue)) := by
    unfold weight
    exact pmfExp_pos_of_forall_pos law _ (fun _ => Real.exp_pos _)
  have havg_exp (oldSample : ι → α) :
      Real.exp (averagedScore oldSample) =
        pmfExp law (fun newValue => weight (extendDraw oldSample newValue)) := by
    unfold averagedScore
    rw [Real.exp_log (hmean_pos oldSample)]
  have hcoordinate (oldSample : ι → α) (coordinate : ι) :
      pmfFunctionalEntropy law (fun value =>
        Real.exp (averagedScore (Function.update oldSample coordinate value))) ≤
        someTerm oldSample coordinate := by
    calc
      pmfFunctionalEntropy law (fun value =>
          Real.exp (averagedScore (Function.update oldSample coordinate value))) =
          pmfFunctionalEntropy law (fun value =>
            pmfExp law (fun newValue =>
              weight (extendDraw (Function.update oldSample coordinate value) newValue))) := by
            apply congrArg (pmfFunctionalEntropy law)
            funext value
            exact havg_exp (Function.update oldSample coordinate value)
      _ ≤ pmfExp law (fun newValue =>
          pmfFunctionalEntropy law (fun value =>
            weight (extendDraw (Function.update oldSample coordinate value) newValue))) := by
            exact pmfFunctionalEntropy_exp_mixture_le law law
              (fun value newValue =>
                score (extendDraw (Function.update oldSample coordinate value) newValue))
      _ = someTerm oldSample coordinate := rfl
  have hfirst_bound :
      pmfFunctionalEntropy (pmfProduct ι α law) (fun oldSample =>
        pmfExp law (fun newValue => weight (extendDraw oldSample newValue))) ≤
        pmfExp (pmfProduct ι α law) (fun oldSample =>
          ∑ coordinate : ι, someTerm oldSample coordinate) := by
    calc
      pmfFunctionalEntropy (pmfProduct ι α law) (fun oldSample =>
          pmfExp law (fun newValue => weight (extendDraw oldSample newValue))) =
          pmfFunctionalEntropy (pmfProduct ι α law) (fun oldSample =>
            Real.exp (averagedScore oldSample)) := by
            apply congrArg (pmfFunctionalEntropy (pmfProduct ι α law))
            funext oldSample
            exact (havg_exp oldSample).symm
      _ ≤ pmfExp (pmfProduct ι α law) (fun oldSample =>
          ∑ coordinate : ι,
            pmfFunctionalEntropy law (fun value =>
              Real.exp (averagedScore (Function.update oldSample coordinate value)))) :=
          htensor averagedScore
      _ ≤ pmfExp (pmfProduct ι α law) (fun oldSample =>
          ∑ coordinate : ι, someTerm oldSample coordinate) := by
            apply pmfExp_le_pmfExp_of_forall_le
            intro oldSample
            exact Finset.sum_le_sum (fun coordinate _ => hcoordinate oldSample coordinate)
  have hupdate_none (oldSample : ι → α) (newValue value : α) :
      Function.update (extendDraw oldSample newValue) none value =
        extendDraw oldSample value := by
    funext coordinate
    cases coordinate <;> simp [extendDraw]
  have hupdate_some (oldSample : ι → α) (newValue value : α) (coordinate : ι) :
      Function.update (extendDraw oldSample newValue) (some coordinate) value =
        extendDraw (Function.update oldSample coordinate value) newValue := by
    funext target
    cases target with
    | none => simp [extendDraw]
    | some target =>
        by_cases htarget : target = coordinate
        · subst target
          simp [extendDraw]
        · simp [Function.update_of_ne, extendDraw, htarget]
  have hright_expand :
      pmfExp (pmfProduct (Option ι) α law) (fun sample =>
        ∑ coordinate : Option ι,
          pmfFunctionalEntropy law (fun value =>
            weight (Function.update sample coordinate value))) =
        pmfExp (pmfProduct ι α law) (fun oldSample =>
          noneTerm oldSample + ∑ coordinate : ι, someTerm oldSample coordinate) := by
    rw [pmfExp_pmfProduct_option_eq_pairExp]
    unfold pmfPairExp
    apply pmfExp_congr
    intro oldSample
    change pmfExp law (fun newValue =>
      ∑ coordinate : Option ι,
        pmfFunctionalEntropy law (fun value =>
          weight (Function.update (extendDraw oldSample newValue) coordinate value))) = _
    calc
      pmfExp law (fun newValue =>
          ∑ coordinate : Option ι,
            pmfFunctionalEntropy law (fun value =>
              weight (Function.update (extendDraw oldSample newValue) coordinate value))) =
          pmfExp law (fun newValue =>
            pmfFunctionalEntropy law (fun value =>
              weight (Function.update (extendDraw oldSample newValue) none value)) +
            ∑ coordinate : ι,
              pmfFunctionalEntropy law (fun value =>
                weight (Function.update (extendDraw oldSample newValue) (some coordinate) value))) := by
            apply pmfExp_congr
            intro newValue
            exact Fintype.sum_option _
      _ = pmfExp law (fun newValue =>
            pmfFunctionalEntropy law (fun value =>
              weight (Function.update (extendDraw oldSample newValue) none value))) +
          pmfExp law (fun newValue =>
            ∑ coordinate : ι,
              pmfFunctionalEntropy law (fun value =>
                weight (Function.update (extendDraw oldSample newValue) (some coordinate) value))) := by
            rw [pmfExp_add]
      _ = noneTerm oldSample + ∑ coordinate : ι, someTerm oldSample coordinate := by
        congr 1
        · calc
            pmfExp law (fun newValue =>
                pmfFunctionalEntropy law (fun value =>
                  weight (Function.update (extendDraw oldSample newValue) none value))) =
                pmfExp law (fun _newValue => noneTerm oldSample) := by
                  apply pmfExp_congr
                  intro newValue
                  unfold noneTerm
                  congr 1
                  funext value
                  rw [hupdate_none oldSample newValue value]
            _ = noneTerm oldSample := pmfExp_const _ _
        · rw [pmfExp_univ_sum]
          apply Finset.sum_congr rfl
          intro coordinate _
          unfold someTerm
          apply pmfExp_congr
          intro newValue
          congr 1
          funext value
          rw [hupdate_some oldSample newValue value coordinate]
  change pmfFunctionalEntropy (pmfProduct (Option ι) α law) weight ≤ _
  rw [pmfFunctionalEntropy_pmfProduct_option_decompose law weight, hright_expand]
  calc
    pmfFunctionalEntropy (pmfProduct ι α law) (fun oldSample =>
        pmfExp law (fun newValue => weight (extendDraw oldSample newValue))) +
        pmfExp (pmfProduct ι α law) noneTerm ≤
        pmfExp (pmfProduct ι α law) (fun oldSample =>
          ∑ coordinate : ι, someTerm oldSample coordinate) +
        pmfExp (pmfProduct ι α law) noneTerm := by
          gcongr
    _ = pmfExp (pmfProduct ι α law) (fun oldSample =>
          noneTerm oldSample + ∑ coordinate : ι, someTerm oldSample coordinate) := by
          rw [pmfExp_add]
          ring

/-- Entropy tensorization for every finite iid product.  The successor step
uses `Option (Fin n)` and then transports across the canonical equivalence
with `Fin (n + 1)`. -/
theorem finiteProductEntropyTensorizesExp_fin
    {α : Type*} [Fintype α] [DecidableEq α]
    (law : PMF α) (n : ℕ) :
    FiniteProductEntropyTensorizesExp (ι := Fin n) law := by
  induction n with
  | zero => exact finiteProductEntropyTensorizesExp_empty law
  | succ n ih =>
      simpa [Nat.succ_eq_add_one] using
        finiteProductEntropyTensorizesExp_equiv (optionFinEquivFinSucc n) law
          (finiteProductEntropyTensorizesExp_option law ih)

end AppliedModelingLib
