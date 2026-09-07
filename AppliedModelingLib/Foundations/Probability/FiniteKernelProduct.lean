import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import AppliedModelingLib.Foundations.Probability.FiniteIID

/-!
# Finite products of kernels

This module constructs the kernel of a finite family of conditionally independent
coordinates.  Its value on a measurable rectangle is the product of the
coordinate-kernel masses.
-/

namespace AppliedModelingLib.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

variable {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]

/-- Expose a family-level Markov-kernel instance at a chosen index. -/
instance isMarkovKernel_apply_of_forall {Index : Type*}
    (kappa : Index → Kernel alpha beta) [hkappa : ∀ index, IsMarkovKernel (kappa index)]
    (index : Index) : IsMarkovKernel (kappa index) :=
  hkappa index

/-- The measurable equivalence that appends one coordinate to a finite vector. -/
def finSnocMeasurableEquiv (n : Nat) :
    ((Fin n -> beta) × beta) ≃ᵐ (Fin (n + 1) -> beta) :=
  MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => beta) (Fin.last n)).symm

@[simp]
theorem finSnocMeasurableEquiv_apply (n : Nat) (p : (Fin n -> beta) × beta) :
    finSnocMeasurableEquiv (beta := beta) n p = Fin.snoc p.1 p.2 := by
  ext i
  simp [finSnocMeasurableEquiv, MeasurableEquiv.piFinSuccAbove,
    Fin.snocEquiv_apply]
  change (@Fin.snoc n (fun _ : Fin (n + 1) => beta) p.1 p.2) i =
    (@Fin.snoc n (fun _ : Fin (n + 1) => beta) p.1 p.2) i
  rfl

/-- Appending a last coordinate to a finite vector is measurable. -/
theorem measurable_finSnoc (n : Nat) :
    Measurable (fun p : (Fin n -> beta) × beta =>
      @Fin.snoc n (fun _ : Fin (n + 1) => beta) p.1 p.2) := by
  have heq : (fun p : (Fin n -> beta) × beta =>
      @Fin.snoc n (fun _ : Fin (n + 1) => beta) p.1 p.2) =
      finSnocMeasurableEquiv (beta := beta) n := by
    funext p
    exact (finSnocMeasurableEquiv_apply n p).symm
  rw [heq]
  exact (finSnocMeasurableEquiv (beta := beta) n).measurable

/-- A finite product of kernels, interpreted as conditionally independent coordinates. -/
noncomputable def finiteKernelProduct :
    (n : Nat) -> (Fin n -> Kernel alpha beta) -> Kernel alpha (Fin n -> beta)
  | 0, _ => Kernel.deterministic (fun _ i => Fin.elim0 i) measurable_const
  | n + 1, kappa =>
      Kernel.map
        (finiteKernelProduct n (fun i => kappa i.castSucc) ×ₖ kappa (Fin.last n))
        (finSnocMeasurableEquiv (beta := beta) n)

/-- The preimage of a finite measurable rectangle under last-coordinate append. -/
theorem finSnocMeasurableEquiv_preimage_pi
    (n : Nat) (A : Fin (n + 1) -> Set beta) :
    finSnocMeasurableEquiv (beta := beta) n ⁻¹' Set.pi Set.univ A =
      Set.pi Set.univ (fun i : Fin n => A i.castSucc) ×ˢ A (Fin.last n) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_prod, finSnocMeasurableEquiv_apply]
  rw [Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- Markov coordinate kernels give a Markov finite product kernel. -/
theorem finiteKernelProduct_isMarkov
    (n : Nat) (kappa : Fin n -> Kernel alpha beta)
    (hkappa : forall i, IsMarkovKernel (kappa i)) :
    IsMarkovKernel (finiteKernelProduct n kappa) := by
  induction n with
  | zero =>
      simp only [finiteKernelProduct]
      infer_instance
  | succ n ih =>
      letI : forall i : Fin n, IsMarkovKernel (kappa i.castSucc) :=
        fun i => hkappa i.castSucc
      letI : IsMarkovKernel (finiteKernelProduct n (fun i => kappa i.castSucc)) :=
        ih (fun i => kappa i.castSucc) (fun i => hkappa i.castSucc)
      letI : IsMarkovKernel (kappa (Fin.last n)) := hkappa (Fin.last n)
      exact Kernel.IsMarkovKernel.map _
        (finSnocMeasurableEquiv (beta := beta) n).measurable

/-- A finite conditional-product kernel evaluates on a rectangle coordinatewise. -/
theorem finiteKernelProduct_apply_pi
    (n : Nat) (kappa : Fin n -> Kernel alpha beta)
    (hkappa : forall i, IsMarkovKernel (kappa i))
    (a : alpha) (A : Fin n -> Set beta) (hA : forall i, MeasurableSet (A i)) :
    finiteKernelProduct n kappa a (Set.pi Set.univ A) =
      ∏ i, kappa i a (A i) := by
  induction n with
  | zero =>
      have hset : Set.pi Set.univ A = Set.univ := by
        ext x
        simp
      rw [hset]
      letI : IsMarkovKernel (finiteKernelProduct 0 kappa) :=
        finiteKernelProduct_isMarkov 0 kappa hkappa
      rw [measure_univ]
      exact (Fin.prod_univ_zero (fun i => kappa i a (A i))).symm
  | succ n ih =>
      let kappaInit : Fin n -> Kernel alpha beta := fun i => kappa i.castSucc
      let AInit : Fin n -> Set beta := fun i => A i.castSucc
      have hkappaInit : forall i, IsMarkovKernel (kappaInit i) :=
        fun i => hkappa i.castSucc
      letI : forall i : Fin n, IsMarkovKernel (kappaInit i) := hkappaInit
      letI : IsMarkovKernel (finiteKernelProduct n kappaInit) :=
        finiteKernelProduct_isMarkov n kappaInit hkappaInit
      letI : IsMarkovKernel (kappa (Fin.last n)) := hkappa (Fin.last n)
      have hpi : MeasurableSet (Set.pi Set.univ A) :=
        MeasurableSet.pi Set.countable_univ (fun i _ => hA i)
      rw [finiteKernelProduct, Kernel.map_apply'
        _ (finSnocMeasurableEquiv (beta := beta) n).measurable a hpi]
      rw [finSnocMeasurableEquiv_preimage_pi]
      rw [Kernel.prod_apply_prod]
      rw [ih kappaInit hkappaInit AInit (fun i => hA i.castSucc)]
      exact (Fin.prod_univ_castSucc (fun i => kappa i a (A i))).symm

/--
The finite product of one Markov kernel repeated at every coordinate is the
canonical finite-IID sample law at each source point.

This uses Mathlib's `Measure.pi_eq` and `Measure.pi_pi` from
[`MeasureTheory/Constructions/Pi.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Constructions/Pi.lean)
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported.
-/
theorem finiteKernelProduct_constant_apply_eq_finiteIIDSampleLaw
    (n : Nat) (kappa : Kernel alpha beta) [IsMarkovKernel kappa] (a : alpha) :
    finiteKernelProduct n (fun _ => kappa) a = finiteIIDSampleLaw (kappa a) n := by
  letI : ∀ _ : Fin n, IsProbabilityMeasure (kappa a) := fun _ => inferInstance
  symm
  apply Measure.pi_eq
  intro A hA
  exact finiteKernelProduct_apply_pi n (fun _ => kappa) (fun _ => inferInstance) a A hA

/-- The conditionally IID finite-batch kernel induced by one Markov kernel. -/
noncomputable def finiteIIDBatchKernel (n : Nat) (kappa : Kernel alpha beta) :
    Kernel alpha (Fin n -> beta) :=
  finiteKernelProduct n (fun _ => kappa)

/-- A finite IID batch kernel preserves the Markov property of its one-observation kernel. -/
theorem finiteIIDBatchKernel_isMarkov
    (n : Nat) (kappa : Kernel alpha beta) [IsMarkovKernel kappa] :
    IsMarkovKernel (finiteIIDBatchKernel n kappa) :=
  finiteKernelProduct_isMarkov n (fun _ => kappa) (fun _ => inferInstance)

instance finiteIIDBatchKernel.isMarkov
    (n : Nat) (kappa : Kernel alpha beta) [IsMarkovKernel kappa] :
    IsMarkovKernel (finiteIIDBatchKernel n kappa) :=
  finiteIIDBatchKernel_isMarkov n kappa

/-- At every source point, a finite IID batch kernel is the product sample law. -/
theorem finiteIIDBatchKernel_apply_eq_finiteIIDSampleLaw
    (n : Nat) (kappa : Kernel alpha beta) [IsMarkovKernel kappa] (a : alpha) :
    finiteIIDBatchKernel n kappa a = finiteIIDSampleLaw (kappa a) n :=
  finiteKernelProduct_constant_apply_eq_finiteIIDSampleLaw n kappa a

end

end AppliedModelingLib.Probability
