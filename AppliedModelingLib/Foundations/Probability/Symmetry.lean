import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace AppliedModelingLib
namespace Probability

open MeasureTheory

/-!
# Symmetry Tools for Probability Kernels

These lemmas package a common continuous-probability argument: if a
measure-preserving symmetry acts on users and an action on items is transitive,
then a diagonally invariant item-user kernel has the same user integral at
every item.
-/

/--
Diagonal invariance transports a kernel's user integral along an item
symmetry.
-/
theorem integral_kernel_eq_of_diagonal_invariance
    {Sym User Item : Type*} [MeasurableSpace User]
    (userMeasure : Measure User)
    (userAction : Sym → User → User)
    (itemAction : Sym → Item → Item)
    (kernel : Item → User → ℝ)
    (h_measurePreserving :
      ∀ g : Sym, MeasurePreserving (userAction g) userMeasure userMeasure)
    (h_measurableEmbedding :
      ∀ g : Sym, MeasurableEmbedding (userAction g))
    (h_invariant :
      ∀ g : Sym, ∀ x : Item, ∀ u : User,
        kernel (itemAction g x) (userAction g u) = kernel x u)
    (g : Sym) (x : Item) :
    (∫ u, kernel (itemAction g x) u ∂userMeasure) =
      ∫ u, kernel x u ∂userMeasure := by
  calc
    (∫ u, kernel (itemAction g x) u ∂userMeasure)
        = ∫ u, kernel (itemAction g x) (userAction g u) ∂userMeasure := by
          exact
            ((h_measurePreserving g).integral_comp
              (h_measurableEmbedding g)
              (fun u : User => kernel (itemAction g x) u)).symm
    _ = ∫ u, kernel x u ∂userMeasure := by
          simp [h_invariant]

/--
If item symmetries are transitive from an anchor item and the kernel is
diagonally invariant, then the user integral of the kernel is constant across
items.
-/
theorem integral_kernel_eq_anchor_of_transitive_diagonal_invariance
    {Sym User Item : Type*} [MeasurableSpace User]
    (userMeasure : Measure User)
    (userAction : Sym → User → User)
    (itemAction : Sym → Item → Item)
    (kernel : Item → User → ℝ)
    (anchor : Item)
    (h_measurePreserving :
      ∀ g : Sym, MeasurePreserving (userAction g) userMeasure userMeasure)
    (h_measurableEmbedding :
      ∀ g : Sym, MeasurableEmbedding (userAction g))
    (h_invariant :
      ∀ g : Sym, ∀ x : Item, ∀ u : User,
        kernel (itemAction g x) (userAction g u) = kernel x u)
    (h_transitive : ∀ x : Item, ∃ g : Sym, itemAction g anchor = x) :
    ∀ x : Item,
      (∫ u, kernel x u ∂userMeasure) =
        ∫ u, kernel anchor u ∂userMeasure := by
  intro x
  rcases h_transitive x with ⟨g, hg⟩
  simpa [hg] using
    integral_kernel_eq_of_diagonal_invariance
      userMeasure userAction itemAction kernel h_measurePreserving
      h_measurableEmbedding h_invariant g anchor

end Probability
end AppliedModelingLib
