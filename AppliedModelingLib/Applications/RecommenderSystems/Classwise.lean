import AppliedModelingLib.Applications.RecommenderSystems.Policy

open scoped BigOperators

namespace AppliedModelingLib
namespace Policy

/-- Lift a class-level policy along a quotient/classification map `τ : α → κ`. -/
def liftAlong {α κ β : Type*} (τ : α → κ) (ρ : Policy κ β) : Policy α β :=
  fun a => ρ (τ a)

/-- A policy on `α` is classwise if it is constant on fibers of `τ`. -/
def IsClasswise {α κ β : Type*} (τ : α → κ) (ρ : Policy α β) : Prop :=
  ∀ a a', τ a = τ a' → ρ a = ρ a'

/-- The set of policies that are constant on fibers of `τ`. -/
def ClasswisePolicies {α κ β : Type*} (τ : α → κ) : Set (Policy α β) :=
  {ρ | IsClasswise τ ρ}

@[simp] theorem liftAlong_apply {α κ β : Type*}
    (τ : α → κ) (ρ : Policy κ β) (a : α) :
    liftAlong τ ρ a = ρ (τ a) := rfl

@[simp] theorem mem_classwisePolicies {α κ β : Type*}
    (τ : α → κ) (ρ : Policy α β) :
    ρ ∈ ClasswisePolicies τ ↔ IsClasswise τ ρ := Iff.rfl

theorem liftAlong_isClasswise {α κ β : Type*}
    (τ : α → κ) (ρ : Policy κ β) :
    IsClasswise τ (liftAlong τ ρ) := by
  intro a a' h
  simp [liftAlong, h]

/--
Chosen representatives for the fibers of `τ`. This is the exact data needed to
turn a classwise policy on `α` into a policy on the class space `κ`.
-/
structure FiberRepresentatives {α κ : Type*} (τ : α → κ) where
  repr : κ → α
  repr_spec : ∀ k, τ (repr k) = k

/-- A surjective classification map has a chosen representative in every fiber. -/
noncomputable def FiberRepresentatives.ofSurjective {α κ : Type*}
    {τ : α → κ} (hτ : Function.Surjective τ) : FiberRepresentatives τ where
  repr := fun k => Classical.choose (hτ k)
  repr_spec := fun k => Classical.choose_spec (hτ k)

/-- Descend a policy on `α` to the class space `κ` by evaluating it on representatives. -/
def descendAlong {α κ β : Type*} {τ : α → κ}
    (reps : FiberRepresentatives τ) (ρ : Policy α β) : Policy κ β :=
  fun k => ρ (reps.repr k)

@[simp] theorem descendAlong_apply {α κ β : Type*} {τ : α → κ}
    (reps : FiberRepresentatives τ) (ρ : Policy α β) (k : κ) :
    descendAlong reps ρ k = ρ (reps.repr k) := rfl

@[simp] theorem descendAlong_liftAlong {α κ β : Type*}
    (τ : α → κ) (reps : FiberRepresentatives τ) (ρ : Policy κ β) :
    descendAlong reps (liftAlong τ ρ) = ρ := by
  funext k
  simp [descendAlong, liftAlong, reps.repr_spec]

theorem liftAlong_descendAlong_eq_of_isClasswise {α κ β : Type*}
    (τ : α → κ) (reps : FiberRepresentatives τ) (ρ : Policy α β)
    (hρ : IsClasswise τ ρ) :
    liftAlong τ (descendAlong reps ρ) = ρ := by
  funext a
  exact hρ (reps.repr (τ a)) a (reps.repr_spec (τ a))

/--
A policy on `α` is classwise exactly when it comes from lifting some policy on `κ`.
The only extra input needed is one representative in each fiber of `τ`.
-/
theorem isClasswise_iff_exists_liftAlong {α κ β : Type*}
    (τ : α → κ) (reps : FiberRepresentatives τ) (ρ : Policy α β) :
    IsClasswise τ ρ ↔ ∃ ρκ : Policy κ β, liftAlong τ ρκ = ρ := by
  constructor
  · intro hρ
    refine ⟨descendAlong reps ρ, ?_⟩
    exact liftAlong_descendAlong_eq_of_isClasswise τ reps ρ hρ
  · rintro ⟨ρκ, hEq⟩
    rw [← hEq]
    exact liftAlong_isClasswise τ ρκ

/--
Fiber-cardinality weighted sums over classes are the same as sums over the
underlying population when the summand only depends on the class.
-/
theorem sum_fiber_card_mul {α κ : Type*} [Fintype α] [Fintype κ] [DecidableEq κ]
    (τ : α → κ) (f : κ → ℝ) :
    (∑ k : κ, (((Finset.univ : Finset α).filter fun a => τ a = k).card : ℝ) * f k) =
      ∑ a : α, f (τ a) := by
  classical
  calc
    (∑ k : κ, (((Finset.univ : Finset α).filter fun a => τ a = k).card : ℝ) * f k)
        = ∑ k : κ, ∑ a ∈ (Finset.univ : Finset α) with τ a = k, f (τ a) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          calc
            (((Finset.univ : Finset α).filter fun a => τ a = k).card : ℝ) * f k
                = ∑ a ∈ (Finset.univ : Finset α) with τ a = k, f k := by
                  simp [nsmul_eq_mul, mul_comm]
            _ = ∑ a ∈ (Finset.univ : Finset α) with τ a = k, f (τ a) := by
                  refine Finset.sum_congr rfl ?_
                  intro a ha
                  have hτ : τ a = k := by
                    simpa using ha
                  rw [hτ]
    _ = ∑ a : α, f (τ a) := by
          simpa using (Finset.sum_fiberwise (s := (Finset.univ : Finset α)) (g := τ)
            (f := fun a => f (τ a)))

/--
Taking a finite minimum after lifting along a surjective class map gives the
same value as taking the minimum on the class space.  Surjectivity is packaged
as chosen fiber representatives.
-/
theorem finiteMin_comp_of_fiberRepresentatives {α κ : Type*}
    [Fintype α] [Fintype κ] [Nonempty α] [Nonempty κ]
    (τ : α → κ) (reps : FiberRepresentatives τ) (f : κ → ℝ) :
    finiteMin (fun a : α => f (τ a)) = finiteMin f := by
  unfold finiteMin
  apply le_antisymm
  · apply Finset.le_inf'
    intro k _hk
    have hle := Finset.inf'_le (s := (Finset.univ : Finset α))
      (f := fun a : α => f (τ a)) (b := reps.repr k) (by simp)
    simpa [reps.repr_spec k] using hle
  · apply Finset.le_inf'
    intro a _ha
    exact Finset.inf'_le (s := (Finset.univ : Finset κ))
      (f := f) (b := τ a) (by simp)

end Policy
end AppliedModelingLib
