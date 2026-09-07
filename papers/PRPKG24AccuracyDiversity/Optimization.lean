import PRPKG24AccuracyDiversity.Representation
import AppliedModelingLib.Foundations.Math.Asymptotics

open scoped BigOperators

namespace PRPKG24AccuracyDiversity

namespace ConsumptionModel

/--
Finite code for allocations of exactly `N` items.

Each count is stored as a `Fin (N + 1)`, so the search space is finite. The
subtype proof records that the decoded allocation has total `N`.
-/
abbrev FeasibleAllocationCode (T N : ℕ) :=
  AppliedModelingLib.Allocation.FeasibleCode (ItemType T) N

namespace FeasibleAllocationCode

/-- Decode a finite allocation code into the library's count-allocation type. -/
abbrev toAllocation {T N : ℕ} (x : FeasibleAllocationCode T N) :
    CountAllocation T :=
  AppliedModelingLib.Allocation.FeasibleCode.toAllocation x

@[simp] theorem toAllocation_count {T N : ℕ}
    (x : FeasibleAllocationCode T N) (t : ItemType T) :
    x.toAllocation.count t = (x.1 t).val := rfl

/-- Decoded feasible codes have the requested total. -/
theorem toAllocation_feasible {T N : ℕ}
    (x : FeasibleAllocationCode T N) :
    FeasibleAtTotal N x.toAllocation :=
  AppliedModelingLib.Allocation.FeasibleCode.toAllocation_hasTotal x

/-- A fixed-total allocation can be encoded in the finite search space. -/
def ofFeasible {T N : ℕ} (a : CountAllocation T)
    (hfeas : FeasibleAtTotal N a) : FeasibleAllocationCode T N :=
  AppliedModelingLib.Allocation.FeasibleCode.ofHasTotal a hfeas

@[simp] theorem toAllocation_ofFeasible {T N : ℕ}
    (a : CountAllocation T) (hfeas : FeasibleAtTotal N a) :
    (ofFeasible a hfeas).toAllocation = a :=
  AppliedModelingLib.Allocation.FeasibleCode.toAllocation_ofHasTotal a hfeas

/-- A canonical feasible code putting all `N` items on one available type. -/
noncomputable def singleton {T N : ℕ} [Nonempty (ItemType T)] :
    FeasibleAllocationCode T N :=
  AppliedModelingLib.Allocation.FeasibleCode.singleton (κ := ItemType T) (N := N)

end FeasibleAllocationCode

/-- A finite fixed-total count-allocation problem always has an objective maximizer. -/
theorem exists_isOptimalAtTotal {T : ℕ} [Nonempty (ItemType T)]
    (M : ConsumptionModel T) (N : ℕ) :
    ∃ a : CountAllocation T, M.IsOptimalAtTotal N a := by
  obtain ⟨a, htotal, hopt⟩ :=
    AppliedModelingLib.Allocation.exists_isOptimalAtTotal
      M.likelihood M.valueOfCount N
  refine ⟨a, ?_, ?_⟩
  · exact htotal
  · intro b hb
    exact hopt b hb

/-- Objective values attainable by allocations of exactly `N` items. -/
def attainableValuesAtTotal {T : ℕ}
    (M : ConsumptionModel T) (N : ℕ) : Set ℝ := {r | ∃ a : CountAllocation T, FeasibleAtTotal N a ∧ r = M.objective a}

/-- Supremal objective value among allocations of size `N`. -/
noncomputable def optimalValueAtTotal {T : ℕ}
    (M : ConsumptionModel T) (N : ℕ) : ℝ := sSup (attainableValuesAtTotal M N)

/-- The set of optimal allocations of size `N`. -/
def optimalAllocationsAtTotal {T : ℕ}
    (M : ConsumptionModel T) (N : ℕ) : Set (CountAllocation T) := {a | M.IsOptimalAtTotal N a}

/--
A theorem target: every optimal allocation at size `N` approximately matches a
specified γ-homogeneity profile.
-/
noncomputable def ApproxHomogeneityOfOptima {T : ℕ}
    (M : ConsumptionModel T) (N : ℕ) (G : GammaHomogeneityProfile T) (ε : ℝ) : Prop := ∀ a : CountAllocation T, M.IsOptimalAtTotal N a → G.Approx a ε

/--
A theorem target for asymptotic statements: there exists an error schedule tending to zero
such that all positive-size optimal allocations approximately match the profile.

The target intentionally ignores `N = 0`: the paper's claims are limits as
`n → ∞`, and zero-size allocations need not match a nonzero target profile.
-/
def AsymptoticHomogeneityTarget {T : ℕ}
    (Mseq : ℕ → ConsumptionModel T) (G : GammaHomogeneityProfile T)
    (TendsToZero : (ℕ → ℝ) → Prop) : Prop :=
  ∃ ε : ℕ → ℝ,
    TendsToZero ε ∧ ∀ N a, 0 < N → (Mseq N).IsOptimalAtTotal N a → G.Approx a (ε N)

/-- The default PRPKG asymptotic target using the reusable filter-based zero predicate. -/
def AsymptoticHomogeneity {T : ℕ}
    (Mseq : ℕ → ConsumptionModel T) (G : GammaHomogeneityProfile T) : Prop :=
  AsymptoticHomogeneityTarget Mseq G AppliedModelingLib.Math.TendsToZero

theorem AsymptoticHomogeneityTarget.mono_rate {T : ℕ}
    {Mseq : ℕ → ConsumptionModel T} {G : GammaHomogeneityProfile T}
    {Rate₁ Rate₂ : (ℕ → ℝ) → Prop}
    (hRate : ∀ ε, Rate₁ ε → Rate₂ ε) :
    AsymptoticHomogeneityTarget Mseq G Rate₁ →
      AsymptoticHomogeneityTarget Mseq G Rate₂ := by
  intro ⟨ε, hε, happrox⟩
  exact ⟨ε, hRate ε hε, happrox⟩

theorem AsymptoticHomogeneityTarget.of_exactInvRate {T : ℕ}
    {Mseq : ℕ → ConsumptionModel T} {G : GammaHomogeneityProfile T} :
    AsymptoticHomogeneityTarget Mseq G AppliedModelingLib.Math.ExactInvRate →
      AsymptoticHomogeneity Mseq G :=
  AsymptoticHomogeneityTarget.mono_rate
    (fun ε hε => AppliedModelingLib.Math.ExactInvRate_implies_TendsToZero ε hε)

theorem AsymptoticHomogeneityTarget.of_exactInvSqrtRate {T : ℕ}
    {Mseq : ℕ → ConsumptionModel T} {G : GammaHomogeneityProfile T} :
    AsymptoticHomogeneityTarget Mseq G AppliedModelingLib.Math.ExactInvSqrtRate →
      AsymptoticHomogeneity Mseq G :=
  AsymptoticHomogeneityTarget.mono_rate
    (fun ε hε => AppliedModelingLib.Math.ExactInvSqrtRate_implies_TendsToZero ε hε)

/--
Uniform `O(1)` count error for every positive-size optimum gives a paper-style
exact `C / N` asymptotic homogeneity target.
-/
theorem AsymptoticHomogeneityTarget.of_uniform_count_abs_error {T : ℕ}
    {Mseq : ℕ → ConsumptionModel T} {G : GammaHomogeneityProfile T} {C : ℝ}
    (hC : 0 < C)
    (hclose :
      ∀ N (a : CountAllocation T), 0 < N → (Mseq N).IsOptimalAtTotal N a →
        ∀ t, |(a.count t : ℝ) - (N : ℝ) * G.targetShare t| ≤ C) :
    AsymptoticHomogeneityTarget Mseq G AppliedModelingLib.Math.ExactInvRate := by
  refine ⟨fun N => C / (N : ℝ), ?_, ?_⟩
  · exact ⟨C, hC, fun N => rfl⟩
  · intro N a hN hopt
    exact GammaHomogeneityProfile.approx_of_count_abs_error
      G a hopt.1 hN (hclose N a hN hopt)

end ConsumptionModel
end PRPKG24AccuracyDiversity
