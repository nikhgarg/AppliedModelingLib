import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Continuum Cutoff Matching Markets

This module provides a reusable interface for continuum matching markets
represented by cutoff vectors.  It is designed for formalizations that use a
supply/demand theorem while keeping the model-level identification of "stable
matching", "demand", and "market clearing" outside the shared API.

## Main declarations

- `CutoffMarket`: an abstract cutoff-market surface.
- `SupplyDemandInterface`: stable matchings are exactly cutoff-demand
  matchings at market-clearing cutoffs.
- `MarketClearingCapacityInterface`: exact-fill market-clearing semantics,
  used when a paper specializes clearing to aggregate demand equaling capacity.
- `CompleteLatticeOn`: a lightweight complete-lattice statement over a
  predicate and a relation.
- `CutoffLatticeInterface`: market-clearing cutoffs form a complete lattice.
- `unique_of_least_greatest_eq`: a generic uniqueness consequence used by
  symmetric equal-cutoff arguments.
- `constantCoordinates_of_coordinatewise_least_swap_closed`: a reusable
  finite-coordinate symmetry lemma for equal-cutoff arguments.
-/

namespace AppliedModelingLib
namespace Matching

universe u v w x

/--
Abstract continuum cutoff market.

The `Student` and `College` carriers are intentionally external parameters.
The source-specific paper layer decides whether students are values, types,
or richer signal/preference records, and proves that its source definitions
instantiate this generic surface.
-/
structure CutoffMarket (Student : Type u) (College : Type v) where
  /-- Cutoff vectors or an equivalent cutoff object. -/
  Cutoff : Type w
  /-- Matchings in the source model. -/
  Matching : Type x
  /-- Student/type demand at a cutoff. -/
  demandAt : Cutoff → Student → Option College
  /-- Aggregate demand for a college at a cutoff. -/
  aggregateDemand : Cutoff → College → ℝ
  /-- College capacity or supply. -/
  capacity : College → ℝ
  /-- Source-model stability predicate. -/
  isStable : Matching → Prop
  /-- Market-clearing cutoff predicate. -/
  marketClearing : Cutoff → Prop
  /-- A matching is represented by demand at this cutoff. -/
  representedByCutoff : Matching → Cutoff → Prop

namespace CutoffMarket

variable {Student : Type u} {College : Type v}

/-- Demand correspondence notation for a cutoff market. -/
abbrev Demand (M : CutoffMarket Student College) :
    M.Cutoff → Student → Option College :=
  M.demandAt

/-- Aggregate demand notation for a cutoff market. -/
abbrev AggregateDemand (M : CutoffMarket Student College) :
    M.Cutoff → College → ℝ :=
  M.aggregateDemand

/-- Capacity/supply notation for a cutoff market. -/
abbrev Capacity (M : CutoffMarket Student College) : College → ℝ :=
  M.capacity

/-- Stability notation for a cutoff market. -/
abbrev Stable (M : CutoffMarket Student College) : M.Matching → Prop :=
  M.isStable

/-- Market-clearing notation for a cutoff market. -/
abbrev MarketClearing (M : CutoffMarket Student College) : M.Cutoff → Prop :=
  M.marketClearing

/-- Cutoff representation notation for a cutoff market. -/
abbrev RepresentedByCutoff (M : CutoffMarket Student College) :
    M.Matching → M.Cutoff → Prop :=
  M.representedByCutoff

end CutoffMarket

/--
Supply/demand interface for cutoff markets.

This is the reusable theorem shape needed from the Azevedo-Leshno supply and
demand lemma by the Peng-Garg matching-market papers.
-/
structure SupplyDemandInterface {Student : Type u} {College : Type v}
    (M : CutoffMarket Student College) : Prop where
  /-- Stable matchings are exactly matchings represented by market-clearing cutoffs. -/
  stable_iff_exists_marketClearing_cutoff :
    ∀ μ : M.Matching,
      M.Stable μ ↔
        ∃ P : M.Cutoff, M.MarketClearing P ∧ M.RepresentedByCutoff μ P
  /-- Every market-clearing cutoff induces some stable matching. -/
  marketClearing_induces_stable :
    ∀ P : M.Cutoff,
      M.MarketClearing P →
        ∃ μ : M.Matching, M.Stable μ ∧ M.RepresentedByCutoff μ P

namespace SupplyDemandInterface

variable {Student : Type u} {College : Type v}
variable {M : CutoffMarket Student College}

/--
Choose a market-clearing cutoff representing a stable matching.

This is the reusable Azevedo-Leshno bridge needed by paper arguments that
begin with an arbitrary stable matching and then reason analytically about a
specific cutoff vector.
-/
noncomputable def marketClearingCutoffOfStable
    (I : SupplyDemandInterface M) {μ : M.Matching} (hμ : M.Stable μ) :
    M.Cutoff :=
  Classical.choose ((I.stable_iff_exists_marketClearing_cutoff μ).1 hμ)

/-- Stable matchings have market-clearing cutoff representations. -/
theorem exists_marketClearing_cutoff_of_stable
    (I : SupplyDemandInterface M) {μ : M.Matching} (hμ : M.Stable μ) :
    ∃ P : M.Cutoff, M.MarketClearing P ∧ M.RepresentedByCutoff μ P :=
  (I.stable_iff_exists_marketClearing_cutoff μ).1 hμ

/-- The chosen cutoff of a stable matching is market clearing. -/
theorem marketClearingCutoffOfStable_marketClearing
    (I : SupplyDemandInterface M) {μ : M.Matching} (hμ : M.Stable μ) :
    M.MarketClearing (I.marketClearingCutoffOfStable hμ) :=
  (Classical.choose_spec (I.exists_marketClearing_cutoff_of_stable hμ)).1

/-- The chosen cutoff of a stable matching represents that matching. -/
theorem marketClearingCutoffOfStable_represents
    (I : SupplyDemandInterface M) {μ : M.Matching} (hμ : M.Stable μ) :
    M.RepresentedByCutoff μ (I.marketClearingCutoffOfStable hμ) :=
  (Classical.choose_spec (I.exists_marketClearing_cutoff_of_stable hμ)).2

/--
Any property true of all market-clearing cutoffs holds for the chosen cutoff
representing a stable matching.
-/
theorem property_marketClearingCutoffOfStable
    (I : SupplyDemandInterface M) {μ : M.Matching} (hμ : M.Stable μ)
    {property : M.Cutoff → Prop}
    (hproperty : ∀ P : M.Cutoff, M.MarketClearing P → property P) :
    property (I.marketClearingCutoffOfStable hμ) :=
  hproperty _ (I.marketClearingCutoffOfStable_marketClearing hμ)

/--
If the market-clearing cutoff is unique, the selected cutoff is independent of
the stable matching used to obtain it.
-/
theorem marketClearingCutoffOfStable_eq_of_unique_marketClearing
    (I : SupplyDemandInterface M) {μ ν : M.Matching}
    (hμ : M.Stable μ) (hν : M.Stable ν)
    (hunique :
      ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q) :
    I.marketClearingCutoffOfStable hμ =
      I.marketClearingCutoffOfStable hν :=
  hunique _ _
    (I.marketClearingCutoffOfStable_marketClearing hμ)
    (I.marketClearingCutoffOfStable_marketClearing hν)

/-- A matching represented by a market-clearing cutoff is stable. -/
theorem stable_of_marketClearing_cutoff
    (I : SupplyDemandInterface M) {μ : M.Matching} {P : M.Cutoff}
    (hP : M.MarketClearing P) (hrep : M.RepresentedByCutoff μ P) :
    M.Stable μ :=
  (I.stable_iff_exists_marketClearing_cutoff μ).2 ⟨P, hP, hrep⟩

/-- If a market-clearing cutoff exists, then a stable matching exists. -/
theorem exists_stable_of_exists_marketClearing
    (I : SupplyDemandInterface M)
    (hne : ∃ P : M.Cutoff, M.MarketClearing P) :
    ∃ μ : M.Matching, M.Stable μ := by
  rcases hne with ⟨P, hP⟩
  rcases I.marketClearing_induces_stable P hP with ⟨μ, hμ, _hrep⟩
  exact ⟨μ, hμ⟩

end SupplyDemandInterface

/--
Exact-fill semantics for market-clearing cutoffs.

Some papers specialize the Azevedo-Leshno clearing condition to settings where
every college is active, so market clearing means aggregate demand equals
capacity at every college.  This interface keeps that semantic bridge explicit
instead of baking it into the abstract `CutoffMarket.marketClearing` predicate.
-/
structure MarketClearingCapacityInterface {Student : Type u} {College : Type v}
    (M : CutoffMarket Student College) : Prop where
  /-- A market-clearing cutoff fills every college exactly. -/
  marketClearing_aggregateDemand_eq_capacity :
    ∀ P : M.Cutoff, M.MarketClearing P →
      ∀ c : College, M.aggregateDemand P c = M.capacity c

namespace MarketClearingCapacityInterface

variable {Student : Type u} {College : Type v}
variable {M : CutoffMarket Student College}

/-- Exact-fill capacity equality at a market-clearing cutoff. -/
theorem aggregateDemand_eq_capacity
    (K : MarketClearingCapacityInterface M) {P : M.Cutoff}
    (hP : M.MarketClearing P) (c : College) :
    M.aggregateDemand P c = M.capacity c :=
  K.marketClearing_aggregateDemand_eq_capacity P hP c

/-- Exact-fill capacity equality summed over a finite active block. -/
theorem aggregateDemand_sum_eq_capacity_sum
    (K : MarketClearingCapacityInterface M) {P : M.Cutoff}
    (hP : M.MarketClearing P) (active : Finset College) :
    Finset.sum active (fun c => M.aggregateDemand P c) =
      Finset.sum active (fun c => M.capacity c) :=
  Finset.sum_congr rfl (by
    intro c _hc
    exact K.aggregateDemand_eq_capacity hP c)

/--
The Azevedo-Leshno selected cutoff of a stable matching satisfies exact-fill
capacity equality whenever the source model provides exact-fill clearing
semantics.
-/
theorem marketClearingCutoffOfStable_aggregateDemand_eq_capacity
    (K : MarketClearingCapacityInterface M) (I : SupplyDemandInterface M)
    {μ : M.Matching} (hμ : M.Stable μ) (c : College) :
    M.aggregateDemand (I.marketClearingCutoffOfStable hμ) c =
      M.capacity c :=
  K.aggregateDemand_eq_capacity
    (I.marketClearingCutoffOfStable_marketClearing hμ) c

/--
The Azevedo-Leshno selected cutoff of a stable matching satisfies exact-fill
capacity equality summed over any finite active block.
-/
theorem marketClearingCutoffOfStable_aggregateDemand_sum_eq_capacity_sum
    (K : MarketClearingCapacityInterface M) (I : SupplyDemandInterface M)
    {μ : M.Matching} (hμ : M.Stable μ) (active : Finset College) :
    Finset.sum active
        (fun c => M.aggregateDemand (I.marketClearingCutoffOfStable hμ) c) =
      Finset.sum active (fun c => M.capacity c) :=
  K.aggregateDemand_sum_eq_capacity_sum
    (I.marketClearingCutoffOfStable_marketClearing hμ) active

end MarketClearingCapacityInterface

/-- `x` is an upper bound of `S`, among elements satisfying `valid`. -/
def IsUpperBoundOn {α : Type u} (valid : α → Prop)
    (le : α → α → Prop) (S : Set α) (x : α) : Prop :=
  valid x ∧ ∀ y, S y → valid y → le y x

/-- `x` is a lower bound of `S`, among elements satisfying `valid`. -/
def IsLowerBoundOn {α : Type u} (valid : α → Prop)
    (le : α → α → Prop) (S : Set α) (x : α) : Prop :=
  valid x ∧ ∀ y, S y → valid y → le x y

/-- `x` is a least upper bound of `S`, among elements satisfying `valid`. -/
def IsLeastUpperBoundOn {α : Type u} (valid : α → Prop)
    (le : α → α → Prop) (S : Set α) (x : α) : Prop :=
  IsUpperBoundOn valid le S x ∧
    ∀ z, IsUpperBoundOn valid le S z → le x z

/-- `x` is a greatest lower bound of `S`, among elements satisfying `valid`. -/
def IsGreatestLowerBoundOn {α : Type u} (valid : α → Prop)
    (le : α → α → Prop) (S : Set α) (x : α) : Prop :=
  IsLowerBoundOn valid le S x ∧
    ∀ z, IsLowerBoundOn valid le S z → le z x

/--
Complete-lattice structure on the elements satisfying `valid`.

This avoids committing the reusable market API to a global `CompleteLattice`
instance on all possible cutoff vectors.  The paper layer can later identify
this relation with coordinatewise order.  The primitive closure fields below
cover nonempty valid families; `exists_lub` and `exists_glb` recover the
empty-family endpoints whenever the valid carrier is nonempty.
-/
structure CompleteLatticeOn {α : Type u} (valid : α → Prop)
    (le : α → α → Prop) : Prop where
  /-- A complete lattice has a nonempty carrier, so the empty-family extrema
  can be represented by valid elements. -/
  exists_valid : ∃ x, valid x
  le_refl : ∀ {x}, valid x → le x x
  le_trans : ∀ {x y z}, valid x → valid y → valid z →
    le x y → le y z → le x z
  le_antisymm : ∀ {x y}, valid x → valid y → le x y → le y x → x = y
  sup_exists : ∀ S : Set α,
    (∃ x, S x ∧ valid x) →
      ∃ x, IsLeastUpperBoundOn valid le S x
  inf_exists : ∀ S : Set α,
    (∃ x, S x ∧ valid x) →
      ∃ x, IsGreatestLowerBoundOn valid le S x

namespace CompleteLatticeOn

variable {α : Type u} {valid : α → Prop} {le : α → α → Prop}

/-- The set of all valid elements has a greatest element when nonempty. -/
theorem exists_greatest
    (L : CompleteLatticeOn valid le) (hne : ∃ x, valid x) :
    ∃ top, valid top ∧ ∀ x, valid x → le x top := by
  rcases L.sup_exists {x | valid x} (by
      rcases hne with ⟨x, hx⟩
      exact ⟨x, hx, hx⟩) with ⟨top, htop⟩
  refine ⟨top, htop.1.1, ?_⟩
  intro x hx
  exact htop.1.2 x hx hx

/-- The set of all valid elements has a least element when nonempty. -/
theorem exists_least
    (L : CompleteLatticeOn valid le) (hne : ∃ x, valid x) :
    ∃ bot, valid bot ∧ ∀ x, valid x → le bot x := by
  rcases L.inf_exists {x | valid x} (by
      rcases hne with ⟨x, hx⟩
      exact ⟨x, hx, hx⟩) with ⟨bot, hbot⟩
  refine ⟨bot, hbot.1.1, ?_⟩
  intro x hx
  exact hbot.1.2 x hx hx

/-- Every valid subset has a least upper bound when the valid carrier is nonempty. -/
theorem exists_lub
    (L : CompleteLatticeOn valid le) (hne : ∃ x, valid x) (S : Set α) :
    ∃ x, IsLeastUpperBoundOn valid le S x := by
  by_cases hS : ∃ x, S x ∧ valid x
  · exact L.sup_exists S hS
  · rcases L.exists_least hne with ⟨bot, hbot_valid, hbot_le⟩
    refine ⟨bot, ?_⟩
    constructor
    · refine ⟨hbot_valid, ?_⟩
      intro y hy hy_valid
      exact False.elim (hS ⟨y, hy, hy_valid⟩)
    · intro z hz
      exact hbot_le z hz.1

/-- Every valid subset has a greatest lower bound when the valid carrier is nonempty. -/
theorem exists_glb
    (L : CompleteLatticeOn valid le) (hne : ∃ x, valid x) (S : Set α) :
    ∃ x, IsGreatestLowerBoundOn valid le S x := by
  by_cases hS : ∃ x, S x ∧ valid x
  · exact L.inf_exists S hS
  · rcases L.exists_greatest hne with ⟨top, htop_valid, hle_top⟩
    refine ⟨top, ?_⟩
    constructor
    · refine ⟨htop_valid, ?_⟩
      intro y hy hy_valid
      exact False.elim (hS ⟨y, hy, hy_valid⟩)
    · intro z hz
      exact hle_top z hz.1

/--
If the least and greatest valid elements coincide, then the valid element is
unique.  Symmetric equal-cutoff arguments reduce to this kind of order-theoretic
fact after a lattice theorem supplies extrema and model symmetries identify
their scalar values.
-/
theorem unique_of_least_greatest_eq
    (L : CompleteLatticeOn valid le)
    {bot top : α}
    (hbot : valid bot ∧ ∀ x, valid x → le bot x)
    (htop : valid top ∧ ∀ x, valid x → le x top)
    (h_eq : bot = top) :
    ∀ x y, valid x → valid y → x = y := by
  intro x y hx hy
  have hxy : le x y := by
    have hx_top : le x top := htop.2 x hx
    have htop_y : le top y := by
      simpa [h_eq] using hbot.2 y hy
    exact L.le_trans hx htop.1 hy hx_top htop_y
  have hyx : le y x := by
    have hy_top : le y top := htop.2 y hy
    have htop_x : le top x := by
      simpa [h_eq] using hbot.2 x hx
    exact L.le_trans hy htop.1 hx hy_top htop_x
  exact L.le_antisymm hx hy hxy hyx

end CompleteLatticeOn

/-- Coordinatewise order on real cutoff vectors. -/
def CoordinatewiseLe {College : Type v} (P Q : College → ℝ) : Prop :=
  ∀ c, P c ≤ Q c

/-- A real cutoff vector has a single common coordinate value. -/
def ConstantCoordinates {College : Type v} (P : College → ℝ) : Prop :=
  ∃ x : ℝ, ∀ c, P c = x

/-- Swap two coordinates of a real cutoff vector. -/
def coordinateSwap {College : Type v} [DecidableEq College]
    (P : College → ℝ) (c d : College) : College → ℝ :=
  fun e => P (Equiv.swap c d e)

/--
A coordinatewise least element of a swap-closed set of real cutoff vectors is
constant.  This is the finite-dimensional symmetry step used in equal-cutoff
proofs: swapping two coordinates of the least clearing cutoff gives another
clearing cutoff, so leastness forces both coordinate inequalities.
-/
theorem constantCoordinates_of_coordinatewise_least_swap_closed
    {College : Type v} [DecidableEq College]
    {Z : Set (College → ℝ)} {bot : College → ℝ}
    (hbotZ : bot ∈ Z)
    (hleast : ∀ P : College → ℝ, P ∈ Z → CoordinatewiseLe bot P)
    (hswap :
      ∀ P : College → ℝ, P ∈ Z → ∀ c d : College,
        coordinateSwap P c d ∈ Z) :
    ConstantCoordinates bot := by
  classical
  by_cases hne : Nonempty College
  · rcases hne with ⟨c0⟩
    refine ⟨bot c0, ?_⟩
    intro c
    have hswapZ : coordinateSwap bot c0 c ∈ Z :=
      hswap bot hbotZ c0 c
    have hle_c_c0 : bot c ≤ bot c0 := by
      have h := hleast (coordinateSwap bot c0 c) hswapZ c
      simpa [CoordinatewiseLe, coordinateSwap] using h
    have hle_c0_c : bot c0 ≤ bot c := by
      have h := hleast (coordinateSwap bot c0 c) hswapZ c0
      simpa [CoordinatewiseLe, coordinateSwap] using h
    exact le_antisymm hle_c_c0 hle_c0_c
  · refine ⟨0, ?_⟩
    intro c
    exact False.elim (hne ⟨c⟩)

/--
A coordinatewise greatest element of a swap-closed set of real cutoff vectors is
constant.
-/
theorem constantCoordinates_of_coordinatewise_greatest_swap_closed
    {College : Type v} [DecidableEq College]
    {Z : Set (College → ℝ)} {top : College → ℝ}
    (htopZ : top ∈ Z)
    (hgreatest : ∀ P : College → ℝ, P ∈ Z → CoordinatewiseLe P top)
    (hswap :
      ∀ P : College → ℝ, P ∈ Z → ∀ c d : College,
        coordinateSwap P c d ∈ Z) :
    ConstantCoordinates top := by
  classical
  by_cases hne : Nonempty College
  · rcases hne with ⟨c0⟩
    refine ⟨top c0, ?_⟩
    intro c
    have hswapZ : coordinateSwap top c0 c ∈ Z :=
      hswap top htopZ c0 c
    have hle_c0_c : top c0 ≤ top c := by
      have h := hgreatest (coordinateSwap top c0 c) hswapZ c
      simpa [CoordinatewiseLe, coordinateSwap] using h
    have hle_c_c0 : top c ≤ top c0 := by
      have h := hgreatest (coordinateSwap top c0 c) hswapZ c0
      simpa [CoordinatewiseLe, coordinateSwap] using h
    exact le_antisymm hle_c_c0 hle_c0_c
  · refine ⟨0, ?_⟩
    intro c
    exact False.elim (hne ⟨c⟩)

/--
Both coordinatewise extrema of a swap-closed set of real cutoff vectors are
constant.
-/
theorem constantCoordinates_of_coordinatewise_extrema_swap_closed
    {College : Type v} [DecidableEq College]
    {Z : Set (College → ℝ)} {bot top : College → ℝ}
    (hbotZ : bot ∈ Z) (htopZ : top ∈ Z)
    (hleast : ∀ P : College → ℝ, P ∈ Z → CoordinatewiseLe bot P)
    (hgreatest : ∀ P : College → ℝ, P ∈ Z → CoordinatewiseLe P top)
    (hswap :
      ∀ P : College → ℝ, P ∈ Z → ∀ c d : College,
        coordinateSwap P c d ∈ Z) :
    ConstantCoordinates bot ∧ ConstantCoordinates top :=
  ⟨constantCoordinates_of_coordinatewise_least_swap_closed
      hbotZ hleast hswap,
    constantCoordinates_of_coordinatewise_greatest_swap_closed
      htopZ hgreatest hswap⟩

/--
Reusable equal-cutoff theorem for symmetric coordinate cutoff markets.  If a
market-clearing set is closed under coordinate swaps, has coordinatewise least
and greatest elements, and constant cutoff vectors clear a strictly decreasing
scalar demand equation, then every market-clearing cutoff vector is unique.

This packages the common source proof: symmetry makes the two extrema constant,
strict scalar clearing identifies their common values, and every clearing
cutoff is trapped coordinatewise between equal extrema.
-/
theorem unique_coordinatewise_cutoff_of_swap_closed_strict_antitone_scalar_clearing
    {College : Type v} [DecidableEq College]
    {Z : Set (College → ℝ)} {bot top : College → ℝ}
    {demand : ℝ → ℝ} {supply : ℝ}
    (hbotZ : bot ∈ Z) (htopZ : top ∈ Z)
    (hleast : ∀ P : College → ℝ, P ∈ Z → CoordinatewiseLe bot P)
    (hgreatest : ∀ P : College → ℝ, P ∈ Z → CoordinatewiseLe P top)
    (hswap :
      ∀ P : College → ℝ, P ∈ Z → ∀ c d : College,
        coordinateSwap P c d ∈ Z)
    (hclearing :
      ∀ P : College → ℝ, ∀ x : ℝ,
        P ∈ Z → (∀ c, P c = x) → demand x = supply)
    (hstrict : ∀ x y : ℝ, x < y → demand y < demand x) :
    ∀ P Q : College → ℝ, P ∈ Z → Q ∈ Z → P = Q := by
  classical
  have hconst :
      ConstantCoordinates bot ∧ ConstantCoordinates top :=
    constantCoordinates_of_coordinatewise_extrema_swap_closed
      hbotZ htopZ hleast hgreatest hswap
  rcases hconst.1 with ⟨x, hx⟩
  rcases hconst.2 with ⟨y, hy⟩
  have hxy : x = y := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hlt_demand : demand y < demand x := hstrict x y hlt
      rw [hclearing bot x hbotZ hx, hclearing top y htopZ hy] at hlt_demand
      exact (lt_irrefl supply) hlt_demand
    · have hlt_demand : demand x < demand y := hstrict y x hgt
      rw [hclearing bot x hbotZ hx, hclearing top y htopZ hy] at hlt_demand
      exact (lt_irrefl supply) hlt_demand
  have hbot_top : bot = top := by
    funext c
    rw [hx c, hy c, hxy]
  intro P Q hP hQ
  have hP_eq_bot : P = bot := by
    funext c
    have hbot_le_P : bot c ≤ P c := hleast P hP c
    have hP_le_bot : P c ≤ bot c := by
      simpa [← hbot_top] using hgreatest P hP c
    exact le_antisymm hP_le_bot hbot_le_P
  have hQ_eq_bot : Q = bot := by
    funext c
    have hbot_le_Q : bot c ≤ Q c := hleast Q hQ c
    have hQ_le_bot : Q c ≤ bot c := by
      simpa [← hbot_top] using hgreatest Q hQ c
    exact le_antisymm hQ_le_bot hbot_le_Q
  rw [hP_eq_bot, hQ_eq_bot]

/--
Complete-lattice version of the symmetric equal-cutoff theorem.  This is the
source-shaped form used when a lattice theorem supplies nonempty coordinatewise
least and greatest market-clearing cutoffs, while model-specific arguments
supply swap closure and strict scalar clearing.
-/
theorem unique_coordinatewise_cutoff_of_complete_lattice_swap_closed_strict_antitone_scalar_clearing
    {College : Type v} [DecidableEq College]
    {marketClearing : (College → ℝ) → Prop}
    {demand : ℝ → ℝ} {supply : ℝ}
    (hne : ∃ P : College → ℝ, marketClearing P)
    (L : CompleteLatticeOn marketClearing CoordinatewiseLe)
    (hswap :
      ∀ P : College → ℝ, marketClearing P → ∀ c d : College,
        marketClearing (coordinateSwap P c d))
    (hclearing :
      ∀ P : College → ℝ, ∀ x : ℝ,
        marketClearing P → (∀ c, P c = x) → demand x = supply)
    (hstrict : ∀ x y : ℝ, x < y → demand y < demand x) :
    ∀ P Q : College → ℝ, marketClearing P → marketClearing Q → P = Q := by
  classical
  rcases L.exists_least hne with ⟨bot, hbot⟩
  rcases L.exists_greatest hne with ⟨top, htop⟩
  exact
    unique_coordinatewise_cutoff_of_swap_closed_strict_antitone_scalar_clearing
      (Z := {P : College → ℝ | marketClearing P})
      (bot := bot) (top := top)
      (demand := demand) (supply := supply)
      hbot.1 htop.1 hbot.2 htop.2 hswap hclearing hstrict

/--
Reusable lattice interface for market-clearing cutoffs.

This is a reusable complete-lattice surface for market-clearing cutoff
arguments.  It is intentionally broader than a tiny extrema certificate so that
future formalizations can reuse the complete-lattice statement.
-/
structure CutoffLatticeInterface {Student : Type u} {College : Type v}
    (M : CutoffMarket Student College) where
  /-- The order on cutoff vectors, typically coordinatewise order. -/
  leCutoff : M.Cutoff → M.Cutoff → Prop
  /-- The market-clearing cutoff set is nonempty. -/
  nonempty_marketClearing : ∃ P : M.Cutoff, M.MarketClearing P
  /-- Market-clearing cutoffs form a complete lattice in this order. -/
  complete_marketClearing :
    CompleteLatticeOn M.MarketClearing leCutoff

namespace CutoffLatticeInterface

variable {Student : Type u} {College : Type v}
variable {M : CutoffMarket Student College}

/-- The greatest market-clearing cutoff supplied by the lattice interface. -/
noncomputable def greatestMarketClearingCutoff
    (L : CutoffLatticeInterface M) : M.Cutoff :=
  Classical.choose
    (L.complete_marketClearing.exists_greatest L.nonempty_marketClearing)

/-- The least market-clearing cutoff supplied by the lattice interface. -/
noncomputable def leastMarketClearingCutoff
    (L : CutoffLatticeInterface M) : M.Cutoff :=
  Classical.choose
    (L.complete_marketClearing.exists_least L.nonempty_marketClearing)

/-- A market-clearing cutoff set with a complete lattice has a greatest cutoff. -/
theorem exists_greatest_marketClearing
    (L : CutoffLatticeInterface M) :
    ∃ top : M.Cutoff,
      M.MarketClearing top ∧
        ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff P top :=
  L.complete_marketClearing.exists_greatest L.nonempty_marketClearing

/-- A market-clearing cutoff set with a complete lattice has a least cutoff. -/
theorem exists_least_marketClearing
    (L : CutoffLatticeInterface M) :
    ∃ bot : M.Cutoff,
      M.MarketClearing bot ∧
        ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff bot P :=
  L.complete_marketClearing.exists_least L.nonempty_marketClearing

/-- The named greatest cutoff is market clearing. -/
theorem greatestMarketClearingCutoff_marketClearing
    (L : CutoffLatticeInterface M) :
    M.MarketClearing (L.greatestMarketClearingCutoff) :=
  (Classical.choose_spec L.exists_greatest_marketClearing).1

/-- Every market-clearing cutoff is below the named greatest cutoff. -/
theorem le_greatestMarketClearingCutoff
    (L : CutoffLatticeInterface M) {P : M.Cutoff}
    (hP : M.MarketClearing P) :
    L.leCutoff P L.greatestMarketClearingCutoff :=
  (Classical.choose_spec L.exists_greatest_marketClearing).2 P hP

/-- The named least cutoff is market clearing. -/
theorem leastMarketClearingCutoff_marketClearing
    (L : CutoffLatticeInterface M) :
    M.MarketClearing (L.leastMarketClearingCutoff) :=
  (Classical.choose_spec L.exists_least_marketClearing).1

/-- The named least cutoff is below every market-clearing cutoff. -/
theorem leastMarketClearingCutoff_le
    (L : CutoffLatticeInterface M) {P : M.Cutoff}
    (hP : M.MarketClearing P) :
    L.leCutoff L.leastMarketClearingCutoff P :=
  (Classical.choose_spec L.exists_least_marketClearing).2 P hP

/--
If the least and greatest market-clearing cutoffs coincide, the market-clearing
cutoff is unique.
-/
theorem unique_marketClearing_of_least_greatest_eq
    (L : CutoffLatticeInterface M)
    {bot top : M.Cutoff}
    (hbot :
      M.MarketClearing bot ∧
        ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff bot P)
    (htop :
      M.MarketClearing top ∧
        ∀ P : M.Cutoff, M.MarketClearing P → L.leCutoff P top)
    (h_eq : bot = top) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q :=
  L.complete_marketClearing.unique_of_least_greatest_eq hbot htop h_eq

/--
Coordinate-representation version of the symmetric equal-cutoff theorem.

This is the reusable bridge between an Azevedo-Leshno-style cutoff lattice and
paper models whose cutoff objects are represented by real coordinate vectors.
If the lattice order implies coordinatewise order under `coord`, market
clearing is closed under coordinate swaps, and constant coordinate cutoffs
clear a strictly decreasing scalar demand equation, then the market-clearing
cutoff is unique.
-/
theorem unique_marketClearing_of_coordinate_symmetry_strict_antitone_scalar_clearing
    {CollegeCoord : Type v} [DecidableEq CollegeCoord]
    (L : CutoffLatticeInterface M)
    (coord : M.Cutoff → CollegeCoord → ℝ)
    (hcoord_ext : ∀ P Q : M.Cutoff, coord P = coord Q → P = Q)
    (horder :
      ∀ P Q : M.Cutoff,
        L.leCutoff P Q → CoordinatewiseLe (coord P) (coord Q))
    (hswap :
      ∀ P : M.Cutoff, M.MarketClearing P → ∀ c d : CollegeCoord,
        ∃ Q : M.Cutoff,
          M.MarketClearing Q ∧ coord Q = coordinateSwap (coord P) c d)
    {demand : ℝ → ℝ} {supply : ℝ}
    (hclearing :
      ∀ P : M.Cutoff, ∀ x : ℝ,
        M.MarketClearing P → (∀ c, coord P c = x) → demand x = supply)
    (hstrict : ∀ x y : ℝ, x < y → demand y < demand x) :
    ∀ P Q : M.Cutoff, M.MarketClearing P → M.MarketClearing Q → P = Q := by
  classical
  let bot : M.Cutoff := L.leastMarketClearingCutoff
  let top : M.Cutoff := L.greatestMarketClearingCutoff
  have hbot_mc : M.MarketClearing bot := by
    simpa [bot] using L.leastMarketClearingCutoff_marketClearing
  have htop_mc : M.MarketClearing top := by
    simpa [top] using L.greatestMarketClearingCutoff_marketClearing
  have hleast :
      ∀ P : M.Cutoff, M.MarketClearing P →
        L.leCutoff bot P := by
    intro P hP
    simpa [bot] using L.leastMarketClearingCutoff_le hP
  have hgreatest :
      ∀ P : M.Cutoff, M.MarketClearing P →
        L.leCutoff P top := by
    intro P hP
    simpa [top] using L.le_greatestMarketClearingCutoff hP
  let Z : Set (CollegeCoord → ℝ) :=
    {R | ∃ P : M.Cutoff, M.MarketClearing P ∧ coord P = R}
  have hbotZ : coord bot ∈ Z := ⟨bot, hbot_mc, rfl⟩
  have htopZ : coord top ∈ Z := ⟨top, htop_mc, rfl⟩
  have hleast_coord :
      ∀ R : CollegeCoord → ℝ, R ∈ Z →
        CoordinatewiseLe (coord bot) R := by
    intro R hR
    rcases hR with ⟨P, hP, rfl⟩
    exact horder bot P (hleast P hP)
  have hgreatest_coord :
      ∀ R : CollegeCoord → ℝ, R ∈ Z →
        CoordinatewiseLe R (coord top) := by
    intro R hR
    rcases hR with ⟨P, hP, rfl⟩
    exact horder P top (hgreatest P hP)
  have hswap_coord :
      ∀ R : CollegeCoord → ℝ, R ∈ Z → ∀ c d : CollegeCoord,
        coordinateSwap R c d ∈ Z := by
    intro R hR c d
    rcases hR with ⟨P, hP, rfl⟩
    rcases hswap P hP c d with ⟨Q, hQ, hcoordQ⟩
    exact ⟨Q, hQ, hcoordQ⟩
  have hconst :
      ConstantCoordinates (coord bot) ∧ ConstantCoordinates (coord top) :=
    constantCoordinates_of_coordinatewise_extrema_swap_closed
      (Z := Z) hbotZ htopZ hleast_coord hgreatest_coord hswap_coord
  rcases hconst.1 with ⟨x, hx⟩
  rcases hconst.2 with ⟨y, hy⟩
  have hxy : x = y := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hlt_demand : demand y < demand x := hstrict x y hlt
      rw [hclearing bot x hbot_mc hx, hclearing top y htop_mc hy] at hlt_demand
      exact (lt_irrefl supply) hlt_demand
    · have hlt_demand : demand x < demand y := hstrict y x hgt
      rw [hclearing bot x hbot_mc hx, hclearing top y htop_mc hy] at hlt_demand
      exact (lt_irrefl supply) hlt_demand
  have hbot_top_coord : coord bot = coord top := by
    funext c
    rw [hx c, hy c, hxy]
  have hbot_top : bot = top := hcoord_ext bot top hbot_top_coord
  intro P Q hP hQ
  have hP_coord : coord P = coord bot := by
    funext c
    have hbot_le_P : coord bot c ≤ coord P c :=
      horder bot P (hleast P hP) c
    have hP_le_bot : coord P c ≤ coord bot c := by
      have hP_le_top : coord P c ≤ coord top c :=
        horder P top (hgreatest P hP) c
      simpa [hbot_top] using hP_le_top
    exact le_antisymm hP_le_bot hbot_le_P
  have hQ_coord : coord Q = coord bot := by
    funext c
    have hbot_le_Q : coord bot c ≤ coord Q c :=
      horder bot Q (hleast Q hQ) c
    have hQ_le_bot : coord Q c ≤ coord bot c := by
      have hQ_le_top : coord Q c ≤ coord top c :=
        horder Q top (hgreatest Q hQ) c
      simpa [hbot_top] using hQ_le_top
    exact le_antisymm hQ_le_bot hbot_le_Q
  exact (hcoord_ext P bot hP_coord).trans (hcoord_ext Q bot hQ_coord).symm

end CutoffLatticeInterface

/--
Combining the supply/demand bridge with a nonempty complete lattice of
market-clearing cutoffs gives existence of a stable matching.
-/
theorem SupplyDemandInterface.exists_stable_of_cutoffLattice
    {Student : Type u} {College : Type v} {M : CutoffMarket Student College}
    (I : SupplyDemandInterface M) (L : CutoffLatticeInterface M) :
    ∃ μ : M.Matching, M.Stable μ :=
  I.exists_stable_of_exists_marketClearing L.nonempty_marketClearing

end Matching
end AppliedModelingLib
