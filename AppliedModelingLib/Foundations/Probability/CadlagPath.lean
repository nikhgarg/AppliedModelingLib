import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.ContinuousOn

/-!
# Càdlàg paths

This module records the elementary path-regularity predicate used by
continuous-time stochastic-process constructions.  It deliberately does not
choose a topology on a path space; in particular, it does not define a
Skorokhod topology.
-/

namespace AppliedModelingLib.Probability

open Filter Topology

/-- A path is càdlàg when it is right-continuous and has a left limit at every
time. -/
def IsCadlagPath {Time State : Type*} [Preorder Time] [TopologicalSpace Time]
    [TopologicalSpace State] (path : Time → State) : Prop :=
  (∀ time, ContinuousWithinAt path (Set.Ici time) time) ∧
    ∀ time, ∃ leftLimit,
      Tendsto path (nhdsWithin time (Set.Iio time)) (nhds leftLimit)

/-- Càdlàg regularity relative to a prescribed time domain.  At the left
endpoint the left-limit filter is empty, as is standard for paths on a
half-line or compact time interval. -/
def IsCadlagOn {Time State : Type*} [Preorder Time] [TopologicalSpace Time]
    [TopologicalSpace State] (domain : Set Time) (path : Time → State) : Prop :=
  (∀ time, time ∈ domain →
    ContinuousWithinAt path (domain ∩ Set.Ici time) time) ∧
    ∀ time, time ∈ domain → ∃ leftLimit,
      Tendsto path (nhdsWithin time (domain ∩ Set.Iio time)) (nhds leftLimit)

/-- A path bundled with its càdlàg regularity on a prescribed time domain. -/
structure CadlagPathOn (Time State : Type*) [Preorder Time] [TopologicalSpace Time]
    [TopologicalSpace State] (domain : Set Time) where
  toFun : Time → State
  isCadlag : IsCadlagOn domain toFun

instance {Time State : Type*} [Preorder Time] [TopologicalSpace Time]
    [TopologicalSpace State] {domain : Set Time} :
    CoeFun (CadlagPathOn Time State domain) (fun _ => Time → State) where
  coe path := path.toFun

namespace CadlagPathOn

/-- The constant path is càdlàg on every time domain. -/
def constant {Time State : Type*} [Preorder Time] [TopologicalSpace Time]
    [TopologicalSpace State] (domain : Set Time) (value : State) :
    CadlagPathOn Time State domain where
  toFun := fun _ => value
  isCadlag := by
    constructor
    · intro _ _
      exact continuousAt_const.continuousWithinAt
    · intro _ _
      exact ⟨value, tendsto_const_nhds⟩

@[simp]
theorem constant_apply {Time State : Type*} [Preorder Time] [TopologicalSpace Time]
    [TopologicalSpace State] (domain : Set Time) (value : State) (time : Time) :
    constant domain value time = value := rfl

end CadlagPathOn

namespace IsCadlagPath

variable {Time State Target : Type*} [Preorder Time] [TopologicalSpace Time]
  [TopologicalSpace State] [TopologicalSpace Target]

/-- Every continuous path is càdlàg. -/
theorem of_continuous {path : Time → State} (hpath : Continuous path) :
    IsCadlagPath path := by
  constructor
  · intro time
    exact hpath.continuousAt.continuousWithinAt
  · intro time
    exact ⟨path time, hpath.continuousAt.tendsto.mono_left inf_le_left⟩

/-- A continuous state transformation preserves càdlàg path regularity. -/
theorem continuous_comp {path : Time → State} (hpath : IsCadlagPath path)
    {map : State → Target} (hmap : Continuous map) :
    IsCadlagPath (map ∘ path) := by
  constructor
  · intro time
    exact hmap.continuousAt.comp_continuousWithinAt (hpath.1 time)
  · intro time
    rcases hpath.2 time with ⟨leftLimit, hleft⟩
    exact ⟨map leftLimit, hmap.continuousAt.tendsto.comp hleft⟩

/-- Pairing two càdlàg paths preserves càdlàg regularity. -/
theorem prod {Other : Type*} [TopologicalSpace Other]
    {first : Time → State} {second : Time → Other}
    (hfirst : IsCadlagPath first) (hsecond : IsCadlagPath second) :
    IsCadlagPath (fun time => (first time, second time)) := by
  constructor
  · intro time
    exact (hfirst.1 time).prodMk (hsecond.1 time)
  · intro time
    obtain ⟨firstLimit, hfirstLimit⟩ := hfirst.2 time
    obtain ⟨secondLimit, hsecondLimit⟩ := hsecond.2 time
    exact ⟨(firstLimit, secondLimit), hfirstLimit.prodMk_nhds hsecondLimit⟩

/-- A globally càdlàg path is càdlàg after restricting its time domain. -/
theorem on_of_isCadlagPath {path : Time → State} (hpath : IsCadlagPath path)
    (domain : Set Time) :
    IsCadlagOn domain path := by
  constructor
  · intro time _htime
    exact (hpath.1 time).mono (Set.inter_subset_right)
  · intro time _htime
    rcases hpath.2 time with ⟨leftLimit, hleft⟩
    exact ⟨leftLimit, hleft.mono_left
      (nhdsWithin_mono time Set.inter_subset_right)⟩

end IsCadlagPath

namespace IsCadlagOn

variable {Time State Target : Type*} [Preorder Time] [TopologicalSpace Time]
  [TopologicalSpace State] [TopologicalSpace Target]

/-- A continuous state transformation preserves càdlàg regularity on a
prescribed time domain. -/
theorem continuous_comp {domain : Set Time} {path : Time → State}
    (hpath : IsCadlagOn domain path) {map : State → Target} (hmap : Continuous map) :
    IsCadlagOn domain (map ∘ path) := by
  constructor
  · intro time htime
    exact hmap.continuousAt.comp_continuousWithinAt (hpath.1 time htime)
  · intro time htime
    rcases hpath.2 time htime with ⟨leftLimit, hleft⟩
    exact ⟨map leftLimit, hmap.continuousAt.tendsto.comp hleft⟩

/-- Pairing two càdlàg paths on the same time domain preserves càdlàg
regularity. -/
theorem prod {Other : Type*} [TopologicalSpace Other]
    {domain : Set Time} {first : Time → State} {second : Time → Other}
    (hfirst : IsCadlagOn domain first) (hsecond : IsCadlagOn domain second) :
    IsCadlagOn domain (fun time => (first time, second time)) := by
  constructor
  · intro time htime
    exact (hfirst.1 time htime).prodMk (hsecond.1 time htime)
  · intro time htime
    obtain ⟨firstLimit, hfirstLimit⟩ := hfirst.2 time htime
    obtain ⟨secondLimit, hsecondLimit⟩ := hsecond.2 time htime
    exact ⟨(firstLimit, secondLimit), hfirstLimit.prodMk_nhds hsecondLimit⟩

/-- The sum of two càdlàg paths on the same time domain is càdlàg. -/
theorem add {domain : Set Time} {first second : Time → State}
    [Add State] [ContinuousAdd State]
    (hfirst : IsCadlagOn domain first) (hsecond : IsCadlagOn domain second) :
    IsCadlagOn domain (fun time => first time + second time) := by
  simpa [Function.comp_def] using
    (hfirst.prod hsecond).continuous_comp (continuous_fst.add continuous_snd)

/-- Pointwise negation preserves càdlàg regularity on a fixed time domain. -/
theorem neg {domain : Set Time} {path : Time → State}
    [Neg State] [ContinuousNeg State]
    (hpath : IsCadlagOn domain path) :
    IsCadlagOn domain (fun time => -path time) := by
  simpa [Function.comp_def] using
    hpath.continuous_comp (map := fun value : State => -value) continuous_neg

/-- Càdlàg regularity restricts to a smaller prescribed time domain. -/
theorem restrict {domain subdomain : Set Time} {path : Time → State}
    (hpath : IsCadlagOn domain path) (hsubdomain : subdomain ⊆ domain) :
    IsCadlagOn subdomain path := by
  constructor
  · intro time htime
    exact (hpath.1 time (hsubdomain htime)).mono (by
      intro other hother
      exact ⟨hsubdomain hother.1, hother.2⟩)
  · intro time htime
    rcases hpath.2 time (hsubdomain htime) with ⟨leftLimit, hleft⟩
    refine ⟨leftLimit, hleft.mono_left ?_⟩
    exact nhdsWithin_mono time (by
      intro other hother
      exact ⟨hsubdomain hother.1, hother.2⟩)

/-- Bundle a path once its càdlàg regularity on the prescribed domain is
available. -/
def toCadlagPathOn {domain : Set Time} {path : Time → State}
    (hpath : IsCadlagOn domain path) : CadlagPathOn Time State domain :=
  ⟨path, hpath⟩

end IsCadlagOn

namespace CadlagPathOn

variable {Time State : Type*} [Preorder Time] [TopologicalSpace Time]
  [TopologicalSpace State]

/-- Pointwise addition of two bundled càdlàg paths on the same time domain. -/
def add {domain : Set Time} [Add State] [ContinuousAdd State]
    (first second : CadlagPathOn Time State domain) :
    CadlagPathOn Time State domain :=
  ⟨fun time => first time + second time, first.isCadlag.add second.isCadlag⟩

@[simp]
theorem add_apply {domain : Set Time} [Add State] [ContinuousAdd State]
    (first second : CadlagPathOn Time State domain) (time : Time) :
    first.add second time = first time + second time := rfl

/-- Pointwise negation of a bundled càdlàg path. -/
def neg {domain : Set Time} [Neg State] [ContinuousNeg State]
    (path : CadlagPathOn Time State domain) : CadlagPathOn Time State domain :=
  ⟨fun time => -path time, path.isCadlag.neg⟩

@[simp]
theorem neg_apply {domain : Set Time} [Neg State] [ContinuousNeg State]
    (path : CadlagPathOn Time State domain) (time : Time) :
    path.neg time = -path time := rfl

/-- Restrict a bundled càdlàg path to a smaller time domain. -/
def restrict {domain subdomain : Set Time}
    (path : CadlagPathOn Time State domain) (hsubdomain : subdomain ⊆ domain) :
    CadlagPathOn Time State subdomain :=
  ⟨path, path.isCadlag.restrict hsubdomain⟩

end CadlagPathOn

end AppliedModelingLib.Probability
