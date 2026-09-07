import Cslib.Foundations.Data.RelatesInSteps
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Find
import Mathlib.GroupTheory.Perm.List
import Mathlib.Order.WellFoundedSet
import Mathlib.Tactic.Linarith

namespace AppliedModelingLib
namespace Foundations.Graph

/--
On a finite type, a non-well-founded relation has a directed cycle in its
transitive closure.
-/
theorem exists_transGen_self_of_not_wellFounded
    {α : Type*} [Finite α]
    {r : α → α → Prop} (h : ¬ WellFounded r) :
    ∃ i, Relation.TransGen r i i := by
  classical
  by_contra hcycle
  have hnoCycle : ∀ i, ¬ Relation.TransGen r i i := by
    intro i hi
    exact hcycle ⟨i, hi⟩
  haveI : Std.Irrefl (Relation.TransGen r) := ⟨hnoCycle⟩
  haveI : IsTrans α (Relation.TransGen r) := inferInstance
  have hwfTrans : WellFounded (Relation.TransGen r) :=
    Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen r)
  have hsub : Subrelation r (Relation.TransGen r) := by
    intro i j hij
    exact Relation.TransGen.single hij
  exact h (Subrelation.wf hsub hwfTrans)

/-- Convert a transitive-closure path into a positive step-indexed path. -/
theorem exists_relatesInSteps_pos_of_transGen
    {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.TransGen r a b) :
    ∃ n, 0 < n ∧ Relation.RelatesInSteps r a b n := by
  induction h with
  | single h =>
      exact ⟨1, by decide, Relation.RelatesInSteps.single h⟩
  | tail hab hbc ih =>
      obtain ⟨n, _hnpos, hn⟩ := ih
      exact ⟨n + 1, Nat.succ_pos n,
        Relation.RelatesInSteps.tail _ _ _ n hn hbc⟩

/-- Convert a step-indexed path into a concrete list chain. -/
theorem exists_chain_list_of_relatesInSteps
    {α : Type*} {r : α → α → Prop} {a b : α} :
    ∀ {n}, Relation.RelatesInSteps r a b n →
      ∃ l : List α,
        l.length = n + 1 ∧ l.head? = some a ∧
          l.getLast? = some b ∧ l.IsChain r := by
  intro n h
  induction h with
  | refl =>
      exact ⟨[a], by simp⟩
  | tail t' t'' n h₁ h₂ ih =>
      obtain ⟨l, hlen, hhead, hlast, hchain⟩ := ih
      refine ⟨l ++ [t''], ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · rw [List.head?_append_of_ne_nil]
        · exact hhead
        · intro hnil
          simp [hnil] at hlen
      · simp
      · apply hchain.append (by simp)
        intro x hx y hy
        rw [List.head?_singleton, Option.mem_some_iff] at hy
        subst y
        have hx' : t' = x := by
          simpa [hlast] using hx
        subst x
        exact h₂

/--
In a concrete chain list, earlier entries are related to later entries by a
step-indexed path whose length is the index gap.
-/
theorem isChain_relatesInSteps_getElem
    {α : Type*} {r : α → α → Prop} {l : List α}
    (hchain : l.IsChain r) :
    ∀ {i j : ℕ} (hi : i < l.length) (hj : j < l.length), i ≤ j →
      Relation.RelatesInSteps r (l[i]'hi) (l[j]'hj) (j - i) := by
  intro i j hi hj hij
  induction j generalizing i with
  | zero =>
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hij
      subst i
      exact Relation.RelatesInSteps.refl _
  | succ j ih =>
      rcases Nat.lt_or_eq_of_le hij with hijlt | rfl
      · have hij_le : i ≤ j := Nat.lt_succ_iff.mp hijlt
        have hj_prev : j < l.length := Nat.lt_of_succ_lt hj
        have hprev := ih hi hj_prev hij_le
        have hedge : r (l[j]'hj_prev) (l[j + 1]'hj) := by
          exact hchain.getElem j hj
        have hsub : (j + 1 - i) = (j - i) + 1 := by omega
        simpa [hsub] using
          Relation.RelatesInSteps.tail _ _ _ (j - i) hprev hedge
      · simp

/--
A closed chain over a nodup list induces directed edges along `List.formPerm`.
-/
theorem edge_formPerm_of_closed_nodup_chain
    {α : Type*} [DecidableEq α] {r : α → α → Prop} {l : List α}
    (hnodup : l.Nodup) (hlen : 0 < l.length)
    (hchain : (l ++ [l[0]]).IsChain r) :
    ∀ x, x ∈ l → r x (l.formPerm x) := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  rw [List.formPerm_apply_getElem l hnodup k hk]
  have hrelFull :
      r ((l ++ [l[0]])[k]'(by simp; omega))
        ((l ++ [l[0]])[k + 1]'(by simp [hk])) := by
    exact hchain.getElem k (by simp [hk])
  by_cases hknext : k + 1 < l.length
  · have hmod : (k + 1) % l.length = k + 1 := Nat.mod_eq_of_lt hknext
    simpa [List.getElem_append, hk, hknext, hmod] using hrelFull
  · have hkLast : k + 1 = l.length := by omega
    have hmod : (k + 1) % l.length = 0 := by
      rw [hkLast, Nat.mod_self]
    simpa [List.getElem_append, hk, hkLast, hmod] using hrelFull

/--
Every positive closed walk in an irreflexive relation contains a simple directed
cycle represented as a nodup list whose `formPerm` edges follow the relation.
-/
theorem exists_simple_cycle_list_of_stepCycle
    {α : Type*} [DecidableEq α] {r : α → α → Prop}
    (hirr : ∀ a : α, ¬ r a a)
    (hcycle : ∃ i n, 0 < n ∧ Relation.RelatesInSteps r i i n) :
    ∃ cycle : List α,
      cycle.Nodup ∧ 2 ≤ cycle.length ∧
        ∀ i, i ∈ cycle → r i (cycle.formPerm i) := by
  classical
  let P : ℕ → Prop := fun n => ∃ i : α, 0 < n ∧ Relation.RelatesInSteps r i i n
  have hP : ∃ n, P n := by
    obtain ⟨i, n, hn, hsteps⟩ := hcycle
    exact ⟨n, i, hn, hsteps⟩
  let n := Nat.find hP
  have hnP : P n := Nat.find_spec hP
  obtain ⟨a, hnpos, hsteps⟩ := hnP
  obtain ⟨walk, hwalk_len, hhead, hlast, hchain⟩ :=
    exists_chain_list_of_relatesInSteps (r := r) hsteps
  let cycle : List α := walk.dropLast
  have hcycle_len : cycle.length = n := by
    simp [cycle, List.length_dropLast, hwalk_len]
  have hcycle_pos : 0 < cycle.length := by omega
  have hwalk_nonempty : walk ≠ [] := by
    intro hnil
    simp [hnil] at hwalk_len
  have hcycle_head : cycle[0] = a := by
    have hhead_get : walk.head hwalk_nonempty = a :=
      (List.head_eq_iff_head?_eq_some hwalk_nonempty).2 hhead
    have hwalk0 : walk[0]'(by omega) = a := by
      simpa [List.head_eq_getElem_zero hwalk_nonempty] using hhead_get
    simpa [cycle, List.getElem_dropLast] using hwalk0
  have hwalk_last : walk.getLast hwalk_nonempty = a := by
    have hlast' : some (walk.getLast hwalk_nonempty) = some a := by
      simpa [List.getLast?_eq_getLast_of_ne_nil hwalk_nonempty] using hlast
    exact Option.some.inj hlast'
  have hclosed_chain : (cycle ++ [cycle[0]]).IsChain r := by
    have hdrop : cycle ++ [cycle[0]] = walk := by
      simpa [cycle, hcycle_head, hwalk_last] using
        (List.dropLast_append_getLast hwalk_nonempty :
          walk.dropLast ++ [walk.getLast hwalk_nonempty] = walk)
    simpa [hdrop] using hchain
  have hnodup : cycle.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro p q hpq
    apply Fin.ext
    by_contra hvalne
    have shorter_contra {p q : Fin cycle.length} (hlt : p.1 < q.1)
        (hpq : cycle[p] = cycle[q]) : False := by
      have hpw : p.1 < walk.length := by omega
      have hqw : q.1 < walk.length := by omega
      have heqwalk : walk[p.1]'hpw = walk[q.1]'hqw := by
        simpa [cycle, List.getElem_dropLast] using hpq
      have hsubsteps :=
        isChain_relatesInSteps_getElem (r := r) hchain hpw hqw (le_of_lt hlt)
      have hclosed :
          Relation.RelatesInSteps r (walk[p.1]'hpw) (walk[p.1]'hpw) (q.1 - p.1) := by
        simpa [heqwalk] using hsubsteps
      have hshortP : P (q.1 - p.1) :=
        ⟨walk[p.1]'hpw, Nat.sub_pos_of_lt hlt, hclosed⟩
      have hminle : n ≤ q.1 - p.1 := Nat.find_min' hP hshortP
      have hshort : q.1 - p.1 < n := by omega
      omega
    rcases Nat.lt_or_gt_of_ne hvalne with hp_lt_q | hq_lt_p
    · exact (shorter_contra hp_lt_q hpq).elim
    · exact (shorter_contra hq_lt_p hpq.symm).elim
  have hn_ne_one : n ≠ 1 := by
    intro hn1
    have hsteps1 : Relation.RelatesInSteps r a a (0 + 1) := by
      simpa [hn1] using hsteps
    obtain ⟨t, ht_edge, ht_zero⟩ := Relation.RelatesInSteps.succ' hsteps1
    have hta : t = a := Relation.RelatesInSteps.zero ht_zero
    subst t
    exact hirr a ht_edge
  have hlen_two : 2 ≤ cycle.length := by omega
  exact ⟨cycle, hnodup, hlen_two,
    edge_formPerm_of_closed_nodup_chain (r := r) hnodup hcycle_pos hclosed_chain⟩

/-- A finite nonempty irreflexive relation in which every vertex has an
outgoing edge has a simple directed cycle. -/
theorem exists_simple_cycle_list_of_forall_exists_edge
    {α : Type*} [Finite α] [Nonempty α] [DecidableEq α]
    {r : α → α → Prop}
    (hirr : ∀ a : α, ¬ r a a)
    (hstep : ∀ a : α, ∃ b : α, r a b) :
    ∃ cycle : List α,
      cycle.Nodup ∧ 2 ≤ cycle.length ∧
        ∀ a, a ∈ cycle → r a (cycle.formPerm a) := by
  have hnotwf : ¬ WellFounded (Function.swap r) := by
    intro hwf
    obtain ⟨a, -, hmin⟩ := hwf.has_min Set.univ Set.univ_nonempty
    obtain ⟨b, hab⟩ := hstep a
    exact hmin b (by simp) hab
  obtain ⟨a, hcycle⟩ := exists_transGen_self_of_not_wellFounded hnotwf
  have hcycle' : Relation.TransGen r a a := by
    simpa only [Function.swap] using hcycle.swap
  obtain ⟨n, hnpos, hsteps⟩ := exists_relatesInSteps_pos_of_transGen hcycle'
  exact exists_simple_cycle_list_of_stepCycle hirr ⟨a, n, hnpos, hsteps⟩

/-- In a finite directed acyclic graph with a unique sink, every vertex has a
directed path to that sink. -/
theorem reaches_unique_sink_of_no_cycle
    {α : Type*} [Finite α] {r : α → α → Prop}
    (hcycle : ∀ a, ¬ Relation.TransGen r a a)
    (sink : α)
    (hunique : ∀ a, (∀ other, ¬ r a other) → a = sink)
    (start : α) :
    Relation.ReflTransGen r start sink := by
  classical
  have hwf : WellFounded (Function.swap r) := by
    by_contra hnot
    obtain ⟨a, hclosed⟩ := exists_transGen_self_of_not_wellFounded hnot
    apply hcycle a
    simpa only [Function.swap] using hclosed.swap
  let reachable : Set α := {vertex | Relation.ReflTransGen r start vertex}
  have hnonempty : reachable.Nonempty := ⟨start, Relation.ReflTransGen.refl⟩
  obtain ⟨minimal, hminimal, hmin⟩ := hwf.has_min reachable hnonempty
  have hnoout : ∀ other, ¬ r minimal other := by
    intro other hstep
    have hreach : other ∈ reachable := Relation.ReflTransGen.tail hminimal hstep
    exact hmin other hreach hstep
  have hminimalEq : minimal = sink := hunique minimal hnoout
  simpa [hminimalEq] using hminimal

/-- A positive fixed-length relation path induces a transitive-closure path. -/
theorem relatesInSteps_to_transGen_of_pos
    {α : Type*} {r : α → α → Prop} {a b : α} {n : ℕ}
    (hn : 0 < n) (hsteps : Relation.RelatesInSteps r a b n) :
    Relation.TransGen r a b := by
  induction n generalizing a b with
  | zero => omega
  | succ n ih =>
      obtain ⟨middle, hprevious, hedge⟩ := Relation.RelatesInSteps.succ' hsteps
      cases n with
      | zero =>
          have hmiddle : middle = b := Relation.RelatesInSteps.zero hedge
          subst middle
          exact Relation.TransGen.single hprevious
      | succ n =>
          exact Relation.TransGen.head hprevious (ih (Nat.succ_pos n) hedge)

/-- A path in an acyclic relation can be represented by a nodup concrete list. -/
theorem exists_nodup_chain_list_of_transGen_of_no_cycle
    {α : Type*} [DecidableEq α] {r : α → α → Prop} {start finish : α}
    (hcycle : ∀ vertex, ¬ Relation.TransGen r vertex vertex)
    (hpath : Relation.TransGen r start finish) :
    ∃ path : List α, path.Nodup ∧ 2 ≤ path.length ∧ path.head? = some start ∧
      path.getLast? = some finish ∧ path.IsChain r := by
  obtain ⟨steps, hstepsPos, hsteps⟩ := exists_relatesInSteps_pos_of_transGen hpath
  obtain ⟨path, hlength, hhead, hlast, hchain⟩ :=
    exists_chain_list_of_relatesInSteps hsteps
  refine ⟨path, ?_, ?_, hhead, hlast, hchain⟩
  · rw [List.nodup_iff_injective_getElem]
    intro p q hpq
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hpqLt | hqpLt
    · have hstepsCycle := isChain_relatesInSteps_getElem (r := r) hchain p.2 q.2
        (Nat.le_of_lt hpqLt)
      have hpositive : 0 < q.1 - p.1 := Nat.sub_pos_of_lt hpqLt
      have hclosed : Relation.TransGen r (path[p]) (path[p]) := by
        simpa [hpq] using relatesInSteps_to_transGen_of_pos hpositive hstepsCycle
      exact hcycle (path[p]) hclosed
    · have hstepsCycle := isChain_relatesInSteps_getElem (r := r) hchain q.2 p.2
        (Nat.le_of_lt hqpLt)
      have hpositive : 0 < p.1 - q.1 := Nat.sub_pos_of_lt hqpLt
      have hclosed : Relation.TransGen r (path[q]) (path[q]) := by
        simpa [hpq] using relatesInSteps_to_transGen_of_pos hpositive hstepsCycle
      exact hcycle (path[q]) hclosed
  · rw [hlength]
    omega

/--
Any directed reachability witness between distinct finite endpoints has a
vertex-simple concrete path.  Unlike
`exists_nodup_chain_list_of_transGen_of_no_cycle`, this result does not assume
the ambient relation is acyclic: it chooses a shortest witness and removes a
repeated-vertex loop.  This is the finite directed-path fact needed when a
strongly connected comparison graph is used to bound score differences.
-/
theorem exists_nodup_chain_list_of_reaches
    {α : Type*} [DecidableEq α] {r : α → α → Prop} {start finish : α}
    (hne : start ≠ finish) (hreach : Relation.ReflTransGen r start finish) :
    ∃ path : List α, path.Nodup ∧ 2 ≤ path.length ∧ path.head? = some start ∧
      path.getLast? = some finish ∧ path.IsChain r := by
  classical
  let P : ℕ → Prop := fun n => Relation.RelatesInSteps r start finish n
  have hP : ∃ n, P n := by
    obtain ⟨n, hn⟩ := hreach.relatesInSteps
    exact ⟨n, hn⟩
  let n := Nat.find hP
  have hnP : P n := Nat.find_spec hP
  have hnpos : 0 < n := by
    by_contra hzero
    have hzero' : n = 0 := Nat.eq_zero_of_not_pos hzero
    have hzeroSteps : Relation.RelatesInSteps r start finish 0 := by
      simpa only [P, hzero'] using hnP
    have : start = finish := Relation.RelatesInSteps.zero hzeroSteps
    exact hne this
  obtain ⟨path, hlength, hhead, hlast, hchain⟩ :=
    exists_chain_list_of_relatesInSteps (r := r) hnP
  have hpath_ne : path ≠ [] := by
    intro hnil
    simp [hnil] at hlength
  have hfirst : path[0]'(by omega) = start := by
    have hhead' : path.head hpath_ne = start :=
      (List.head_eq_iff_head?_eq_some hpath_ne).2 hhead
    simpa [List.head_eq_getElem_zero hpath_ne] using hhead'
  have hlast' : path.getLast hpath_ne = finish := by
    have : some (path.getLast hpath_ne) = some finish := by
      simpa [List.getLast?_eq_getLast_of_ne_nil hpath_ne] using hlast
    exact Option.some.inj this
  have hlastElem : path[path.length - 1]'(by omega) = finish := by
    rw [← List.getLast_eq_getElem hpath_ne]
    exact hlast'
  have hnodup : path.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro i j hij
    apply Fin.ext
    by_contra hneIndex
    rcases Nat.lt_or_gt_of_ne hneIndex with hijlt | hjilt
    · have hipath : i.1 < path.length := i.2
      have hjpath : j.1 < path.length := j.2
      have hlastIndex : path.length - 1 < path.length := by omega
      have hprefix := isChain_relatesInSteps_getElem (r := r) hchain
        (i := 0) (j := i.1) (by omega) hipath (by omega)
      have hsuffix := isChain_relatesInSteps_getElem (r := r) hchain
        (i := j.1) (j := path.length - 1) hjpath hlastIndex (by omega)
      have hshort : P (i.1 + (path.length - 1 - j.1)) := by
        change Relation.RelatesInSteps r start finish _
        have hsuffix' : Relation.RelatesInSteps r (path[i.1]'hipath)
            (path[path.length - 1]'hlastIndex) (path.length - 1 - j.1) := by
          simpa [hij] using hsuffix
        have hjoined := Relation.RelatesInSteps.trans hprefix hsuffix'
        simpa [hfirst, hlastElem] using hjoined
      have hmin : n ≤ i.1 + (path.length - 1 - j.1) := Nat.find_min' hP hshort
      have : i.1 + (path.length - 1 - j.1) < n := by omega
      omega
    · have hipath : i.1 < path.length := i.2
      have hjpath : j.1 < path.length := j.2
      have hlastIndex : path.length - 1 < path.length := by omega
      have hprefix := isChain_relatesInSteps_getElem (r := r) hchain
        (i := 0) (j := j.1) (by omega) hjpath (by omega)
      have hsuffix := isChain_relatesInSteps_getElem (r := r) hchain
        (i := i.1) (j := path.length - 1) hipath hlastIndex (by omega)
      have hshort : P (j.1 + (path.length - 1 - i.1)) := by
        change Relation.RelatesInSteps r start finish _
        have hsuffix' : Relation.RelatesInSteps r (path[j.1]'hjpath)
            (path[path.length - 1]'hlastIndex) (path.length - 1 - i.1) := by
          simpa [hij.symm] using hsuffix
        have hjoined := Relation.RelatesInSteps.trans hprefix hsuffix'
        simpa [hfirst, hlastElem] using hjoined
      have hmin : n ≤ j.1 + (path.length - 1 - i.1) := Nat.find_min' hP hshort
      have : j.1 + (path.length - 1 - i.1) < n := by omega
      omega
  refine ⟨path, hnodup, ?_, hhead, hlast, hchain⟩
  rw [hlength]
  omega

/--
If a potential changes between the endpoints of a reflexive-transitive path,
it changes across one edge of that path.  This elementary path-localization
fact is useful for turning connectedness into a strict-concavity witness.
-/
theorem exists_edge_of_reflTransGen_of_potential_ne
    {α β : Type*} {r : α → α → Prop} (potential : α → β)
    {start finish : α} (hpath : Relation.ReflTransGen r start finish)
    (hpotential : potential start ≠ potential finish) :
    ∃ first second, r first second ∧ potential first ≠ potential second := by
  by_contra hnoEdge
  push Not at hnoEdge
  have hconstant : ∀ {first second}, Relation.ReflTransGen r first second →
      potential first = potential second := by
    intro first second hreach
    induction hreach with
    | refl => rfl
    | tail _ hedge ih => exact ih.trans (hnoEdge _ _ hedge)
  exact hpotential (hconstant hpath)

/-- Along a nodup relation-chain, the list permutation follows the chain from
every vertex other than the final one. -/
theorem isChain_edge_formPerm_of_ne_getLast
    {α : Type*} [DecidableEq α] {r : α → α → Prop} {path : List α}
    (hnodup : path.Nodup) (hchain : path.IsChain r) (hpathNe : path ≠ [])
    {vertex : α} (hvertex : vertex ∈ path)
    (hnotLast : vertex ≠ path.getLast hpathNe) :
    r vertex (path.formPerm vertex) := by
  obtain ⟨index, hindex, rfl⟩ := List.getElem_of_mem hvertex
  have hnext : index + 1 < path.length := by
    by_contra hnot
    have hlast : index + 1 = path.length := by omega
    apply hnotLast
    rw [List.getLast_eq_getElem hpathNe]
    have hindexEq : index = path.length - 1 := by omega
    simp [hindexEq]
  rw [List.formPerm_apply_getElem path hnodup index hindex]
  simpa [Nat.mod_eq_of_lt hnext] using hchain.getElem index hnext

/-- In a nodup list of length at least two, its permutation sends the
penultimate element to its final element. -/
theorem formPerm_penultimate_eq_getLast
    {α : Type*} [DecidableEq α] (path : List α) (hnodup : path.Nodup)
    (hlen : 2 ≤ path.length) :
    path.formPerm path[path.length - 2] =
      path.getLast (List.ne_nil_of_length_pos (by omega)) := by
  have hindex : path.length - 2 < path.length := by omega
  rw [List.formPerm_apply_getElem path hnodup (path.length - 2) hindex]
  have hmod : (path.length - 2 + 1) % path.length = path.length - 1 := by
    have hbound : path.length - 1 < path.length := by omega
    have hsum : path.length - 2 + 1 = path.length - 1 := by omega
    rw [hsum, Nat.mod_eq_of_lt hbound]
  calc
    path[(path.length - 2 + 1) % path.length] = path[path.length - 1] := by
      simp [hmod]
    _ = path.getLast (List.ne_nil_of_length_pos (by omega)) :=
      (List.getLast_eq_getElem _).symm

/-- The penultimate and final elements of a nodup list of length at least two
are distinct. -/
theorem penultimate_ne_getLast_of_nodup
    {α : Type*} [DecidableEq α] (path : List α) (hnodup : path.Nodup)
    (hlen : 2 ≤ path.length) :
    path[path.length - 2] ≠ path.getLast (List.ne_nil_of_length_pos (by omega)) := by
  rw [List.getLast_eq_getElem]
  intro hEq
  have hleft : path.length - 2 < path.length := by omega
  have hright : path.length - 1 < path.length := by omega
  rw [List.nodup_iff_injective_getElem] at hnodup
  have hfin : (⟨path.length - 2, hleft⟩ : Fin path.length) =
      ⟨path.length - 1, hright⟩ := hnodup hEq
  have hindex : path.length - 2 = path.length - 1 := Fin.mk.inj hfin
  omega

/-- The list permutation maps a nonempty list's final element to its head. -/
theorem formPerm_getLast_eq_head_of_head?_eq
    {α : Type*} [DecidableEq α] (path : List α) (hpathNe : path ≠ [])
    {head : α} (hhead : path.head? = some head) :
    path.formPerm (path.getLast hpathNe) = head := by
  cases path with
  | nil => simp at hpathNe
  | cons first tail =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst first
      exact List.formPerm_apply_getLast head tail

end Foundations.Graph
end AppliedModelingLib
