import AppliedModelingLib.Foundations.Graph.Cycle
import AppliedModelingLib.Foundations.Math.FiniteOptimization
import AppliedModelingLib.Learning.HumanFeedback.PairwiseCountMLE

/-!
# Graph and Compactness Infrastructure for Finite Pairwise-Count MLEs

This module isolates the directed-comparison-graph arguments behind the MLE
existence theorem of Noothigattu--Peters--Procaccia (2020).  In particular, it
records the cut obtained from a connected pair that lacks directed
reachability.  The likelihood-improvement and compactness arguments build on
this graph interface without baking a paper-specific statement into the core
count model.
-/

namespace AppliedModelingLib
namespace Learning
namespace HumanFeedback
namespace PairwiseCountDataset

/-- The undirected comparison adjacency is symmetric. -/
theorem adjacent_symmetric {Alternative : Type*} (dataset : PairwiseCountDataset Alternative) :
    Symmetric dataset.adjacent := by
  intro first second hadjacent
  rcases hadjacent with hforward | hreverse
  · exact Or.inr hforward
  · exact Or.inl hreverse

/-- A directed comparison edge lies within one undirected component. -/
theorem edge_connectedTo {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    {first second : Alternative} (hedge : dataset.edge first second) :
    dataset.connectedTo first second :=
  Relation.ReflTransGen.single (Or.inl hedge)

/-- Directed reachability implies undirected component membership. -/
theorem reaches_connectedTo {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    {first second : Alternative} (hreach : dataset.reaches first second) :
    dataset.connectedTo first second :=
  hreach.mono (fun _ _ hedge => Or.inl hedge)

/-- Undirected component membership is symmetric. -/
theorem connectedTo_symm {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    {first second : Alternative} (hconnected : dataset.connectedTo first second) :
    dataset.connectedTo second first :=
  Relation.ReflTransGen.symmetric (adjacent_symmetric dataset) hconnected

/-- Undirected component membership is transitive. -/
theorem connectedTo_trans {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    {first second third : Alternative}
    (hfirstSecond : dataset.connectedTo first second)
    (hsecondThird : dataset.connectedTo second third) :
    dataset.connectedTo first third :=
  hfirstSecond.trans hsecondThird

/-- The vertices that have a directed path to `target`. -/
noncomputable def predecessorBlock {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (target : Alternative) : Finset Alternative := by
  classical
  exact Finset.univ.filter (fun candidate => dataset.reaches candidate target)

/-- Membership in the predecessor block is exactly directed reachability to its target. -/
theorem mem_predecessorBlock {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (target candidate : Alternative) :
    candidate ∈ dataset.predecessorBlock target ↔ dataset.reaches candidate target := by
  classical
  simp [predecessorBlock]

/-- The target itself belongs to its predecessor block. -/
theorem target_mem_predecessorBlock {Alternative : Type*} [Fintype Alternative]
    [DecidableEq Alternative] (dataset : PairwiseCountDataset Alternative) (target : Alternative) :
    target ∈ dataset.predecessorBlock target := by
  rw [mem_predecessorBlock]
  exact Relation.ReflTransGen.refl

/-- No directed edge can enter the predecessor block from its complement. -/
theorem not_edge_to_predecessorBlock_from_outside
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (target outside inside : Alternative)
    (houtside : outside ∉ dataset.predecessorBlock target)
    (hinside : inside ∈ dataset.predecessorBlock target) :
    ¬ dataset.edge outside inside := by
  intro hedge
  rw [mem_predecessorBlock] at hinside houtside
  exact houtside (Relation.ReflTransGen.head hedge hinside)

/--
If `start` and `target` are undirected-connected but `start` cannot reach
`target`, the predecessor block of `target` has an edge going out and none
coming in.  This is the source proof's source strongly connected component,
obtained without invoking a separate condensation-DAG construction.
-/
theorem exists_outgoing_edge_of_connected_not_reaches
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (start target : Alternative)
    (hconnected : dataset.connectedTo start target)
    (hnotReach : ¬ dataset.reaches start target) :
    ∃ inside outside,
      inside ∈ dataset.predecessorBlock target ∧
        outside ∉ dataset.predecessorBlock target ∧ dataset.edge inside outside := by
  classical
  have hstartOut : start ∉ dataset.predecessorBlock target := by
    rwa [mem_predecessorBlock]
  have htargetIn : target ∈ dataset.predecessorBlock target :=
    target_mem_predecessorBlock dataset target
  by_contra hnoOutgoing
  push_neg at hnoOutgoing
  have hmembership : ∀ {first second : Alternative}, dataset.adjacent first second →
      (first ∈ dataset.predecessorBlock target ↔ second ∈ dataset.predecessorBlock target) := by
    intro first second hadjacent
    constructor
    · intro hfirst
      by_contra hsecond
      rcases hadjacent with hedge | hedge
      · exact hnoOutgoing first second hfirst hsecond hedge
      · exact (not_edge_to_predecessorBlock_from_outside dataset target second first hsecond hfirst)
          hedge
    · intro hsecond
      by_contra hfirst
      rcases hadjacent with hedge | hedge
      · exact (not_edge_to_predecessorBlock_from_outside dataset target first second hfirst hsecond)
          hedge
      · exact hnoOutgoing second first hsecond hfirst hedge
  have hpreserves : ∀ {first second : Alternative}, dataset.connectedTo first second →
      first ∈ dataset.predecessorBlock target → second ∈ dataset.predecessorBlock target := by
    intro first second hpath hfirst
    induction hpath with
    | refl => exact hfirst
    | tail hprefix hedge ih => exact (hmembership hedge).mp ih
  have hreverse := connectedTo_symm dataset hconnected
  have hstartIn := hpreserves hreverse htargetIn
  exact hstartOut hstartIn

/-- Add a common utility shift to a selected finite block of alternatives. -/
def scoreShiftOn {Alternative : Type*} [DecidableEq Alternative]
    (block : Finset Alternative) (score : ScoreVector Alternative) (shift : ℝ) :
    ScoreVector Alternative :=
  fun alternative => if alternative ∈ block then score alternative + shift else score alternative

/-- A selected coordinate receives the specified block shift. -/
@[simp] theorem scoreShiftOn_apply_mem {Alternative : Type*} [DecidableEq Alternative]
    (block : Finset Alternative) (score : ScoreVector Alternative) (shift : ℝ)
    {alternative : Alternative} (hmem : alternative ∈ block) :
    scoreShiftOn block score shift alternative = score alternative + shift := by
  simp [scoreShiftOn, hmem]

/-- A coordinate outside the selected block is unchanged. -/
@[simp] theorem scoreShiftOn_apply_not_mem {Alternative : Type*} [DecidableEq Alternative]
    (block : Finset Alternative) (score : ScoreVector Alternative) (shift : ℝ)
    {alternative : Alternative} (hnotmem : alternative ∉ block) :
    scoreShiftOn block score shift alternative = score alternative := by
  simp [scoreShiftOn, hnotmem]

/-- A pair entirely inside the shifted block retains its score difference. -/
theorem scoreShiftOn_sub_of_mem
    {Alternative : Type*} [DecidableEq Alternative]
    (block : Finset Alternative) (score : ScoreVector Alternative) (shift : ℝ)
    {first second : Alternative} (hfirst : first ∈ block) (hsecond : second ∈ block) :
    scoreShiftOn block score shift first - scoreShiftOn block score shift second =
      score first - score second := by
  simp [scoreShiftOn, hfirst, hsecond]

/-- A pair entirely outside the shifted block retains its score difference. -/
theorem scoreShiftOn_sub_of_not_mem
    {Alternative : Type*} [DecidableEq Alternative]
    (block : Finset Alternative) (score : ScoreVector Alternative) (shift : ℝ)
    {first second : Alternative} (hfirst : first ∉ block) (hsecond : second ∉ block) :
    scoreShiftOn block score shift first - scoreShiftOn block score shift second =
      score first - score second := by
  simp [scoreShiftOn, hfirst, hsecond]

/-- An edge from the shifted block to its complement gains exactly the shift in score gap. -/
theorem scoreShiftOn_sub_of_mem_not_mem
    {Alternative : Type*} [DecidableEq Alternative]
    (block : Finset Alternative) (score : ScoreVector Alternative) (shift : ℝ)
    {first second : Alternative} (hfirst : first ∈ block) (hsecond : second ∉ block) :
    scoreShiftOn block score shift first - scoreShiftOn block score shift second =
      (score first - score second) + shift := by
  simp [scoreShiftOn, hfirst, hsecond]
  ring

/-- Strict monotonicity of a CDF-like link is preserved after taking its logarithm. -/
theorem strictMono_log_comp_of_strictMono (link : CDFLikePairwiseLink)
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    StrictMono (fun gap : ℝ => Real.log (link gap)) := by
  intro first second hfirstSecond
  exact Real.strictMonoOn_log (link.openProbability hstrict first).1
    (link.openProbability hstrict second).1 (hstrict hfirstSecond)

/--
Shifting a block with no incoming positive-count edge strictly improves the
finite likelihood whenever that block has a positive-count outgoing edge.
This is the likelihood contradiction used for the necessity direction of the
comparison-graph MLE existence criterion.
-/
theorem pairwiseLogLikelihood_lt_scoreShiftOn_of_cut
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (hstrict : StrictMono (link : ℝ → ℝ)) (block : Finset Alternative)
    (score : ScoreVector Alternative)
    (hnoIncoming : ∀ outside inside,
      outside ∉ block → inside ∈ block → ¬ dataset.edge outside inside)
    (houtgoing : ∃ inside outside,
      inside ∈ block ∧ outside ∉ block ∧ dataset.edge inside outside) :
    pairwiseLogLikelihood dataset link score <
      pairwiseLogLikelihood dataset link (scoreShiftOn block score 1) := by
  unfold pairwiseLogLikelihood
  refine Finset.sum_lt_sum ?_ ?_
  · rintro ⟨first, second⟩ hpair
    by_cases hcount : dataset.count first second = 0
    · simp [hcount]
    have hedge : dataset.edge first second := Nat.pos_of_ne_zero hcount
    by_cases hfirst : first ∈ block
    · by_cases hsecond : second ∈ block
      · have hgap := scoreShiftOn_sub_of_mem block score (1 : ℝ) hfirst hsecond
        rw [show randomUtilityWinProbability link (scoreShiftOn block score 1) first second =
          randomUtilityWinProbability link score first second by
          unfold randomUtilityWinProbability
          congr 1]
      · have hgap := scoreShiftOn_sub_of_mem_not_mem block score (1 : ℝ) hfirst hsecond
        have hlink : link (score first - score second) <
            link (scoreShiftOn block score 1 first - scoreShiftOn block score 1 second) := by
          rw [hgap]
          exact hstrict (by linarith)
        have hlog : Real.log (link (score first - score second)) <
            Real.log (link (scoreShiftOn block score 1 first - scoreShiftOn block score 1 second)) :=
          Real.strictMonoOn_log (link.openProbability hstrict _).1
            (link.openProbability hstrict _).1 hlink
        exact (mul_lt_mul_of_pos_left hlog (by exact_mod_cast hedge)).le
    · by_cases hsecond : second ∈ block
      · exact (hnoIncoming first second hfirst hsecond hedge).elim
      · have hgap := scoreShiftOn_sub_of_not_mem block score (1 : ℝ) hfirst hsecond
        rw [show randomUtilityWinProbability link (scoreShiftOn block score 1) first second =
          randomUtilityWinProbability link score first second by
          unfold randomUtilityWinProbability
          congr 1]
  · obtain ⟨inside, outside, hinside, houtside, hedge⟩ := houtgoing
    refine ⟨(inside, outside), ?_, ?_⟩
    · exact Finset.mem_offDiag.2 ⟨Finset.mem_univ inside, Finset.mem_univ outside,
        edge_ne dataset hedge⟩
    · have hgap := scoreShiftOn_sub_of_mem_not_mem block score (1 : ℝ) hinside houtside
      have hlink : link (score inside - score outside) <
          link (scoreShiftOn block score 1 inside - scoreShiftOn block score 1 outside) := by
        rw [hgap]
        exact hstrict (by linarith)
      have hlog : Real.log (link (score inside - score outside)) <
          Real.log (link (scoreShiftOn block score 1 inside - scoreShiftOn block score 1 outside)) :=
        Real.strictMonoOn_log (link.openProbability hstrict _).1
          (link.openProbability hstrict _).1 hlink
      exact mul_lt_mul_of_pos_left hlog (by exact_mod_cast hedge)

/--
An MLE cannot exist when an undirected-connected pair has no directed path in
one direction: the predecessor block construction gives a strictly better
unrestricted score vector, contradicting global maximality after reference
normalization.
-/
theorem not_exists_pairwiseMLE_of_connected_not_reaches
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference start target : Alternative) (hstrict : StrictMono (link : ℝ → ℝ))
    (hconnected : dataset.connectedTo start target)
    (hnotReach : ¬ dataset.reaches start target) :
    ¬ ∃ score : ScoreVector Alternative, isPairwiseMLE dataset link reference score := by
  intro hexists
  obtain ⟨score, hmle⟩ := hexists
  obtain ⟨inside, outside, hinside, houtside, hedge⟩ :=
    exists_outgoing_edge_of_connected_not_reaches dataset start target hconnected hnotReach
  have himprove := pairwiseLogLikelihood_lt_scoreShiftOn_of_cut dataset link hstrict
    (dataset.predecessorBlock target) score
    (fun incoming blockVertex hincoming hblock =>
      not_edge_to_predecessorBlock_from_outside dataset target incoming blockVertex
        hincoming hblock)
    ⟨inside, outside, hinside, houtside, hedge⟩
  have hmax := isPairwiseMLE_global_max dataset link reference score hmle
    (scoreShiftOn (dataset.predecessorBlock target) score 1)
  exact (not_lt_of_ge hmax) himprove

/--
The existence of a fixed-reference finite MLE forces every undirected
comparison component to be strongly connected, exactly the necessity half of
source Lemma 2.1.
-/
theorem everyComponentStronglyConnected_of_exists_pairwiseMLE
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference : Alternative) (hstrict : StrictMono (link : ℝ → ℝ))
    (hexists : ∃ score : ScoreVector Alternative, isPairwiseMLE dataset link reference score) :
    dataset.everyComponentStronglyConnected := by
  intro first second hconnected
  by_contra hnotReach
  exact not_exists_pairwiseMLE_of_connected_not_reaches dataset link reference first second
    hstrict hconnected hnotReach hexists

/--
Along a finite directed reachability path, a potential with uniformly bounded
edge increments can increase by at most `(card - 1)` such increments.  This
is graph infrastructure: the relation need not be a comparison graph.
-/
theorem potential_sub_le_card_sub_one_mul_of_reaches
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (relation : Alternative → Alternative → Prop) (potential : Alternative → ℝ)
    (bound : ℝ) (hboundNonneg : 0 ≤ bound)
    (hbound : ∀ first second, relation first second → potential second - potential first ≤ bound)
    {start finish : Alternative} (hreach : Relation.ReflTransGen relation start finish) :
    potential finish - potential start ≤ ((Fintype.card Alternative - 1 : ℕ) : ℝ) * bound := by
  by_cases hsame : start = finish
  · subst finish
    simp only [sub_self]
    exact mul_nonneg (by positivity) hboundNonneg
  obtain ⟨path, hnodup, _hlen, hhead, hlast, hchain⟩ :=
    AppliedModelingLib.Foundations.Graph.exists_nodup_chain_list_of_reaches hsame hreach
  have hpath_ne : path ≠ [] := by
    intro hnil
    simp [hnil] at hhead
  have hzeroIndex : 0 < path.length := List.length_pos_of_ne_nil hpath_ne
  have hfirst : path[0]'hzeroIndex = start := by
    have hhead' : path.head hpath_ne = start :=
      (List.head_eq_iff_head?_eq_some hpath_ne).2 hhead
    simpa [List.head_eq_getElem_zero hpath_ne] using hhead'
  have hlastIndex : path.length - 1 < path.length := by
    have : 0 < path.length := List.length_pos_of_ne_nil hpath_ne
    omega
  have hlast' : path.getLast hpath_ne = finish := by
    have : some (path.getLast hpath_ne) = some finish := by
      simpa [List.getLast?_eq_getLast_of_ne_nil hpath_ne] using hlast
    exact Option.some.inj this
  have hlast : path[path.length - 1]'hlastIndex = finish := by
    rw [← List.getLast_eq_getElem hpath_ne]
    exact hlast'
  have hsteps := AppliedModelingLib.Foundations.Graph.isChain_relatesInSteps_getElem
    (r := relation) hchain (i := 0) (j := path.length - 1) hzeroIndex hlastIndex
      (by omega)
  have hpathBound :
      potential (path[path.length - 1]'hlastIndex) -
          potential (path[0]'hzeroIndex) ≤
        ((path.length - 1 : ℕ) : ℝ) * bound := by
    have hstepBound : ∀ {initial terminal : Alternative} {steps : ℕ},
        Relation.RelatesInSteps relation initial terminal steps →
          potential terminal - potential initial ≤ (steps : ℝ) * bound := by
      intro initial terminal steps hpath
      induction hpath with
      | refl => simp
      | tail middle terminal steps hprevious hedge ih =>
          have hedgeBound := hbound middle terminal hedge
          calc
            potential terminal - potential initial =
                (potential terminal - potential middle) +
                  (potential middle - potential initial) := by ring
            _ ≤ bound + (steps : ℝ) * bound := add_le_add hedgeBound ih
            _ = ((steps + 1 : ℕ) : ℝ) * bound := by
              push_cast
              ring
    exact hstepBound hsteps
  have hlengthBound : path.length - 1 ≤ Fintype.card Alternative - 1 := by
    have hcard := hnodup.length_le_card
    omega
  have hcastLength : ((path.length - 1 : ℕ) : ℝ) ≤
      ((Fintype.card Alternative - 1 : ℕ) : ℝ) := by
    exact_mod_cast hlengthBound
  have hmulBound := mul_le_mul_of_nonneg_right hcastLength hboundNonneg
  calc
    potential finish - potential start =
        potential (path[path.length - 1]'hlastIndex) -
          potential (path[0]'hzeroIndex) := by
      rw [hfirst, hlast]
    _ ≤ ((path.length - 1 : ℕ) : ℝ) * bound := hpathBound
    _ ≤ ((Fintype.card Alternative - 1 : ℕ) : ℝ) * bound := hmulBound

/--
If a finite score vector has a coordinate more than `card * bound` above a
zero reference, then some finite score cut has a gap strictly larger than
`bound`.  The returned lower block contains the reference, excludes the large
coordinate, and every score difference from its complement into the block is
at least the displayed gap.  This is the ordered-score pigeonhole step in the
proof of Noothigattu--Peters--Procaccia Lemma 2.3.
-/
theorem exists_score_cut_of_score_gt_card_mul
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (score : ScoreVector Alternative) (reference target : Alternative) (bound : ℝ)
    (hreference : score reference = 0) (hboundNonneg : 0 ≤ bound)
    (hlarge : (Fintype.card Alternative : ℝ) * bound < score target) :
    ∃ lower : Finset Alternative, ∃ gap : ℝ,
      reference ∈ lower ∧ target ∉ lower ∧ bound < gap ∧
        ∀ low high, low ∈ lower → high ∉ lower → gap ≤ score high - score low := by
  classical
  let increase : Alternative → Alternative → Prop := fun first second =>
    score first < score second ∧ score second - score first ≤ bound
  let reachable : Finset Alternative := (Finset.univ : Finset Alternative).filter
    (fun alternative => Relation.ReflTransGen increase reference alternative ∧
      score alternative ≤ score target)
  have hcardBoundNonneg : 0 ≤ (Fintype.card Alternative : ℝ) * bound := by positivity
  have htargetPos : 0 < score target := hcardBoundNonneg.trans_lt hlarge
  have hrefReachable : reference ∈ reachable := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, Relation.ReflTransGen.refl, ?_⟩
    simpa [hreference] using htargetPos.le
  let reachableScores : Finset ℝ := reachable.image score
  have hreachableScoresNonempty : reachableScores.Nonempty := by
    refine ⟨score reference, Finset.mem_image.2 ⟨reference, hrefReachable, rfl⟩⟩
  let cut : ℝ := reachableScores.max' hreachableScoresNonempty
  have hcutMem : cut ∈ reachableScores := Finset.max'_mem _ _
  obtain ⟨anchor, hanchorReachable, hanchorCut⟩ := Finset.mem_image.mp hcutMem
  have hanchorPath : Relation.ReflTransGen increase reference anchor :=
    (Finset.mem_filter.mp hanchorReachable).2.1
  have hanchorPathBound := potential_sub_le_card_sub_one_mul_of_reaches increase score bound
    hboundNonneg (fun first second hstep => hstep.2) hanchorPath
  have hanchorBound : score anchor ≤ ((Fintype.card Alternative - 1 : ℕ) : ℝ) * bound := by
    rw [hreference] at hanchorPathBound
    simpa using hanchorPathBound
  have hlengthCast : ((Fintype.card Alternative - 1 : ℕ) : ℝ) ≤
      (Fintype.card Alternative : ℝ) := by
    exact_mod_cast Nat.sub_le (Fintype.card Alternative) 1
  have hanchorCardBound : score anchor ≤ (Fintype.card Alternative : ℝ) * bound :=
    hanchorBound.trans (mul_le_mul_of_nonneg_right hlengthCast hboundNonneg)
  have hcutLtTarget : cut < score target := by
    rw [← hanchorCut]
    exact hanchorCardBound.trans_lt hlarge
  have hrefCut : score reference ≤ cut := by
    apply Finset.le_max'
    exact Finset.mem_image.2 ⟨reference, hrefReachable, rfl⟩
  let lower : Finset Alternative := (Finset.univ : Finset Alternative).filter
    (fun alternative => score alternative ≤ cut)
  have hrefLower : reference ∈ lower := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simpa [hreference] using hrefCut
  have htargetNotLower : target ∉ lower := by
    intro htargetLower
    have htargetLeCut : score target ≤ cut := (Finset.mem_filter.mp htargetLower).2
    exact (not_le_of_gt hcutLtTarget) htargetLeCut
  let upper : Finset Alternative := (Finset.univ : Finset Alternative).filter
    (fun alternative => cut < score alternative)
  have htargetUpper : target ∈ upper := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hcutLtTarget⟩
  let upperScores : Finset ℝ := upper.image score
  have hupperScoresNonempty : upperScores.Nonempty := by
    refine ⟨score target, Finset.mem_image.2 ⟨target, htargetUpper, rfl⟩⟩
  let next : ℝ := upperScores.min' hupperScoresNonempty
  have hnextMem : next ∈ upperScores := Finset.min'_mem _ _
  obtain ⟨nextAlternative, hnextUpper, hnextScore⟩ := Finset.mem_image.mp hnextMem
  have hcutLtNext : cut < next := by
    have : cut < score nextAlternative := (Finset.mem_filter.mp hnextUpper).2
    simpa [hnextScore] using this
  have hnextLeTarget : next ≤ score target := by
    apply Finset.min'_le
    exact Finset.mem_image.2 ⟨target, htargetUpper, rfl⟩
  have hgap : bound < next - cut := by
    by_contra hnot
    have hgapLe : next - cut ≤ bound := le_of_not_gt hnot
    have hstep : increase anchor nextAlternative := by
      constructor
      · calc
          score anchor = cut := hanchorCut
          _ < next := hcutLtNext
          _ = score nextAlternative := hnextScore.symm
      · calc
          score nextAlternative - score anchor = next - cut := by rw [hanchorCut, hnextScore]
          _ ≤ bound := hgapLe
    have hnextPath : Relation.ReflTransGen increase reference nextAlternative :=
      Relation.ReflTransGen.tail hanchorPath hstep
    have hnextReachable : nextAlternative ∈ reachable := by
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hnextPath, ?_⟩
      calc
        score nextAlternative = next := hnextScore
        _ ≤ score target := hnextLeTarget
    have hnextLeCut : score nextAlternative ≤ cut := by
      apply Finset.le_max'
      exact Finset.mem_image.2 ⟨nextAlternative, hnextReachable, rfl⟩
    have : next ≤ cut := by simpa [hnextScore] using hnextLeCut
    exact (not_le_of_gt hcutLtNext) this
  refine ⟨lower, next - cut, hrefLower, htargetNotLower, hgap, ?_⟩
  intro low high hlow hhigh
  have hlowLeCut : score low ≤ cut := (Finset.mem_filter.mp hlow).2
  have hhighGtCut : cut < score high := by
    apply lt_of_not_ge
    intro hhighLeCut
    apply hhigh
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hhighLeCut⟩
  have hhighUpper : high ∈ upper :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hhighGtCut⟩
  have hnextLeHigh : next ≤ score high := by
    apply Finset.min'_le
    exact Finset.mem_image.2 ⟨high, hhighUpper, rfl⟩
  linarith

/-- A per-edge upper bound on score increases accumulates along a fixed-length path. -/
theorem score_sub_le_of_relatesInSteps
    {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (score : ScoreVector Alternative) (bound : ℝ)
    (hbound : ∀ first second, dataset.edge first second → score second - score first ≤ bound)
    {start finish : Alternative} {steps : ℕ}
    (hsteps : Relation.RelatesInSteps dataset.edge start finish steps) :
    score finish - score start ≤ (steps : ℝ) * bound := by
  induction hsteps with
  | refl => simp
  | tail middle finish steps hprevious hedge ih =>
      have hedgeBound := hbound middle finish hedge
      calc
        score finish - score start =
            (score finish - score middle) + (score middle - score start) := by ring
        _ ≤ bound + (steps : ℝ) * bound := add_le_add hedgeBound ih
        _ = ((steps + 1 : ℕ) : ℝ) * bound := by
          push_cast
          ring

/--
On a finite comparison graph, a uniform upper bound on edgewise score
increases bounds the total score increase along any directed reachability
path by `(card - 1)` times that edge bound.
-/
theorem score_sub_le_card_sub_one_mul_of_reaches
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (score : ScoreVector Alternative)
    (bound : ℝ) (hboundNonneg : 0 ≤ bound)
    (hbound : ∀ first second, dataset.edge first second → score second - score first ≤ bound)
    {start finish : Alternative} (hreach : dataset.reaches start finish) :
    score finish - score start ≤ ((Fintype.card Alternative - 1 : ℕ) : ℝ) * bound := by
  by_cases hsame : start = finish
  · subst finish
    simp only [sub_self]
    exact mul_nonneg (by positivity) hboundNonneg
  obtain ⟨path, hnodup, _hlen, hhead, hlast, hchain⟩ :=
    AppliedModelingLib.Foundations.Graph.exists_nodup_chain_list_of_reaches hsame hreach
  have hpath_ne : path ≠ [] := by
    intro hnil
    simp [hnil] at hhead
  have hzeroIndex : 0 < path.length := List.length_pos_of_ne_nil hpath_ne
  have hfirst : path[0]'hzeroIndex = start := by
    have hhead' : path.head hpath_ne = start :=
      (List.head_eq_iff_head?_eq_some hpath_ne).2 hhead
    simpa [List.head_eq_getElem_zero hpath_ne] using hhead'
  have hlastIndex : path.length - 1 < path.length := by
    have : 0 < path.length := List.length_pos_of_ne_nil hpath_ne
    omega
  have hlast' : path.getLast hpath_ne = finish := by
    have : some (path.getLast hpath_ne) = some finish := by
      simpa [List.getLast?_eq_getLast_of_ne_nil hpath_ne] using hlast
    exact Option.some.inj this
  have hlast : path[path.length - 1]'hlastIndex = finish := by
    rw [← List.getLast_eq_getElem hpath_ne]
    exact hlast'
  have hsteps := AppliedModelingLib.Foundations.Graph.isChain_relatesInSteps_getElem
    (r := dataset.edge) hchain (i := 0) (j := path.length - 1) hzeroIndex hlastIndex (by omega)
  have hpathBound := score_sub_le_of_relatesInSteps dataset score bound hbound hsteps
  have hlengthBound : path.length - 1 ≤ Fintype.card Alternative - 1 := by
    have hcard := hnodup.length_le_card
    omega
  have hcastLength : ((path.length - 1 : ℕ) : ℝ) ≤
      ((Fintype.card Alternative - 1 : ℕ) : ℝ) := by
    exact_mod_cast hlengthBound
  have hmulBound := mul_le_mul_of_nonneg_right hcastLength hboundNonneg
  calc
    score finish - score start =
        score (path[path.length - 1]'hlastIndex) - score (path[0]'hzeroIndex) := by
      rw [hfirst, hlast]
    _ ≤ ((path.length - 1 : ℕ) : ℝ) * bound := hpathBound
    _ ≤ ((Fintype.card Alternative - 1 : ℕ) : ℝ) * bound := hmulBound

/-- The finite multiset of score values in one undirected comparison component. -/
noncomputable def componentScoreValues
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (score : ScoreVector Alternative)
    (componentMember : Alternative) : Finset ℝ := by
  classical
  exact ((Finset.univ.filter fun alternative =>
    dataset.connectedTo alternative componentMember).image score)

/-- Every comparison component contributes at least its designated member's score value. -/
theorem componentScoreValues_nonempty
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (score : ScoreVector Alternative)
    (componentMember : Alternative) :
    (dataset.componentScoreValues score componentMember).Nonempty := by
  classical
  refine ⟨score componentMember, ?_⟩
  refine Finset.mem_image.2 ⟨componentMember, ?_, rfl⟩
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩

/-- The least score value in an undirected comparison component. -/
noncomputable def componentScoreMinimum
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (score : ScoreVector Alternative)
    (componentMember : Alternative) : ℝ :=
  (dataset.componentScoreValues score componentMember).min'
    (componentScoreValues_nonempty dataset score componentMember)

/-- A component minimum is no greater than the score of any member of that component. -/
theorem componentScoreMinimum_le_score
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (score : ScoreVector Alternative)
    (componentMember alternative : Alternative)
    (hconnected : dataset.connectedTo alternative componentMember) :
    dataset.componentScoreMinimum score componentMember ≤ score alternative := by
  classical
  apply Finset.min'_le
  refine Finset.mem_image.2 ⟨alternative, ?_, rfl⟩
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hconnected⟩

/-- Connected component members induce the same finite score-value set. -/
theorem componentScoreValues_eq_of_connected
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (score : ScoreVector Alternative)
    {first second : Alternative} (hconnected : dataset.connectedTo first second) :
    dataset.componentScoreValues score first = dataset.componentScoreValues score second := by
  classical
  apply Finset.ext
  intro value
  simp only [componentScoreValues, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨alternative, hfirst, hvalue⟩
    exact ⟨alternative, connectedTo_trans dataset hfirst hconnected, hvalue⟩
  · rintro ⟨alternative, hsecond, hvalue⟩
    exact ⟨alternative, connectedTo_trans dataset hsecond
      (connectedTo_symm dataset hconnected), hvalue⟩

/-- Connected component members have the same finite score minimum. -/
theorem componentScoreMinimum_eq_of_connected
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (score : ScoreVector Alternative)
    {first second : Alternative} (hconnected : dataset.connectedTo first second) :
    dataset.componentScoreMinimum score first = dataset.componentScoreMinimum score second := by
  simp only [componentScoreMinimum,
    componentScoreValues_eq_of_connected dataset score hconnected]

/-- Shift every comparison component so that its least score is zero. -/
noncomputable def normalizeByComponents
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (score : ScoreVector Alternative) :
    ScoreVector Alternative :=
  fun alternative => score alternative - dataset.componentScoreMinimum score alternative

/-- Component-minimum normalization makes every coordinate nonnegative. -/
theorem normalizeByComponents_nonneg
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (score : ScoreVector Alternative)
    (alternative : Alternative) :
    0 ≤ dataset.normalizeByComponents score alternative := by
  unfold normalizeByComponents
  exact sub_nonneg.mpr (componentScoreMinimum_le_score dataset score alternative alternative
    Relation.ReflTransGen.refl)

/-- Every component has a coordinate equal to zero after minimum normalization. -/
theorem exists_normalizeByComponents_eq_zero_in_component
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (score : ScoreVector Alternative)
    (componentMember : Alternative) :
    ∃ alternative, dataset.connectedTo alternative componentMember ∧
      dataset.normalizeByComponents score alternative = 0 := by
  classical
  let values := dataset.componentScoreValues score componentMember
  have hvalues : values.Nonempty := componentScoreValues_nonempty dataset score componentMember
  obtain ⟨alternative, halternative, hscore⟩ :=
    Finset.mem_image.mp (Finset.min'_mem values hvalues)
  have hconnected : dataset.connectedTo alternative componentMember := by
    simpa [values, componentScoreValues] using halternative
  refine ⟨alternative, hconnected, ?_⟩
  unfold normalizeByComponents
  rw [componentScoreMinimum_eq_of_connected dataset score hconnected]
  dsimp [componentScoreMinimum, values] at hscore ⊢
  linarith

/-- Component-minimum normalization preserves the score gap of every graph edge. -/
theorem normalizeByComponents_sub_eq_of_edge
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (score : ScoreVector Alternative)
    {first second : Alternative} (hedge : dataset.edge first second) :
    dataset.normalizeByComponents score first - dataset.normalizeByComponents score second =
      score first - score second := by
  unfold normalizeByComponents
  have hconnected := edge_connectedTo dataset hedge
  rw [componentScoreMinimum_eq_of_connected dataset score hconnected]
  ring

/-- Component-minimum normalization preserves the finite pairwise likelihood. -/
theorem pairwiseLogLikelihood_normalizeByComponents
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (score : ScoreVector Alternative) :
    pairwiseLogLikelihood dataset link (dataset.normalizeByComponents score) =
      pairwiseLogLikelihood dataset link score := by
  unfold pairwiseLogLikelihood
  apply Finset.sum_congr rfl
  rintro ⟨first, second⟩ hpair
  by_cases hcount : dataset.count first second = 0
  · simp [hcount]
  have hedge : dataset.edge first second := Nat.pos_of_ne_zero hcount
  have hgap := normalizeByComponents_sub_eq_of_edge dataset score hedge
  unfold randomUtilityWinProbability
  rw [hgap]

/-- A score vector is normalized at the least score in every comparison component. -/
def IsComponentMinNormalized
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (score : ScoreVector Alternative) : Prop :=
  (∀ alternative, 0 ≤ score alternative) ∧
    ∀ componentMember, ∃ alternative,
      dataset.connectedTo alternative componentMember ∧ score alternative = 0

/-- Component-minimum normalization satisfies the canonical per-component convention. -/
theorem isComponentMinNormalized_normalizeByComponents
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (score : ScoreVector Alternative) :
    dataset.IsComponentMinNormalized (dataset.normalizeByComponents score) := by
  constructor
  · exact normalizeByComponents_nonneg dataset score
  · exact exists_normalizeByComponents_eq_zero_in_component dataset score

/-- The finite undirected comparison component containing a designated alternative. -/
noncomputable def undirectedComponent
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (root : Alternative) : Finset Alternative := by
  classical
  exact Finset.univ.filter (fun alternative => dataset.connectedTo alternative root)

/-- Membership in an undirected comparison component is the corresponding reachability predicate. -/
theorem mem_undirectedComponent
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (root alternative : Alternative) :
    alternative ∈ dataset.undirectedComponent root ↔ dataset.connectedTo alternative root := by
  classical
  simp [undirectedComponent]

/-- Every directed edge either stays inside an undirected component or stays outside it. -/
theorem edge_mem_undirectedComponent_iff
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (root first second : Alternative)
    (hedge : dataset.edge first second) :
    first ∈ dataset.undirectedComponent root ↔ second ∈ dataset.undirectedComponent root := by
  rw [mem_undirectedComponent, mem_undirectedComponent]
  have hconnected := edge_connectedTo dataset hedge
  constructor
  · intro hfirst
    exact connectedTo_trans dataset (connectedTo_symm dataset hconnected) hfirst
  · intro hsecond
    exact connectedTo_trans dataset hconnected hsecond

/-- Shifting one whole undirected comparison component preserves likelihood. -/
theorem pairwiseLogLikelihood_scoreShiftOn_undirectedComponent
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (score : ScoreVector Alternative) (root : Alternative) (shift : ℝ) :
    pairwiseLogLikelihood dataset link
      (scoreShiftOn (dataset.undirectedComponent root) score shift) =
        pairwiseLogLikelihood dataset link score := by
  unfold pairwiseLogLikelihood
  apply Finset.sum_congr rfl
  rintro ⟨first, second⟩ hpair
  by_cases hcount : dataset.count first second = 0
  · simp [hcount]
  have hedge : dataset.edge first second := Nat.pos_of_ne_zero hcount
  have hmem := edge_mem_undirectedComponent_iff dataset root first second hedge
  by_cases hfirst : first ∈ dataset.undirectedComponent root
  · have hsecond : second ∈ dataset.undirectedComponent root := hmem.mp hfirst
    have hgap := scoreShiftOn_sub_of_mem (dataset.undirectedComponent root) score shift
      hfirst hsecond
    unfold randomUtilityWinProbability
    rw [hgap]
  · have hsecond : second ∉ dataset.undirectedComponent root := by
      intro hsecond
      exact hfirst (hmem.mpr hsecond)
    have hgap := scoreShiftOn_sub_of_not_mem (dataset.undirectedComponent root) score shift
      hfirst hsecond
    unfold randomUtilityWinProbability
    rw [hgap]

/-- Under continuity and strict monotonicity of the link, finite likelihood is continuous. -/
theorem continuous_pairwiseLogLikelihood
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    Continuous (pairwiseLogLikelihood dataset link) := by
  unfold pairwiseLogLikelihood
  apply continuous_finset_sum
  intro pair _
  apply Continuous.const_mul
  apply (hcontinuous.comp ((continuous_apply pair.1).sub (continuous_apply pair.2))).log
  intro score
  exact ne_of_gt (link.openProbability hstrict _).1

/--
A compactness reduction for finite pairwise likelihoods.  If every
component-minimum-normalized score vector outside the finite cube has lower
likelihood than zero, continuity yields a fixed-reference MLE. The following
source-specific coercivity theorem discharges this explicit barrier premise
from directed strong connectivity and the CDF endpoint limit.
-/
theorem exists_pairwiseMLE_of_componentMinNormalized_compactBarrier
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference : Alternative) (bound : ℝ) (hbound : 0 ≤ bound)
    (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ))
    (hbarrier : ∀ score : ScoreVector Alternative,
      dataset.IsComponentMinNormalized score →
      (∃ alternative, bound < score alternative) →
      pairwiseLogLikelihood dataset link score < pairwiseLogLikelihood dataset link 0) :
    ∃ score : ScoreVector Alternative, isPairwiseMLE dataset link reference score := by
  let cube : Set (ScoreVector Alternative) :=
    Set.univ.pi (fun _ : Alternative => Set.Icc (0 : ℝ) bound)
  have hcubeCompact : IsCompact cube := by
    dsimp [cube]
    exact isCompact_univ_pi fun _ : Alternative => isCompact_Icc
  have hzeroCube : (0 : ScoreVector Alternative) ∈ cube := by
    intro alternative _
    exact ⟨le_rfl, hbound⟩
  obtain ⟨maxScore, hmaxCube, hmax⟩ := hcubeCompact.exists_isMaxOn ⟨0, hzeroCube⟩
    (continuous_pairwiseLogLikelihood dataset link hcontinuous hstrict).continuousOn
  have hglobal : ∀ candidate : ScoreVector Alternative,
      pairwiseLogLikelihood dataset link candidate ≤ pairwiseLogLikelihood dataset link maxScore := by
    intro candidate
    let normalized := dataset.normalizeByComponents candidate
    have hnormalized : dataset.IsComponentMinNormalized normalized :=
      isComponentMinNormalized_normalizeByComponents dataset candidate
    have hnormalizedLikelihood : pairwiseLogLikelihood dataset link normalized =
        pairwiseLogLikelihood dataset link candidate :=
      pairwiseLogLikelihood_normalizeByComponents dataset link candidate
    by_cases hnormalizedCube : normalized ∈ cube
    · calc
        pairwiseLogLikelihood dataset link candidate =
            pairwiseLogLikelihood dataset link normalized := hnormalizedLikelihood.symm
        _ ≤ pairwiseLogLikelihood dataset link maxScore := hmax hnormalizedCube
    · have houtside : ∃ alternative, bound < normalized alternative := by
        by_contra hnot
        push_neg at hnot
        apply hnormalizedCube
        intro alternative _
        exact ⟨hnormalized.1 alternative, hnot alternative⟩
      have hless := hbarrier normalized hnormalized houtside
      have hzeroMax := hmax hzeroCube
      exact (hnormalizedLikelihood.symm ▸ hless.le).trans hzeroMax
  let mleScore : ScoreVector Alternative :=
    scoreShiftOn (dataset.undirectedComponent reference) maxScore (-maxScore reference)
  have hrefmem : reference ∈ dataset.undirectedComponent reference := by
    rw [mem_undirectedComponent]
    exact Relation.ReflTransGen.refl
  have hnormalizedReference : isReferenceNormalized reference mleScore := by
    dsimp [isReferenceNormalized, mleScore]
    simp [scoreShiftOn, hrefmem]
  have hmleLikelihood : pairwiseLogLikelihood dataset link mleScore =
      pairwiseLogLikelihood dataset link maxScore := by
    dsimp [mleScore]
    exact pairwiseLogLikelihood_scoreShiftOn_undirectedComponent dataset link maxScore reference
      (-maxScore reference)
  refine ⟨mleScore, hnormalizedReference, ?_⟩
  intro candidate _hcandidate
  calc
    pairwiseLogLikelihood dataset link candidate ≤ pairwiseLogLikelihood dataset link maxScore :=
      hglobal candidate
    _ = pairwiseLogLikelihood dataset link mleScore := hmleLikelihood.symm

/-- Every finite pairwise likelihood summand is nonpositive for a CDF-like link. -/
theorem pairwiseLogLikelihoodSummand_nonpos
    {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (link : CDFLikePairwiseLink) (score : ScoreVector Alternative)
    (first second : Alternative) :
    (dataset.count first second : ℝ) *
      Real.log (randomUtilityWinProbability link score first second) ≤ 0 := by
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact_mod_cast (Nat.zero_le (dataset.count first second))
  · apply Real.log_nonpos
    · exact link.nonneg _
    · exact link.le_one _

/-- The full likelihood is at most any one of its off-diagonal summands. -/
theorem pairwiseLogLikelihood_le_summand
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (score : ScoreVector Alternative) (first second : Alternative)
    (hpair : (first, second) ∈ (Finset.univ : Finset Alternative).offDiag) :
    pairwiseLogLikelihood dataset link score ≤
      (dataset.count first second : ℝ) *
        Real.log (randomUtilityWinProbability link score first second) := by
  unfold pairwiseLogLikelihood
  rw [Finset.sum_eq_add_sum_diff_singleton (first, second)]
  · have hrest : ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag \ {(first, second)},
        (dataset.count pair.1 pair.2 : ℝ) *
          Real.log (randomUtilityWinProbability link score pair.1 pair.2) ≤ 0 := by
        apply Finset.sum_nonpos
        intro pair hpair
        exact pairwiseLogLikelihoodSummand_nonpos dataset link score pair.1 pair.2
    linarith
  · intro hnot
    exact (hnot hpair).elim

/-- The lower-tail CDF limit supplies an arbitrarily unfavorable finite score gap. -/
theorem exists_pos_log_link_neg_lt
    (link : CDFLikePairwiseLink) (hstrict : StrictMono (link : ℝ → ℝ))
    (target : ℝ) :
    ∃ bound : ℝ, 0 < bound ∧ Real.log (link (-bound)) < target := by
  have hneighborhood : Set.Iio (Real.exp target) ∈ nhds (0 : ℝ) :=
    Iio_mem_nhds (Real.exp_pos target)
  have hsmall : ∀ᶠ gap in Filter.atBot, link gap < Real.exp target :=
    link.tendsto_atBot_zero.eventually hneighborhood
  obtain ⟨gap, hgap, hnegative⟩ :=
    (hsmall.and (Filter.eventually_le_atBot (-1 : ℝ))).exists
  refine ⟨-gap, by linarith, ?_⟩
  have hlog : Real.log (link gap) < Real.log (Real.exp target) :=
    Real.strictMonoOn_log (link.openProbability hstrict gap).1 (Real.exp_pos target) hgap
  calc
    Real.log (link (- -gap)) = Real.log (link gap) := by ring_nf
    _ < Real.log (Real.exp target) := hlog
    _ = target := Real.log_exp target

/--
Componentwise directed strong connectivity makes the finite pairwise
log-likelihood coercive after minimum normalization, and therefore guarantees
the existence of a fixed-reference MLE. The formal proof deliberately chooses
a convenient bound from the CDF tail limit instead of tracking the appendix's
more explicit numerical constant.
-/
theorem exists_pairwiseMLE_of_everyComponentStronglyConnected
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference : Alternative) (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ))
    (hstrong : dataset.everyComponentStronglyConnected) :
    ∃ score : ScoreVector Alternative, isPairwiseMLE dataset link reference score := by
  let zeroLikelihood : ℝ := pairwiseLogLikelihood dataset link 0
  obtain ⟨edgeBound, hedgeBoundPos, hedgeBound⟩ :=
    exists_pos_log_link_neg_lt link hstrict zeroLikelihood
  let cubeBound : ℝ := ((Fintype.card Alternative - 1 : ℕ) : ℝ) * edgeBound
  have hcubeBoundNonneg : 0 ≤ cubeBound := by
    dsimp [cubeBound]
    positivity
  apply exists_pairwiseMLE_of_componentMinNormalized_compactBarrier dataset link reference
    cubeBound hcubeBoundNonneg hcontinuous hstrict
  intro score hnormalized houtside
  obtain ⟨alternative, halternativeLarge⟩ := houtside
  obtain ⟨anchor, hconnected, hanchorZero⟩ := hnormalized.2 alternative
  have hreach : dataset.reaches anchor alternative := hstrong anchor alternative hconnected
  have hsteep : ∃ first second,
      dataset.edge first second ∧ edgeBound < score second - score first := by
    by_contra hnotSteep
    push_neg at hnotSteep
    have hpathBound := score_sub_le_card_sub_one_mul_of_reaches dataset score edgeBound
      hedgeBoundPos.le (fun first second hedge => hnotSteep first second hedge) hreach
    dsimp [cubeBound] at halternativeLarge
    have hpathBound' : score alternative ≤
        ((Fintype.card Alternative - 1 : ℕ) : ℝ) * edgeBound := by
      simpa [hanchorZero] using hpathBound
    exact (not_lt_of_ge hpathBound') halternativeLarge
  obtain ⟨first, second, hedge, hsteepGap⟩ := hsteep
  have hactualGap : score first - score second < -edgeBound := by linarith
  have hlink : link (score first - score second) < link (-edgeBound) := hstrict hactualGap
  have hlog : Real.log (link (score first - score second)) < zeroLikelihood := by
    calc
      Real.log (link (score first - score second)) < Real.log (link (-edgeBound)) :=
        Real.strictMonoOn_log (link.openProbability hstrict _).1
          (link.openProbability hstrict _).1 hlink
      _ < zeroLikelihood := hedgeBound
  have hlogNonpos : Real.log (link (score first - score second)) ≤ 0 := by
    apply Real.log_nonpos
    · exact link.nonneg _
    · exact link.le_one _
  have hcountOne : (1 : ℝ) ≤ dataset.count first second := by
    exact_mod_cast (Nat.succ_le_iff.mpr hedge)
  have hterm : (dataset.count first second : ℝ) *
      Real.log (randomUtilityWinProbability link score first second) < zeroLikelihood := by
    have hproduct : (dataset.count first second : ℝ) *
        Real.log (link (score first - score second)) ≤
          (1 : ℝ) * Real.log (link (score first - score second)) :=
      mul_le_mul_of_nonpos_right hcountOne hlogNonpos
    calc
      (dataset.count first second : ℝ) *
          Real.log (randomUtilityWinProbability link score first second) =
            (dataset.count first second : ℝ) *
              Real.log (link (score first - score second)) := rfl
      _ ≤ Real.log (link (score first - score second)) := by simpa using hproduct
      _ < zeroLikelihood := hlog
  have hpair : (first, second) ∈ (Finset.univ : Finset Alternative).offDiag :=
    Finset.mem_offDiag.2 ⟨Finset.mem_univ first, Finset.mem_univ second, edge_ne dataset hedge⟩
  calc
    pairwiseLogLikelihood dataset link score ≤
        (dataset.count first second : ℝ) *
          Real.log (randomUtilityWinProbability link score first second) :=
      pairwiseLogLikelihood_le_summand dataset link score first second hpair
    _ < zeroLikelihood := hterm
    _ = pairwiseLogLikelihood dataset link 0 := rfl

/-- Source Lemma 2.1, in the finite fixed-reference likelihood model. -/
theorem pairwiseMLE_exists_iff_everyComponentStronglyConnected
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference : Alternative) (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    (∃ score : ScoreVector Alternative, isPairwiseMLE dataset link reference score) ↔
      dataset.everyComponentStronglyConnected := by
  constructor
  · exact everyComponentStronglyConnected_of_exists_pairwiseMLE dataset link reference hstrict
  · exact exists_pairwiseMLE_of_everyComponentStronglyConnected dataset link reference hcontinuous
      hstrict

/--
The source perfect-fit distance `δ(x,y)`, totalized by zero only for pairs
without two positive directed counts. Under Lemma 2.3's complete-positive
count premise the first branch is always used, so this is exactly the source
inverse-image distance.
-/
noncomputable def perfectFitDistance
    {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (link : CDFLikePairwiseLink) (hcontinuous : Continuous (link : ℝ → ℝ))
    (first second : Alternative) : ℝ :=
  if hpositive : 0 < dataset.count first second ∧ 0 < dataset.count second first then
    Classical.choose (link.exists_eq_of_mem_Ioo hcontinuous (by
      have hforward : 0 < (dataset.count first second : ℝ) := by
        exact_mod_cast hpositive.1
      have hreverse : 0 < (dataset.count second first : ℝ) := by
        exact_mod_cast hpositive.2
      have hdenominator : 0 <
          (dataset.count first second : ℝ) + (dataset.count second first : ℝ) :=
        add_pos hforward hreverse
      constructor
      · exact div_pos hforward hdenominator
      · exact (div_lt_one hdenominator).2 (lt_add_of_pos_right _ hreverse)))
  else 0

/-- Perfect-fit distance realizes the empirical pair frequency when both directed counts are positive. -/
theorem link_perfectFitDistance_eq_empirical_frequency
    {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (link : CDFLikePairwiseLink) (hcontinuous : Continuous (link : ℝ → ℝ))
    (first second : Alternative)
    (hforward : 0 < dataset.count first second)
    (hreverse : 0 < dataset.count second first) :
    link (dataset.perfectFitDistance link hcontinuous first second) =
      (dataset.count first second : ℝ) /
        ((dataset.count first second : ℝ) + (dataset.count second first : ℝ)) := by
  classical
  have hforwardReal : 0 < (dataset.count first second : ℝ) := by
    exact_mod_cast hforward
  have hreverseReal : 0 < (dataset.count second first : ℝ) := by
    exact_mod_cast hreverse
  have hdenominator : 0 <
      (dataset.count first second : ℝ) + (dataset.count second first : ℝ) :=
    add_pos hforwardReal hreverseReal
  have hfrequency :
      (dataset.count first second : ℝ) /
          ((dataset.count first second : ℝ) + (dataset.count second first : ℝ)) ∈
        Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos hforwardReal hdenominator
    · exact (div_lt_one hdenominator).2 (lt_add_of_pos_right _ hreverseReal)
  unfold perfectFitDistance
  rw [dif_pos ⟨hforward, hreverse⟩]
  exact Classical.choose_spec (link.exists_eq_of_mem_Ioo hcontinuous hfrequency)

/-- The finite maximum of all (totalized) source perfect-fit distances. -/
noncomputable def maxPerfectFitDistance
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (hcontinuous : Continuous (link : ℝ → ℝ)) (reference : Alternative) : ℝ := by
  classical
  let values : Finset ℝ :=
    ((Finset.univ : Finset Alternative) ×ˢ Finset.univ).image
      (fun pair => dataset.perfectFitDistance link hcontinuous pair.1 pair.2)
  exact values.max' (by
    refine ⟨dataset.perfectFitDistance link hcontinuous reference reference, ?_⟩
    simp [values])

/-- Every source perfect-fit distance is at most its finite maximum. -/
theorem perfectFitDistance_le_maxPerfectFitDistance
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (hcontinuous : Continuous (link : ℝ → ℝ)) (reference first second : Alternative) :
    dataset.perfectFitDistance link hcontinuous first second ≤
      dataset.maxPerfectFitDistance link hcontinuous reference := by
  classical
  unfold maxPerfectFitDistance
  apply Finset.le_max'
  simp

/-- The source's finite `ℓ∞` norm for a score vector, anchored only to witness nonemptiness. -/
noncomputable def scoreSupNorm
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (reference : Alternative) (score : ScoreVector Alternative) : ℝ := by
  classical
  let values : Finset ℝ := (Finset.univ : Finset Alternative).image (fun alternative => |score alternative|)
  exact values.max' (by
    refine ⟨|score reference|, ?_⟩
    simp [values])

/-- Every score coordinate is bounded in absolute value by the finite source `ℓ∞` norm. -/
theorem abs_score_le_scoreSupNorm
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (reference alternative : Alternative) (score : ScoreVector Alternative) :
    |score alternative| ≤ scoreSupNorm reference score := by
  classical
  unfold scoreSupNorm
  apply Finset.le_max'
  simp

/-- The finite score sup norm is attained at some alternative. -/
theorem exists_abs_score_eq_scoreSupNorm
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (reference : Alternative) (score : ScoreVector Alternative) :
    ∃ alternative, |score alternative| = scoreSupNorm reference score := by
  classical
  unfold scoreSupNorm
  let values : Finset ℝ := (Finset.univ : Finset Alternative).image (fun alternative => |score alternative|)
  have hvalues : values.Nonempty := by
    refine ⟨|score reference|, Finset.mem_image.2 ⟨reference, Finset.mem_univ _, rfl⟩⟩
  have hmaxMem : values.max' hvalues ∈ values := Finset.max'_mem _ _
  obtain ⟨alternative, _, hscore⟩ := Finset.mem_image.mp hmaxMem
  exact ⟨alternative, hscore⟩

/-- The totalized perfect-fit distance is zero on a diagonal pair. -/
theorem perfectFitDistance_self
    {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (link : CDFLikePairwiseLink) (hcontinuous : Continuous (link : ℝ → ℝ))
    (alternative : Alternative) :
    dataset.perfectFitDistance link hcontinuous alternative alternative = 0 := by
  unfold perfectFitDistance
  simp [dataset.diagonal_zero]

/--
For a fully observed finite comparison dataset, shifting every score in the
lower side of a strictly-too-wide score cut toward the upper side strictly
raises likelihood.  Each cross-pair gap remains above its perfect-fit
distance, so the two-direction coin-flip term improves; within-block terms
are unchanged.  This is the likelihood-improvement half of source Lemma 2.3.
-/
theorem pairwiseLogLikelihood_lt_scoreShiftOn_of_complete_perfectFit_cut
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (hcontinuous : Continuous (link : ℝ → ℝ)) (hstrict : StrictMono (link : ℝ → ℝ))
    (score : ScoreVector Alternative) (lower : Finset Alternative)
    (reference : Alternative) (bound gap : ℝ)
    (hcomplete : ∀ first second, first ≠ second → 0 < dataset.count first second)
    (hbound : dataset.maxPerfectFitDistance link hcontinuous reference ≤ bound)
    (hlower : lower.Nonempty) (hupper : ((Finset.univ : Finset Alternative) \ lower).Nonempty)
    (hgap : bound < gap)
    (hcross : ∀ low high, low ∈ lower → high ∉ lower → gap ≤ score high - score low) :
    pairwiseLogLikelihood dataset link score <
      pairwiseLogLikelihood dataset link
        (scoreShiftOn lower score ((gap - bound) / 2)) := by
  let upper : Finset Alternative := (Finset.univ : Finset Alternative) \ lower
  let shift : ℝ := (gap - bound) / 2
  have hshiftPos : 0 < shift := by
    dsimp [shift]
    linarith
  have hcover : lower ∪ upper = (Finset.univ : Finset Alternative) := by
    dsimp [upper]
    exact Finset.union_sdiff_of_subset (fun alternative _ => Finset.mem_univ alternative)
  have hdisjoint : Disjoint lower upper := by
    dsimp [upper]
    exact Finset.disjoint_sdiff
  have hleftEq :
      (∑ first ∈ lower, ∑ second ∈ lower,
        pairwiseLogLikelihoodSummand dataset link
          (scoreShiftOn lower score shift) (first, second)) =
        ∑ first ∈ lower, ∑ second ∈ lower,
          pairwiseLogLikelihoodSummand dataset link score (first, second) := by
    apply Finset.sum_congr rfl
    intro first hfirst
    apply Finset.sum_congr rfl
    intro second hsecond
    have hscoreGap := scoreShiftOn_sub_of_mem lower score shift hfirst hsecond
    unfold pairwiseLogLikelihoodSummand randomUtilityWinProbability
    rw [hscoreGap]
  have hrightEq :
      (∑ first ∈ upper, ∑ second ∈ upper,
        pairwiseLogLikelihoodSummand dataset link
          (scoreShiftOn lower score shift) (first, second)) =
        ∑ first ∈ upper, ∑ second ∈ upper,
          pairwiseLogLikelihoodSummand dataset link score (first, second) := by
    apply Finset.sum_congr rfl
    intro first hfirst
    apply Finset.sum_congr rfl
    intro second hsecond
    have hfirstNotLower : first ∉ lower := (Finset.mem_sdiff.mp hfirst).2
    have hsecondNotLower : second ∉ lower := (Finset.mem_sdiff.mp hsecond).2
    have hscoreGap := scoreShiftOn_sub_of_not_mem lower score shift hfirstNotLower hsecondNotLower
    unfold pairwiseLogLikelihoodSummand randomUtilityWinProbability
    rw [hscoreGap]
  have hcrossTerm : ∀ low high, low ∈ lower → high ∈ upper →
      pairwiseLogTerm dataset link score high low <
        pairwiseLogTerm dataset link (scoreShiftOn lower score shift) high low := by
    intro low high hlow hhigh
    have hhighNotLower : high ∉ lower := (Finset.mem_sdiff.mp hhigh).2
    have hne : high ≠ low := by
      intro heq
      subst high
      exact hhighNotLower hlow
    have hforward : 0 < dataset.count high low := hcomplete high low hne
    have hreverse : 0 < dataset.count low high := hcomplete low high hne.symm
    let perfectFit := dataset.perfectFitDistance link hcontinuous high low
    have hperfectFit : link perfectFit =
        (dataset.count high low : ℝ) /
          ((dataset.count high low : ℝ) + (dataset.count low high : ℝ)) := by
      dsimp [perfectFit]
      exact link_perfectFitDistance_eq_empirical_frequency dataset link hcontinuous high low
        hforward hreverse
    have hperfectFitBound : perfectFit ≤ bound := by
      dsimp [perfectFit]
      exact (perfectFitDistance_le_maxPerfectFitDistance dataset link hcontinuous reference high low).trans
        hbound
    have hcurrentGap : gap ≤ score high - score low := hcross low high hlow hhighNotLower
    have hcandidateGap :
        scoreShiftOn lower score shift high - scoreShiftOn lower score shift low =
          (score high - score low) - shift := by
      rw [scoreShiftOn_apply_not_mem lower score shift hhighNotLower,
        scoreShiftOn_apply_mem lower score shift hlow]
      ring
    have hperfectFitImproved : perfectFit < (score high - score low) - shift := by
      dsimp [shift] at hshiftPos ⊢
      linarith
    have himprovedCurrent : (score high - score low) - shift < score high - score low := by
      linarith
    have himprovement := pairwiseLogTermAtGap_lt_of_perfectFit_between dataset link hstrict high low
      perfectFit ((score high - score low) - shift) (score high - score low)
      hforward hreverse hperfectFit hperfectFitImproved himprovedCurrent
    calc
      pairwiseLogTerm dataset link score high low =
          pairwiseLogTermAtGap dataset link high low (score high - score low) :=
        pairwiseLogTerm_eq_atGap dataset link score high low
      _ < pairwiseLogTermAtGap dataset link high low
          ((score high - score low) - shift) := himprovement
      _ = pairwiseLogTerm dataset link (scoreShiftOn lower score shift) high low := by
        rw [pairwiseLogTerm_eq_atGap dataset link (scoreShiftOn lower score shift) high low,
          hcandidateGap]
  have hcrossTerms :
      (∑ low ∈ lower, ∑ high ∈ upper, pairwiseLogTerm dataset link score high low) <
        ∑ low ∈ lower, ∑ high ∈ upper,
          pairwiseLogTerm dataset link (scoreShiftOn lower score shift) high low := by
    refine Finset.sum_lt_sum ?_ ?_
    · intro low hlow
      refine Finset.sum_le_sum ?_
      intro high hhigh
      exact (hcrossTerm low high hlow hhigh).le
    · obtain ⟨low, hlow⟩ := hlower
      obtain ⟨high, hhigh⟩ := hupper
      change high ∈ upper at hhigh
      exact ⟨low, hlow, Finset.sum_lt_sum
        (fun high' hhigh' => (hcrossTerm low high' hlow hhigh').le)
        ⟨high, hhigh, hcrossTerm low high hlow hhigh⟩⟩
  have hcrossScore := sum_crossPairIndices_pairwiseLogLikelihoodSummand dataset link score
    lower upper hdisjoint
  have hcrossCandidate := sum_crossPairIndices_pairwiseLogLikelihoodSummand dataset link
    (scoreShiftOn lower score shift) lower upper hdisjoint
  have hcrossLt :
      (∑ pair ∈ crossPairIndices lower upper,
        pairwiseLogLikelihoodSummand dataset link score pair) <
      ∑ pair ∈ crossPairIndices lower upper,
        pairwiseLogLikelihoodSummand dataset link (scoreShiftOn lower score shift) pair := by
    rw [hcrossScore, hcrossCandidate]
    exact hcrossTerms
  have hscoreBlocks := pairwiseLogLikelihood_eq_block_sums dataset link score lower upper
    hcover hdisjoint
  have hcandidateBlocks := pairwiseLogLikelihood_eq_block_sums dataset link
    (scoreShiftOn lower score shift) lower upper hcover hdisjoint
  rw [hscoreBlocks, hcandidateBlocks, hleftEq, hrightEq]
  linarith

/--
Source Lemma 2.3's finite MLE bound.  With a positive count in each direction
for every distinct pair, every reference-normalized MLE has `ℓ∞` norm at most
the number of alternatives times the largest perfect-fit distance.  A large
negative coordinate uses the same cut argument after score reflection, with
the lower original-score block shifted upward.
-/
theorem scoreSupNorm_le_card_mul_maxPerfectFitDistance_of_pairwiseMLE
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (hcontinuous : Continuous (link : ℝ → ℝ)) (hstrict : StrictMono (link : ℝ → ℝ))
    (reference : Alternative) (score : ScoreVector Alternative)
    (hmle : isPairwiseMLE dataset link reference score)
    (hcomplete : ∀ first second, first ≠ second → 0 < dataset.count first second) :
    scoreSupNorm reference score ≤ (Fintype.card Alternative : ℝ) *
      dataset.maxPerfectFitDistance link hcontinuous reference := by
  let bound := dataset.maxPerfectFitDistance link hcontinuous reference
  change scoreSupNorm reference score ≤ (Fintype.card Alternative : ℝ) * bound
  have hboundNonneg : 0 ≤ bound := by
    rw [← perfectFitDistance_self dataset link hcontinuous reference]
    exact perfectFitDistance_le_maxPerfectFitDistance dataset link hcontinuous reference reference reference
  by_contra hnot
  have hlargeNorm : (Fintype.card Alternative : ℝ) * bound < scoreSupNorm reference score :=
    lt_of_not_ge hnot
  obtain ⟨target, htargetNorm⟩ := exists_abs_score_eq_scoreSupNorm reference score
  have htargetLarge : (Fintype.card Alternative : ℝ) * bound < |score target| := by
    rw [htargetNorm]
    exact hlargeNorm
  have hreference : score reference = 0 := hmle.1
  by_cases htargetNonneg : 0 ≤ score target
  · have htargetPositive : (Fintype.card Alternative : ℝ) * bound < score target := by
      simpa [abs_of_nonneg htargetNonneg] using htargetLarge
    obtain ⟨lower, gap, hrefLower, htargetNotLower, hgap, hcross⟩ :=
      exists_score_cut_of_score_gt_card_mul score reference target bound hreference hboundNonneg
        htargetPositive
    have hlower : lower.Nonempty := ⟨reference, hrefLower⟩
    have hupper : ((Finset.univ : Finset Alternative) \ lower).Nonempty := by
      refine ⟨target, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, htargetNotLower⟩⟩
    have himprove := pairwiseLogLikelihood_lt_scoreShiftOn_of_complete_perfectFit_cut
      dataset link hcontinuous hstrict score lower reference bound gap hcomplete le_rfl hlower hupper hgap hcross
    have hmax := isPairwiseMLE_global_max dataset link reference score hmle
      (scoreShiftOn lower score ((gap - bound) / 2))
    exact (not_lt_of_ge hmax) himprove
  · have htargetNeg : score target < 0 := lt_of_not_ge htargetNonneg
    let reflectedScore : ScoreVector Alternative := fun alternative => -score alternative
    have hreflectedReference : reflectedScore reference = 0 := by
      dsimp [reflectedScore]
      rw [hreference]
      norm_num
    have htargetReflected : (Fintype.card Alternative : ℝ) * bound < reflectedScore target := by
      dsimp [reflectedScore]
      rw [abs_of_neg htargetNeg] at htargetLarge
      exact htargetLarge
    obtain ⟨reflectedLower, gap, hreflectedLower, htargetNotReflectedLower, hgap, hreflectedCross⟩ :=
      exists_score_cut_of_score_gt_card_mul reflectedScore reference target bound
        hreflectedReference hboundNonneg htargetReflected
    let lower : Finset Alternative := (Finset.univ : Finset Alternative) \ reflectedLower
    have hlower : lower.Nonempty := by
      refine ⟨target, ?_⟩
      exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, htargetNotReflectedLower⟩
    have hupper : ((Finset.univ : Finset Alternative) \ lower).Nonempty := by
      refine ⟨reference, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, ?_⟩⟩
      intro hreflectedOutside
      exact (Finset.mem_sdiff.mp hreflectedOutside).2 hreflectedLower
    have hcross : ∀ low high, low ∈ lower → high ∉ lower → gap ≤ score high - score low := by
      intro low high hlow hhigh
      have hlowNotReflected : low ∉ reflectedLower := (Finset.mem_sdiff.mp hlow).2
      have hhighReflected : high ∈ reflectedLower := by
        by_contra hhighNotReflected
        apply hhigh
        exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hhighNotReflected⟩
      have hreflectedGap := hreflectedCross high low hhighReflected hlowNotReflected
      dsimp [reflectedScore] at hreflectedGap
      linarith
    have himprove := pairwiseLogLikelihood_lt_scoreShiftOn_of_complete_perfectFit_cut
      dataset link hcontinuous hstrict score lower reference bound gap hcomplete le_rfl hlower hupper hgap hcross
    have hmax := isPairwiseMLE_global_max dataset link reference score hmle
      (scoreShiftOn lower score ((gap - bound) / 2))
    exact (not_lt_of_ge hmax) himprove

end PairwiseCountDataset
end HumanFeedback
end Learning
end AppliedModelingLib
