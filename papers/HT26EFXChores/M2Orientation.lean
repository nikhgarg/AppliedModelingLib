import Mathlib
import AppliedModelingLib.SocialChoice.FairDivision.Chores
import HT26EFXChores.BalancedOrientation

/-!
# The all-small orientation branch of M2

This formalizes Case 1 of the source M2 proof. It derives the balanced Hall
quotas from no deficiency, including the source's exceptional remainder-two
tight-pair argument, then orients endpoints to produce EFX because an oriented
edge is small for its owner. It also records source-faithful structural and
fairness bridges used by the later singleton- and pair-deficiency cases.

Source: `EFXadditivechores.tex`, Case 1 of Lemma M2, lines 1053--1080.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- The small-item certificate in the M2-properties lemma is an immediate
additive form of EFX: removing any owned small chore subtracts one. -/
theorem smallItemCertificate_of_efx
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (allocation : Allocation (Fin 4) Item)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (agent : Fin 4) (hsmall : ∃ item ∈ allocation agent, IsSmallChore cost agent item) :
    ∀ other, additiveChoreCost cost agent (allocation agent) - 1 ≤
      additiveChoreCost cost agent (allocation other) := by
  obtain ⟨item, hitem, hcost⟩ := hsmall
  intro other
  exact EFXForChores.additive_sub_one_le_of_small cost allocation hefx agent other item hitem hcost

/-- In an EFX allocation whose owners find all of their chores small, the
M2-properties certificates hold: a nonempty bundle has the unit-slack
certificate, while an all-large bundle must be empty and is envy-free. -/
theorem allSmallOwner_efx_certificates
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (allocation : Allocation (Fin 4) Item) (hr : 2 < r)
    (hcost : IsOneOrRChoreCost cost r)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (hownerSmall : ∀ agent item, item ∈ allocation agent → IsSmallChore cost agent item) :
    (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
      additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
    (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
      additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) := by
  constructor
  · intro i hsmall
    exact smallItemCertificate_of_efx Item cost allocation hefx i hsmall
  · intro i hlarge j
    have hempty : allocation i = ∅ := by
      by_contra hnotempty
      obtain ⟨item, hitem⟩ := Finset.nonempty_iff_ne_empty.mpr hnotempty
      have hsmall := hownerSmall i item hitem
      have hlargeItem := hlarge item hitem
      rw [IsSmallChore] at hsmall
      rw [IsLargeChore] at hlargeItem
      linarith
    rw [hempty]
    simp only [additiveChoreCost, Finset.sum_empty]
    exact additiveChoreCost_nonneg cost
      (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) i (allocation j)

/--
The integer step behind the source's easy no-deficiency quota cases.  Here
`vertexCount` is the size of a vertex subset and `longCount` counts its long
vertices.  The exceptional remainder-two/tight-pair configuration is the only
case not covered by this inequality.
-/
theorem m2HallArithmeticOfNoDeficiency
    (itemCount quotient remainder incidence vertexCount longCount : ℕ)
    (hdecompose : itemCount = 4 * quotient + remainder)
    (hremainder : remainder < 4) (hremainderTwo : remainder ≠ 2)
    (hvertexBound : vertexCount ≤ 4)
    (hdeficiency : vertexCount * itemCount ≤ 4 * incidence)
    (hlongVertex : longCount ≤ vertexCount) (hlongRemainder : longCount ≤ remainder) :
    vertexCount * quotient + longCount ≤ incidence := by
  interval_cases vertexCount <;> interval_cases remainder <;> omega

/-- The remaining remainder-two branch is automatic when a vertex set contains
at most one selected long vertex. -/
theorem m2HallArithmeticRemainderTwo
    (itemCount quotient incidence vertexCount longCount : ℕ)
    (hdecompose : itemCount = 4 * quotient + 2)
    (hvertexBound : vertexCount ≤ 4)
    (hdeficiency : vertexCount * itemCount ≤ 4 * incidence)
    (hlongVertex : longCount ≤ vertexCount) (hlongOne : longCount ≤ 1) :
    vertexCount * quotient + longCount ≤ incidence := by
  interval_cases vertexCount <;> omega

/-- Among the six pairs of four agents, at most two forbidden pairs leave an
available pair. This is the final combinatorial choice needed in the
remainder-two no-deficiency case. -/
theorem existsPairAvoidingAtMostTwo
    (forbidden : Finset (Finset (Fin 4))) (hforbidden : forbidden.card ≤ 2) :
    ∃ pair : Finset (Fin 4), pair.card = 2 ∧ pair ∉ forbidden := by
  let pair01 : Finset (Fin 4) := {0, 1}
  let pair02 : Finset (Fin 4) := {0, 2}
  let pair03 : Finset (Fin 4) := {0, 3}
  have hcard01 : pair01.card = 2 := by decide
  have hcard02 : pair02.card = 2 := by decide
  have hcard03 : pair03.card = 2 := by decide
  by_contra hchoice
  push Not at hchoice
  have hmem01 : pair01 ∈ forbidden := hchoice pair01 hcard01
  have hmem02 : pair02 ∈ forbidden := hchoice pair02 hcard02
  have hmem03 : pair03 ∈ forbidden := hchoice pair03 hcard03
  have hsubset : ({pair01, pair02, pair03} : Finset (Finset (Fin 4))) ⊆ forbidden := by
    intro pair hpair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
    rcases hpair with hpair | hpair | hpair
    · simpa [hpair] using hmem01
    · simpa [hpair] using hmem02
    · simpa [hpair] using hmem03
  have hthree : ({pair01, pair02, pair03} : Finset (Finset (Fin 4))).card = 3 := by
    decide
  have hle := Finset.card_le_card hsubset
  omega

/-- If every member of a family claims a disjoint block of `2q + 1` chores
from a pool of `4q + 2`, the family has at most two members. -/
theorem atMostTwoOfDisjointM2Fibres
    {Index Item : Type} [DecidableEq Item] (forbidden : Finset Index)
    (fibres : Index → Finset Item) (chores : Finset Item) (q : ℕ)
    (hdisjoint : (forbidden : Set Index).PairwiseDisjoint fibres)
    (hsubset : ∀ index ∈ forbidden, fibres index ⊆ chores)
    (hsize : ∀ index ∈ forbidden, (fibres index).card = 2 * q + 1)
    (hchores : chores.card = 4 * q + 2) :
    forbidden.card ≤ 2 := by
  have hunionSubset : forbidden.biUnion fibres ⊆ chores := by
    intro item hitem
    obtain ⟨index, hindex, hitemIndex⟩ := Finset.mem_biUnion.mp hitem
    exact hsubset index hindex hitemIndex
  have hbiunionCard : (forbidden.biUnion fibres).card =
      forbidden.card * (2 * q + 1) := by
    rw [Finset.card_biUnion hdisjoint]
    calc
      ∑ index ∈ forbidden, (fibres index).card =
          ∑ _index ∈ forbidden, (2 * q + 1) := Finset.sum_congr rfl hsize
      _ = forbidden.card * (2 * q + 1) := Finset.sum_const (2 * q + 1)
  have hupper : forbidden.card * (2 * q + 1) ≤ 4 * q + 2 := by
    rw [← hbiunionCard, ← hchores]
    exact Finset.card_le_card hunionSubset
  by_contra hnot
  have hthree : 3 ≤ forbidden.card := by omega
  have hthreeMul : 3 * (2 * q + 1) ≤ forbidden.card * (2 * q + 1) :=
    Nat.mul_le_mul_right (2 * q + 1) hthree
  omega

/-- The number of M2 chores incident to an agent set: those that are small for
at least one of its agents. -/
noncomputable def m2Incidence {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) (agents : Finset (Fin 4)) : ℕ :=
  (chores.filter fun item => (smallAgentSet cost item ∩ agents).Nonempty).card

/-- Four times the source deficiency, expressed integrally so maximizers can
be selected without introducing rational arithmetic. -/
noncomputable def m2ScaledDeficiency {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) (agents : Finset (Fin 4)) : ℤ :=
  (agents.card : ℤ) * chores.card - 4 * m2Incidence cost chores agents

theorem m2ScaledDeficiency_pos_iff
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (agents : Finset (Fin 4)) :
    0 < m2ScaledDeficiency cost chores agents ↔
      4 * m2Incidence cost chores agents < agents.card * chores.card := by
  unfold m2ScaledDeficiency
  omega

/-- A maximum-deficiency set exists because there are only sixteen subsets of
the four-agent set. This is the source's tie-unbroken maximizer; later case
constructions additionally use the source's smallest-cardinality tie break. -/
theorem exists_m2ScaledDeficiency_maximizer
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) : ∃ maximum : Finset (Fin 4),
      ∀ agents, m2ScaledDeficiency cost chores agents ≤ m2ScaledDeficiency cost chores maximum := by
  obtain ⟨maximum, _, hmaximum⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Finset (Fin 4))) (m2ScaledDeficiency cost chores)
      Finset.univ_nonempty
  exact ⟨maximum, fun agents => hmaximum agents (Finset.mem_univ _)⟩

/-- The source chooses, among maximum-deficiency sets, one with the smallest
cardinality. This finite selection realizes that tie break exactly. -/
theorem exists_m2ScaledDeficiency_maximizer_min_card
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) : ∃ maximum : Finset (Fin 4),
      (∀ agents, m2ScaledDeficiency cost chores agents ≤
        m2ScaledDeficiency cost chores maximum) ∧
      ∀ agents, m2ScaledDeficiency cost chores agents =
          m2ScaledDeficiency cost chores maximum → maximum.card ≤ agents.card := by
  obtain ⟨greatest, _, hgreatest⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Finset (Fin 4))) (m2ScaledDeficiency cost chores)
      Finset.univ_nonempty
  let maximizers := (Finset.univ : Finset (Finset (Fin 4))).filter fun agents =>
    m2ScaledDeficiency cost chores agents = m2ScaledDeficiency cost chores greatest
  have hgreatestMem : greatest ∈ maximizers := by simp [maximizers]
  obtain ⟨maximum, hmaximumMem, hsmallest⟩ :=
    Finset.exists_min_image maximizers Finset.card ⟨greatest, hgreatestMem⟩
  refine ⟨maximum, ?_, ?_⟩
  · intro agents
    have hmaximumEq : m2ScaledDeficiency cost chores maximum =
        m2ScaledDeficiency cost chores greatest := by
      simpa [maximizers] using hmaximumMem
    rw [hmaximumEq]
    exact hgreatest agents (Finset.mem_univ _)
  · intro agents hEq
    apply hsmallest agents
    simp [maximizers]
    have hmaximumEq : m2ScaledDeficiency cost chores maximum =
        m2ScaledDeficiency cost chores greatest := by
      simpa [maximizers] using hmaximumMem
    exact hEq.trans hmaximumEq

/-- A tight pair is precisely the exceptional pair from the source's
remainder-two Case 1 argument. -/
noncomputable def m2TightPairs {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) (q : ℕ) : Finset (Finset (Fin 4)) :=
  (Finset.univ : Finset (Finset (Fin 4))).filter fun agents =>
    agents.card = 2 ∧ m2Incidence cost chores agents = 2 * q + 1

/-- The chores of the complementary small-agent type of an agent pair. -/
noncomputable def m2ComplementaryFibre {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) (agents : Finset (Fin 4)) :
    Finset Item :=
  chores.filter fun item => smallAgentSet cost item = agentsᶜ

private theorem not_m2Incident_iff_smallSet_eq_compl
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item) (item : Item)
    (agents : Finset (Fin 4)) (hsmall : (smallAgentSet cost item).card = 2)
    (hagents : agents.card = 2) :
    ¬ (smallAgentSet cost item ∩ agents).Nonempty ↔ smallAgentSet cost item = agentsᶜ := by
  constructor
  · intro hdisjoint
    apply Finset.eq_of_subset_of_card_le
    · intro agent hagent
      rw [Finset.mem_compl]
      intro hagentSet
      exact hdisjoint ⟨agent, by
        simp only [Finset.mem_inter]
        exact ⟨hagent, hagentSet⟩⟩
    · rw [Finset.card_compl, hagents, hsmall]
      norm_num
  · intro heq hnonempty
    obtain ⟨agent, hinter⟩ := hnonempty
    simp only [Finset.mem_inter] at hinter
    have hsmallAgent : agent ∈ agentsᶜ := by simpa [← heq] using hinter.1
    rw [Finset.mem_compl] at hsmallAgent
    exact hsmallAgent hinter.2

private theorem m2SmallSet_meets_of_agentCard_at_least_three
    (small agents : Finset (Fin 4)) (hsmall : small.card = 2)
    (hagents : 3 ≤ agents.card) : (small ∩ agents).Nonempty := by
  by_contra hdisjoint
  have hsubset : small ⊆ agentsᶜ := by
    intro agent hagent
    rw [Finset.mem_compl]
    intro hagentSet
    exact hdisjoint ⟨agent, by
      simp only [Finset.mem_inter]
      exact ⟨hagent, hagentSet⟩⟩
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_compl, hsmall] at hcard
  norm_num at hcard
  omega

/-- Any three or four agents are incident to every M2 edge.  Thus their source
incidence number is the full chore count, which rules them out as positively
deficient sets. -/
theorem m2Incidence_eq_card_of_agentCard_at_least_three
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (agents : Finset (Fin 4))
    (hsmall : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hagents : 3 ≤ agents.card) : m2Incidence cost chores agents = chores.card := by
  unfold m2Incidence
  congr 1
  apply Finset.filter_eq_self.mpr
  intro item hitem
  exact m2SmallSet_meets_of_agentCard_at_least_three (smallAgentSet cost item) agents
    (hsmall item hitem) hagents

/-- In an M2 instance, a positively deficient agent set has at most two
agents. This is the source reduction that leaves only singleton and pair
maximal-deficiency cases after Case 1. -/
theorem m2PositiveDeficiency_agentCard_le_two
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (agents : Finset (Fin 4))
    (hsmall : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hpositive : 4 * m2Incidence cost chores agents < agents.card * chores.card) :
    agents.card ≤ 2 := by
  by_contra hnot
  have hagents : 3 ≤ agents.card := by omega
  have hincidence := m2Incidence_eq_card_of_agentCard_at_least_three cost chores agents
    hsmall hagents
  have hupper : agents.card ≤ 4 := by simpa using Finset.card_le_univ agents
  rw [hincidence] at hpositive
  interval_cases agents.card <;> omega

/-- The first case split of the source M2 proof.  If the no-deficiency Hall
inequalities fail, a deficient witness may be chosen among singleton or pair
agent sets; the later source branches add maximality to this witness. -/
theorem m2NoDeficiency_or_existsSmallDeficient
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item)
    (hsmall : ∀ item ∈ chores, IsSmallForExactlyTwo cost item) :
    (∀ agents : Finset (Fin 4),
      agents.card * chores.card ≤ 4 * m2Incidence cost chores agents) ∨
      ∃ agents : Finset (Fin 4), agents.card ≤ 2 ∧
        4 * m2Incidence cost chores agents < agents.card * chores.card := by
  by_cases hnoDeficiency : ∀ agents : Finset (Fin 4),
      agents.card * chores.card ≤ 4 * m2Incidence cost chores agents
  · exact Or.inl hnoDeficiency
  · right
    push Not at hnoDeficiency
    obtain ⟨agents, hpositive⟩ := hnoDeficiency
    exact ⟨agents, m2PositiveDeficiency_agentCard_le_two cost chores agents hsmall hpositive,
      hpositive⟩

/-- A positive source maximum-deficiency set selected with the stated tie break
is necessarily a singleton or a pair. -/
theorem m2PositiveMaximizer_card_one_or_two
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (maximum : Finset (Fin 4))
    (hpositive : 0 < m2ScaledDeficiency cost chores maximum)
    (hsmall : ∀ item ∈ chores, IsSmallForExactlyTwo cost item) :
    maximum.card = 1 ∨ maximum.card = 2 := by
  have hincidencePositive : 4 * m2Incidence cost chores maximum < maximum.card * chores.card :=
    m2ScaledDeficiency_pos_iff cost chores maximum |>.mp hpositive
  have hcardUpper := m2PositiveDeficiency_agentCard_le_two cost chores maximum hsmall
    hincidencePositive
  have hcardPos : 0 < maximum.card := by
    by_contra hzero
    have hzeroCard : maximum.card = 0 := by omega
    have hempty : maximum = ∅ := Finset.card_eq_zero.mp hzeroCard
    subst maximum
    simp [m2ScaledDeficiency, m2Incidence] at hpositive
  omega

/-- M2 incidence is monotone under enlarging the agent set. -/
theorem m2Incidence_mono
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) {smaller larger : Finset (Fin 4)}
    (hsubset : smaller ⊆ larger) :
    m2Incidence cost chores smaller ≤ m2Incidence cost chores larger := by
  unfold m2Incidence
  apply Finset.card_le_card
  intro item hitem
  have hitem' : item ∈ chores ∧ (smallAgentSet cost item ∩ smaller).Nonempty := by
    simpa using hitem
  refine (Finset.mem_filter.mpr ⟨hitem'.1, ?_⟩)
  obtain ⟨agent, hagent⟩ := hitem'.2
  refine ⟨agent, ?_⟩
  simp only [Finset.mem_inter] at hagent ⊢
  exact ⟨hagent.1, hsubset hagent.2⟩

/-- The triangle of chores not incident to the distinguished singleton agent
in source Case 2. -/
noncomputable def m2SingletonTriangle {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) (special : Fin 4) : Finset Item :=
  chores.filter fun item => special ∉ smallAgentSet cost item

private theorem m2Incidence_singleton_eq_card_filter
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (special : Fin 4) :
    m2Incidence cost chores {special} =
      (chores.filter fun item => special ∈ smallAgentSet cost item).card := by
  unfold m2Incidence
  congr 1
  ext item
  simp only [Finset.mem_filter]
  constructor
  · intro h
    obtain ⟨agent, hinter⟩ := h.2
    rcases Finset.mem_inter.mp hinter with ⟨hsmall, hsingle⟩
    have hagent : agent = special := Finset.mem_singleton.mp hsingle
    exact ⟨h.1, by simpa [hagent] using hsmall⟩
  · intro h
    exact ⟨h.1, ⟨special, Finset.mem_inter.mpr ⟨h.2, by simp⟩⟩⟩

/-- The source triangle contains all chores except the `d₁` chores incident to
the distinguished singleton. -/
theorem m2SingletonTriangle_card
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (special : Fin 4) :
    (m2SingletonTriangle cost chores special).card =
      chores.card - m2Incidence cost chores {special} := by
  have hsplit := chores.card_filter_add_card_filter_not
    (fun item => special ∈ smallAgentSet cost item)
  rw [m2Incidence_singleton_eq_card_filter]
  unfold m2SingletonTriangle
  omega

/-- In Case 2, the degree of an agent in the triangle is exactly the increase
in source incidence caused by adjoining that agent to the singleton. -/
theorem m2SingletonTriangle_degree_eq_incidenceIncrement
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (special agent : Fin 4) :
    m2Incidence cost chores (insert agent {special}) =
      m2Incidence cost chores {special} +
        ((m2SingletonTriangle cost chores special).filter fun item =>
          agent ∈ smallAgentSet cost item).card := by
  let incidentSpecial := chores.filter fun item => special ∈ smallAgentSet cost item
  let incidentTriangle := (m2SingletonTriangle cost chores special).filter fun item =>
    agent ∈ smallAgentSet cost item
  have hdisjoint : Disjoint incidentSpecial incidentTriangle := by
    rw [Finset.disjoint_left]
    intro item hspecial htriangle
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp htriangle).1).2
      (Finset.mem_filter.mp hspecial).2
  have hunion : incidentSpecial ∪ incidentTriangle =
      chores.filter fun item => (smallAgentSet cost item ∩ insert agent {special}).Nonempty := by
    ext item
    constructor
    · intro hitem
      rcases Finset.mem_union.mp hitem with hspecial | htriangle
      · rcases Finset.mem_filter.mp hspecial with ⟨hchore, hsmall⟩
        exact Finset.mem_filter.mpr ⟨hchore,
          ⟨special, Finset.mem_inter.mpr ⟨hsmall, by simp⟩⟩⟩
      · rcases Finset.mem_filter.mp htriangle with ⟨htriangle, hagent⟩
        rcases Finset.mem_filter.mp htriangle with ⟨hchore, hnotSpecial⟩
        exact Finset.mem_filter.mpr ⟨hchore,
          ⟨agent, Finset.mem_inter.mpr ⟨hagent, by simp⟩⟩⟩
    · intro hitem
      rcases Finset.mem_filter.mp hitem with ⟨hchore, hpair⟩
      obtain ⟨vertex, hvertex⟩ := hpair
      rcases Finset.mem_inter.mp hvertex with ⟨hvertex, hvertexPair⟩
      rw [Finset.mem_insert] at hvertexPair
      rcases hvertexPair with hvertexEq | hvertexEq
      · subst vertex
        by_cases hspecial : special ∈ smallAgentSet cost item
        · exact Finset.mem_union_left incidentTriangle
            (Finset.mem_filter.mpr ⟨hchore, hspecial⟩)
        · exact Finset.mem_union_right incidentSpecial
            (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hchore, hspecial⟩, hvertex⟩)
      · have hvertexEq' : vertex = special := Finset.mem_singleton.mp hvertexEq
        subst vertex
        exact Finset.mem_union_left incidentTriangle
          (Finset.mem_filter.mpr ⟨hchore, hvertex⟩)
  have hcard := Finset.card_union_of_disjoint hdisjoint
  rw [hunion] at hcard
  have hincSpecial : m2Incidence cost chores {special} = incidentSpecial.card := by
    unfold m2Incidence
    congr 1
    ext item
    simp only [Finset.mem_filter]
    constructor
    · intro h
      obtain ⟨vertex, hinter⟩ := h.2
      rcases Finset.mem_inter.mp hinter with ⟨hvertex, hsingle⟩
      have hvertexEq : vertex = special := Finset.mem_singleton.mp hsingle
      exact Finset.mem_filter.mpr ⟨h.1,
        by simpa [incidentSpecial, hvertexEq] using hvertex⟩
    · intro h
      rcases Finset.mem_filter.mp h with ⟨hchore, hsmall⟩
      exact ⟨hchore, ⟨special, Finset.mem_inter.mpr ⟨hsmall, by simp⟩⟩⟩
  change (chores.filter fun item => (smallAgentSet cost item ∩ insert agent {special}).Nonempty).card =
    m2Incidence cost chores {special} + incidentTriangle.card
  rw [hincSpecial]
  exact hcard

/-- The cross fiber from `present` to `absent`: chores that are small for the
former member of a pair but not the latter.  In source Case 3 these are the
aggregated `b` and `c` quantities. -/
noncomputable def m2PairCrossFibre {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item)
    (present absent : Fin 4) : Finset Item :=
  chores.filter fun item => present ∈ smallAgentSet cost item ∧ absent ∉ smallAgentSet cost item

/-- The common-small fiber of a named pair.  With pair `{1,2}` in the paper,
this is the source's type-`12` fiber. -/
noncomputable def m2PairCoreFibre {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item)
    (first second : Fin 4) : Finset Item :=
  chores.filter fun item => first ∈ smallAgentSet cost item ∧ second ∈ smallAgentSet cost item

/-- The fiber small for neither member of a named pair.  Under the M2
two-small-agent hypothesis this is the complementary type, `34` for the
paper's pair `{1,2}`. -/
noncomputable def m2PairOutsideFibre {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item)
    (first second : Fin 4) : Finset Item :=
  chores.filter fun item => first ∉ smallAgentSet cost item ∧ second ∉ smallAgentSet cost item

/-- The common-small fiber depends only on the underlying unordered pair. -/
theorem m2PairCoreFibre_swap {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) (first second : Fin 4) :
    m2PairCoreFibre cost chores second first = m2PairCoreFibre cost chores first second := by
  ext item
  simp [m2PairCoreFibre, and_comm]

/-- The outside fiber depends only on the underlying unordered pair. -/
theorem m2PairOutsideFibre_swap {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) (first second : Fin 4) :
    m2PairOutsideFibre cost chores second first = m2PairOutsideFibre cost chores first second := by
  ext item
  simp [m2PairOutsideFibre, and_comm]

/-- Any ordered pair of distinct four-agent labels can be moved to the source
labels `0,1`.  The explicit finite equivalence is used to transport the
labelled Case 3 constructions without treating their labels as substantive. -/
private theorem existsFin4Equiv_map_zero_one (first second : Fin 4)
    (hdistinct : first ≠ second) :
    ∃ labels : Fin 4 ≃ Fin 4, labels 0 = first ∧ labels 1 = second := by
  fin_cases first <;> fin_cases second <;> simp_all
  · exact ⟨Equiv.refl _, by decide, by decide⟩
  · exact ⟨Equiv.swap 1 2, by decide, by decide⟩
  · exact ⟨Equiv.swap 1 3, by decide, by decide⟩
  · exact ⟨Equiv.swap 0 1, by decide, by decide⟩
  · exact ⟨(Equiv.swap 0 1).trans (Equiv.swap 0 2), by decide, by decide⟩
  · exact ⟨(Equiv.swap 0 1).trans (Equiv.swap 0 3), by decide, by decide⟩
  · exact ⟨(Equiv.swap 0 2).trans (Equiv.swap 0 1), by decide, by decide⟩
  · exact ⟨Equiv.swap 0 2, by decide, by decide⟩
  · exact ⟨(Equiv.swap 0 2).trans (Equiv.swap 1 3), by decide, by decide⟩
  · exact ⟨(Equiv.swap 0 3).trans (Equiv.swap 0 1), by decide, by decide⟩
  · exact ⟨Equiv.swap 0 3, by decide, by decide⟩
  · exact ⟨(Equiv.swap 0 3).trans (Equiv.swap 1 2), by decide, by decide⟩

/-- The pair fibers of a relabelled instance are the original pair fibers
whose two labels have been moved to `0,1`. -/
private theorem m2PairCoreFibre_relabel_zero_one
    {Item : Type} [DecidableEq Item] (labels : Fin 4 ≃ Fin 4)
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) (first second : Fin 4)
    (hzero : labels 0 = first) (hone : labels 1 = second) :
    m2PairCoreFibre (relabelChoreCost labels cost) chores 0 1 =
      m2PairCoreFibre cost chores first second := by
  ext item
  simp [m2PairCoreFibre, smallAgentSet, relabelChoreCost, IsSmallChore, hzero, hone]

private theorem m2PairCrossFibre_relabel_zero_one
    {Item : Type} [DecidableEq Item] (labels : Fin 4 ≃ Fin 4)
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) (first second : Fin 4)
    (hzero : labels 0 = first) (hone : labels 1 = second) :
    m2PairCrossFibre (relabelChoreCost labels cost) chores 0 1 =
      m2PairCrossFibre cost chores first second ∧
    m2PairCrossFibre (relabelChoreCost labels cost) chores 1 0 =
      m2PairCrossFibre cost chores second first := by
  constructor <;> ext item <;>
    simp [m2PairCrossFibre, smallAgentSet, relabelChoreCost, IsSmallChore, hzero, hone]

private theorem m2PairOutsideFibre_relabel_zero_one
    {Item : Type} [DecidableEq Item] (labels : Fin 4 ≃ Fin 4)
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) (first second : Fin 4)
    (hzero : labels 0 = first) (hone : labels 1 = second) :
    m2PairOutsideFibre (relabelChoreCost labels cost) chores 0 1 =
      m2PairOutsideFibre cost chores first second := by
  ext item
  simp [m2PairOutsideFibre, smallAgentSet, relabelChoreCost, IsSmallChore, hzero, hone]

/-- The four fibers associated with two distinct named agents partition the
finite chore pool.  This is only a Boolean classification of membership; the
M2 exact-two hypothesis is used later for the cost labels of each fiber. -/
theorem m2PairFibres_union_eq
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4) :
    m2PairCoreFibre cost chores first second ∪
        m2PairCrossFibre cost chores first second ∪
        m2PairCrossFibre cost chores second first ∪
        m2PairOutsideFibre cost chores first second = chores := by
  ext item
  by_cases hitem : item ∈ chores
  · by_cases hfirst : first ∈ smallAgentSet cost item <;>
      by_cases hsecond : second ∈ smallAgentSet cost item <;>
      simp [m2PairCoreFibre, m2PairCrossFibre, m2PairOutsideFibre,
        hitem, hfirst, hsecond]
  · simp [m2PairCoreFibre, m2PairCrossFibre, m2PairOutsideFibre, hitem]

/-- Different Boolean membership patterns for a named pair give disjoint
fibers.  The three displayed disjointness statements are the exact unions
needed to assemble the Case 3 allocation in stages. -/
theorem m2PairCore_disjoint_crosses_outside
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4) :
    Disjoint (m2PairCoreFibre cost chores first second)
        (m2PairCrossFibre cost chores first second ∪
          m2PairCrossFibre cost chores second first ∪
          m2PairOutsideFibre cost chores first second) := by
  rw [Finset.disjoint_left]
  intro item hcore hother
  rcases Finset.mem_filter.mp hcore with ⟨_, hfirst, hsecond⟩
  rcases Finset.mem_union.mp hother with hcrosses | houtside
  · rcases Finset.mem_union.mp hcrosses with hcross | hcross
    · rcases Finset.mem_filter.mp hcross with ⟨_, _, habsent⟩
      exact (habsent hsecond).elim
    · rcases Finset.mem_filter.mp hcross with ⟨_, hpresent, habsent⟩
      exact (habsent hfirst).elim
  · rcases Finset.mem_filter.mp houtside with ⟨_, hnotFirst, _⟩
    exact (hnotFirst hfirst).elim

theorem m2PairCrossFirst_disjoint_crossSecond_outside
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4) :
    Disjoint (m2PairCrossFibre cost chores first second)
        (m2PairCrossFibre cost chores second first ∪
          m2PairOutsideFibre cost chores first second) := by
  rw [Finset.disjoint_left]
  intro item hfirst hother
  rcases Finset.mem_filter.mp hfirst with ⟨_, hsmallFirst, hnotSecond⟩
  rcases Finset.mem_union.mp hother with hcross | houtside
  · rcases Finset.mem_filter.mp hcross with ⟨_, _, hnotFirst⟩
    exact (hnotFirst hsmallFirst).elim
  · rcases Finset.mem_filter.mp houtside with ⟨_, hnotFirst, _⟩
    exact (hnotFirst hsmallFirst).elim

theorem m2PairCrossSecond_disjoint_outside
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4) :
    Disjoint (m2PairCrossFibre cost chores second first)
        (m2PairOutsideFibre cost chores first second) := by
  rw [Finset.disjoint_left]
  intro item hcross houtside
  have hsmallSecond := (Finset.mem_filter.mp hcross).2.1
  have hnotSecond := (Finset.mem_filter.mp houtside).2.2
  exact (hnotSecond hsmallSecond).elim

/-- The cardinalities of the four labelled pair fibers add to the full chore
count.  This is the counting bridge from the source's `a,b,c,f` notation to
the actual finite sets. -/
theorem m2PairFibres_card_sum
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4) :
    (m2PairCoreFibre cost chores first second).card +
        (m2PairCrossFibre cost chores first second).card +
        (m2PairCrossFibre cost chores second first).card +
        (m2PairOutsideFibre cost chores first second).card = chores.card := by
  have hcoreDisjoint : Disjoint (m2PairCoreFibre cost chores first second)
      (m2PairCrossFibre cost chores first second ∪
        (m2PairCrossFibre cost chores second first ∪
          m2PairOutsideFibre cost chores first second)) := by
    simpa only [Finset.union_assoc] using
      m2PairCore_disjoint_crosses_outside cost chores first second
  calc
    (m2PairCoreFibre cost chores first second).card +
          (m2PairCrossFibre cost chores first second).card +
          (m2PairCrossFibre cost chores second first).card +
          (m2PairOutsideFibre cost chores first second).card =
        (m2PairCoreFibre cost chores first second).card +
          ((m2PairCrossFibre cost chores first second ∪
            (m2PairCrossFibre cost chores second first ∪
              m2PairOutsideFibre cost chores first second))).card := by
      rw [Finset.card_union_of_disjoint
        (m2PairCrossFirst_disjoint_crossSecond_outside cost chores first second),
        Finset.card_union_of_disjoint
          (m2PairCrossSecond_disjoint_outside cost chores first second)]
      omega
    _ = (m2PairCoreFibre cost chores first second ∪
          (m2PairCrossFibre cost chores first second ∪
            (m2PairCrossFibre cost chores second first ∪
              m2PairOutsideFibre cost chores first second))).card := by
      rw [Finset.card_union_of_disjoint hcoreDisjoint]
    _ = chores.card := by
      simpa only [Finset.union_assoc] using congrArg Finset.card
        (m2PairFibres_union_eq cost chores first second)

/-- For a named pair, M2 incidence is precisely the total size of the three
fibers that are small for at least one member.  Together with the four-fiber
partition, this identifies the source deficiency inequality with the strict
dominance of the outside fiber. -/
theorem m2Pair_incidence_eq_nonOutside_card
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4) :
    m2Incidence cost chores {first, second} =
      (m2PairCoreFibre cost chores first second).card +
        (m2PairCrossFibre cost chores first second).card +
        (m2PairCrossFibre cost chores second first).card := by
  have hcoreDisjoint : Disjoint (m2PairCoreFibre cost chores first second)
      (m2PairCrossFibre cost chores first second ∪
        m2PairCrossFibre cost chores second first) := by
    rw [Finset.disjoint_left]
    intro item hcore hcrosses
    rcases Finset.mem_filter.mp hcore with ⟨_, hfirst, hsecond⟩
    rcases Finset.mem_union.mp hcrosses with hcross | hcross
    · exact (Finset.mem_filter.mp hcross).2.2 hsecond
    · exact (Finset.mem_filter.mp hcross).2.2 hfirst
  have hcrossDisjoint : Disjoint (m2PairCrossFibre cost chores first second)
      (m2PairCrossFibre cost chores second first) := by
    rw [Finset.disjoint_left]
    intro item hfirst hsecond
    exact (Finset.mem_filter.mp hsecond).2.2 (Finset.mem_filter.mp hfirst).2.1
  have hincident :
      (chores.filter fun item => (smallAgentSet cost item ∩ {first, second}).Nonempty) =
        m2PairCoreFibre cost chores first second ∪
          (m2PairCrossFibre cost chores first second ∪
            m2PairCrossFibre cost chores second first) := by
    ext item
    by_cases hfirst : first ∈ smallAgentSet cost item <;>
      by_cases hsecond : second ∈ smallAgentSet cost item <;>
      simp [m2PairCoreFibre, m2PairCrossFibre, hfirst, hsecond]
  unfold m2Incidence
  rw [hincident, Finset.card_union_of_disjoint hcoreDisjoint,
    Finset.card_union_of_disjoint hcrossDisjoint]
  omega

/-- A positive deficient pair has a strictly larger complementary fiber than
the combined core and cross fibers.  This is the source inequality
`f > a + b + c` used to enter every Case 3 subcase. -/
theorem m2PairPositive_outside_gt_nonOutside
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4)
    (hpositive : 4 * m2Incidence cost chores {first, second} < 2 * chores.card) :
    (m2PairCoreFibre cost chores first second).card +
        (m2PairCrossFibre cost chores first second).card +
        (m2PairCrossFibre cost chores second first).card <
      (m2PairOutsideFibre cost chores first second).card := by
  rw [m2Pair_incidence_eq_nonOutside_card] at hpositive
  have hsum := m2PairFibres_card_sum cost chores first second
  omega

private theorem isSmallChore_of_mem_smallAgentSet
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (agent : Fin 4) (item : Item) (hsmall : agent ∈ smallAgentSet cost item) :
    IsSmallChore cost agent item := by
  simpa [smallAgentSet, IsSmallChore] using hsmall

private theorem isLargeChore_of_not_mem_smallAgentSet
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (hcost : IsOneOrRChoreCost cost r) (agent : Fin 4) (item : Item)
    (hnotSmall : agent ∉ smallAgentSet cost item) :
    IsLargeChore cost r agent item := by
  rcases hcost agent item with hsmall | hlarge
  · apply (hnotSmall ?_).elim
    simp [smallAgentSet, IsSmallChore, hsmall]
  · exact hlarge

private theorem m2PairOutsideFibre_small_for_two
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (item : Item)
    (htwo : IsSmallForExactlyTwo cost item)
    (houtside : item ∈ m2PairOutsideFibre cost chores 0 1) :
    IsSmallChore cost 2 item := by
  have hnotZero : (0 : Fin 4) ∉ smallAgentSet cost item :=
    (Finset.mem_filter.mp houtside).2.1
  have hnotOne : (1 : Fin 4) ∉ smallAgentSet cost item :=
    (Finset.mem_filter.mp houtside).2.2
  have hmemTwo : (2 : Fin 4) ∈ smallAgentSet cost item := by
    by_contra hnotTwo
    have hsubset : smallAgentSet cost item ⊆ ({3} : Finset (Fin 4)) := by
      intro agent hagent
      fin_cases agent
      · exact (hnotZero hagent).elim
      · exact (hnotOne hagent).elim
      · exact (hnotTwo hagent).elim
      · simp
    have hcard := Finset.card_le_card hsubset
    rw [show ({3} : Finset (Fin 4)).card = 1 by decide] at hcard
    change (smallAgentSet cost item).card = 2 at htwo
    omega
  exact isSmallChore_of_mem_smallAgentSet cost 2 item hmemTwo

private theorem m2PairOutsideFibre_small_for_three
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (item : Item)
    (htwo : IsSmallForExactlyTwo cost item)
    (houtside : item ∈ m2PairOutsideFibre cost chores 0 1) :
    IsSmallChore cost 3 item := by
  have hnotZero : (0 : Fin 4) ∉ smallAgentSet cost item :=
    (Finset.mem_filter.mp houtside).2.1
  have hnotOne : (1 : Fin 4) ∉ smallAgentSet cost item :=
    (Finset.mem_filter.mp houtside).2.2
  have hmemThree : (3 : Fin 4) ∈ smallAgentSet cost item := by
    by_contra hnotThree
    have hsubset : smallAgentSet cost item ⊆ ({2} : Finset (Fin 4)) := by
      intro agent hagent
      fin_cases agent
      · exact (hnotZero hagent).elim
      · exact (hnotOne hagent).elim
      · simp
      · exact (hnotThree hagent).elim
    have hcard := Finset.card_le_card hsubset
    rw [show ({2} : Finset (Fin 4)).card = 1 by decide] at hcard
    change (smallAgentSet cost item).card = 2 at htwo
    omega
  exact isSmallChore_of_mem_smallAgentSet cost 3 item hmemThree

/-- Under the M2 exact-two condition, a chore small for both agents `0,1` is
large for agent `2`.  This is the cost label of the unique core chore in
source Case 3.2.2. -/
private theorem m2PairCoreFibre_large_for_two
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (item : Item) (hcost : IsOneOrRChoreCost cost r)
    (htwo : IsSmallForExactlyTwo cost item)
    (hcore : item ∈ m2PairCoreFibre cost chores 0 1) :
    IsLargeChore cost r 2 item := by
  have hzero : (0 : Fin 4) ∈ smallAgentSet cost item :=
    (Finset.mem_filter.mp hcore).2.1
  have hone : (1 : Fin 4) ∈ smallAgentSet cost item :=
    (Finset.mem_filter.mp hcore).2.2
  have hnotTwo : (2 : Fin 4) ∉ smallAgentSet cost item := by
    intro hmemTwo
    have hsubset : ({0, 1, 2} : Finset (Fin 4)) ⊆ smallAgentSet cost item := by
      intro agent hagent
      simp only [Finset.mem_insert, Finset.mem_singleton] at hagent
      rcases hagent with rfl | rfl | rfl
      · exact hzero
      · exact hone
      · exact hmemTwo
    have hcard := Finset.card_le_card hsubset
    change (smallAgentSet cost item).card = 2 at htwo
    rw [show ({0, 1, 2} : Finset (Fin 4)).card = 3 by decide] at hcard
    omega
  exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 2 item hnotTwo

/-- The symmetric core-fiber cost label for agent `3`. -/
private theorem m2PairCoreFibre_large_for_three
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (item : Item) (hcost : IsOneOrRChoreCost cost r)
    (htwo : IsSmallForExactlyTwo cost item)
    (hcore : item ∈ m2PairCoreFibre cost chores 0 1) :
    IsLargeChore cost r 3 item := by
  have hzero : (0 : Fin 4) ∈ smallAgentSet cost item :=
    (Finset.mem_filter.mp hcore).2.1
  have hone : (1 : Fin 4) ∈ smallAgentSet cost item :=
    (Finset.mem_filter.mp hcore).2.2
  have hnotThree : (3 : Fin 4) ∉ smallAgentSet cost item := by
    intro hmemThree
    have hsubset : ({0, 1, 3} : Finset (Fin 4)) ⊆ smallAgentSet cost item := by
      intro agent hagent
      simp only [Finset.mem_insert, Finset.mem_singleton] at hagent
      rcases hagent with rfl | rfl | rfl
      · exact hzero
      · exact hone
      · exact hmemThree
    have hcard := Finset.card_le_card hsubset
    change (smallAgentSet cost item).card = 2 at htwo
    rw [show ({0, 1, 3} : Finset (Fin 4)).card = 3 by decide] at hcard
    omega
  exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 3 item hnotThree

/-- The Case 3.1 quotas for the common-small fiber: only the two members of
the deficient pair receive these chores. -/
def m2PairCoreQuota (first second : Fin 4) (firstCount secondCount : ℕ)
    (agent : Fin 4) : ℕ :=
  if agent = first then firstCount else if agent = second then secondCount else 0

/-- The Case 3.1 quotas for the complementary fiber.  After the two prescribed
shares for the deficient pair, the remaining chores are split as evenly as
possible between the complementary pair.  This labelled form is used before
the final relabelling transport. -/
def m2PairOutsideQuota (firstCount secondCount : ℕ) (outsideCard : ℕ)
    (agent : Fin 4) : ℕ :=
  if agent = 0 then firstCount else
    if agent = 1 then secondCount else
      if agent = 2 then (outsideCard - firstCount - secondCount) / 2 else
        outsideCard - firstCount - secondCount -
          (outsideCard - firstCount - secondCount) / 2

/-- The labelled allocation shape used in source Case 3.1.  The common-small
fiber is split between agents `0,1`; each cross fiber is assigned to the
agent for whom it is small; and the complementary fiber is shared according
to `m2PairOutsideQuota`.  Keeping this shape named lets the EFX verification
state its cardinal hypotheses separately from the source's arithmetic which
produces them. -/
noncomputable def m2PairSplitAllocation {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item)
    (coreAllocation outsideAllocation : Allocation (Fin 4) Item) :
    Allocation (Fin 4) Item :=
  fun agent => coreAllocation agent ∪
    (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
      ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
        outsideAllocation agent)

private theorem m2PairCoreQuota_sum (first second : Fin 4) (hdistinct : first ≠ second)
    (firstCount secondCount : ℕ) :
    Finset.univ.sum (m2PairCoreQuota first second firstCount secondCount) =
      firstCount + secondCount := by
  classical
  rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  fin_cases first <;> fin_cases second <;> simp_all [m2PairCoreQuota] <;> omega

private theorem m2PairOutsideQuota_sum (firstCount secondCount outsideCard : ℕ)
    (hshares : firstCount + secondCount ≤ outsideCard) :
    Finset.univ.sum (m2PairOutsideQuota firstCount secondCount outsideCard) = outsideCard := by
  rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  simp [m2PairOutsideQuota]
  omega

private theorem m2PairCrossFibre_eq_triangleDegree
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (present absent : Fin 4) :
    m2PairCrossFibre cost chores present absent =
      (m2SingletonTriangle cost chores absent).filter fun item =>
        present ∈ smallAgentSet cost item := by
  ext item
  simp [m2PairCrossFibre, m2SingletonTriangle, and_left_comm, and_comm]

/-- A cross-fiber cardinality is exactly the incidence increment from adding
its present endpoint to the singleton containing its absent endpoint. -/
theorem m2PairCrossFibre_card_eq_incidenceIncrement
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (present absent : Fin 4) :
    m2Incidence cost chores (insert present {absent}) =
      m2Incidence cost chores {absent} +
        (m2PairCrossFibre cost chores present absent).card := by
  rw [m2PairCrossFibre_eq_triangleDegree]
  exact m2SingletonTriangle_degree_eq_incidenceIncrement cost chores absent present

/-- The degree lower bound used in the singleton maximum-deficiency branch.
For a singleton maximum and any other agent, adding that agent increases the
incidence count by at least one quarter of the chore count. -/
theorem m2SingletonMax_incidenceIncrement_lower
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (singleton : Finset (Fin 4))
    (hmaximum : ∀ agents, m2ScaledDeficiency cost chores agents ≤
      m2ScaledDeficiency cost chores singleton)
    (hsingleton : singleton.card = 1) (other : Fin 4) (hother : other ∉ singleton) :
    chores.card ≤ 4 * (m2Incidence cost chores (insert other singleton) -
      m2Incidence cost chores singleton) := by
  have hpairCard : (insert other singleton).card = 2 := by
    rw [Finset.card_insert_of_notMem hother, hsingleton]
  have hincidenceMono : m2Incidence cost chores singleton ≤
      m2Incidence cost chores (insert other singleton) :=
    m2Incidence_mono cost chores (Finset.subset_insert other singleton)
  have hdeficiency := hmaximum (insert other singleton)
  unfold m2ScaledDeficiency at hdeficiency
  rw [hpairCard, hsingleton] at hdeficiency
  omega

/-- Source Case 2's degree inequality: maximal deficiency of `{special}`
forces every other triangle vertex to have degree at least one quarter of all
chores. -/
theorem m2SingletonMax_triangleDegree_lower
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (special other : Fin 4)
    (hmaximum : ∀ agents, m2ScaledDeficiency cost chores agents ≤
      m2ScaledDeficiency cost chores {special}) (hother : other ≠ special) :
    chores.card ≤ 4 *
      ((m2SingletonTriangle cost chores special).filter fun item =>
        other ∈ smallAgentSet cost item).card := by
  have hotherMem : other ∉ ({special} : Finset (Fin 4)) := by simpa using hother
  have hlower := m2SingletonMax_incidenceIncrement_lower cost chores {special}
    hmaximum (by simp) other hotherMem
  rw [m2SingletonTriangle_degree_eq_incidenceIncrement] at hlower
  simpa using hlower

/-- A deficient singleton has at most `⌊m / 4⌋` incident chores, matching the
first numerical bound in the source singleton branch. -/
theorem m2SingletonDeficient_incidence_le_quotient
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (singleton : Finset (Fin 4)) (quotient remainder : ℕ)
    (hdecompose : chores.card = 4 * quotient + remainder) (hremainder : remainder < 4)
    (hsingleton : singleton.card = 1)
    (hdeficient : 4 * m2Incidence cost chores singleton < singleton.card * chores.card) :
    m2Incidence cost chores singleton ≤ quotient := by
  rw [hsingleton, hdecompose] at hdeficient
  omega

/-- The cross-incidence upper bound from the pair maximum-deficiency branch.
For either member of a maximum pair, adding the other member contributes at
most one quarter of the full chore count. -/
theorem m2PairMax_incidenceIncrement_upper
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (pair : Finset (Fin 4))
    (hmaximum : ∀ agents, m2ScaledDeficiency cost chores agents ≤
      m2ScaledDeficiency cost chores pair)
    (hpair : pair.card = 2) (agent : Fin 4) (hagent : agent ∈ pair) :
    4 * (m2Incidence cost chores pair - m2Incidence cost chores {agent}) ≤ chores.card := by
  have hsingletonCard : ({agent} : Finset (Fin 4)).card = 1 := by simp
  have hincidenceMono : m2Incidence cost chores {agent} ≤ m2Incidence cost chores pair :=
    m2Incidence_mono cost chores (Finset.singleton_subset_iff.mpr hagent)
  have hdeficiency := hmaximum ({agent} : Finset (Fin 4))
  unfold m2ScaledDeficiency at hdeficiency
  rw [hpair, hsingletonCard] at hdeficiency
  omega

/-- The source bounds `b,c ≤ m/4` in Case 3, stated directly for either
cross fiber of an explicitly named maximum pair. -/
theorem m2PairMax_crossFibre_upper
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (pair : Finset (Fin 4)) (present absent : Fin 4)
    (hmaximum : ∀ agents, m2ScaledDeficiency cost chores agents ≤
      m2ScaledDeficiency cost chores pair)
    (hpairEq : pair = insert present {absent}) (hdistinct : present ≠ absent) :
    4 * (m2PairCrossFibre cost chores present absent).card ≤ chores.card := by
  have hpairCard : pair.card = 2 := by
    rw [hpairEq]
    simp [hdistinct]
  have habsent : absent ∈ pair := by
    rw [hpairEq]
    simp
  have hupper := m2PairMax_incidenceIncrement_upper cost chores pair hmaximum hpairCard
    absent habsent
  rw [hpairEq, m2PairCrossFibre_card_eq_incidenceIncrement] at hupper
  omega

private theorem m2Fibre_card_of_tight
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q : ℕ)
    (hsmall : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hchores : chores.card = 4 * q + 2) {agents : Finset (Fin 4)}
    (htight : agents ∈ m2TightPairs cost chores q) :
    (m2ComplementaryFibre cost chores agents).card = 2 * q + 1 := by
  have htight' : agents.card = 2 ∧ m2Incidence cost chores agents = 2 * q + 1 := by
    simpa [m2TightPairs] using htight
  have hdisjoint : Disjoint
      (chores.filter fun item => (smallAgentSet cost item ∩ agents).Nonempty)
      (m2ComplementaryFibre cost chores agents) := by
    rw [Finset.disjoint_left]
    intro item hincident hfibre
    have hfibre' : item ∈ chores ∧ smallAgentSet cost item = agentsᶜ := by
      simpa [m2ComplementaryFibre] using hfibre
    have hincident' : item ∈ chores ∧ (smallAgentSet cost item ∩ agents).Nonempty := by
      simpa using hincident
    have hsmallItem : (smallAgentSet cost item).card = 2 := by
      exact hsmall item hfibre'.1
    have hnotIncident : ¬ (smallAgentSet cost item ∩ agents).Nonempty := by
      apply (not_m2Incident_iff_smallSet_eq_compl cost item agents hsmallItem htight'.1).mpr
      exact hfibre'.2
    exact hnotIncident hincident'.2
  have hunion :
      (chores.filter fun item => (smallAgentSet cost item ∩ agents).Nonempty) ∪
        m2ComplementaryFibre cost chores agents = chores := by
    ext item
    by_cases hitem : item ∈ chores
    · have hsmallItem : (smallAgentSet cost item).card = 2 := hsmall item hitem
      have hnotIncident : ¬ (smallAgentSet cost item ∩ agents).Nonempty ↔
          smallAgentSet cost item = agentsᶜ :=
        not_m2Incident_iff_smallSet_eq_compl cost item agents hsmallItem htight'.1
      simp only [Finset.mem_union, Finset.mem_filter]
      simp only [m2ComplementaryFibre, Finset.mem_filter]
      simp only [hitem, true_and]
      apply iff_true_intro
      by_cases hincident : (smallAgentSet cost item ∩ agents).Nonempty
      · exact Or.inl hincident
      · exact Or.inr (hnotIncident.mp hincident)
    · simp [m2ComplementaryFibre, hitem]
  have hcardUnion := Finset.card_union_of_disjoint hdisjoint
  rw [hunion] at hcardUnion
  have hinc := htight'.2
  change (chores.filter fun item => (smallAgentSet cost item ∩ agents).Nonempty).card =
    2 * q + 1 at hinc
  omega

private theorem m2ComplementaryFibres_disjoint
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) {first second : Finset (Fin 4)} (hne : first ≠ second) :
    Disjoint (m2ComplementaryFibre cost chores first)
      (m2ComplementaryFibre cost chores second) := by
  rw [Finset.disjoint_left]
  intro item hfirst hsecond
  have hfirst' : item ∈ chores ∧ smallAgentSet cost item = firstᶜ := by
    simpa [m2ComplementaryFibre] using hfirst
  have hsecond' : item ∈ chores ∧ smallAgentSet cost item = secondᶜ := by
    simpa [m2ComplementaryFibre] using hsecond
  apply hne
  apply compl_injective
  exact hfirst'.2.symm.trans hsecond'.2

private theorem m2TightPairs_card_le_two
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q : ℕ)
    (hsmall : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hchores : chores.card = 4 * q + 2) :
    (m2TightPairs cost chores q).card ≤ 2 := by
  apply atMostTwoOfDisjointM2Fibres (m2TightPairs cost chores q)
    (m2ComplementaryFibre cost chores) chores q
  · intro first hfirst second hsecond hne
    exact m2ComplementaryFibres_disjoint cost chores hne
  · intro agents _ item hitem
    exact (by simpa [m2ComplementaryFibre] using hitem :
      item ∈ chores ∧ smallAgentSet cost item = agentsᶜ).1
  · intro agents hagents
    exact m2Fibre_card_of_tight cost chores q hsmall hchores hagents
  · exact hchores

/-- A balanced M2 quota vector: selected long agents receive `q + 1`, and all
other agents receive `q`. -/
def m2Quota (q : ℕ) (longAgents : Finset (Fin 4)) (agent : Fin 4) : ℕ :=
  q + if agent ∈ longAgents then 1 else 0

/-- The Case 2 target vector: the singleton agent has no triangle quota, and
the other three agents receive `q` or `q + 1` triangle chores. -/
def m2SingletonQuota (special : Fin 4) (q : ℕ) (longAgents : Finset (Fin 4))
    (agent : Fin 4) : ℕ :=
  if agent = special then 0 else q + if agent ∈ longAgents then 1 else 0

private theorem m2SingletonQuota_sum_other (special : Fin 4) (q : ℕ)
    (longAgents : Finset (Fin 4)) (hlong : longAgents ⊆ Finset.univ.erase special) :
    ∑ agent ∈ Finset.univ.erase special, m2SingletonQuota special q longAgents agent =
      3 * q + longAgents.card := by
  have hrewrite : ∀ agent ∈ Finset.univ.erase special,
      m2SingletonQuota special q longAgents agent = q + if agent ∈ longAgents then 1 else 0 := by
    intro agent hagent
    simp [m2SingletonQuota, (Finset.mem_erase.mp hagent).1]
  rw [show (∑ agent ∈ Finset.univ.erase special,
      m2SingletonQuota special q longAgents agent) =
    ∑ agent ∈ Finset.univ.erase special, (q + if agent ∈ longAgents then 1 else 0) by
      apply Finset.sum_congr rfl
      exact hrewrite]
  have hspecialLong : special ∉ longAgents := by
    intro hspecial
    exact (Finset.mem_erase.mp (hlong hspecial)).1 rfl
  simp [Finset.sum_add_distrib, Finset.card_erase_of_mem (Finset.mem_univ special), hspecialLong]

private theorem m2SingletonQuota_range (special : Fin 4) (q : ℕ)
    (longAgents : Finset (Fin 4)) : ∀ agent, agent ≠ special →
      q ≤ m2SingletonQuota special q longAgents agent ∧
        m2SingletonQuota special q longAgents agent ≤ q + 1 := by
  intro agent hagent
  simp [m2SingletonQuota, hagent]
  split <;> omega

private theorem exists_m2SingletonLongAgents (special : Fin 4) (remainder : ℕ)
    (hremainder : remainder < 4) :
    ∃ longAgents : Finset (Fin 4), longAgents ⊆ Finset.univ.erase special ∧
      longAgents.card = remainder := by
  obtain ⟨longAgents, hsubset, hcard⟩ :=
    (Finset.univ.erase special).exists_subset_card_eq (by
      rw [Finset.card_erase_of_mem (Finset.mem_univ special)]
      norm_num
      omega : remainder ≤ (Finset.univ.erase special).card)
  exact ⟨longAgents, hsubset, hcard⟩

/-- The balanced quota vector has total `4q + |longAgents|`.  Although it is
introduced in the M₂ orientation proof, this is also the generic finite
balanced-cardinality accounting used for homogeneous chore costs. -/
theorem m2Quota_sum (q : ℕ) (longAgents : Finset (Fin 4)) :
    Finset.univ.sum (m2Quota q longAgents) = 4 * q + longAgents.card := by
  simp [m2Quota, Finset.sum_add_distrib, Finset.sum_const, Nat.mul_comm]

/-- Any prescribed nonnegative integral quota vector whose sum is the finite
chore-pool size can be realized by a feasible allocation.  This is the
all-agents endpoint specialization of the paper's partial Hall orientation,
and is used when a source subcase only requires a balanced cardinal split. -/
theorem existsAllocationOfQuota
    (Agent Item : Type) [Fintype Agent] [DecidableEq Agent] [DecidableEq Item]
    (chores : Finset Item) (quota : Agent → ℕ)
    (hsum : Finset.univ.sum quota = chores.card) :
    ∃ allocation : Allocation Agent Item,
      IsAllocationOf allocation chores ∧ ∀ agent, (allocation agent).card = quota agent := by
  classical
  have hhall : ∀ vertices : Finset Agent, vertices.sum quota ≤
      (chores.filter fun _item => ((Finset.univ : Finset Agent) ∩ vertices).Nonempty).card := by
    intro vertices
    by_cases hvertices : vertices = ∅
    · simp [hvertices]
    · have hsumLe : vertices.sum quota ≤ (Finset.univ : Finset Agent).sum quota :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by omega)
      have hfilterAll :
          (chores.filter fun _item =>
            ((Finset.univ : Finset Agent) ∩ vertices).Nonempty) = chores := by
        apply Finset.filter_eq_self.mpr
        intro item _
        rw [Finset.univ_inter]
        exact Finset.nonempty_iff_ne_empty.mpr hvertices
      rw [hfilterAll]
      exact hsumLe.trans_eq hsum
  obtain ⟨owner, _, hcard⟩ :=
    partialBalancedOrientation Agent Item chores (fun _item => Finset.univ) quota hhall
  let fibres : Agent → Finset Item := fun agent => chores.filter fun item => owner item = some agent
  have hdisjoint : ((Finset.univ : Finset Agent) : Set Agent).PairwiseDisjoint fibres := by
    intro first hfirst second hsecond hne
    change Disjoint (fibres first) (fibres second)
    rw [Finset.disjoint_left]
    intro item hfirstItem hsecondItem
    have hfirstOwner : owner item = some first := (Finset.mem_filter.mp hfirstItem).2
    have hsecondOwner : owner item = some second := (Finset.mem_filter.mp hsecondItem).2
    exact hne (Option.some.inj (hfirstOwner.symm.trans hsecondOwner))
  have hunionSubset : (Finset.univ : Finset Agent).biUnion fibres ⊆ chores := by
    intro item hitem
    obtain ⟨agent, _, hagentItem⟩ := Finset.mem_biUnion.mp hitem
    exact (Finset.mem_filter.mp hagentItem).1
  have hcardUnion : ((Finset.univ : Finset Agent).biUnion fibres).card = chores.card := by
    rw [Finset.card_biUnion hdisjoint]
    calc
      ∑ agent ∈ Finset.univ, (fibres agent).card =
          ∑ agent ∈ Finset.univ, quota agent := by
        apply Finset.sum_congr rfl
        intro agent _
        exact hcard agent
      _ = chores.card := hsum
  have hunion : (Finset.univ : Finset Agent).biUnion fibres = chores :=
    Finset.eq_of_subset_of_card_le hunionSubset (by rw [hcardUnion])
  have htotal : ∀ item ∈ chores, ∃ agent, owner item = some agent := by
    intro item hitem
    have hitemUnion : item ∈ (Finset.univ : Finset Agent).biUnion fibres := by
      rw [hunion]
      exact hitem
    obtain ⟨agent, _, hagentItem⟩ := Finset.mem_biUnion.mp hitemUnion
    exact ⟨agent, (Finset.mem_filter.mp hagentItem).2⟩
  refine ⟨allocationOfOwner chores owner,
    isAllocationOf_allocationOfOwner chores owner htotal, ?_⟩
  intro agent
  have hfiber : allocationOfOwner chores owner agent = fibres agent := by
    ext item
    simp [allocationOfOwner, fibres]
  rw [hfiber]
  exact hcard agent

/-- For a fixed M₂ small-agent type, assigning every extra balanced quota only
to agents of that type gives a global one-small-item slack certificate.  The
agents outside the type receive the base quota and see every bundle as
all-large, while agents in the type see every bundle as all-small. -/
theorem existsM2SingleSmallType_quotaAllocation_unitSlack
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q : ℕ) (smallAgents longAgents : Finset (Fin 4))
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hsmallType : ∀ item ∈ chores, smallAgentSet cost item = smallAgents)
    (hdecompose : chores.card = 4 * q + longAgents.card)
    (hlongSubset : longAgents ⊆ smallAgents) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧
      (∀ agent, (allocation agent).card = m2Quota q longAgents agent) ∧
      (∀ agent other,
        additiveChoreCost cost agent (allocation agent) - 1 ≤
          additiveChoreCost cost agent (allocation other)) ∧
      EFXForChores (additiveChoreCost cost) allocation := by
  classical
  obtain ⟨allocation, hallocation, hquota⟩ :=
    existsAllocationOfQuota (Fin 4) Item chores (m2Quota q longAgents) (by
      rw [m2Quota_sum, hdecompose])
  have hsmallCost (agent : Fin 4) (hagent : agent ∈ smallAgents)
      (item : Item) (hitem : item ∈ chores) : cost agent item = 1 := by
    have hmem : agent ∈ smallAgentSet cost item := by
      simpa [hsmallType item hitem] using hagent
    simpa [smallAgentSet] using hmem
  have hlargeCost (agent : Fin 4) (hagent : agent ∉ smallAgents)
      (item : Item) (hitem : item ∈ chores) : cost agent item = r := by
    rcases hcost agent item with hsmall | hlarge
    · exfalso
      apply hagent
      have hmem : agent ∈ smallAgentSet cost item := by
        simpa [smallAgentSet, IsSmallChore] using hsmall
      simpa [hsmallType item hitem] using hmem
    · exact hlarge
  have hcardLower (agent : Fin 4) : q ≤ (allocation agent).card := by
    rw [hquota agent]
    simp [m2Quota]
  have hcardUpper (agent : Fin 4) : (allocation agent).card ≤ q + 1 := by
    rw [hquota agent]
    by_cases hagent : agent ∈ longAgents <;> simp [m2Quota, hagent]
  have hunit : ∀ agent other,
      additiveChoreCost cost agent (allocation agent) - 1 ≤
        additiveChoreCost cost agent (allocation other) := by
    intro agent other
    by_cases hagentSmall : agent ∈ smallAgents
    · have hconstantOwn : ∀ item ∈ allocation agent, cost agent item = 1 := by
        intro item hitem
        exact hsmallCost agent hagentSmall item (hallocation.1 agent item hitem)
      have hconstantOther : ∀ item ∈ allocation other, cost agent item = 1 := by
        intro item hitem
        exact hsmallCost agent hagentSmall item (hallocation.1 other item hitem)
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost agent (allocation agent) 1
        hconstantOwn,
        additiveChoreCost_eq_card_nsmul_of_constant cost agent (allocation other) 1
          hconstantOther]
      norm_num [nsmul_eq_mul]
      have hupper : ((allocation agent).card : ℝ) ≤ q + 1 := by
        exact_mod_cast hcardUpper agent
      have hlower : (q : ℝ) ≤ (allocation other).card := by
        exact_mod_cast hcardLower other
      linarith
    · have hagentNotLong : agent ∉ longAgents := fun hlong => hagentSmall
        (hlongSubset hlong)
      have hcardAgent : (allocation agent).card = q := by
        rw [hquota agent]
        simp [m2Quota, hagentNotLong]
      have hconstantOwn : ∀ item ∈ allocation agent, cost agent item = r := by
        intro item hitem
        exact hlargeCost agent hagentSmall item (hallocation.1 agent item hitem)
      have hconstantOther : ∀ item ∈ allocation other, cost agent item = r := by
        intro item hitem
        exact hlargeCost agent hagentSmall item (hallocation.1 other item hitem)
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost agent (allocation agent) r
        hconstantOwn,
        additiveChoreCost_eq_card_nsmul_of_constant cost agent (allocation other) r
          hconstantOther, hcardAgent]
      simp only [nsmul_eq_mul]
      have hlower : (q : ℝ) ≤ (allocation other).card := by
        exact_mod_cast hcardLower other
      have hrnonneg : 0 ≤ r := by linarith
      nlinarith
  have hefx : EFXForChores (additiveChoreCost cost) allocation := by
    intro agent other
    by_cases hempty : allocation agent = ∅
    · exact Or.inl hempty
    · right
      intro item hitem
      rw [additiveChoreCost_erase cost agent (allocation agent) item hitem]
      have hitemLower : 1 ≤ cost agent item :=
        IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
      linarith [hunit agent other]
  exact ⟨allocation, hallocation, hquota, hunit, hefx⟩

/-- The agents receiving the incomplete round in the source order
`0,1,2,3`, restricted to remainders below three.  In the one-type B.4.3(a)
nonexceptional branch, this reserves every extra quota for a small agent. -/
def m2EarlyRoundLongAgents (remainder : ℕ) : Finset (Fin 4) :=
  match remainder with
  | 0 => ∅
  | 1 => {0}
  | _ => {0, 1}

theorem m2EarlyRoundLongAgents_card (remainder : ℕ) (hremainder : remainder < 3) :
    (m2EarlyRoundLongAgents remainder).card = remainder := by
  interval_cases remainder <;> simp [m2EarlyRoundLongAgents] at *

theorem m2EarlyRoundLongAgents_subset_smallType (remainder : ℕ) :
    m2EarlyRoundLongAgents remainder ⊆ ({0, 1} : Finset (Fin 4)) := by
  intro agent hagent
  cases remainder with
  | zero => simp [m2EarlyRoundLongAgents] at hagent
  | succ remainder =>
    cases remainder with
    | zero =>
      have hzero : agent = 0 := by
        simpa [m2EarlyRoundLongAgents] using hagent
      subst agent
      simp
    | succ remainder => simpa [m2EarlyRoundLongAgents] using hagent

theorem m2EarlyRoundLongAgents_quota_le_zero (q remainder : ℕ)
    (hremainder : remainder < 3) (agent : Fin 4) (hagent : agent ≠ 0) :
    m2Quota q (m2EarlyRoundLongAgents remainder) agent ≤
      m2Quota q (m2EarlyRoundLongAgents remainder) 0 := by
  interval_cases remainder <;> fin_cases agent <;>
    simp [m2EarlyRoundLongAgents, m2Quota] at *

/-- The remainder-three round-robin allocation for a fixed type-`(0,1)` M₂
pool.  Every agent except the selected auxiliary endpoint has the usual
unit-slack certificate; the selected endpoint has one extra all-large chore,
and its sole non-unit comparison is with the other auxiliary endpoint.

This is the explicit residual schedule used in Case B.4.3(a), rather than an
exceptionality certificate: `special` is the third recipient in the source
round-robin order and `companion` is the fourth. -/
theorem existsM2Type01_remainderThree_controlled
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q : ℕ) (special companion : Fin 4)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htype : ∀ item ∈ chores,
      smallAgentSet cost item = ({0, 1} : Finset (Fin 4)))
    (hcard : chores.card = 4 * q + 3)
    (hspecial : special ∈ ({2, 3} : Finset (Fin 4)))
    (hcompanion : companion ∈ ({2, 3} : Finset (Fin 4)))
    (hne : special ≠ companion) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧
      (∀ agent, (allocation agent).card =
        m2Quota q (Finset.univ.erase companion) agent) ∧
      (∀ agent, agent ≠ special → ∀ other,
        additiveChoreCost cost agent (allocation agent) - 1 ≤
          additiveChoreCost cost agent (allocation other)) ∧
      (∀ item ∈ allocation special, IsLargeChore cost r special item) ∧
      (∀ other, other ≠ companion →
        additiveChoreCost cost special (allocation special) ≤
          additiveChoreCost cost special (allocation other)) ∧
      additiveChoreCost cost special (allocation special) - r ≤
        additiveChoreCost cost special (allocation companion) := by
  classical
  let longAgents : Finset (Fin 4) := Finset.univ.erase companion
  obtain ⟨allocation, hallocation, hquota⟩ :=
    existsAllocationOfQuota (Fin 4) Item chores (m2Quota q longAgents) (by
      rw [m2Quota_sum]
      dsimp [longAgents]
      norm_num
      exact hcard.symm)
  have hspecialNotSmall : special ∉ ({0, 1} : Finset (Fin 4)) := by
    fin_cases special <;> simp_all
  have hcompanionNotSmall : companion ∉ ({0, 1} : Finset (Fin 4)) := by
    fin_cases companion <;> simp_all
  have hremainingSmall (agent : Fin 4) (hagentSpecial : agent ≠ special)
      (hagentCompanion : agent ≠ companion) : agent ∈ ({0, 1} : Finset (Fin 4)) := by
    fin_cases agent <;> fin_cases special <;> fin_cases companion <;> simp_all
  have hsmallCost (agent : Fin 4) (hagent : agent ∈ ({0, 1} : Finset (Fin 4)))
      (item : Item) (hitem : item ∈ chores) : cost agent item = 1 := by
    have hmem : agent ∈ smallAgentSet cost item := by
      simpa [htype item hitem] using hagent
    simpa [smallAgentSet] using hmem
  have hlargeCost (agent : Fin 4) (hagent : agent ∉ ({0, 1} : Finset (Fin 4)))
      (item : Item) (hitem : item ∈ chores) : cost agent item = r := by
    rcases hcost agent item with hsmall | hlarge
    · exfalso
      apply hagent
      have hmem : agent ∈ smallAgentSet cost item := by
        simpa [smallAgentSet, IsSmallChore] using hsmall
      simpa [htype item hitem] using hmem
    · exact hlarge
  have hcardLower (agent : Fin 4) : q ≤ (allocation agent).card := by
    rw [hquota agent]
    simp [m2Quota]
  have hcardSpecial : (allocation special).card = q + 1 := by
    rw [hquota special]
    simp [longAgents, m2Quota, hne]
  have hcardCompanion : (allocation companion).card = q := by
    rw [hquota companion]
    simp [longAgents, m2Quota]
  have hspecialLarge : ∀ item ∈ allocation special,
      IsLargeChore cost r special item := by
    intro item hitem
    exact hlargeCost special hspecialNotSmall item (hallocation.1 special item hitem)
  have hunit : ∀ agent, agent ≠ special → ∀ other,
      additiveChoreCost cost agent (allocation agent) - 1 ≤
        additiveChoreCost cost agent (allocation other) := by
    intro agent hagentSpecial other
    by_cases hagentCompanion : agent = companion
    · subst agent
      have hcompanionCost : additiveChoreCost cost companion (allocation companion) =
          (q : ℝ) * r := by
        rw [additiveChoreCost_eq_card_nsmul_of_constant cost companion
          (allocation companion) r
          (fun item hitem => hlargeCost companion hcompanionNotSmall item
            (hallocation.1 companion item hitem)), hcardCompanion]
        simp only [nsmul_eq_mul]
      have hotherCost : additiveChoreCost cost companion (allocation other) =
          ((allocation other).card : ℝ) * r := by
        rw [additiveChoreCost_eq_card_nsmul_of_constant cost companion
          (allocation other) r
          (fun item hitem => hlargeCost companion hcompanionNotSmall item
            (hallocation.1 other item hitem))]
        simp only [nsmul_eq_mul]
      rw [hcompanionCost, hotherCost]
      have hotherCard : (q : ℝ) ≤ (allocation other).card := by
        exact_mod_cast hcardLower other
      have hrnonneg : 0 ≤ r := by linarith
      nlinarith
    · have hagentSmall := hremainingSmall agent hagentSpecial hagentCompanion
      have hcardAgent : (allocation agent).card = q + 1 := by
        rw [hquota agent]
        simp [longAgents, m2Quota, hagentCompanion]
      have hagentCost : additiveChoreCost cost agent (allocation agent) =
          (q + 1 : ℕ) := by
        rw [additiveChoreCost_eq_card_nsmul_of_constant cost agent
          (allocation agent) 1
          (fun item hitem => hsmallCost agent hagentSmall item
            (hallocation.1 agent item hitem)), hcardAgent]
        norm_num
      have hotherCost : additiveChoreCost cost agent (allocation other) =
          (allocation other).card := by
        rw [additiveChoreCost_eq_card_nsmul_of_constant cost agent
          (allocation other) 1
          (fun item hitem => hsmallCost agent hagentSmall item
            (hallocation.1 other item hitem))]
        norm_num
      rw [hagentCost, hotherCost]
      have hotherCard : (q : ℝ) ≤ (allocation other).card := by
        exact_mod_cast hcardLower other
      push_cast
      linarith
  have hspecialAway : ∀ other, other ≠ companion →
      additiveChoreCost cost special (allocation special) ≤
        additiveChoreCost cost special (allocation other) := by
    intro other hotherCompanion
    by_cases hotherSpecial : other = special
    · subst other
      exact le_rfl
    · have hcardOther : (allocation other).card = q + 1 := by
        rw [hquota other]
        simp [longAgents, m2Quota, hotherCompanion]
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost special
        (allocation special) r
        (fun item hitem => hlargeCost special hspecialNotSmall item
          (hallocation.1 special item hitem)), hcardSpecial,
        additiveChoreCost_eq_card_nsmul_of_constant cost special (allocation other) r
          (fun item hitem => hlargeCost special hspecialNotSmall item
            (hallocation.1 other item hitem)), hcardOther]
  have hspecialCompanion :
      additiveChoreCost cost special (allocation special) - r ≤
        additiveChoreCost cost special (allocation companion) := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost special
      (allocation special) r
      (fun item hitem => hlargeCost special hspecialNotSmall item
        (hallocation.1 special item hitem)), hcardSpecial,
      additiveChoreCost_eq_card_nsmul_of_constant cost special (allocation companion) r
        (fun item hitem => hlargeCost special hspecialNotSmall item
          (hallocation.1 companion item hitem)), hcardCompanion]
    simp only [nsmul_eq_mul]
    push_cast
    ring_nf
    exact le_rfl
  refine ⟨allocation, hallocation, ?_, hunit, hspecialLarge, hspecialAway,
    hspecialCompanion⟩
  intro agent
  simpa [longAgents] using hquota agent

private theorem m2Quota_sum_on (q : ℕ) (longAgents agents : Finset (Fin 4)) :
    agents.sum (m2Quota q longAgents) =
      agents.card * q + (agents ∩ longAgents).card := by
  simp [m2Quota, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_const, Nat.mul_comm]

private theorem m2Quota_balanced (q : ℕ) (longAgents : Finset (Fin 4)) :
    ∀ first second, m2Quota q longAgents first ≤ m2Quota q longAgents second + 1 := by
  intro first second
  simp only [m2Quota]
  split <;> split <;> omega

/-- The source's remainder-two calculation, including its single exceptional
tight-pair case. -/
private theorem m2HallArithmeticRemainderTwoOfNonTight
    (itemCount quotient incidence vertexCount longCount : ℕ)
    (hdecompose : itemCount = 4 * quotient + 2)
    (hvertexBound : vertexCount ≤ 4)
    (hdeficiency : vertexCount * itemCount ≤ 4 * incidence)
    (hlongVertex : longCount ≤ vertexCount) (hlongTwo : longCount ≤ 2)
    (hnontight : vertexCount = 2 → longCount = 2 → 2 * quotient + 1 < incidence) :
    vertexCount * quotient + longCount ≤ incidence := by
  interval_cases vertexCount <;> interval_cases longCount <;> omega

private theorem m2Pair_eq_of_inter_card_two
    (first second : Finset (Fin 4)) (hfirst : first.card = 2)
    (hsecond : second.card = 2) (hinter : (first ∩ second).card = 2) :
    first = second := by
  have hinterEqFirst : first ∩ second = first :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  apply Finset.eq_of_subset_of_card_le
  · intro agent hagent
    have hmemInter : agent ∈ first ∩ second := by simpa [hinterEqFirst] using hagent
    exact (Finset.mem_inter.mp hmemInter).2
  · omega

/-- The EFX verification for Case 3.2.1: all remaining chores have one fixed
small-agent type, so balancing bundle cardinalities is sufficient. -/
theorem efxOfM2SingleSmallTypeBalanced
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (allocation : Allocation (Fin 4) Item)
    (smallAgents : Finset (Fin 4))
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hsmallType : ∀ item ∈ chores, smallAgentSet cost item = smallAgents)
    (halloc : IsAllocationOf allocation chores)
    (hbalanced : ∀ first second, (allocation first).card ≤ (allocation second).card + 1) :
    EFXForChores (additiveChoreCost cost) allocation := by
  apply efxForChores_of_balanced_card_and_agentwise_constant cost allocation
    (fun agent => if agent ∈ smallAgents then 1 else r)
  · intro agent
    split
    · norm_num
    · linarith
  · intro agent owner item hitem
    have hchore : item ∈ chores := isAllocationOf_mem_goods halloc hitem
    by_cases hsmallAgent : agent ∈ smallAgents
    · rw [if_pos hsmallAgent]
      have hmemSmallSet : agent ∈ smallAgentSet cost item := by
        simpa [hsmallType item hchore] using hsmallAgent
      simpa [smallAgentSet, IsSmallChore] using hmemSmallSet
    · rw [if_neg hsmallAgent]
      rcases hcost agent item with hsmall | hlarge
      · exfalso
        apply hsmallAgent
        have hmemSmallSet : agent ∈ smallAgentSet cost item := by
          simp [smallAgentSet, IsSmallChore, hsmall]
        simpa [hsmallType item hchore] using hmemSmallSet
      · exact hlarge
  · exact hbalanced

/-- Assemble the source singleton-branch allocation from a partial orientation.
Every partial-owner fiber assigned to a non-special agent is retained, and all
unassigned chores fall back to the special agent. The quota sum then forces the
special bundle to have size `q`, after which the source EFX shape applies. -/
theorem existsEfxOfM2SingletonPartialOwner_certified
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (special : Fin 4) (q : ℕ) (partialOwner : Item → Option (Fin 4))
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r) (quota : Fin 4 → ℕ)
    (hcounts : ∀ agent,
      (chores.filter fun item => partialOwner item = some agent).card = quota agent)
    (hsumOther : ∑ agent ∈ (Finset.univ.erase special), quota agent = chores.card - q)
    (hqle : q ≤ chores.card)
    (hquotaRange : ∀ agent, agent ≠ special → q ≤ quota agent ∧ quota agent ≤ q + 1)
    (hsmall : ∀ agent item, agent ≠ special → partialOwner item = some agent →
      IsSmallChore cost agent item)
    (hlarge : ∀ agent item, agent ≠ special → partialOwner item = some agent →
      IsLargeChore cost r special item) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) := by
  let owner := ownerWithFallback special partialOwner
  let allocation := allocationOfOwner chores owner
  have halloc : IsAllocationOf allocation chores := by
    exact isAllocationOf_allocationOfOwnerWithFallback chores special partialOwner
  have hotherCard : ∀ agent, agent ≠ special → (allocation agent).card = quota agent := by
    intro agent hagent
    rw [show allocation = allocationOfOwner chores (ownerWithFallback special partialOwner) by rfl]
    rw [allocationOfOwnerWithFallback_eq_partialFiber chores special agent partialOwner hagent]
    exact hcounts agent
  have hotherSum : ∑ agent ∈ Finset.univ.erase special, (allocation agent).card =
      chores.card - q := by
    calc
      ∑ agent ∈ Finset.univ.erase special, (allocation agent).card =
          ∑ agent ∈ Finset.univ.erase special, quota agent := by
        apply Finset.sum_congr rfl
        intro agent hagent
        exact hotherCard agent (Finset.mem_erase.mp hagent).1
      _ = chores.card - q := hsumOther
  have htotalSum := sum_card_allocation_eq_card_of_isAllocation allocation chores halloc
  have hsumErase := Finset.sum_erase_add (Finset.univ : Finset (Fin 4))
    (fun agent => (allocation agent).card) (Finset.mem_univ special)
  have hspecialCard : (allocation special).card = q := by
    rw [hotherSum, htotalSum] at hsumErase
    change chores.card - q + (allocation special).card = chores.card at hsumErase
    omega
  have hcardLower : ∀ agent, q ≤ (allocation agent).card := by
    intro agent
    by_cases hagent : agent = special
    · simp [hagent, hspecialCard]
    · rw [hotherCard agent hagent]
      exact (hquotaRange agent hagent).1
  have hcardOtherUpper : ∀ agent, agent ≠ special → (allocation agent).card ≤ q + 1 := by
    intro agent hagent
    rw [hotherCard agent hagent]
    exact (hquotaRange agent hagent).2
  have hotherSmall : ∀ agent item, agent ≠ special → item ∈ allocation agent →
      IsSmallChore cost agent item := by
    intro agent item hagent hitem
    have hpartialMem : partialOwner item = some agent := by
      have hmemFiber : item ∈ chores.filter fun other => partialOwner other = some agent := by
        rw [← allocationOfOwnerWithFallback_eq_partialFiber chores special agent partialOwner hagent]
        exact hitem
      exact (Finset.mem_filter.mp hmemFiber).2
    exact hsmall agent item hagent hpartialMem
  have hotherLarge : ∀ agent item, agent ≠ special → item ∈ allocation agent →
      IsLargeChore cost r special item := by
    intro agent item hagent hitem
    have hpartialMem : partialOwner item = some agent := by
      have hmemFiber : item ∈ chores.filter fun other => partialOwner other = some agent := by
        rw [← allocationOfOwnerWithFallback_eq_partialFiber chores special agent partialOwner hagent]
        exact hitem
      exact (Finset.mem_filter.mp hmemFiber).2
    exact hlarge agent item hagent hpartialMem
  have hefx : EFXForChores (additiveChoreCost cost) allocation :=
    efxForChores_of_single_special_balanced_shape cost r allocation special q hcost (by linarith)
      hspecialCard hcardLower hcardOtherUpper hotherSmall hotherLarge
  refine ⟨allocation, halloc, hefx, ?_, ?_⟩
  · intro agent hsmallAgent
    exact smallItemCertificate_of_efx Item cost allocation hefx agent hsmallAgent
  · intro agent hallLarge comparison
    by_cases hagent : agent = special
    · subst agent
      exact envyFreeForChores_single_special_of_all_large cost r allocation special q hcost
        (by linarith) hspecialCard hcardLower hotherLarge hallLarge comparison
    · have hempty : allocation agent = ∅ := by
        by_contra hnotempty
        obtain ⟨item, hitem⟩ := Finset.nonempty_iff_ne_empty.mpr hnotempty
        have hsmallItem := hotherSmall agent item hagent hitem
        have hlargeItem := hallLarge item hitem
        rw [IsSmallChore] at hsmallItem
        rw [IsLargeChore] at hlargeItem
        linarith
      rw [hempty]
      simp only [additiveChoreCost, Finset.sum_empty]
      exact additiveChoreCost_nonneg cost
        (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) agent (allocation comparison)

/-- The singleton-deficiency partial-owner construction at its basic EFX
existence interface. Its stronger certificates are retained above. -/
theorem existsEfxOfM2SingletonPartialOwner
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (special : Fin 4) (q : ℕ) (partialOwner : Item → Option (Fin 4))
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r) (quota : Fin 4 → ℕ)
    (hcounts : ∀ agent,
      (chores.filter fun item => partialOwner item = some agent).card = quota agent)
    (hsumOther : ∑ agent ∈ (Finset.univ.erase special), quota agent = chores.card - q)
    (hqle : q ≤ chores.card)
    (hquotaRange : ∀ agent, agent ≠ special → q ≤ quota agent ∧ quota agent ≤ q + 1)
    (hsmall : ∀ agent item, agent ≠ special → partialOwner item = some agent →
      IsSmallChore cost agent item)
    (hlarge : ∀ agent item, agent ≠ special → partialOwner item = some agent →
      IsLargeChore cost r special item) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨allocation, halloc, hefx, _, _⟩ :=
    existsEfxOfM2SingletonPartialOwner_certified Item r cost chores special q partialOwner hr hcost
      quota hcounts hsumOther hqle hquotaRange hsmall hlarge
  exact ⟨allocation, halloc, hefx⟩

/-- A Hall-oriented partial assignment of the singleton branch's triangle
chores can be completed by giving its unassigned chores to the deficient
agent.  This packages the orientation step and the fallback allocation step
while keeping the source's endpoint hypotheses explicit. -/
theorem existsEfxOfM2SingletonPartialOrientation_certified
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores edges : Finset Item) (special : Fin 4) (q : ℕ)
    (endpoints : Item → Finset (Fin 4)) (quota : Fin 4 → ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r) (hedges : edges ⊆ chores)
    (hhall : ∀ vertices : Finset (Fin 4), vertices.sum quota ≤
      (edges.filter fun item => (endpoints item ∩ vertices).Nonempty).card)
    (hsumOther : ∑ agent ∈ (Finset.univ.erase special), quota agent = chores.card - q)
    (hqle : q ≤ chores.card)
    (hquotaRange : ∀ agent, agent ≠ special → q ≤ quota agent ∧ quota agent ≤ q + 1)
    (hsmallEndpoint : ∀ agent item, agent ≠ special → item ∈ edges →
      agent ∈ endpoints item → IsSmallChore cost agent item)
    (hlargeEndpoint : ∀ agent item, agent ≠ special → item ∈ edges →
      agent ∈ endpoints item → IsLargeChore cost r special item) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) := by
  classical
  obtain ⟨owner, howner, hcard⟩ :=
    partialBalancedOrientation (Fin 4) Item edges endpoints quota hhall
  let partialOwner : Item → Option (Fin 4) := fun item =>
    if item ∈ edges then owner item else none
  have hcounts : ∀ agent,
      (chores.filter fun item => partialOwner item = some agent).card = quota agent := by
    intro agent
    have hfilter : chores.filter fun item => partialOwner item = some agent =
        edges.filter fun item => owner item = some agent := by
      ext item
      by_cases hitem : item ∈ edges
      · have hchore : item ∈ chores := hedges hitem
        simp [partialOwner, hitem, hchore]
      · simp [partialOwner, hitem]
    rw [hfilter, hcard agent]
  apply existsEfxOfM2SingletonPartialOwner_certified Item r cost chores special q partialOwner
    hr hcost quota hcounts hsumOther hqle hquotaRange
  · intro agent item hagent hassigned
    have hedge : item ∈ edges := by
      by_contra hnot
      simp [partialOwner, hnot] at hassigned
    have hownerEq : owner item = some agent := by
      simpa [partialOwner, hedge] using hassigned
    exact hsmallEndpoint agent item hagent hedge (howner item hedge agent hownerEq)
  · intro agent item hagent hassigned
    have hedge : item ∈ edges := by
      by_contra hnot
      simp [partialOwner, hnot] at hassigned
    have hownerEq : owner item = some agent := by
      simpa [partialOwner, hedge] using hassigned
    exact hlargeEndpoint agent item hagent hedge (howner item hedge agent hownerEq)

/-- The singleton partial-orientation construction at its basic EFX-existence
interface. Its small-removal and all-large envy-free certificates are retained
by `existsEfxOfM2SingletonPartialOrientation_certified`. -/
theorem existsEfxOfM2SingletonPartialOrientation
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores edges : Finset Item) (special : Fin 4) (q : ℕ)
    (endpoints : Item → Finset (Fin 4)) (quota : Fin 4 → ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r) (hedges : edges ⊆ chores)
    (hhall : ∀ vertices : Finset (Fin 4), vertices.sum quota ≤
      (edges.filter fun item => (endpoints item ∩ vertices).Nonempty).card)
    (hsumOther : ∑ agent ∈ (Finset.univ.erase special), quota agent = chores.card - q)
    (hqle : q ≤ chores.card)
    (hquotaRange : ∀ agent, agent ≠ special → q ≤ quota agent ∧ quota agent ≤ q + 1)
    (hsmallEndpoint : ∀ agent item, agent ≠ special → item ∈ edges →
      agent ∈ endpoints item → IsSmallChore cost agent item)
    (hlargeEndpoint : ∀ agent item, agent ≠ special → item ∈ edges →
      agent ∈ endpoints item → IsLargeChore cost r special item) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨allocation, halloc, hefx, _, _⟩ :=
    existsEfxOfM2SingletonPartialOrientation_certified Item r cost chores edges special q endpoints
      quota hr hcost hedges hhall hsumOther hqle hquotaRange hsmallEndpoint hlargeEndpoint
  exact ⟨allocation, halloc, hefx⟩

/-- The Hall calculation for a triangle on the three agents other than a
special agent.  Singletons use their degree bounds; any two of the three
triangle vertices meet every edge. -/
theorem singletonTriangleHall
    {Edge : Type} [DecidableEq Edge] (edges : Finset Edge)
    (endpoints : Edge → Finset (Fin 4)) (special : Fin 4) (quota : Fin 4 → ℕ)
    (hquotaSpecial : quota special = 0)
    (hends : ∀ edge ∈ edges, (endpoints edge).card = 2)
    (hnoSpecial : ∀ edge ∈ edges, special ∉ endpoints edge)
    (hdegree : ∀ agent, agent ≠ special → quota agent ≤
      (edges.filter fun edge => agent ∈ endpoints edge).card)
    (htotal : ∑ agent ∈ Finset.univ.erase special, quota agent ≤ edges.card) :
    ∀ vertices : Finset (Fin 4), vertices.sum quota ≤
      (edges.filter fun edge => (endpoints edge ∩ vertices).Nonempty).card := by
  intro vertices
  let others := vertices.erase special
  have hsum : vertices.sum quota = others.sum quota := by
    by_cases hspecial : special ∈ vertices
    · have hsumErase := Finset.sum_erase_add vertices quota hspecial
      change others.sum quota + quota special = vertices.sum quota at hsumErase
      rw [hquotaSpecial, Nat.add_zero] at hsumErase
      exact hsumErase.symm
    · have herase : vertices.erase special = vertices := Finset.erase_eq_of_notMem hspecial
      simp [others, herase]
  rw [hsum]
  have hfilter :
      (edges.filter fun edge => (endpoints edge ∩ vertices).Nonempty) =
        (edges.filter fun edge => (endpoints edge ∩ others).Nonempty) := by
    ext edge
    constructor
    · intro hedge
      rcases Finset.mem_filter.mp hedge with ⟨hedgeMem, hinter⟩
      obtain ⟨vertex, hvertex⟩ := hinter
      rcases Finset.mem_inter.mp hvertex with ⟨hendpoint, hvertices⟩
      have hnotSpecial : vertex ≠ special := by
        intro hEq
        subst vertex
        exact hnoSpecial edge hedgeMem hendpoint
      exact Finset.mem_filter.mpr ⟨hedgeMem,
        ⟨vertex, Finset.mem_inter.mpr
          ⟨hendpoint, Finset.mem_erase.mpr ⟨hnotSpecial, hvertices⟩⟩⟩⟩
    · intro hedge
      rcases Finset.mem_filter.mp hedge with ⟨hedgeMem, hinter⟩
      obtain ⟨vertex, hvertex⟩ := hinter
      rcases Finset.mem_inter.mp hvertex with ⟨hendpoint, hother⟩
      exact Finset.mem_filter.mpr ⟨hedgeMem,
        ⟨vertex, Finset.mem_inter.mpr ⟨hendpoint, (Finset.mem_erase.mp hother).2⟩⟩⟩
  rw [hfilter]
  by_cases hnone : others.card = 0
  · have hempty : others = ∅ := Finset.card_eq_zero.mp hnone
    simp [hempty]
  by_cases hone : others.card = 1
  · obtain ⟨agent, hagent⟩ := Finset.card_eq_one.mp hone
    have hagentNe : agent ≠ special := by
      intro hEq
      subst agent
      have hspecialMem : special ∈ others := by simp [hagent]
      exact (Finset.mem_erase.mp hspecialMem).1 rfl
    have hsumOne : others.sum quota = quota agent := by simp [hagent]
    rw [hsumOne, hagent]
    have hfilterOne :
        (edges.filter fun edge => (endpoints edge ∩ {agent}).Nonempty) =
          edges.filter fun edge => agent ∈ endpoints edge := by
      ext edge
      constructor
      · intro hedge
        rcases Finset.mem_filter.mp hedge with ⟨hedgeMem, hinter⟩
        obtain ⟨vertex, hvertex⟩ := hinter
        have hvertexEq : vertex = agent :=
          Finset.mem_singleton.mp (Finset.mem_inter.mp hvertex).2
        exact Finset.mem_filter.mpr ⟨hedgeMem,
          by simpa [hvertexEq] using (Finset.mem_inter.mp hvertex).1⟩
      · intro hedge
        rcases Finset.mem_filter.mp hedge with ⟨hedgeMem, hendpoint⟩
        exact Finset.mem_filter.mpr ⟨hedgeMem,
          ⟨agent, Finset.mem_inter.mpr ⟨hendpoint, by simp⟩⟩⟩
    rw [hfilterOne]
    exact hdegree agent hagentNe
  · have htwo : 2 ≤ others.card := by omega
    have hothersSub : others ⊆ Finset.univ.erase special := by
      intro agent hagent
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hagent).1,
        Finset.mem_univ _⟩
    have hcover : ∀ edge ∈ edges, (endpoints edge ∩ others).Nonempty := by
      intro edge hedge
      by_contra hdisjoint
      have hendSub : endpoints edge ⊆ (Finset.univ.erase special) \ others := by
        intro agent hagent
        apply Finset.mem_sdiff.mpr
        constructor
        · apply Finset.mem_erase.mpr
          constructor
          · intro hEq
            subst agent
            exact hnoSpecial edge hedge hagent
          · exact Finset.mem_univ _
        · intro hother
          exact hdisjoint ⟨agent, Finset.mem_inter.mpr ⟨hagent, hother⟩⟩
      have hcardEnd := Finset.card_le_card hendSub
      rw [hends edge hedge, Finset.card_sdiff_of_subset hothersSub,
        Finset.card_erase_of_mem (Finset.mem_univ special)] at hcardEnd
      norm_num at hcardEnd
      omega
    have hfilterAll : (edges.filter fun edge => (endpoints edge ∩ others).Nonempty) = edges := by
      apply Finset.filter_eq_self.mpr
      exact hcover
    rw [hfilterAll]
    exact (Finset.sum_le_sum_of_subset_of_nonneg (by
      intro agent hagent
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hagent).1, Finset.mem_univ _⟩)
      (by omega)).trans htotal

/-- The finite allocation underlying source Case 3.1 after its integer split
has been selected, in the source's displayed labelling where the maximally
deficient pair is `{0,1}`.  The common-small fiber is split according to
`firstCore, secondCore`; the two cross fibers go wholly to their named
endpoints; and the complementary fiber is split with the remaining two
agents as evenly as possible.  This theorem establishes feasibility and the
component quota equations; the following fairness theorem verifies EFX from
the source's two split inequalities. -/
theorem existsM2PairSplitAllocation
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (firstCore secondCore firstOutside secondOutside : ℕ)
    (hcoreShares : firstCore + secondCore =
      (m2PairCoreFibre cost chores 0 1).card)
    (houtsideShares : firstOutside + secondOutside ≤
      (m2PairOutsideFibre cost chores 0 1).card) :
    ∃ coreAllocation outsideAllocation : Allocation (Fin 4) Item,
      IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1) ∧
      (∀ agent, (coreAllocation agent).card =
        m2PairCoreQuota 0 1 firstCore secondCore agent) ∧
      IsAllocationOf outsideAllocation (m2PairOutsideFibre cost chores 0 1) ∧
      (∀ agent, (outsideAllocation agent).card =
        m2PairOutsideQuota firstOutside secondOutside
          (m2PairOutsideFibre cost chores 0 1).card agent) ∧
      IsAllocationOf
        (fun agent => coreAllocation agent ∪
          (allocateAllTo (Fin 4) Item 0
            (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1
            (m2PairCrossFibre cost chores 1 0)) agent ∪ outsideAllocation agent))
        chores := by
  classical
  let core := m2PairCoreFibre cost chores 0 1
  let firstCross := m2PairCrossFibre cost chores 0 1
  let secondCross := m2PairCrossFibre cost chores 1 0
  let outside := m2PairOutsideFibre cost chores 0 1
  obtain ⟨coreAllocation, hcoreAllocation, hcoreCard⟩ :=
    existsAllocationOfQuota (Fin 4) Item core
      (m2PairCoreQuota 0 1 firstCore secondCore) (by
        rw [m2PairCoreQuota_sum 0 1 (by decide), ← hcoreShares])
  obtain ⟨outsideAllocation, houtsideAllocation, houtsideCard⟩ :=
    existsAllocationOfQuota (Fin 4) Item outside
      (m2PairOutsideQuota firstOutside secondOutside outside.card) (by
        rw [m2PairOutsideQuota_sum firstOutside secondOutside outside.card houtsideShares])
  refine ⟨coreAllocation, outsideAllocation, hcoreAllocation, hcoreCard,
    houtsideAllocation, houtsideCard, ?_⟩
  let firstCrossAllocation := allocateAllTo (Fin 4) Item 0 firstCross
  let secondCrossAllocation := allocateAllTo (Fin 4) Item 1 secondCross
  have hfirstCrossAllocation : IsAllocationOf firstCrossAllocation firstCross :=
    isAllocationOf_allocateAllTo 0 firstCross
  have hsecondCrossAllocation : IsAllocationOf secondCrossAllocation secondCross :=
    isAllocationOf_allocateAllTo 1 secondCross
  have hsecondOutsideDisjoint : Disjoint secondCross outside := by
    exact m2PairCrossSecond_disjoint_outside cost chores 0 1
  have hsecondOutsideAllocation : IsAllocationOf
      (fun agent => secondCrossAllocation agent ∪ outsideAllocation agent)
      (secondCross ∪ outside) :=
    isAllocationOf_union secondCrossAllocation outsideAllocation secondCross outside
      hsecondOutsideDisjoint hsecondCrossAllocation houtsideAllocation
  have hfirstRestDisjoint : Disjoint firstCross (secondCross ∪ outside) := by
    exact m2PairCrossFirst_disjoint_crossSecond_outside cost chores 0 1
  have hfirstRestAllocation : IsAllocationOf
      (fun agent => firstCrossAllocation agent ∪
        (secondCrossAllocation agent ∪ outsideAllocation agent))
      (firstCross ∪ (secondCross ∪ outside)) :=
    isAllocationOf_union firstCrossAllocation
      (fun agent => secondCrossAllocation agent ∪ outsideAllocation agent)
      firstCross (secondCross ∪ outside) hfirstRestDisjoint hfirstCrossAllocation
      hsecondOutsideAllocation
  have hcoreRestDisjoint : Disjoint core (firstCross ∪ (secondCross ∪ outside)) := by
    simpa only [core, firstCross, secondCross, outside, Finset.union_assoc] using
      m2PairCore_disjoint_crosses_outside cost chores 0 1
  have hfull : IsAllocationOf
      (fun agent => coreAllocation agent ∪
        (firstCrossAllocation agent ∪
          (secondCrossAllocation agent ∪ outsideAllocation agent)))
      (core ∪ (firstCross ∪ (secondCross ∪ outside))) :=
    isAllocationOf_union coreAllocation
      (fun agent => firstCrossAllocation agent ∪
        (secondCrossAllocation agent ∪ outsideAllocation agent))
      core (firstCross ∪ (secondCross ∪ outside)) hcoreRestDisjoint hcoreAllocation
      hfirstRestAllocation
  dsimp only [firstCrossAllocation, secondCrossAllocation] at hfull
  have hpool : core ∪ (firstCross ∪ (secondCross ∪ outside)) = chores := by
    simpa only [core, firstCross, secondCross, outside, Finset.union_assoc] using
      m2PairFibres_union_eq cost chores 0 1
  have hfull' : IsAllocationOf
      (fun agent => coreAllocation agent ∪
        ((allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)))
      (core ∪ (firstCross ∪ (secondCross ∪ outside))) := by
    simpa only [firstCross, secondCross] using hfull
  have hfinal := Eq.mp
    (congrArg (fun goods => IsAllocationOf
      (fun agent => coreAllocation agent ∪
        ((allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent))) goods) hpool) hfull'
  simpa only [Finset.union_assoc] using hfinal

/-- The corrective allocation in the residue-three cross-fiber subcase of
Lemma `M2properties`.  When the first pair agent owns only outside chores,
one such chore is moved to the smaller complementary bundle: the resulting
outside quotas are `q`, `q + 1 - c`, `q + 1`, and `q + 1`. -/
theorem existsM2PairCrossResidueThreeAllocation
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q c : ℕ)
    (hcore : (m2PairCoreFibre cost chores 0 1).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores 1 0).card = c)
    (houtside : (m2PairOutsideFibre cost chores 0 1).card = 4 * q + 3 - c)
    (hc : c ≤ q) :
    ∃ coreAllocation outsideAllocation : Allocation (Fin 4) Item,
      IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1) ∧
      (∀ agent, (coreAllocation agent).card = m2PairCoreQuota 0 1 0 0 agent) ∧
      IsAllocationOf outsideAllocation (m2PairOutsideFibre cost chores 0 1) ∧
      (∀ agent, (outsideAllocation agent).card =
        m2PairOutsideQuota q (q + 1 - c)
          (m2PairOutsideFibre cost chores 0 1).card agent) ∧
      IsAllocationOf
        (fun agent => coreAllocation agent ∪
          (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) chores := by
  apply existsM2PairSplitAllocation Item cost chores 0 0 q (q + 1 - c)
  · omega
  · rw [houtside]
    omega

/-- The corrected residue-three outside quotas have the displayed cardinality
shape: the two complementary agents each receive `q + 1` chores. -/
theorem m2PairCrossResidueThree_outsideQuota_shape (q c : ℕ) (hc : c ≤ q) :
    m2PairOutsideQuota q (q + 1 - c) (4 * q + 3 - c) 0 = q ∧
    m2PairOutsideQuota q (q + 1 - c) (4 * q + 3 - c) 1 = q + 1 - c ∧
    m2PairOutsideQuota q (q + 1 - c) (4 * q + 3 - c) 2 = q + 1 ∧
    m2PairOutsideQuota q (q + 1 - c) (4 * q + 3 - c) 3 = q + 1 := by
  simp [m2PairOutsideQuota]
  omega

private theorem m2PairSplitAllocation_two_eq_outside
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (hcoreEmpty : coreAllocation 2 = ∅) :
    (fun agent => coreAllocation agent ∪
      (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
        ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
          outsideAllocation agent)) 2 = outsideAllocation 2 := by
  simp [hcoreEmpty, allocateAllTo]

private theorem m2PairSplitAllocation_three_eq_outside
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (hcoreEmpty : coreAllocation 3 = ∅) :
    (fun agent => coreAllocation agent ∪
      (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
        ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
          outsideAllocation agent)) 3 = outsideAllocation 3 := by
  simp [hcoreEmpty, allocateAllTo]

private theorem m2PairSplitAllocation_two_card
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (firstOutside secondOutside : ℕ)
    (hcoreEmpty : coreAllocation 2 = ∅)
    (houtsideCard : (outsideAllocation 2).card =
      m2PairOutsideQuota firstOutside secondOutside
        (m2PairOutsideFibre cost chores 0 1).card 2) :
    ((fun agent => coreAllocation agent ∪
      (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
        ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
          outsideAllocation agent)) 2).card =
      m2PairOutsideQuota firstOutside secondOutside
        (m2PairOutsideFibre cost chores 0 1).card 2 := by
  rw [m2PairSplitAllocation_two_eq_outside cost chores coreAllocation outsideAllocation
    hcoreEmpty]
  exact houtsideCard

private theorem m2PairSplitAllocation_three_card
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (firstOutside secondOutside : ℕ)
    (hcoreEmpty : coreAllocation 3 = ∅)
    (houtsideCard : (outsideAllocation 3).card =
      m2PairOutsideQuota firstOutside secondOutside
        (m2PairOutsideFibre cost chores 0 1).card 3) :
    ((fun agent => coreAllocation agent ∪
      (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
        ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
          outsideAllocation agent)) 3).card =
      m2PairOutsideQuota firstOutside secondOutside
        (m2PairOutsideFibre cost chores 0 1).card 3 := by
  rw [m2PairSplitAllocation_three_eq_outside cost chores coreAllocation outsideAllocation
    hcoreEmpty]
  exact houtsideCard

/-- The complementary pair receives only its own-small fiber in the Case 3.1
split allocation. -/
private theorem m2PairSplitAllocation_two_ownSmall
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (hcoreEmpty : coreAllocation 2 = ∅)
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1))
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item) :
    ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 2,
      IsSmallChore cost 2 item := by
  intro item hitem
  have houtside : item ∈ outsideAllocation 2 := by
    rw [← m2PairSplitAllocation_two_eq_outside cost chores coreAllocation outsideAllocation
      hcoreEmpty]
    exact hitem
  have hpool : item ∈ m2PairOutsideFibre cost chores 0 1 :=
    houtsideAllocation.1 2 item houtside
  exact m2PairOutsideFibre_small_for_two cost chores item
    (htwo item (Finset.mem_filter.mp hpool).1) hpool

private theorem m2PairSplitAllocation_three_ownSmall
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (hcoreEmpty : coreAllocation 3 = ∅)
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1))
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item) :
    ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 3,
      IsSmallChore cost 3 item := by
  intro item hitem
  have houtside : item ∈ outsideAllocation 3 := by
    rw [← m2PairSplitAllocation_three_eq_outside cost chores coreAllocation outsideAllocation
      hcoreEmpty]
    exact hitem
  have hpool : item ∈ m2PairOutsideFibre cost chores 0 1 :=
    houtsideAllocation.1 3 item houtside
  exact m2PairOutsideFibre_small_for_three cost chores item
    (htwo item (Finset.mem_filter.mp hpool).1) hpool

/-- Agent 0's own large chores in the source Case 3.1 split are exactly her
assigned portion of the complementary (`34`) fiber. -/
private theorem m2PairSplitAllocation_zero_largeSet
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1)) :
    largeChoreSet cost r 0
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0) = outsideAllocation 0 := by
  have hleftSmall : ∀ item ∈ coreAllocation 0 ∪ m2PairCrossFibre cost chores 0 1,
      IsSmallChore cost 0 item := by
    intro item hitem
    rcases Finset.mem_union.mp hitem with hcore | hcross
    · have hpool : item ∈ m2PairCoreFibre cost chores 0 1 :=
        hcoreAllocation.1 0 item hcore
      exact isSmallChore_of_mem_smallAgentSet cost 0 item (Finset.mem_filter.mp hpool).2.1
    · exact isSmallChore_of_mem_smallAgentSet cost 0 item (Finset.mem_filter.mp hcross).2.1
  have hrightLarge : ∀ item ∈ outsideAllocation 0, IsLargeChore cost r 0 item := by
    intro item houtside
    have hpool : item ∈ m2PairOutsideFibre cost chores 0 1 :=
      houtsideAllocation.1 0 item houtside
    exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 0 item
      (Finset.mem_filter.mp hpool).2.1
  have hshape :
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0 =
        (coreAllocation 0 ∪ m2PairCrossFibre cost chores 0 1) ∪ outsideAllocation 0 := by
    simp [allocateAllTo, Finset.union_assoc]
  rw [hshape]
  exact largeChoreSet_union_eq_right_of_left_small_right_large cost r 0
    (coreAllocation 0 ∪ m2PairCrossFibre cost chores 0 1) (outsideAllocation 0)
    hr hleftSmall hrightLarge

/-- The cardinal version of the preceding large-set identity. -/
private theorem m2PairSplitAllocation_zero_largeCard
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (firstOutside : ℕ) (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1))
    (houtsideCard : (outsideAllocation 0).card = firstOutside) :
    (largeChoreSet cost r 0
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0)).card = firstOutside := by
  rw [m2PairSplitAllocation_zero_largeSet r cost chores coreAllocation outsideAllocation
    hr hcost hcoreAllocation houtsideAllocation, houtsideCard]

/-- From agent 0's perspective, agent 1's large chores are precisely agent
1's cross fiber and complementary-fiber portion. -/
private theorem m2PairSplitAllocation_one_largeSet_for_zero
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1)) :
    largeChoreSet cost r 0
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1) =
      m2PairCrossFibre cost chores 1 0 ∪ outsideAllocation 1 := by
  have hleftSmall : ∀ item ∈ coreAllocation 1, IsSmallChore cost 0 item := by
    intro item hcore
    have hpool : item ∈ m2PairCoreFibre cost chores 0 1 :=
      hcoreAllocation.1 1 item hcore
    exact isSmallChore_of_mem_smallAgentSet cost 0 item (Finset.mem_filter.mp hpool).2.1
  have hrightLarge : ∀ item ∈
      m2PairCrossFibre cost chores 1 0 ∪ outsideAllocation 1,
      IsLargeChore cost r 0 item := by
    intro item hitem
    rcases Finset.mem_union.mp hitem with hcross | houtside
    · exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 0 item
        (Finset.mem_filter.mp hcross).2.2
    · have hpool : item ∈ m2PairOutsideFibre cost chores 0 1 :=
        houtsideAllocation.1 1 item houtside
      exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 0 item
        (Finset.mem_filter.mp hpool).2.1
  have hshape :
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1 =
        coreAllocation 1 ∪ (m2PairCrossFibre cost chores 1 0 ∪ outsideAllocation 1) := by
    simp [allocateAllTo]
  rw [hshape]
  exact largeChoreSet_union_eq_right_of_left_small_right_large cost r 0
    (coreAllocation 1) (m2PairCrossFibre cost chores 1 0 ∪ outsideAllocation 1)
    hr hleftSmall hrightLarge

private theorem m2PairSplitAllocation_zero_card
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (firstCore firstOutside : ℕ)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1))
    (hcoreCard : (coreAllocation 0).card = firstCore)
    (houtsideCard : (outsideAllocation 0).card = firstOutside) :
    ((fun agent => coreAllocation agent ∪
      (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
        ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
          outsideAllocation agent)) 0).card =
      firstCore + (m2PairCrossFibre cost chores 0 1).card + firstOutside := by
  let core := m2PairCoreFibre cost chores 0 1
  let cross := m2PairCrossFibre cost chores 0 1
  let outside := m2PairOutsideFibre cost chores 0 1
  have hcoreCross : Disjoint (coreAllocation 0) cross := by
    rw [Finset.disjoint_left]
    intro item hcore hcross
    have hcorePool : item ∈ core := hcoreAllocation.1 0 item hcore
    have hsmallOne := (Finset.mem_filter.mp hcorePool).2.2
    have hnotOne := (Finset.mem_filter.mp hcross).2.2
    exact (hnotOne hsmallOne).elim
  have hleftOutside : Disjoint (coreAllocation 0 ∪ cross) (outsideAllocation 0) := by
    rw [Finset.disjoint_left]
    intro item hleft houtside
    have houtsidePool : item ∈ outside := houtsideAllocation.1 0 item houtside
    have hnotZero := (Finset.mem_filter.mp houtsidePool).2.1
    rcases Finset.mem_union.mp hleft with hcore | hcross
    · have hcorePool : item ∈ core := hcoreAllocation.1 0 item hcore
      exact (hnotZero (Finset.mem_filter.mp hcorePool).2.1).elim
    · exact (hnotZero (Finset.mem_filter.mp hcross).2.1).elim
  have hshape :
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 cross) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0 =
        (coreAllocation 0 ∪ cross) ∪ outsideAllocation 0 := by
    simp [allocateAllTo, Finset.union_assoc]
  rw [show m2PairCrossFibre cost chores 0 1 = cross by rfl, hshape,
    Finset.card_union_of_disjoint hleftOutside, Finset.card_union_of_disjoint hcoreCross,
    hcoreCard, houtsideCard]

private theorem m2PairSplitAllocation_one_card
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (secondCore secondOutside : ℕ)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1))
    (hcoreCard : (coreAllocation 1).card = secondCore)
    (houtsideCard : (outsideAllocation 1).card = secondOutside) :
    ((fun agent => coreAllocation agent ∪
      (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
        ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
          outsideAllocation agent)) 1).card =
      secondCore + (m2PairCrossFibre cost chores 1 0).card + secondOutside := by
  let core := m2PairCoreFibre cost chores 0 1
  let cross := m2PairCrossFibre cost chores 1 0
  let outside := m2PairOutsideFibre cost chores 0 1
  have hcoreCross : Disjoint (coreAllocation 1) cross := by
    rw [Finset.disjoint_left]
    intro item hcore hcross
    have hcorePool : item ∈ core := hcoreAllocation.1 1 item hcore
    have hsmallZero := (Finset.mem_filter.mp hcorePool).2.1
    have hnotZero := (Finset.mem_filter.mp hcross).2.2
    exact (hnotZero hsmallZero).elim
  have hleftOutside : Disjoint (coreAllocation 1 ∪ cross) (outsideAllocation 1) := by
    rw [Finset.disjoint_left]
    intro item hleft houtside
    have houtsidePool : item ∈ outside := houtsideAllocation.1 1 item houtside
    have hnotOne := (Finset.mem_filter.mp houtsidePool).2.2
    rcases Finset.mem_union.mp hleft with hcore | hcross
    · have hcorePool : item ∈ core := hcoreAllocation.1 1 item hcore
      exact (hnotOne (Finset.mem_filter.mp hcorePool).2.2).elim
    · exact (hnotOne (Finset.mem_filter.mp hcross).2.1).elim
  have hshape :
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 cross) agent ∪ outsideAllocation agent)) 1 =
        (coreAllocation 1 ∪ cross) ∪ outsideAllocation 1 := by
    simp [allocateAllTo, Finset.union_assoc]
  rw [show m2PairCrossFibre cost chores 1 0 = cross by rfl, hshape,
    Finset.card_union_of_disjoint hleftOutside, Finset.card_union_of_disjoint hcoreCross,
    hcoreCard, houtsideCard]

private theorem m2PairSplitAllocation_one_largeCard_for_zero
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (secondOutside : ℕ) (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1))
    (houtsideCard : (outsideAllocation 1).card = secondOutside) :
    (largeChoreSet cost r 0
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1)).card =
      (m2PairCrossFibre cost chores 1 0).card + secondOutside := by
  rw [m2PairSplitAllocation_one_largeSet_for_zero r cost chores coreAllocation outsideAllocation
    hr hcost hcoreAllocation houtsideAllocation]
  have hdisjoint : Disjoint (m2PairCrossFibre cost chores 1 0) (outsideAllocation 1) := by
    rw [Finset.disjoint_left]
    intro item hcross houtside
    have houtsidePool : item ∈ m2PairOutsideFibre cost chores 0 1 :=
      houtsideAllocation.1 1 item houtside
    exact (Finset.disjoint_left.mp (m2PairCrossSecond_disjoint_outside cost chores 0 1)
      hcross houtsidePool).elim
  rw [Finset.card_union_of_disjoint hdisjoint, houtsideCard]

/-- The source Case 3.1 inequality `ℓ₁ ≤ c + ℓ₂` certifies every EFX
comparison from agent 0 to agent 1 for the constructed split allocation. -/
private theorem m2PairSplitAllocation_zero_to_one_efx
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (firstCore secondCore firstOutside secondOutside target : ℕ)
    (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1))
    (hcoreCard : ∀ agent, (coreAllocation agent).card =
      m2PairCoreQuota 0 1 firstCore secondCore agent)
    (houtsideCard : ∀ agent, (outsideAllocation agent).card =
      m2PairOutsideQuota firstOutside secondOutside
        (m2PairOutsideFibre cost chores 0 1).card agent)
    (hfirstTarget : (m2PairCrossFibre cost chores 0 1).card + firstCore + firstOutside = target)
    (hsecondTarget : (m2PairCrossFibre cost chores 1 0).card + secondCore + secondOutside = target)
    (hcomparison : firstOutside ≤ (m2PairCrossFibre cost chores 1 0).card + secondOutside) :
    ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0,
      additiveChoreCost cost 0
        ((fun agent => coreAllocation agent ∪
          (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
            ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
              outsideAllocation agent)) 0 \ {item}) ≤
        additiveChoreCost cost 0
          ((fun agent => coreAllocation agent ∪
            (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
              ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
                outsideAllocation agent)) 1) := by
  let allocation : Allocation (Fin 4) Item := fun agent => coreAllocation agent ∪
    (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
      ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
        outsideAllocation agent)
  have hcoreZero : (coreAllocation 0).card = firstCore := by
    simpa [m2PairCoreQuota] using hcoreCard 0
  have hcoreOne : (coreAllocation 1).card = secondCore := by
    simpa [m2PairCoreQuota] using hcoreCard 1
  have houtsideZero : (outsideAllocation 0).card = firstOutside := by
    simpa [m2PairOutsideQuota] using houtsideCard 0
  have houtsideOne : (outsideAllocation 1).card = secondOutside := by
    simpa [m2PairOutsideQuota] using houtsideCard 1
  have hallocationZero : (allocation 0).card = target := by
    rw [show allocation 0 =
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0 by rfl]
    rw [m2PairSplitAllocation_zero_card cost chores coreAllocation outsideAllocation
      firstCore firstOutside hcoreAllocation houtsideAllocation hcoreZero houtsideZero]
    omega
  have hallocationOne : (allocation 1).card = target := by
    rw [show allocation 1 =
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1 by rfl]
    rw [m2PairSplitAllocation_one_card cost chores coreAllocation outsideAllocation
      secondCore secondOutside hcoreAllocation houtsideAllocation hcoreOne houtsideOne]
    omega
  have hlargeZero : (largeChoreSet cost r 0 (allocation 0)).card = firstOutside := by
    rw [show allocation 0 =
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0 by rfl,
      m2PairSplitAllocation_zero_largeSet r cost chores coreAllocation outsideAllocation
        hr hcost hcoreAllocation houtsideAllocation, houtsideZero]
  have hlargeOne : (largeChoreSet cost r 0 (allocation 1)).card =
      (m2PairCrossFibre cost chores 1 0).card + secondOutside := by
    rw [show allocation 1 =
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1 by rfl]
    exact m2PairSplitAllocation_one_largeCard_for_zero r cost chores coreAllocation
      outsideAllocation secondOutside hr hcost hcoreAllocation houtsideAllocation houtsideOne
  change ∀ item ∈ allocation 0, additiveChoreCost cost 0 (allocation 0 \ {item}) ≤
    additiveChoreCost cost 0 (allocation 1)
  exact additiveChoreCost_erase_le_of_largeCard cost r allocation 0 1 target firstOutside
    ((m2PairCrossFibre cost chores 1 0).card + secondOutside) hcost (by linarith)
    hallocationZero hallocationOne hlargeZero hlargeOne hcomparison

private theorem m2PairSplitAllocation_one_largeSet
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1)) :
    largeChoreSet cost r 1
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1) = outsideAllocation 1 := by
  have hleftSmall : ∀ item ∈ coreAllocation 1 ∪ m2PairCrossFibre cost chores 1 0,
      IsSmallChore cost 1 item := by
    intro item hitem
    rcases Finset.mem_union.mp hitem with hcore | hcross
    · have hpool : item ∈ m2PairCoreFibre cost chores 0 1 :=
        hcoreAllocation.1 1 item hcore
      exact isSmallChore_of_mem_smallAgentSet cost 1 item (Finset.mem_filter.mp hpool).2.2
    · exact isSmallChore_of_mem_smallAgentSet cost 1 item (Finset.mem_filter.mp hcross).2.1
  have hrightLarge : ∀ item ∈ outsideAllocation 1, IsLargeChore cost r 1 item := by
    intro item houtside
    have hpool : item ∈ m2PairOutsideFibre cost chores 0 1 :=
      houtsideAllocation.1 1 item houtside
    exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 1 item
      (Finset.mem_filter.mp hpool).2.2
  have hshape :
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1 =
        (coreAllocation 1 ∪ m2PairCrossFibre cost chores 1 0) ∪ outsideAllocation 1 := by
    simp [allocateAllTo, Finset.union_assoc]
  rw [hshape]
  exact largeChoreSet_union_eq_right_of_left_small_right_large cost r 1
    (coreAllocation 1 ∪ m2PairCrossFibre cost chores 1 0) (outsideAllocation 1)
    hr hleftSmall hrightLarge

private theorem m2PairSplitAllocation_zero_largeSet_for_one
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1)) :
    largeChoreSet cost r 1
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0) =
      m2PairCrossFibre cost chores 0 1 ∪ outsideAllocation 0 := by
  have hleftSmall : ∀ item ∈ coreAllocation 0, IsSmallChore cost 1 item := by
    intro item hcore
    have hpool : item ∈ m2PairCoreFibre cost chores 0 1 :=
      hcoreAllocation.1 0 item hcore
    exact isSmallChore_of_mem_smallAgentSet cost 1 item (Finset.mem_filter.mp hpool).2.2
  have hrightLarge : ∀ item ∈
      m2PairCrossFibre cost chores 0 1 ∪ outsideAllocation 0,
      IsLargeChore cost r 1 item := by
    intro item hitem
    rcases Finset.mem_union.mp hitem with hcross | houtside
    · exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 1 item
        (Finset.mem_filter.mp hcross).2.2
    · have hpool : item ∈ m2PairOutsideFibre cost chores 0 1 :=
        houtsideAllocation.1 0 item houtside
      exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 1 item
        (Finset.mem_filter.mp hpool).2.2
  have hshape :
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0 =
        coreAllocation 0 ∪ (m2PairCrossFibre cost chores 0 1 ∪ outsideAllocation 0) := by
    simp [allocateAllTo]
  rw [hshape]
  exact largeChoreSet_union_eq_right_of_left_small_right_large cost r 1
    (coreAllocation 0) (m2PairCrossFibre cost chores 0 1 ∪ outsideAllocation 0)
    hr hleftSmall hrightLarge

private theorem m2PairSplitAllocation_zero_largeCard_for_one
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (firstOutside : ℕ) (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1))
    (houtsideCard : (outsideAllocation 0).card = firstOutside) :
    (largeChoreSet cost r 1
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0)).card =
      (m2PairCrossFibre cost chores 0 1).card + firstOutside := by
  rw [m2PairSplitAllocation_zero_largeSet_for_one r cost chores coreAllocation outsideAllocation
    hr hcost hcoreAllocation houtsideAllocation]
  have hdisjoint : Disjoint (m2PairCrossFibre cost chores 0 1) (outsideAllocation 0) := by
    rw [Finset.disjoint_left]
    intro item hcross houtside
    have houtsidePool : item ∈ m2PairOutsideFibre cost chores 0 1 :=
      houtsideAllocation.1 0 item houtside
    exact (Finset.disjoint_left.mp (m2PairCrossFirst_disjoint_crossSecond_outside cost chores 0 1)
      hcross (Finset.mem_union_right _ houtsidePool)).elim
  rw [Finset.card_union_of_disjoint hdisjoint, houtsideCard]

/-- The source Case 3.1 inequality `ℓ₂ ≤ b + ℓ₁` certifies every EFX
comparison from agent 1 to agent 0 for the constructed split allocation. -/
private theorem m2PairSplitAllocation_one_to_zero_efx
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (firstCore secondCore firstOutside secondOutside target : ℕ)
    (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1))
    (hcoreCard : ∀ agent, (coreAllocation agent).card =
      m2PairCoreQuota 0 1 firstCore secondCore agent)
    (houtsideCard : ∀ agent, (outsideAllocation agent).card =
      m2PairOutsideQuota firstOutside secondOutside
        (m2PairOutsideFibre cost chores 0 1).card agent)
    (hfirstTarget : (m2PairCrossFibre cost chores 0 1).card + firstCore + firstOutside = target)
    (hsecondTarget : (m2PairCrossFibre cost chores 1 0).card + secondCore + secondOutside = target)
    (hcomparison : secondOutside ≤ (m2PairCrossFibre cost chores 0 1).card + firstOutside) :
    ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1,
      additiveChoreCost cost 1
        ((fun agent => coreAllocation agent ∪
          (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
            ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
              outsideAllocation agent)) 1 \ {item}) ≤
        additiveChoreCost cost 1
          ((fun agent => coreAllocation agent ∪
            (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
              ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
                outsideAllocation agent)) 0) := by
  let allocation : Allocation (Fin 4) Item := fun agent => coreAllocation agent ∪
    (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
      ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
        outsideAllocation agent)
  have hcoreZero : (coreAllocation 0).card = firstCore := by
    simpa [m2PairCoreQuota] using hcoreCard 0
  have hcoreOne : (coreAllocation 1).card = secondCore := by
    simpa [m2PairCoreQuota] using hcoreCard 1
  have houtsideZero : (outsideAllocation 0).card = firstOutside := by
    simpa [m2PairOutsideQuota] using houtsideCard 0
  have houtsideOne : (outsideAllocation 1).card = secondOutside := by
    simpa [m2PairOutsideQuota] using houtsideCard 1
  have hallocationZero : (allocation 0).card = target := by
    rw [show allocation 0 =
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0 by rfl]
    rw [m2PairSplitAllocation_zero_card cost chores coreAllocation outsideAllocation
      firstCore firstOutside hcoreAllocation houtsideAllocation hcoreZero houtsideZero]
    omega
  have hallocationOne : (allocation 1).card = target := by
    rw [show allocation 1 =
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1 by rfl]
    rw [m2PairSplitAllocation_one_card cost chores coreAllocation outsideAllocation
      secondCore secondOutside hcoreAllocation houtsideAllocation hcoreOne houtsideOne]
    omega
  have hlargeOne : (largeChoreSet cost r 1 (allocation 1)).card = secondOutside := by
    rw [show allocation 1 =
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1 by rfl,
      m2PairSplitAllocation_one_largeSet r cost chores coreAllocation outsideAllocation
        hr hcost hcoreAllocation houtsideAllocation, houtsideOne]
  have hlargeZero : (largeChoreSet cost r 1 (allocation 0)).card =
      (m2PairCrossFibre cost chores 0 1).card + firstOutside := by
    rw [show allocation 0 =
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0 by rfl]
    exact m2PairSplitAllocation_zero_largeCard_for_one r cost chores coreAllocation
      outsideAllocation firstOutside hr hcost hcoreAllocation houtsideAllocation houtsideZero
  change ∀ item ∈ allocation 1, additiveChoreCost cost 1 (allocation 1 \ {item}) ≤
    additiveChoreCost cost 1 (allocation 0)
  exact additiveChoreCost_erase_le_of_largeCard cost r allocation 1 0 target secondOutside
    ((m2PairCrossFibre cost chores 0 1).card + firstOutside) hcost (by linarith)
    hallocationOne hallocationZero hlargeOne hlargeZero hcomparison

/-- In the labelled Case 3.1 allocation, agents `2` and `3` receive only
chores from the fiber that is large for both members of the deficient pair.
This is the cost-label half of the source's comparisons from agents `0,1` to
the complementary pair. -/
private theorem m2PairSplitAllocation_outside_allLarge
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (evaluator recipient : Fin 4) (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1))
    (hevaluator : evaluator = 0 ∨ evaluator = 1)
    (hrecipient : recipient = 2 ∨ recipient = 3)
    (hcoreEmpty : coreAllocation recipient = ∅) :
    ∀ item ∈ m2PairSplitAllocation cost chores coreAllocation outsideAllocation recipient,
      IsLargeChore cost r evaluator item := by
  intro item hitem
  have houtside : item ∈ outsideAllocation recipient := by
    rcases hrecipient with rfl | rfl
    · change item ∈
        (fun agent => coreAllocation agent ∪
          (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
            ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
              outsideAllocation agent)) 2 at hitem
      rw [m2PairSplitAllocation_two_eq_outside cost chores coreAllocation outsideAllocation
        hcoreEmpty] at hitem
      exact hitem
    · change item ∈
        (fun agent => coreAllocation agent ∪
          (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
            ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
              outsideAllocation agent)) 3 at hitem
      rw [m2PairSplitAllocation_three_eq_outside cost chores coreAllocation outsideAllocation
        hcoreEmpty] at hitem
      exact hitem
  have hpool : item ∈ m2PairOutsideFibre cost chores 0 1 :=
    houtsideAllocation.1 recipient item houtside
  rcases hevaluator with rfl | rfl
  · exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 0 item
      (Finset.mem_filter.mp hpool).2.1
  · exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 1 item
      (Finset.mem_filter.mp hpool).2.2

/-- If the `0`-cross fiber is empty, agent `0`'s labelled pair-split bundle
is exactly her core share together with her outside share.  The displayed
large-set identity isolates the single large core share used in Case 3.2.2. -/
private theorem m2PairSplitAllocation_zero_largeSet_of_crossFirstEmpty
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (evaluator : Fin 4) (hr : 1 < r)
    (hcrossEmpty : m2PairCrossFibre cost chores 0 1 = ∅)
    (hcoreLarge : ∀ item ∈ coreAllocation 0, IsLargeChore cost r evaluator item)
    (houtsideSmall : ∀ item ∈ outsideAllocation 0, IsSmallChore cost evaluator item) :
    largeChoreSet cost r evaluator
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0) = coreAllocation 0 := by
  have hshape :
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0 = coreAllocation 0 ∪ outsideAllocation 0 := by
    simp [allocateAllTo, hcrossEmpty]
  rw [hshape]
  exact largeChoreSet_union_eq_left_of_left_large_right_small cost r evaluator
    (coreAllocation 0) (outsideAllocation 0) hr hcoreLarge houtsideSmall

/-- If agent `1`'s core and cross shares are empty, her pair-split bundle is
entirely in the outside fiber and hence is all large for her.  This is the
source Case 3.2.2 bundle of `ℓ₂` type-`34` chores. -/
private theorem m2PairSplitAllocation_one_allLarge_of_crossSecondEmpty
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (hcost : IsOneOrRChoreCost cost r)
    (hcoreEmpty : coreAllocation 1 = ∅)
    (hcrossEmpty : m2PairCrossFibre cost chores 1 0 = ∅)
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1)) :
    ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1,
      IsLargeChore cost r 1 item := by
  intro item hitem
  have houtside : item ∈ outsideAllocation 1 := by
    simpa [allocateAllTo, hcoreEmpty, hcrossEmpty] using hitem
  have hpool : item ∈ m2PairOutsideFibre cost chores 0 1 :=
    houtsideAllocation.1 1 item houtside
  exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 1 item
    (Finset.mem_filter.mp hpool).2.2

/-- The direct source cost calculation `c_3(B_1)=c_4(B_1)=r+ℓ_1` in Case
3.2.2.  It applies whenever agent `0` has one core chore and `p` outside
chores, with no first cross-fiber chore. -/
private theorem m2PairSplitAllocation_zero_cost_of_coreLarge_outsideSmall
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (evaluator : Fin 4) (p : ℕ) (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1))
    (hcrossEmpty : m2PairCrossFibre cost chores 0 1 = ∅)
    (hcoreCard : (coreAllocation 0).card = 1)
    (houtsideCard : (outsideAllocation 0).card = p)
    (hcoreLarge : ∀ item ∈ coreAllocation 0, IsLargeChore cost r evaluator item)
    (houtsideSmall : ∀ item ∈ outsideAllocation 0, IsSmallChore cost evaluator item) :
    additiveChoreCost cost evaluator
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0) = r + p := by
  have hcard :
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0).card = p + 1 := by
    rw [m2PairSplitAllocation_zero_card cost chores coreAllocation outsideAllocation 1 p
      hcoreAllocation houtsideAllocation hcoreCard houtsideCard, hcrossEmpty]
    simp
    omega
  have hlarge : largeChoreSet cost r evaluator
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0) = coreAllocation 0 :=
    m2PairSplitAllocation_zero_largeSet_of_crossFirstEmpty r cost chores coreAllocation
      outsideAllocation evaluator hr hcrossEmpty hcoreLarge houtsideSmall
  rw [additiveChoreCost_eq_card_add_largeCard cost r evaluator _ hcost, hcard, hlarge,
    hcoreCard]
  norm_num
  ring

/-- The general Case 3.2 cost calculation for agent `0`'s bundle when its
core chores are large and its outside chores are small for a third evaluator.
It extends the one-core-chore calculation used in Case 3.2.2. -/
private theorem m2PairSplitAllocation_zero_cost_of_coreLarge_outsideSmall_general
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (evaluator : Fin 4) (coreCount outsideCount : ℕ) (hr : 1 < r)
    (hcost : IsOneOrRChoreCost cost r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1))
    (hcrossEmpty : m2PairCrossFibre cost chores 0 1 = ∅)
    (hcoreCard : (coreAllocation 0).card = coreCount)
    (houtsideCard : (outsideAllocation 0).card = outsideCount)
    (hcoreLarge : ∀ item ∈ coreAllocation 0, IsLargeChore cost r evaluator item)
    (houtsideSmall : ∀ item ∈ outsideAllocation 0, IsSmallChore cost evaluator item) :
    additiveChoreCost cost evaluator
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 0) =
        (coreCount : ℝ) * r + outsideCount := by
  have hcard :
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 0).card =
        coreCount + outsideCount := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0).card = coreCount + outsideCount
    rw [m2PairSplitAllocation_zero_card cost chores coreAllocation outsideAllocation
      coreCount outsideCount hcoreAllocation houtsideAllocation hcoreCard houtsideCard,
      hcrossEmpty]
    simp
  have hlarge : largeChoreSet cost r evaluator
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 0) = coreAllocation 0 := by
    change largeChoreSet cost r evaluator
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0) = coreAllocation 0
    exact m2PairSplitAllocation_zero_largeSet_of_crossFirstEmpty r cost chores coreAllocation
      outsideAllocation evaluator hr hcrossEmpty hcoreLarge houtsideSmall
  rw [additiveChoreCost_eq_card_add_largeCard cost r evaluator _ hcost, hcard, hlarge,
    hcoreCard]
  norm_num
  ring

/-- The symmetric general Case 3.2 calculation for agent `1`'s bundle.  The
second cross fiber is empty, so this bundle is exactly its core share together
with its outside share. -/
private theorem m2PairSplitAllocation_one_cost_of_coreLarge_outsideSmall_general
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (evaluator : Fin 4) (coreCount outsideCount : ℕ) (hr : 1 < r)
    (hcost : IsOneOrRChoreCost cost r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1))
    (hcrossEmpty : m2PairCrossFibre cost chores 1 0 = ∅)
    (hcoreCard : (coreAllocation 1).card = coreCount)
    (houtsideCard : (outsideAllocation 1).card = outsideCount)
    (hcoreLarge : ∀ item ∈ coreAllocation 1, IsLargeChore cost r evaluator item)
    (houtsideSmall : ∀ item ∈ outsideAllocation 1, IsSmallChore cost evaluator item) :
    additiveChoreCost cost evaluator
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 1) =
        (coreCount : ℝ) * r + outsideCount := by
  have hcard :
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 1).card =
        coreCount + outsideCount := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1).card = coreCount + outsideCount
    rw [m2PairSplitAllocation_one_card cost chores coreAllocation outsideAllocation
      coreCount outsideCount hcoreAllocation houtsideAllocation hcoreCard houtsideCard,
      hcrossEmpty]
    simp
  have hshape :
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 1) =
        coreAllocation 1 ∪ outsideAllocation 1 := by
    simp [m2PairSplitAllocation, allocateAllTo, hcrossEmpty]
  have hlarge : largeChoreSet cost r evaluator
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 1) = coreAllocation 1 := by
    rw [hshape]
    exact largeChoreSet_union_eq_left_of_left_large_right_small cost r evaluator
      (coreAllocation 1) (outsideAllocation 1) hr hcoreLarge houtsideSmall
  rw [additiveChoreCost_eq_card_add_largeCard cost r evaluator _ hcost, hcard, hlarge,
    hcoreCard]
  norm_num
  ring

/-- The complete EFX verification for the labelled source Case 3.1 allocation.
The cardinality hypotheses are exactly the two parts supplied by the paper's
integer split: agents `0,1` have target size `T`, while each complementary
bundle has at least `T - 1` chores and is balanced against every bundle it may
compare to.  The theorem keeps those numerical consequences explicit so the
subsequent source arithmetic and relabelling steps remain independently
auditable. -/
theorem efxOfM2PairSplitOfCardBounds
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (firstCore secondCore firstOutside secondOutside target : ℕ)
    (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1))
    (hcoreCard : ∀ agent, (coreAllocation agent).card =
      m2PairCoreQuota 0 1 firstCore secondCore agent)
    (houtsideCard : ∀ agent, (outsideAllocation agent).card =
      m2PairOutsideQuota firstOutside secondOutside
        (m2PairOutsideFibre cost chores 0 1).card agent)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hfirstTarget : (m2PairCrossFibre cost chores 0 1).card + firstCore + firstOutside = target)
    (hsecondTarget : (m2PairCrossFibre cost chores 1 0).card + secondCore + secondOutside = target)
    (hzeroToOne : firstOutside ≤ (m2PairCrossFibre cost chores 1 0).card + secondOutside)
    (honeToZero : secondOutside ≤ (m2PairCrossFibre cost chores 0 1).card + firstOutside)
    (houtsideTwoCard : target - 1 ≤ (outsideAllocation 2).card)
    (houtsideThreeCard : target - 1 ≤ (outsideAllocation 3).card)
    (hcomplementaryCard : ∀ i j, (i = 2 ∨ i = 3) →
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation i).card ≤
        (m2PairSplitAllocation cost chores coreAllocation outsideAllocation j).card + 1) :
    EFXForChores (additiveChoreCost cost)
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation) := by
  let allocation := m2PairSplitAllocation cost chores coreAllocation outsideAllocation
  have hcoreZero : (coreAllocation 0).card = firstCore := by
    simpa [m2PairCoreQuota] using hcoreCard 0
  have hcoreOne : (coreAllocation 1).card = secondCore := by
    simpa [m2PairCoreQuota] using hcoreCard 1
  have hcoreTwoCard : (coreAllocation 2).card = 0 := by
    simpa [m2PairCoreQuota] using hcoreCard 2
  have hcoreThreeCard : (coreAllocation 3).card = 0 := by
    simpa [m2PairCoreQuota] using hcoreCard 3
  have hcoreTwoEmpty : coreAllocation 2 = ∅ := Finset.card_eq_zero.mp hcoreTwoCard
  have hcoreThreeEmpty : coreAllocation 3 = ∅ := Finset.card_eq_zero.mp hcoreThreeCard
  have houtsideZero : (outsideAllocation 0).card = firstOutside := by
    simpa [m2PairOutsideQuota] using houtsideCard 0
  have houtsideOne : (outsideAllocation 1).card = secondOutside := by
    simpa [m2PairOutsideQuota] using houtsideCard 1
  have hallocationZero : (allocation 0).card = target := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0).card = target
    rw [m2PairSplitAllocation_zero_card cost chores coreAllocation outsideAllocation
      firstCore firstOutside hcoreAllocation houtsideAllocation hcoreZero houtsideZero]
    omega
  have hallocationOne : (allocation 1).card = target := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1).card = target
    rw [m2PairSplitAllocation_one_card cost chores coreAllocation outsideAllocation
      secondCore secondOutside hcoreAllocation houtsideAllocation hcoreOne houtsideOne]
    omega
  have hallocationTwo : target - 1 ≤ (allocation 2).card := by
    change target - 1 ≤
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 2).card
    rw [m2PairSplitAllocation_two_eq_outside cost chores coreAllocation outsideAllocation
      hcoreTwoEmpty]
    exact houtsideTwoCard
  have hallocationThree : target - 1 ≤ (allocation 3).card := by
    change target - 1 ≤
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 3).card
    rw [m2PairSplitAllocation_three_eq_outside cost chores coreAllocation outsideAllocation
      hcoreThreeEmpty]
    exact houtsideThreeCard
  have hlargeZero : (largeChoreSet cost r 0 (allocation 0)).card = firstOutside := by
    change (largeChoreSet cost r 0
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0)).card = firstOutside
    rw [m2PairSplitAllocation_zero_largeSet r cost chores coreAllocation outsideAllocation
      hr hcost hcoreAllocation houtsideAllocation, houtsideZero]
  have hlargeOne : (largeChoreSet cost r 1 (allocation 1)).card = secondOutside := by
    change (largeChoreSet cost r 1
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1)).card = secondOutside
    rw [m2PairSplitAllocation_one_largeSet r cost chores coreAllocation outsideAllocation
      hr hcost hcoreAllocation houtsideAllocation, houtsideOne]
  have hzeroToOne' : ∀ item ∈ allocation 0,
      additiveChoreCost cost 0 (allocation 0 \ {item}) ≤ additiveChoreCost cost 0 (allocation 1) := by
    change ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0,
      additiveChoreCost cost 0
        ((fun agent => coreAllocation agent ∪
          (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
            ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
              outsideAllocation agent)) 0 \ {item}) ≤
        additiveChoreCost cost 0
          ((fun agent => coreAllocation agent ∪
            (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
              ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
                outsideAllocation agent)) 1)
    exact m2PairSplitAllocation_zero_to_one_efx r cost chores coreAllocation outsideAllocation
      firstCore secondCore firstOutside secondOutside target hr hcost hcoreAllocation
      houtsideAllocation hcoreCard houtsideCard hfirstTarget hsecondTarget hzeroToOne
  have honeToZero' : ∀ item ∈ allocation 1,
      additiveChoreCost cost 1 (allocation 1 \ {item}) ≤ additiveChoreCost cost 1 (allocation 0) := by
    change ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1,
      additiveChoreCost cost 1
        ((fun agent => coreAllocation agent ∪
          (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
            ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
              outsideAllocation agent)) 1 \ {item}) ≤
        additiveChoreCost cost 1
          ((fun agent => coreAllocation agent ∪
            (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
              ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
                outsideAllocation agent)) 0)
    exact m2PairSplitAllocation_one_to_zero_efx r cost chores coreAllocation outsideAllocation
      firstCore secondCore firstOutside secondOutside target hr hcost hcoreAllocation
      houtsideAllocation hcoreCard houtsideCard hfirstTarget hsecondTarget honeToZero
  have htwoSmall : ∀ item ∈ allocation 2, IsSmallChore cost 2 item := by
    change ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 2,
      IsSmallChore cost 2 item
    exact m2PairSplitAllocation_two_ownSmall cost chores coreAllocation outsideAllocation
      hcoreTwoEmpty houtsideAllocation htwo
  have hthreeSmall : ∀ item ∈ allocation 3, IsSmallChore cost 3 item := by
    change ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 3,
      IsSmallChore cost 3 item
    exact m2PairSplitAllocation_three_ownSmall cost chores coreAllocation outsideAllocation
      hcoreThreeEmpty houtsideAllocation htwo
  have hzeroToTwoLarge : ∀ item ∈ allocation 2, IsLargeChore cost r 0 item :=
    m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 0 2
      hr hcost hcoreAllocation houtsideAllocation (Or.inl rfl) (Or.inl rfl) hcoreTwoEmpty
  have hzeroToThreeLarge : ∀ item ∈ allocation 3, IsLargeChore cost r 0 item :=
    m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 0 3
      hr hcost hcoreAllocation houtsideAllocation (Or.inl rfl) (Or.inr rfl) hcoreThreeEmpty
  have honeToTwoLarge : ∀ item ∈ allocation 2, IsLargeChore cost r 1 item :=
    m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 1 2
      hr hcost hcoreAllocation houtsideAllocation (Or.inr rfl) (Or.inl rfl) hcoreTwoEmpty
  have honeToThreeLarge : ∀ item ∈ allocation 3, IsLargeChore cost r 1 item :=
    m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 1 3
      hr hcost hcoreAllocation houtsideAllocation (Or.inr rfl) (Or.inr rfl) hcoreThreeEmpty
  rw [efxForChores_iff_forall_doesNotStronglyEnvy]
  intro i j
  fin_cases i <;> fin_cases j
  · exact doesNotStronglyEnvyForChores_self_of_nonneg cost allocation 0
      (fun item => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 0 item)
  · exact Or.inr hzeroToOne'
  · exact Or.inr (additiveChoreCost_erase_le_of_allLarge_comparison cost r allocation 0 2
      target firstOutside hcost (by linarith) hallocationZero hlargeZero hzeroToTwoLarge
      hallocationTwo)
  · exact Or.inr (additiveChoreCost_erase_le_of_allLarge_comparison cost r allocation 0 3
      target firstOutside hcost (by linarith) hallocationZero hlargeZero hzeroToThreeLarge
      hallocationThree)
  · exact Or.inr honeToZero'
  · exact doesNotStronglyEnvyForChores_self_of_nonneg cost allocation 1
      (fun item => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 1 item)
  · exact Or.inr (additiveChoreCost_erase_le_of_allLarge_comparison cost r allocation 1 2
      target secondOutside hcost (by linarith) hallocationOne hlargeOne honeToTwoLarge
      hallocationTwo)
  · exact Or.inr (additiveChoreCost_erase_le_of_allLarge_comparison cost r allocation 1 3
      target secondOutside hcost (by linarith) hallocationOne hlargeOne honeToThreeLarge
      hallocationThree)
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 2 0 hcost
      (by linarith) htwoSmall (hcomplementaryCard 2 0 (Or.inl rfl))
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 2 1 hcost
      (by linarith) htwoSmall (hcomplementaryCard 2 1 (Or.inl rfl))
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 2 2 hcost
      (by linarith) htwoSmall (hcomplementaryCard 2 2 (Or.inl rfl))
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 2 3 hcost
      (by linarith) htwoSmall (hcomplementaryCard 2 3 (Or.inl rfl))
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 3 0 hcost
      (by linarith) hthreeSmall (hcomplementaryCard 3 0 (Or.inr rfl))
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 3 1 hcost
      (by linarith) hthreeSmall (hcomplementaryCard 3 1 (Or.inr rfl))
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 3 2 hcost
      (by linarith) hthreeSmall (hcomplementaryCard 3 2 (Or.inr rfl))
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 3 3 hcost
      (by linarith) hthreeSmall (hcomplementaryCard 3 3 (Or.inr rfl))

private theorem efxOfM2PairCrossResidueThreeSplit
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (q c : ℕ) (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1))
    (hcoreCard : ∀ agent, (coreAllocation agent).card = m2PairCoreQuota 0 1 0 0 agent)
    (houtsideCard : ∀ agent, (outsideAllocation agent).card =
      m2PairOutsideQuota q (q + 1 - c) (m2PairOutsideFibre cost chores 0 1).card agent)
    (hcrossFirstEmpty : m2PairCrossFibre cost chores 0 1 = ∅)
    (hcrossSecondCard : (m2PairCrossFibre cost chores 1 0).card = c)
    (houtsideCardinality : (m2PairOutsideFibre cost chores 0 1).card = 4 * q + 3 - c)
    (hc : c ≤ q) (hcpos : 0 < c) :
    EFXForChores (additiveChoreCost cost)
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation) := by
  let allocation := m2PairSplitAllocation cost chores coreAllocation outsideAllocation
  have hcoreZeroEmpty : coreAllocation 0 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 0
  have hcoreOneEmpty : coreAllocation 1 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 1
  have hcoreTwoEmpty : coreAllocation 2 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 2
  have hcoreThreeEmpty : coreAllocation 3 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 3
  have houtsideZero : (outsideAllocation 0).card = q := by
    simpa [m2PairOutsideQuota] using houtsideCard 0
  have houtsideOne : (outsideAllocation 1).card = q + 1 - c := by
    simpa [m2PairOutsideQuota] using houtsideCard 1
  have hquotaShape := m2PairCrossResidueThree_outsideQuota_shape q c hc
  have hcardZero : (allocation 0).card = q := by
    simp [allocation, m2PairSplitAllocation, allocateAllTo, hcoreZeroEmpty,
      hcrossFirstEmpty, houtsideZero]
  have hcardOne : (allocation 1).card = q + 1 := by
    have hcoreOne : (coreAllocation 1).card = 0 := by
      simpa [m2PairCoreQuota] using hcoreCard 1
    rw [show allocation 1 =
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1 by rfl,
      m2PairSplitAllocation_one_card cost chores coreAllocation outsideAllocation 0 (q + 1 - c)
        hcoreAllocation houtsideAllocation hcoreOne houtsideOne, hcrossSecondCard]
    omega
  have hcardTwo : (allocation 2).card = q + 1 := by
    rw [show allocation 2 =
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 2 by rfl,
      m2PairSplitAllocation_two_eq_outside cost chores coreAllocation outsideAllocation
        hcoreTwoEmpty, houtsideCard 2, houtsideCardinality, hquotaShape.2.2.1]
  have hcardThree : (allocation 3).card = q + 1 := by
    rw [show allocation 3 =
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 3 by rfl,
      m2PairSplitAllocation_three_eq_outside cost chores coreAllocation outsideAllocation
        hcoreThreeEmpty, houtsideCard 3, houtsideCardinality, hquotaShape.2.2.2]
  have hlargeZero : (largeChoreSet cost r 0 (allocation 0)).card = q := by
    change (largeChoreSet cost r 0
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0)).card = q
    exact m2PairSplitAllocation_zero_largeCard r cost chores coreAllocation outsideAllocation q
      (by linarith) hcost hcoreAllocation houtsideAllocation houtsideZero
  have hlargeOne : (largeChoreSet cost r 1 (allocation 1)).card = q + 1 - c := by
    change (largeChoreSet cost r 1
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1)).card = q + 1 - c
    rw [m2PairSplitAllocation_one_largeSet r cost chores coreAllocation outsideAllocation
      (by linarith) hcost hcoreAllocation houtsideAllocation, houtsideOne]
  have hzeroAllLarge : ∀ item ∈ allocation 0, IsLargeChore cost r 0 item := by
    intro item hitem
    have hout : item ∈ outsideAllocation 0 := by
      simpa [allocation, m2PairSplitAllocation, allocateAllTo, hcoreZeroEmpty, hcrossFirstEmpty]
        using hitem
    exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 0 item
      (Finset.mem_filter.mp (houtsideAllocation.1 0 item hout)).2.1
  have honeAllLargeForZero : ∀ item ∈ allocation 1, IsLargeChore cost r 0 item := by
    intro item hitem
    change item ∈ coreAllocation 1 ∪
      (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) 1 ∪
        ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) 1 ∪
          outsideAllocation 1) at hitem
    simp [allocateAllTo, hcoreOneEmpty] at hitem
    rcases hitem with hcross | hout
    · exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 0 item
        (Finset.mem_filter.mp hcross).2.2
    · exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 0 item
        (Finset.mem_filter.mp (houtsideAllocation.1 1 item hout)).2.1
  have hzeroAllLargeForOne : ∀ item ∈ allocation 0, IsLargeChore cost r 1 item := by
    intro item hitem
    have hout : item ∈ outsideAllocation 0 := by
      simpa [allocation, m2PairSplitAllocation, allocateAllTo, hcoreZeroEmpty, hcrossFirstEmpty]
        using hitem
    exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 1 item
      (Finset.mem_filter.mp (houtsideAllocation.1 0 item hout)).2.2
  have hzeroToTwoLarge := m2PairSplitAllocation_outside_allLarge r cost chores
    coreAllocation outsideAllocation 0 2 (by linarith) hcost hcoreAllocation houtsideAllocation
      (Or.inl rfl) (Or.inl rfl) hcoreTwoEmpty
  have hzeroToThreeLarge := m2PairSplitAllocation_outside_allLarge r cost chores
    coreAllocation outsideAllocation 0 3 (by linarith) hcost hcoreAllocation houtsideAllocation
      (Or.inl rfl) (Or.inr rfl) hcoreThreeEmpty
  have honeToTwoLarge := m2PairSplitAllocation_outside_allLarge r cost chores
    coreAllocation outsideAllocation 1 2 (by linarith) hcost hcoreAllocation houtsideAllocation
      (Or.inr rfl) (Or.inl rfl) hcoreTwoEmpty
  have honeToThreeLarge := m2PairSplitAllocation_outside_allLarge r cost chores
    coreAllocation outsideAllocation 1 3 (by linarith) hcost hcoreAllocation houtsideAllocation
      (Or.inr rfl) (Or.inr rfl) hcoreThreeEmpty
  have htwoSmall := m2PairSplitAllocation_two_ownSmall cost chores coreAllocation outsideAllocation
    hcoreTwoEmpty houtsideAllocation htwo
  have hthreeSmall := m2PairSplitAllocation_three_ownSmall cost chores coreAllocation outsideAllocation
    hcoreThreeEmpty houtsideAllocation htwo
  rw [efxForChores_iff_forall_doesNotStronglyEnvy]
  intro i j
  fin_cases i <;> fin_cases j
  · exact doesNotStronglyEnvyForChores_self_of_nonneg cost allocation 0
      (fun item => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 0 item)
  · exact Or.inr (additiveChoreCost_erase_le_of_allLarge_comparison cost r allocation 0 1 q q
      hcost (by linarith) hcardZero hlargeZero honeAllLargeForZero (by rw [hcardOne]; omega))
  · exact Or.inr (additiveChoreCost_erase_le_of_allLarge_comparison cost r allocation 0 2 q q
      hcost (by linarith) hcardZero hlargeZero hzeroToTwoLarge (by rw [hcardTwo]; omega))
  · exact Or.inr (additiveChoreCost_erase_le_of_allLarge_comparison cost r allocation 0 3 q q
      hcost (by linarith) hcardZero hlargeZero hzeroToThreeLarge (by rw [hcardThree]; omega))
  · exact Or.inr (additiveChoreCost_erase_le_of_allLarge_comparison cost r allocation 1 0
      (q + 1) (q + 1 - c) hcost (by linarith) hcardOne hlargeOne hzeroAllLargeForOne
      (by rw [hcardZero]; omega))
  · exact doesNotStronglyEnvyForChores_self_of_nonneg cost allocation 1
      (fun item => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 1 item)
  · exact Or.inr (additiveChoreCost_erase_le_of_allLarge_comparison cost r allocation 1 2
      (q + 1) (q + 1 - c) hcost (by linarith) hcardOne hlargeOne honeToTwoLarge
      (by rw [hcardTwo]; omega))
  · exact Or.inr (additiveChoreCost_erase_le_of_allLarge_comparison cost r allocation 1 3
      (q + 1) (q + 1 - c) hcost (by linarith) hcardOne hlargeOne honeToThreeLarge
      (by rw [hcardThree]; omega))
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 2 0 hcost
      (by linarith) htwoSmall (by omega)
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 2 1 hcost
      (by linarith) htwoSmall (by rw [hcardTwo, hcardOne]; omega)
  · exact doesNotStronglyEnvyForChores_self_of_nonneg cost allocation 2
      (fun item => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 2 item)
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 2 3 hcost
      (by linarith) htwoSmall (by rw [hcardTwo, hcardThree]; omega)
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 3 0 hcost
      (by linarith) hthreeSmall (by omega)
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 3 1 hcost
      (by linarith) hthreeSmall (by rw [hcardThree, hcardOne]; omega)
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 3 2 hcost
      (by linarith) hthreeSmall (by rw [hcardThree, hcardTwo]; omega)
  · exact doesNotStronglyEnvyForChores_self_of_nonneg cost allocation 3
      (fun item => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 3 item)

/-- Source's residue-three correction for a cross-fiber M2 allocation. -/
theorem existsEfxOfM2PairCrossResidueThree
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q c : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcore : (m2PairCoreFibre cost chores 0 1).card = 0)
    (hcrossFirst : (m2PairCrossFibre cost chores 0 1).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores 1 0).card = c)
    (houtside : (m2PairOutsideFibre cost chores 0 1).card = 4 * q + 3 - c)
    (hc : c ≤ q) (hcpos : 0 < c) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨coreAllocation, outsideAllocation, hcoreAllocation, hcoreCard,
    houtsideAllocation, houtsideCard, hallocation⟩ :=
    existsM2PairCrossResidueThreeAllocation Item cost chores q c hcore hcrossSecond houtside hc
  refine ⟨m2PairSplitAllocation cost chores coreAllocation outsideAllocation, ?_, ?_⟩
  · change IsAllocationOf
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) chores
    exact hallocation
  · exact efxOfM2PairCrossResidueThreeSplit r cost chores coreAllocation outsideAllocation q c hr
      hcost htwo hcoreAllocation houtsideAllocation hcoreCard houtsideCard
      (Finset.card_eq_zero.mp hcrossFirst) hcrossSecond houtside hc hcpos

/-- The corrected cross-fiber residue has the certificates required by
Lemma `M2properties`: agent `0` is all-large but envy-free, and every other
nonempty bundle contains a small chore for its owner. -/
theorem existsEfxOfM2PairCrossResidueThree_certified
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q c : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcore : (m2PairCoreFibre cost chores 0 1).card = 0)
    (hcrossFirst : (m2PairCrossFibre cost chores 0 1).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores 1 0).card = c)
    (houtside : (m2PairOutsideFibre cost chores 0 1).card = 4 * q + 3 - c)
    (hc : c ≤ q) (hcpos : 0 < c) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) := by
  classical
  obtain ⟨coreAllocation, outsideAllocation, hcoreAllocation, hcoreCard,
    houtsideAllocation, houtsideCard, hallocation⟩ :=
    existsM2PairCrossResidueThreeAllocation Item cost chores q c hcore hcrossSecond houtside hc
  let allocation := m2PairSplitAllocation cost chores coreAllocation outsideAllocation
  have hcrossFirstEmpty : m2PairCrossFibre cost chores 0 1 = ∅ :=
    Finset.card_eq_zero.mp hcrossFirst
  have hcoreZeroEmpty : coreAllocation 0 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 0
  have hcoreOneEmpty : coreAllocation 1 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 1
  have hcoreTwoEmpty : coreAllocation 2 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 2
  have hcoreThreeEmpty : coreAllocation 3 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 3
  have houtsideZero : (outsideAllocation 0).card = q := by
    simpa [m2PairOutsideQuota] using houtsideCard 0
  have houtsideOne : (outsideAllocation 1).card = q + 1 - c := by
    simpa [m2PairOutsideQuota] using houtsideCard 1
  have hquotaShape := m2PairCrossResidueThree_outsideQuota_shape q c hc
  have hcardZero : (allocation 0).card = q := by
    simp [allocation, m2PairSplitAllocation, allocateAllTo, hcoreZeroEmpty,
      hcrossFirstEmpty, houtsideZero]
  have hcardOne : (allocation 1).card = q + 1 := by
    have hcoreOne : (coreAllocation 1).card = 0 := by
      simpa [m2PairCoreQuota] using hcoreCard 1
    rw [show allocation 1 =
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1 by rfl,
      m2PairSplitAllocation_one_card cost chores coreAllocation outsideAllocation 0 (q + 1 - c)
        hcoreAllocation houtsideAllocation hcoreOne houtsideOne, hcrossSecond]
    omega
  have hcardTwo : (allocation 2).card = q + 1 := by
    rw [show allocation 2 =
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 2 by rfl,
      m2PairSplitAllocation_two_eq_outside cost chores coreAllocation outsideAllocation
        hcoreTwoEmpty, houtsideCard 2, houtside, hquotaShape.2.2.1]
  have hcardThree : (allocation 3).card = q + 1 := by
    rw [show allocation 3 =
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 3 by rfl,
      m2PairSplitAllocation_three_eq_outside cost chores coreAllocation outsideAllocation
        hcoreThreeEmpty, houtsideCard 3, houtside, hquotaShape.2.2.2]
  have hzeroAllLarge : ∀ item ∈ allocation 0, IsLargeChore cost r 0 item := by
    intro item hitem
    have hout : item ∈ outsideAllocation 0 := by
      simpa [allocation, m2PairSplitAllocation, allocateAllTo, hcoreZeroEmpty, hcrossFirstEmpty]
        using hitem
    exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 0 item
      (Finset.mem_filter.mp (houtsideAllocation.1 0 item hout)).2.1
  have honeAllLargeForZero : ∀ item ∈ allocation 1, IsLargeChore cost r 0 item := by
    intro item hitem
    change item ∈ coreAllocation 1 ∪
      (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) 1 ∪
        ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) 1 ∪
          outsideAllocation 1) at hitem
    simp [allocateAllTo, hcoreOneEmpty] at hitem
    rcases hitem with hcross | hout
    · exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 0 item
        (Finset.mem_filter.mp hcross).2.2
    · exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 0 item
        (Finset.mem_filter.mp (houtsideAllocation.1 1 item hout)).2.1
  have hzeroToTwoLarge := m2PairSplitAllocation_outside_allLarge r cost chores
    coreAllocation outsideAllocation 0 2 (by linarith) hcost hcoreAllocation houtsideAllocation
      (Or.inl rfl) (Or.inl rfl) hcoreTwoEmpty
  have hzeroToThreeLarge := m2PairSplitAllocation_outside_allLarge r cost chores
    coreAllocation outsideAllocation 0 3 (by linarith) hcost hcoreAllocation houtsideAllocation
      (Or.inl rfl) (Or.inr rfl) hcoreThreeEmpty
  have htwoSmall := m2PairSplitAllocation_two_ownSmall cost chores coreAllocation outsideAllocation
    hcoreTwoEmpty houtsideAllocation htwo
  have hthreeSmall := m2PairSplitAllocation_three_ownSmall cost chores coreAllocation outsideAllocation
    hcoreThreeEmpty houtsideAllocation htwo
  have halloc : IsAllocationOf allocation chores := by
    change IsAllocationOf
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) chores
    exact hallocation
  have hefx := efxOfM2PairCrossResidueThreeSplit r cost chores coreAllocation outsideAllocation q c
    hr hcost htwo hcoreAllocation houtsideAllocation hcoreCard houtsideCard hcrossFirstEmpty
    hcrossSecond houtside hc hcpos
  refine ⟨allocation, halloc, hefx, ?_, ?_⟩
  · intro i hsmall
    exact smallItemCertificate_of_efx Item cost allocation hefx i hsmall
  · intro i hallLarge j
    fin_cases i
    · fin_cases j
      · exact le_rfl
      · change additiveChoreCost cost 0 (allocation 0) ≤ additiveChoreCost cost 0 (allocation 1)
        rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 (allocation 0) r hzeroAllLarge,
          additiveChoreCost_eq_card_nsmul_of_constant cost 0 (allocation 1) r honeAllLargeForZero,
          hcardZero, hcardOne]
        simp only [nsmul_eq_mul]
        have hq : (q : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ q
        exact mul_le_mul_of_nonneg_right hq (by linarith)
      · change additiveChoreCost cost 0 (allocation 0) ≤ additiveChoreCost cost 0 (allocation 2)
        rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 (allocation 0) r hzeroAllLarge,
          additiveChoreCost_eq_card_nsmul_of_constant cost 0 (allocation 2) r hzeroToTwoLarge,
          hcardZero, hcardTwo]
        simp only [nsmul_eq_mul]
        have hq : (q : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ q
        exact mul_le_mul_of_nonneg_right hq (by linarith)
      · change additiveChoreCost cost 0 (allocation 0) ≤ additiveChoreCost cost 0 (allocation 3)
        rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 (allocation 0) r hzeroAllLarge,
          additiveChoreCost_eq_card_nsmul_of_constant cost 0 (allocation 3) r hzeroToThreeLarge,
          hcardZero, hcardThree]
        simp only [nsmul_eq_mul]
        have hq : (q : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ q
        exact mul_le_mul_of_nonneg_right hq (by linarith)
    · exfalso
      have hcrossNonempty : (m2PairCrossFibre cost chores 1 0).Nonempty := by
        apply Finset.card_pos.mp
        rw [hcrossSecond]
        exact hcpos
      obtain ⟨item, hitem⟩ := hcrossNonempty
      have hitemAllocation : item ∈ allocation 1 := by
        change item ∈ coreAllocation 1 ∪
          (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) 1 ∪
            ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) 1 ∪
              outsideAllocation 1)
        simp [allocateAllTo, hitem]
      have hsmall : IsSmallChore cost 1 item :=
        isSmallChore_of_mem_smallAgentSet cost 1 item
          (Finset.mem_filter.mp hitem).2.1
      have hlarge : cost 1 item = r := by
        simpa [IsLargeChore] using hallLarge item hitemAllocation
      rw [IsSmallChore] at hsmall
      linarith
    · have hempty : allocation 2 = ∅ := by
        by_contra hnotempty
        obtain ⟨item, hitem⟩ := Finset.nonempty_iff_ne_empty.mpr hnotempty
        have hsmall := htwoSmall item hitem
        have hlarge : cost 2 item = r := by
          simpa [IsLargeChore] using hallLarge item hitem
        rw [IsSmallChore] at hsmall
        linarith
      change additiveChoreCost cost 2 (allocation 2) ≤ additiveChoreCost cost 2 (allocation j)
      rw [hempty]
      simp only [additiveChoreCost, Finset.sum_empty]
      exact additiveChoreCost_nonneg cost
        (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 2 (allocation j)
    · have hempty : allocation 3 = ∅ := by
        by_contra hnotempty
        obtain ⟨item, hitem⟩ := Finset.nonempty_iff_ne_empty.mpr hnotempty
        have hsmall := hthreeSmall item hitem
        have hlarge : cost 3 item = r := by
          simpa [IsLargeChore] using hallLarge item hitem
        rw [IsSmallChore] at hsmall
        linarith
      change additiveChoreCost cost 3 (allocation 3) ≤ additiveChoreCost cost 3 (allocation j)
      rw [hempty]
      simp only [additiveChoreCost, Finset.sum_empty]
      exact additiveChoreCost_nonneg cost
        (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 3 (allocation j)

/-- The corrected cross-fiber residue and its M2-properties certificates
transport along the finite relabelling of an arbitrary ordered pair. -/
theorem existsEfxOfM2PairCrossResidueThree_certified_relabel
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4) (q c : ℕ)
    (hdistinct : first ≠ second) (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcore : (m2PairCoreFibre cost chores first second).card = 0)
    (hcrossFirst : (m2PairCrossFibre cost chores first second).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores second first).card = c)
    (houtside : (m2PairOutsideFibre cost chores first second).card = 4 * q + 3 - c)
    (hc : c ≤ q) (hcpos : 0 < c) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) := by
  classical
  obtain ⟨labels, hzero, hone⟩ := existsFin4Equiv_map_zero_one first second hdistinct
  obtain ⟨labelledAllocation, hlabelledAllocation, hlabelledEfx, hsmallCertificate,
    hlargeCertificate⟩ :=
    existsEfxOfM2PairCrossResidueThree_certified Item r (relabelChoreCost labels cost) chores q c
      hr (IsOneOrRChoreCost.relabel labels cost r hcost)
      (by
        intro item hitem
        exact IsSmallForExactlyTwo.relabel labels cost item (htwo item hitem))
      (by
        rw [m2PairCoreFibre_relabel_zero_one labels cost chores first second hzero hone]
        exact hcore)
      (by
        obtain ⟨hfirst, hsecond⟩ :=
          m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
        rw [hfirst]
        exact hcrossFirst)
      (by
        obtain ⟨hfirst, hsecond⟩ :=
          m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
        rw [hsecond]
        exact hcrossSecond)
      (by
        rw [m2PairOutsideFibre_relabel_zero_one labels cost chores first second hzero hone]
        exact houtside)
      hc hcpos
  let allocation := relabelAllocation labels.symm labelledAllocation
  have halloc : IsAllocationOf allocation chores := hlabelledAllocation.relabel labels.symm
  have hefx : EFXForChores (additiveChoreCost cost) allocation := by
    have htransport := hlabelledEfx.relabel labels.symm
    have hcostEq : relabelChoreCost labels.symm (relabelChoreCost labels cost) = cost := by
      funext agent item
      simp [relabelChoreCost]
    rw [hcostEq] at htransport
    exact htransport
  refine ⟨allocation, halloc, hefx, ?_, ?_⟩
  · intro i hsmall j
    rcases hsmall with ⟨item, hitem, hitemSmall⟩
    have hlabelledSmall : ∃ item ∈ labelledAllocation (labels.symm i),
        IsSmallChore (relabelChoreCost labels cost) (labels.symm i) item := by
      refine ⟨item, ?_, ?_⟩
      · simpa [allocation, relabelAllocation] using hitem
      · simpa [relabelChoreCost, IsSmallChore] using hitemSmall
    have hcomparison := hsmallCertificate (labels.symm i) hlabelledSmall (labels.symm j)
    simpa [allocation, relabelAllocation, relabelChoreCost, additiveChoreCost] using hcomparison
  · intro i hallLarge j
    have hlabelledLarge : ∀ item ∈ labelledAllocation (labels.symm i),
        IsLargeChore (relabelChoreCost labels cost) r (labels.symm i) item := by
      intro item hitem
      have hitemOriginal : item ∈ allocation i := by
        simpa [allocation, relabelAllocation] using hitem
      have hlarge := hallLarge item hitemOriginal
      simpa [relabelChoreCost, IsLargeChore] using hlarge
    have hcomparison := hlargeCertificate (labels.symm i) hlabelledLarge (labels.symm j)
    simpa [allocation, relabelAllocation, relabelChoreCost, additiveChoreCost] using hcomparison

/-- In the residue-three cross-fiber subcase of source Case 3.1, a vanishing
core and first cross fiber force the corrected allocation's cardinal
parameters.  This is the bridge from the Case 3.1 incidence data to the
cross-fiber correction. -/
theorem existsEfxOfM2PairCase31CrossResidueThree_certified
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4) (q : ℕ)
    (hdistinct : first ≠ second) (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcore : (m2PairCoreFibre cost chores first second).card = 0)
    (hcrossFirst : (m2PairCrossFibre cost chores first second).card = 0)
    (hdecompose : chores.card = 4 * q + 3)
    (hsecondCrossBound : 4 * (m2PairCrossFibre cost chores second first).card ≤ chores.card)
    (hcrossPresent : 0 < (m2PairCrossFibre cost chores first second).card +
      (m2PairCrossFibre cost chores second first).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) := by
  let c := (m2PairCrossFibre cost chores second first).card
  let f := (m2PairOutsideFibre cost chores first second).card
  have hcrossSecond : (m2PairCrossFibre cost chores second first).card = c := rfl
  have hcpos : 0 < c := by
    dsimp [c]
    rw [hcrossFirst] at hcrossPresent
    omega
  have hc : c ≤ q := by
    dsimp [c]
    rw [hdecompose] at hsecondCrossBound
    omega
  have houtside : (m2PairOutsideFibre cost chores first second).card = 4 * q + 3 - c := by
    have hsum := m2PairFibres_card_sum cost chores first second
    dsimp [c, f]
    rw [hcore, hcrossFirst, hdecompose] at hsum
    omega
  exact existsEfxOfM2PairCrossResidueThree_certified_relabel Item r cost chores first second q c
    hdistinct hr hcost htwo hcore hcrossFirst hcrossSecond houtside hc hcpos


/-- Source Case 3.2.1: if every remaining chore has one fixed small-agent
type, an arbitrary balanced cardinal split is EFX. -/
theorem existsEfxOfM2SingleSmallType
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q remainder : ℕ) (smallAgents : Finset (Fin 4))
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hsmallType : ∀ item ∈ chores, smallAgentSet cost item = smallAgents)
    (hdecompose : chores.card = 4 * q + remainder) (hremainder : remainder < 4) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  classical
  obtain ⟨longAgents, hlongSubset, hlongCard⟩ :=
    (Finset.univ : Finset (Fin 4)).exists_subset_card_eq (by
      simpa using hremainder.le)
  obtain ⟨allocation, halloc, hcard⟩ :=
    existsAllocationOfQuota (Fin 4) Item chores (m2Quota q longAgents) (by
      rw [m2Quota_sum, hlongCard, hdecompose])
  refine ⟨allocation, halloc, efxOfM2SingleSmallTypeBalanced Item r cost chores allocation
    smallAgents hr hcost hsmallType halloc ?_⟩
  intro first second
  rw [hcard first, hcard second]
  exact m2Quota_balanced q longAgents first second

/-- In the fixed-type branch, choosing every long bundle inside the common
small-agent type gives the nonexceptional certificates from Lemma
`M2properties`: the complementary all-large agents have the short quota and
are therefore envy-free. -/
theorem existsEfxOfM2SingleSmallType_certified
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q remainder : ℕ) (smallAgents longAgents : Finset (Fin 4))
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hsmallType : ∀ item ∈ chores, smallAgentSet cost item = smallAgents)
    (hdecompose : chores.card = 4 * q + remainder) (hremainder : remainder < 4)
    (hlongSubset : longAgents ⊆ smallAgents) (hlongCard : longAgents.card = remainder) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ agent, agent ∉ smallAgents → ∀ other,
        additiveChoreCost cost agent (allocation agent) ≤
          additiveChoreCost cost agent (allocation other)) := by
  classical
  obtain ⟨allocation, halloc, hcard⟩ :=
    existsAllocationOfQuota (Fin 4) Item chores (m2Quota q longAgents) (by
      rw [m2Quota_sum, hlongCard, hdecompose])
  have hefx := efxOfM2SingleSmallTypeBalanced Item r cost chores allocation smallAgents hr hcost
    hsmallType halloc (by
      intro first second
      rw [hcard first, hcard second]
      exact m2Quota_balanced q longAgents first second)
  have houtsideFavorite : ∀ agent, agent ∉ smallAgents → ∀ other,
      additiveChoreCost cost agent (allocation agent) ≤
        additiveChoreCost cost agent (allocation other) := by
    intro agent hagent other
    have hagentLong : agent ∉ longAgents := fun hlong => hagent (hlongSubset hlong)
    have hcardAgent : (allocation agent).card = q := by
      rw [hcard agent]
      simp [m2Quota, hagentLong]
    have hcardOther : q ≤ (allocation other).card := by
      rw [hcard other]
      simp [m2Quota]
    have hconstantAgent : ∀ item ∈ allocation agent, cost agent item = r := by
      intro item hitem
      have hchore : item ∈ chores := halloc.1 agent item hitem
      have hnotSmall : ¬ IsSmallChore cost agent item := by
        intro hsmall
        apply hagent
        have hmem : agent ∈ smallAgentSet cost item := by
          simpa [smallAgentSet] using hsmall
        simpa [hsmallType item hchore] using hmem
      rcases hcost agent item with hsmall | hlarge
      · exact (hnotSmall (by simpa [IsSmallChore] using hsmall)).elim
      · exact hlarge
    have hconstantOther : ∀ item ∈ allocation other, cost agent item = r := by
      intro item hitem
      have hchore : item ∈ chores := halloc.1 other item hitem
      have hnotSmall : ¬ IsSmallChore cost agent item := by
        intro hsmall
        apply hagent
        have hmem : agent ∈ smallAgentSet cost item := by
          simpa [smallAgentSet] using hsmall
        simpa [hsmallType item hchore] using hmem
      rcases hcost agent item with hsmall | hlarge
      · exact (hnotSmall (by simpa [IsSmallChore] using hsmall)).elim
      · exact hlarge
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost agent (allocation agent) r hconstantAgent,
      additiveChoreCost_eq_card_nsmul_of_constant cost agent (allocation other) r hconstantOther,
      hcardAgent]
    simp only [nsmul_eq_mul]
    have hcardReal : (q : ℝ) ≤ (allocation other).card := by
      exact_mod_cast hcardOther
    exact mul_le_mul_of_nonneg_right hcardReal (by linarith)
  refine ⟨allocation, halloc, hefx, ?_, ?_, houtsideFavorite⟩
  · intro i hsmall
    exact smallItemCertificate_of_efx Item cost allocation hefx i hsmall
  · intro i hallLarge j
    by_cases hiSmall : i ∈ smallAgents
    · have hempty : allocation i = ∅ := by
        by_contra hnotempty
        obtain ⟨item, hitem⟩ := Finset.nonempty_iff_ne_empty.mpr hnotempty
        have hchore : item ∈ chores := halloc.1 i item hitem
        have hsmallItem : IsSmallChore cost i item := by
          have hmem : i ∈ smallAgentSet cost item := by
            simpa [hsmallType item hchore] using hiSmall
          simpa [smallAgentSet] using hmem
        have hlargeItem := hallLarge item hitem
        rw [IsSmallChore] at hsmallItem
        rw [IsLargeChore] at hlargeItem
        linarith
      rw [hempty]
      simp only [additiveChoreCost, Finset.sum_empty]
      exact additiveChoreCost_nonneg cost
        (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) i (allocation j)
    · have hiLong : i ∉ longAgents := fun hiLong => hiSmall (hlongSubset hiLong)
      have hcardI : (allocation i).card = q := by
        rw [hcard i]
        simp [m2Quota, hiLong]
      have hcardJ : q ≤ (allocation j).card := by
        rw [hcard j]
        simp [m2Quota]
      have hconstantI : ∀ item ∈ allocation i, cost i item = r := by
        intro item hitem
        have hchore : item ∈ chores := halloc.1 i item hitem
        have hnotSmall : ¬ IsSmallChore cost i item := by
          intro hsmall
          apply hiSmall
          have hmem : i ∈ smallAgentSet cost item := by
            simpa [smallAgentSet] using hsmall
          simpa [hsmallType item hchore] using hmem
        rcases hcost i item with hsmall | hlarge
        · exact (hnotSmall (by simpa [IsSmallChore] using hsmall)).elim
        · exact hlarge
      have hconstantJ : ∀ item ∈ allocation j, cost i item = r := by
        intro item hitem
        have hchore : item ∈ chores := halloc.1 j item hitem
        have hnotSmall : ¬ IsSmallChore cost i item := by
          intro hsmall
          apply hiSmall
          have hmem : i ∈ smallAgentSet cost item := by
            simpa [smallAgentSet] using hsmall
          simpa [hsmallType item hchore] using hmem
        rcases hcost i item with hsmall | hlarge
        · exact (hnotSmall (by simpa [IsSmallChore] using hsmall)).elim
        · exact hlarge
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost i (allocation i) r hconstantI,
        additiveChoreCost_eq_card_nsmul_of_constant cost i (allocation j) r hconstantJ,
        hcardI]
      simp only [nsmul_eq_mul]
      have hcardReal : (q : ℝ) ≤ (allocation j).card := by
        exact_mod_cast hcardJ
      exact mul_le_mul_of_nonneg_right hcardReal (by linarith)

/-- The fixed-type branch has the M2-properties certificates unless its
cardinality is the source's `4q+3` exceptional residue. -/
theorem existsEfxOfM2SingleSmallType_certified_of_remainder_ne_three
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q remainder : ℕ) (smallAgents : Finset (Fin 4))
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hsmallType : ∀ item ∈ chores, smallAgentSet cost item = smallAgents)
    (hdecompose : chores.card = 4 * q + remainder) (hremainder : remainder < 4)
    (hremainderNeThree : remainder ≠ 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ agent, agent ∉ smallAgents → ∀ other,
        additiveChoreCost cost agent (allocation agent) ≤
          additiveChoreCost cost agent (allocation other)) := by
  classical
  interval_cases remainder
  · exact existsEfxOfM2SingleSmallType_certified Item r cost chores q 0 smallAgents ∅ hr hcost
      hsmallType hdecompose hremainder (by simp) (by simp)
  · have hchoresPos : 0 < chores.card := by omega
    obtain ⟨item, hitem⟩ := Finset.card_pos.mp hchoresPos
    have hsmallCard : smallAgents.card = 2 := by
      rw [← hsmallType item hitem]
      exact htwo item hitem
    obtain ⟨longAgents, hsubset, hcard⟩ :=
      smallAgents.exists_subset_card_eq (by omega : 1 ≤ smallAgents.card)
    exact existsEfxOfM2SingleSmallType_certified Item r cost chores q 1 smallAgents longAgents hr
      hcost hsmallType hdecompose hremainder hsubset hcard
  · have hchoresPos : 0 < chores.card := by omega
    obtain ⟨item, hitem⟩ := Finset.card_pos.mp hchoresPos
    have hsmallCard : smallAgents.card = 2 := by
      rw [← hsmallType item hitem]
      exact htwo item hitem
    obtain ⟨longAgents, hsubset, hcard⟩ :=
      smallAgents.exists_subset_card_eq (by omega : 2 ≤ smallAgents.card)
    exact existsEfxOfM2SingleSmallType_certified Item r cost chores q 2 smallAgents longAgents hr
      hcost hsmallType hdecompose hremainder hsubset hcard
  · exact (hremainderNeThree rfl).elim

/-- In the nonexceptional fixed-type residue, every agent outside the common
small-agent pair receives the short quota in the certified construction and
is therefore residual-favorite. -/
theorem existsEfxOfM2SingleSmallType_preferred_largeAgent_certified_of_remainder_ne_three
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q remainder : ℕ) (smallAgents : Finset (Fin 4))
    (agent : Fin 4)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hsmallType : ∀ item ∈ chores, smallAgentSet cost item = smallAgents)
    (hdecompose : chores.card = 4 * q + remainder) (hremainder : remainder < 4)
    (hremainderNeThree : remainder ≠ 3) (hagent : agent ∉ smallAgents) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) ∧
      ∀ other, additiveChoreCost cost agent (allocation agent) ≤
        additiveChoreCost cost agent (allocation other) := by
  obtain ⟨allocation, halloc, hefx, hsmallCertificate, hlargeCertificate, houtsideFavorite⟩ :=
    existsEfxOfM2SingleSmallType_certified_of_remainder_ne_three Item r cost chores q remainder
      smallAgents hr hcost htwo hsmallType hdecompose hremainder hremainderNeThree
  exact ⟨allocation, halloc, hefx, hsmallCertificate, hlargeCertificate,
    houtsideFavorite agent hagent⟩

/-- A fixed two-small-agent type with `4q+3` chores is precisely the first
exceptional shape in Lemma `M2properties`, with the complementary type as
the auxiliary pair. -/
theorem fixedSmallType_is_m2Exceptional
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (smallAgents : Finset (Fin 4)) (q : ℕ)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hsmallType : ∀ item ∈ chores, smallAgentSet cost item = smallAgents)
    (hcard : chores.card = 4 * q + 3) :
    ∃ auxiliary : Finset (Fin 4), smallAgents.card = 2 ∧ auxiliary.card = 2 ∧
      Disjoint smallAgents auxiliary ∧
      ((∀ item ∈ chores, smallAgentSet cost item = smallAgents) ∧ chores.card = 4 * q + 3) := by
  classical
  have hchoresPos : 0 < chores.card := by rw [hcard]; omega
  obtain ⟨item, hitem⟩ := Finset.card_pos.mp hchoresPos
  have hsmallCard : smallAgents.card = 2 := by
    rw [← hsmallType item hitem]
    exact htwo item hitem
  refine ⟨smallAgentsᶜ, hsmallCard, ?_, ?_, hsmallType, hcard⟩
  · rw [Finset.card_compl, hsmallCard]
    norm_num
  · exact disjoint_compl_right

/-- The two exceptional residue configurations of Lemma `M2properties`(ii). -/
def IsM2Exceptional {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) : Prop :=
  ∃ dominant auxiliary : Finset (Fin 4), ∃ q : ℕ,
    dominant.card = 2 ∧ auxiliary.card = 2 ∧ Disjoint dominant auxiliary ∧
      (((∀ item ∈ chores, smallAgentSet cost item = dominant) ∧ chores.card = 4 * q + 3) ∨
        (∃ exceptionalItem ∈ chores, smallAgentSet cost exceptionalItem = auxiliary ∧
          (∀ item ∈ chores.erase exceptionalItem, smallAgentSet cost item = dominant) ∧
          (chores.erase exceptionalItem).card = 4 * q + 3))

/-- A residue of one fixed two-small-agent type is exceptional only in the
source's cardinality-three congruence class.  The second exceptional shape is
impossible because it would require both complementary types among fixed-type
chores. -/
theorem not_isM2Exceptional_of_fixedSmallType_remainder_ne_three
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (smallAgents : Finset (Fin 4)) (q remainder : ℕ)
    (hsmallType : ∀ item ∈ chores, smallAgentSet cost item = smallAgents)
    (hdecompose : chores.card = 4 * q + remainder) (hremainder : remainder < 4)
    (hremainderNeThree : remainder ≠ 3) :
    ¬ IsM2Exceptional cost chores := by
  intro hexceptional
  rcases hexceptional with ⟨dominant, auxiliary, exceptionalQ, hdominant, hauxiliary,
    hdisjoint, hshape⟩
  rcases hshape with ⟨hfixed, hcard⟩ | ⟨exceptionalItem, hexceptionalItem,
      hexceptionalType, houtsideType, houtsideCard⟩
  · have hchoresPos : 0 < chores.card := by
      rw [hcard]
      omega
    obtain ⟨item, hitem⟩ := Finset.card_pos.mp hchoresPos
    have hdominantEq : dominant = smallAgents := by
      exact (hfixed item hitem).symm.trans (hsmallType item hitem)
    rw [hcard] at hdecompose
    have : remainder = 3 := by omega
    exact hremainderNeThree this
  · have hauxiliaryEq : auxiliary = smallAgents := by
      exact (hexceptionalType).symm.trans (hsmallType exceptionalItem hexceptionalItem)
    have houtsidePos : 0 < (chores.erase exceptionalItem).card := by
      rw [houtsideCard]
      omega
    obtain ⟨outsideItem, houtsideItem⟩ := Finset.card_pos.mp houtsidePos
    have houtsideChore : outsideItem ∈ chores := (Finset.mem_erase.mp houtsideItem).2
    have hdominantEq : dominant = smallAgents := by
      exact (houtsideType outsideItem houtsideItem).symm.trans
        (hsmallType outsideItem houtsideChore)
    rw [hdominantEq, hauxiliaryEq] at hdisjoint
    have hsmallCard : smallAgents.card = 2 := by
      rw [← hdominantEq]
      exact hdominant
    obtain ⟨agent, hagent⟩ := Finset.card_pos.mp (by omega : 0 < smallAgents.card)
    exact (Finset.disjoint_left.mp hdisjoint hagent hagent).elim

/-- The fixed-type residue-three configuration realizes the first exceptional
alternative of `IsM2Exceptional`. -/
theorem isM2Exceptional_of_fixedSmallType
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (smallAgents : Finset (Fin 4)) (q : ℕ)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hsmallType : ∀ item ∈ chores, smallAgentSet cost item = smallAgents)
    (hcard : chores.card = 4 * q + 3) :
    IsM2Exceptional cost chores := by
  obtain ⟨auxiliary, hsmallCard, hauxCard, hdisjoint, hfixed, hfixedCard⟩ :=
    fixedSmallType_is_m2Exceptional Item cost chores smallAgents q htwo hsmallType hcard
  exact ⟨smallAgents, auxiliary, q, hsmallCard, hauxCard, hdisjoint, Or.inl ⟨hfixed, hfixedCard⟩⟩

/-- The second exceptional shape in Lemma `M2properties`: one common-small
chore for a pair and a residue-three complementary fiber. -/
theorem oneCoreFibre_is_m2Exceptional
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4) (q : ℕ)
    (hdistinct : first ≠ second)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcore : (m2PairCoreFibre cost chores first second).card = 1)
    (hcrossFirst : (m2PairCrossFibre cost chores first second).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores second first).card = 0)
    (houtside : (m2PairOutsideFibre cost chores first second).card = 4 * q + 3) :
    ∃ exceptionalItem ∈ chores,
      smallAgentSet cost exceptionalItem = ({first, second} : Finset (Fin 4)) ∧
      (∀ item ∈ chores.erase exceptionalItem,
        smallAgentSet cost item = ({first, second} : Finset (Fin 4))ᶜ) ∧
      (chores.erase exceptionalItem).card = 4 * q + 3 := by
  obtain ⟨exceptionalItem, hcoreEq⟩ := Finset.card_eq_one.mp hcore
  have hitemCore : exceptionalItem ∈ m2PairCoreFibre cost chores first second := by
    rw [hcoreEq]
    simp
  have hitemChore : exceptionalItem ∈ chores := (Finset.mem_filter.mp hitemCore).1
  have hsmallExceptional : smallAgentSet cost exceptionalItem = ({first, second} : Finset (Fin 4)) := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro agent hagent
      simp only [Finset.mem_insert, Finset.mem_singleton] at hagent
      rcases hagent with rfl | rfl
      · exact (Finset.mem_filter.mp hitemCore).2.1
      · exact (Finset.mem_filter.mp hitemCore).2.2
    · rw [htwo exceptionalItem hitemChore]
      simp [hdistinct]
  have hfirstEmpty : m2PairCrossFibre cost chores first second = ∅ :=
    Finset.card_eq_zero.mp hcrossFirst
  have hsecondEmpty : m2PairCrossFibre cost chores second first = ∅ :=
    Finset.card_eq_zero.mp hcrossSecond
  have hunion := m2PairFibres_union_eq cost chores first second
  have hunion' : ({exceptionalItem} : Finset Item) ∪
      m2PairOutsideFibre cost chores first second = chores := by
    simpa [hcoreEq, hfirstEmpty, hsecondEmpty] using hunion
  have hdisjoint : Disjoint ({exceptionalItem} : Finset Item)
      (m2PairOutsideFibre cost chores first second) := by
    have hbase := m2PairCore_disjoint_crosses_outside cost chores first second
    rw [hcoreEq, hfirstEmpty, hsecondEmpty] at hbase
    simpa using hbase
  have heraseEq : chores.erase exceptionalItem = m2PairOutsideFibre cost chores first second := by
    ext item
    constructor
    · intro hitem
      have hchore := (Finset.mem_erase.mp hitem).2
      have hnot : item ≠ exceptionalItem := (Finset.mem_erase.mp hitem).1
      rw [← hunion'] at hchore
      simp only [Finset.mem_union, Finset.mem_singleton] at hchore
      rcases hchore with rfl | hout
      · exact (hnot rfl).elim
      · exact hout
    · intro hout
      refine Finset.mem_erase.mpr ⟨?_, (Finset.mem_filter.mp hout).1⟩
      intro hEq
      subst item
      exact (Finset.disjoint_left.mp hdisjoint) (by simp) hout
  refine ⟨exceptionalItem, hitemChore, hsmallExceptional, ?_, ?_⟩
  · intro item hitem
    have hout : item ∈ m2PairOutsideFibre cost chores first second := by
      rw [← heraseEq]
      exact hitem
    have hitemChore' : item ∈ chores := (Finset.mem_filter.mp hout).1
    apply Finset.eq_of_subset_of_card_le
    · intro agent hsmall
      have hnotPair : agent ∉ ({first, second} : Finset (Fin 4)) := by
        intro hpair
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
        rcases hpair with rfl | rfl
        · exact (Finset.mem_filter.mp hout).2.1 hsmall
        · exact (Finset.mem_filter.mp hout).2.2 hsmall
      simpa using hnotPair
    · rw [htwo item hitemChore', Finset.card_compl]
      simp [hdistinct]
  · rw [heraseEq, houtside]

/-- The one-core residue-three configuration realizes the second exceptional
alternative of `IsM2Exceptional`. -/
theorem isM2Exceptional_of_oneCoreFibre
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4) (q : ℕ)
    (hdistinct : first ≠ second)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcore : (m2PairCoreFibre cost chores first second).card = 1)
    (hcrossFirst : (m2PairCrossFibre cost chores first second).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores second first).card = 0)
    (houtside : (m2PairOutsideFibre cost chores first second).card = 4 * q + 3) :
    IsM2Exceptional cost chores := by
  obtain ⟨exceptionalItem, hitem, hsmallItem, houtsideType, hresidueCard⟩ :=
    oneCoreFibre_is_m2Exceptional Item cost chores first second q hdistinct htwo hcore
      hcrossFirst hcrossSecond houtside
  let auxiliary : Finset (Fin 4) := {first, second}
  refine ⟨auxiliaryᶜ, auxiliary, q, ?_, ?_, ?_, Or.inr ?_⟩
  · rw [Finset.card_compl]
    simp [auxiliary, hdistinct]
  · simp [auxiliary, hdistinct]
  · exact disjoint_compl_left
  · exact ⟨exceptionalItem, hitem, (by simpa [auxiliary] using hsmallItem),
      (by simpa [auxiliary] using houtsideType), hresidueCard⟩

/-- For a fixed small-agent type, any agent outside that type can be made
envy-free by assigning that agent a short balanced bundle.  This is the
`a = 0` part of the preferred-agent choice in Lemma `M2properties`(iii). -/
theorem existsEfxOfM2SingleSmallType_preferred_largeAgent
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q remainder : ℕ) (smallAgents : Finset (Fin 4))
    (agent : Fin 4)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hsmallType : ∀ item ∈ chores, smallAgentSet cost item = smallAgents)
    (hdecompose : chores.card = 4 * q + remainder) (hremainder : remainder < 4)
    (hagent : agent ∉ smallAgents) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      ∀ other, additiveChoreCost cost agent (allocation agent) ≤
        additiveChoreCost cost agent (allocation other) := by
  classical
  have havailable : remainder ≤ ((Finset.univ : Finset (Fin 4)).erase agent).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ agent), Finset.card_univ]
    norm_num
    omega
  obtain ⟨longAgents, hlongSubset, hlongCard⟩ :=
    ((Finset.univ : Finset (Fin 4)).erase agent).exists_subset_card_eq havailable
  obtain ⟨allocation, halloc, hcard⟩ :=
    existsAllocationOfQuota (Fin 4) Item chores (m2Quota q longAgents) (by
      rw [m2Quota_sum, hlongCard, hdecompose])
  have hagentNotLong : agent ∉ longAgents := by
    intro hlong
    have : agent ∈ ((Finset.univ : Finset (Fin 4)).erase agent) := hlongSubset hlong
    simp at this
  have hagentCard : (allocation agent).card = q := by
    rw [hcard agent]
    simp [m2Quota, hagentNotLong]
  have hcardLower : ∀ other, q ≤ (allocation other).card := by
    intro other
    rw [hcard other]
    simp [m2Quota]
  have hagentLarge : ∀ item ∈ allocation agent, IsLargeChore cost r agent item := by
    intro item hitem
    have hchore : item ∈ chores := halloc.1 agent item hitem
    have hnotSmall : ¬ IsSmallChore cost agent item := by
      intro hsmall
      apply hagent
      have hmem : agent ∈ smallAgentSet cost item := by
        simpa [smallAgentSet] using hsmall
      simpa [hsmallType item hchore] using hmem
    rcases hcost agent item with hsmall | hlarge
    · exact (hnotSmall (by simpa [IsSmallChore] using hsmall)).elim
    · exact hlarge
  have hotherLarge : ∀ other item, other ≠ agent → item ∈ allocation other →
      IsLargeChore cost r agent item := by
    intro other item _ hitem
    have hchore : item ∈ chores := halloc.1 other item hitem
    have hnotSmall : ¬ IsSmallChore cost agent item := by
      intro hsmall
      apply hagent
      have hmem : agent ∈ smallAgentSet cost item := by
        simpa [smallAgentSet] using hsmall
      simpa [hsmallType item hchore] using hmem
    rcases hcost agent item with hsmall | hlarge
    · exact (hnotSmall (by simpa [IsSmallChore] using hsmall)).elim
    · exact hlarge
  have hefx := efxOfM2SingleSmallTypeBalanced Item r cost chores allocation smallAgents hr hcost
    hsmallType halloc (by
      intro first second
      rw [hcard first, hcard second]
      exact m2Quota_balanced q longAgents first second)
  refine ⟨allocation, halloc, hefx, ?_⟩
  exact envyFreeForChores_single_special_of_all_large cost r allocation agent q hcost (by linarith)
    hagentCard hcardLower hotherLarge hagentLarge

/-- The `a = 0` branch of the prescribed-agent clause: if the first of two
disjoint types is absent, every agent in that absent type can receive the
short all-large bundle and be envy-free. -/
theorem existsEfxOfM2TwoTypes_preferred_of_firstCount_zero
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (firstType secondType : Finset (Fin 4)) (agent : Fin 4)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hfirstCard : firstType.card = 2) (hsecondCard : secondType.card = 2)
    (hdisjoint : Disjoint firstType secondType)
    (htypes : ∀ item ∈ chores, smallAgentSet cost item = firstType ∨
      smallAgentSet cost item = secondType)
    (hfirstCount : (chores.filter fun item => smallAgentSet cost item = firstType).card = 0)
    (hagent : agent ∈ firstType) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      ∀ other, additiveChoreCost cost agent (allocation agent) ≤
        additiveChoreCost cost agent (allocation other) := by
  let q := chores.card / 4
  let remainder := chores.card % 4
  have hdecompose : chores.card = 4 * q + remainder := by
    have hmod := Nat.mod_add_div chores.card 4
    dsimp [q, remainder]
    omega
  have hremainder : remainder < 4 := by
    dsimp [remainder]
    exact Nat.mod_lt _ (by omega)
  have hsmallType : ∀ item ∈ chores, smallAgentSet cost item = secondType := by
    intro item hitem
    rcases htypes item hitem with hfirst | hsecond
    · have hmem : item ∈ chores.filter fun item => smallAgentSet cost item = firstType := by
        simp [hitem, hfirst]
      have hempty : chores.filter fun item => smallAgentSet cost item = firstType = ∅ :=
        Finset.card_eq_zero.mp hfirstCount
      rw [hempty] at hmem
      have hfalse : False := by simpa using hmem
      exact False.elim hfalse
    · exact hsecond
  have hagentNotSecond : agent ∉ secondType := by
    intro hagentSecond
    exact (Finset.disjoint_left.mp hdisjoint) hagent hagentSecond
  exact existsEfxOfM2SingleSmallType_preferred_largeAgent Item r cost chores q remainder secondType
    agent hr hcost hsmallType hdecompose hremainder hagentNotSecond

/-- With only two disjoint two-agent small types, naming the endpoints of the
first type identifies its fiber, eliminates both cross fibers, and identifies
the complementary fiber with the second type. -/
private theorem m2PairFibres_of_two_disjoint_smallTypes
    {Item : Type} [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (firstType secondType : Finset (Fin 4))
    (first second : Fin 4)
    (hfirst : first ∈ firstType) (hsecond : second ∈ firstType)
    (hdisjoint : Disjoint firstType secondType)
    (htypes : ∀ item ∈ chores, smallAgentSet cost item = firstType ∨
      smallAgentSet cost item = secondType) :
    (m2PairCoreFibre cost chores first second =
        (chores.filter fun item => smallAgentSet cost item = firstType)) ∧
      m2PairCrossFibre cost chores first second = ∅ ∧
      m2PairCrossFibre cost chores second first = ∅ ∧
      m2PairOutsideFibre cost chores first second =
        (chores.filter fun item => smallAgentSet cost item = secondType) := by
  have hfirstNotSecond : first ∉ secondType := by
    intro h
    exact (Finset.disjoint_left.mp hdisjoint) hfirst h
  have hsecondNotSecond : second ∉ secondType := by
    intro h
    exact (Finset.disjoint_left.mp hdisjoint) hsecond h
  have htypesNe : secondType ≠ firstType := by
    intro hEq
    apply hfirstNotSecond
    rw [hEq]
    exact hfirst
  have hfirstNeSecond : firstType ≠ secondType := htypesNe.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext item
    by_cases hitem : item ∈ chores
    · rcases htypes item hitem with htype | htype
      · simp [m2PairCoreFibre, hitem, htype, hfirst, hsecond]
      · simp [m2PairCoreFibre, hitem, htype, hfirstNotSecond, hsecondNotSecond, htypesNe]
    · simp [m2PairCoreFibre, hitem]
  · ext item
    by_cases hitem : item ∈ chores
    · rcases htypes item hitem with htype | htype
      · simp [m2PairCrossFibre, hitem, htype, hfirst, hsecond]
      · simp [m2PairCrossFibre, hitem, htype, hfirstNotSecond]
    · simp [m2PairCrossFibre, hitem]
  · ext item
    by_cases hitem : item ∈ chores
    · rcases htypes item hitem with htype | htype
      · simp [m2PairCrossFibre, hitem, htype, hfirst, hsecond]
      · simp [m2PairCrossFibre, hitem, htype, hsecondNotSecond]
    · simp [m2PairCrossFibre, hitem]
  · ext item
    by_cases hitem : item ∈ chores
    · rcases htypes item hitem with htype | htype
      · simp [m2PairOutsideFibre, hitem, htype, hfirst, hfirstNeSecond]
      · simp [m2PairOutsideFibre, hitem, htype, hfirstNotSecond, hsecondNotSecond]
    · simp [m2PairOutsideFibre, hitem]

/-- For equal core and outside fibers, the source splits each fiber between
its small endpoints and gives agent `0` the lower core half.  This allocation
is EFX and agent `0` is envy-free. -/
theorem existsEfxOfM2PairEqualFibres_preferredZero
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcore : (m2PairCoreFibre cost chores 0 1).card = a)
    (hcrossFirst : (m2PairCrossFibre cost chores 0 1).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores 1 0).card = 0)
    (houtside : (m2PairOutsideFibre cost chores 0 1).card = a) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) ∧
      ∀ other, additiveChoreCost cost 0 (allocation 0) ≤
        additiveChoreCost cost 0 (allocation other) := by
  classical
  let low := a / 2
  let high := (a + 1) / 2
  obtain ⟨coreAllocation, outsideAllocation, hcoreAllocation, hcoreCard,
    houtsideAllocation, houtsideCard, hfull⟩ :=
    existsM2PairSplitAllocation Item cost chores low high 0 0 (by
      dsimp [low, high]
      rw [hcore]
      omega) (by omega)
  let allocation := m2PairSplitAllocation cost chores coreAllocation outsideAllocation
  have hcoreZero : (coreAllocation 0).card = low := by
    simpa [m2PairCoreQuota] using hcoreCard 0
  have hcoreOne : (coreAllocation 1).card = high := by
    simpa [m2PairCoreQuota] using hcoreCard 1
  have hcoreTwo : coreAllocation 2 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 2
  have hcoreThree : coreAllocation 3 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 3
  have houtsideZero : outsideAllocation 0 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairOutsideQuota] using houtsideCard 0
  have houtsideOne : outsideAllocation 1 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairOutsideQuota] using houtsideCard 1
  have hcrossFirstEmpty : m2PairCrossFibre cost chores 0 1 = ∅ :=
    Finset.card_eq_zero.mp hcrossFirst
  have hcrossSecondEmpty : m2PairCrossFibre cost chores 1 0 = ∅ :=
    Finset.card_eq_zero.mp hcrossSecond
  have hcardZero : (allocation 0).card = low := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0).card = low
    rw [m2PairSplitAllocation_zero_card cost chores coreAllocation outsideAllocation low 0
      hcoreAllocation houtsideAllocation hcoreZero (by simpa [m2PairOutsideQuota] using houtsideCard 0)]
    simp [hcrossFirst]
  have hcardOne : (allocation 1).card = high := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1).card = high
    rw [m2PairSplitAllocation_one_card cost chores coreAllocation outsideAllocation high 0
      hcoreAllocation houtsideAllocation hcoreOne (by simpa [m2PairOutsideQuota] using houtsideCard 1)]
    simp [hcrossSecond]
  have hcardTwo : (allocation 2).card = low := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 2).card = low
    rw [m2PairSplitAllocation_two_eq_outside cost chores coreAllocation outsideAllocation hcoreTwo,
      houtsideCard 2]
    simp [m2PairOutsideQuota, houtside, low]
  have hcardThree : (allocation 3).card = high := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 3).card = high
    rw [m2PairSplitAllocation_three_eq_outside cost chores coreAllocation outsideAllocation hcoreThree,
      houtsideCard 3]
    simp [m2PairOutsideQuota, houtside, low, high]
    omega
  have hzeroSmall : ∀ item ∈ allocation 0, IsSmallChore cost 0 item := by
    intro item hitem
    have hitemCore : item ∈ coreAllocation 0 := by
      simpa [allocation, m2PairSplitAllocation, allocateAllTo, hcrossFirstEmpty, houtsideZero] using hitem
    have hpool := hcoreAllocation.1 0 item hitemCore
    exact isSmallChore_of_mem_smallAgentSet cost 0 item (Finset.mem_filter.mp hpool).2.1
  have honeSmall : ∀ item ∈ allocation 1, IsSmallChore cost 1 item := by
    intro item hitem
    have hitemCore : item ∈ coreAllocation 1 := by
      simpa [allocation, m2PairSplitAllocation, allocateAllTo, hcrossSecondEmpty, houtsideOne] using hitem
    have hpool := hcoreAllocation.1 1 item hitemCore
    exact isSmallChore_of_mem_smallAgentSet cost 1 item (Finset.mem_filter.mp hpool).2.2
  have htwoSmall : ∀ item ∈ allocation 2, IsSmallChore cost 2 item := by
    change ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 2,
      IsSmallChore cost 2 item
    exact m2PairSplitAllocation_two_ownSmall cost chores coreAllocation outsideAllocation
      hcoreTwo houtsideAllocation htwo
  have hthreeSmall : ∀ item ∈ allocation 3, IsSmallChore cost 3 item := by
    change ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 3,
      IsSmallChore cost 3 item
    exact m2PairSplitAllocation_three_ownSmall cost chores coreAllocation outsideAllocation
      hcoreThree houtsideAllocation htwo
  have halloc : IsAllocationOf allocation chores := by
    change IsAllocationOf
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) chores
    exact hfull
  have hbalanced : ∀ i j, (allocation i).card ≤ (allocation j).card + 1 := by
    have hcardRange : ∀ i, (allocation i).card = low ∨ (allocation i).card = high := by
      intro i
      fin_cases i
      · exact Or.inl hcardZero
      · exact Or.inr hcardOne
      · exact Or.inl hcardTwo
      · exact Or.inr hcardThree
    intro i j
    rcases hcardRange i with hi | hi <;> rcases hcardRange j with hj | hj <;>
      rw [hi, hj] <;> dsimp [low, high] <;> omega
  have hownerSmall : ∀ agent item, item ∈ allocation agent → IsSmallChore cost agent item := by
    intro agent item hitem
    fin_cases agent
    · exact hzeroSmall item hitem
    · exact honeSmall item hitem
    · exact htwoSmall item hitem
    · exact hthreeSmall item hitem
  have hefx := efxForChores_of_ownSmall_balanced cost r allocation hcost (by linarith)
    hownerSmall hbalanced
  have honeSmallForZero : ∀ item ∈ allocation 1, IsSmallChore cost 0 item := by
    intro item hitem
    have hitemCore : item ∈ coreAllocation 1 := by
      simpa [allocation, m2PairSplitAllocation, allocateAllTo, hcrossSecondEmpty, houtsideOne] using hitem
    have hpool := hcoreAllocation.1 1 item hitemCore
    exact isSmallChore_of_mem_smallAgentSet cost 0 item (Finset.mem_filter.mp hpool).2.1
  have hzeroToTwoLarge := m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation
    outsideAllocation 0 2 (by linarith) hcost hcoreAllocation houtsideAllocation (Or.inl rfl)
      (Or.inl rfl) hcoreTwo
  have hzeroToThreeLarge := m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation
    outsideAllocation 0 3 (by linarith) hcost hcoreAllocation houtsideAllocation (Or.inl rfl)
      (Or.inr rfl) hcoreThree
  have hzeroConstant : ∀ item ∈ allocation 0, cost 0 item = 1 := by
    intro item hitem
    simpa [IsSmallChore] using hzeroSmall item hitem
  have honeConstant : ∀ item ∈ allocation 1, cost 0 item = 1 := by
    intro item hitem
    simpa [IsSmallChore] using honeSmallForZero item hitem
  have hcertificates := allSmallOwner_efx_certificates Item r cost allocation hr hcost hefx hownerSmall
  refine ⟨allocation, halloc, hefx, hcertificates.1, hcertificates.2, ?_⟩
  · intro other
    fin_cases other
    · exact le_rfl
    · change additiveChoreCost cost 0 (allocation 0) ≤ additiveChoreCost cost 0 (allocation 1)
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 (allocation 0) 1 hzeroConstant,
        additiveChoreCost_eq_card_nsmul_of_constant cost 0 (allocation 1) 1 honeConstant,
        hcardZero, hcardOne]
      simp only [nsmul_eq_mul]
      dsimp [low, high]
      norm_num
      exact_mod_cast (show a / 2 ≤ (a + 1) / 2 by omega)
    · change additiveChoreCost cost 0 (allocation 0) ≤ additiveChoreCost cost 0 (allocation 2)
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 (allocation 0) 1 hzeroConstant,
        additiveChoreCost_eq_card_nsmul_of_constant cost 0 (allocation 2) r hzeroToTwoLarge,
        hcardZero, hcardTwo]
      simp only [nsmul_eq_mul]
      dsimp [low]
      have hnonneg : 0 ≤ (a / 2 : ℝ) := by positivity
      nlinarith
    · change additiveChoreCost cost 0 (allocation 0) ≤ additiveChoreCost cost 0 (allocation 3)
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 (allocation 0) 1 hzeroConstant,
        additiveChoreCost_eq_card_nsmul_of_constant cost 0 (allocation 3) r hzeroToThreeLarge,
        hcardZero, hcardThree]
      simp only [nsmul_eq_mul]
      dsimp [low, high]
      norm_num
      have hdiv : a / 2 ≤ (a + 1) / 2 := by omega
      have hdivReal : ((a / 2 : ℕ) : ℝ) ≤ (((a + 1) / 2 : ℕ) : ℝ) := by
        exact_mod_cast hdiv
      calc
        ((a / 2 : ℕ) : ℝ) ≤ (((a + 1) / 2 : ℕ) : ℝ) := hdivReal
        _ ≤ (((a + 1) / 2 : ℕ) : ℝ) * r := by
          have hhighNonneg : 0 ≤ (((a + 1) / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
          nlinarith

/-- The integer interval calculation in source Case 3.1.  The witnesses split
the `12` and `34` fibers between the deficient pair, with the two final
inequalities exactly those used for their mutual EFX comparison. -/
theorem existsM2CrossSplit (a b c T : ℕ)
    (htotal : a + b + c ≤ 2 * T) (hac : a + c ≤ 2 * T)
    (hb : b ≤ T) (hc : c ≤ T)
    (hcross : 0 < b + c) :
    ∃ a1 a2 l1 l2 : ℕ,
      a1 + a2 = a ∧
      l1 + l2 = 2 * T - a - b - c ∧
      b + a1 + l1 = T ∧
      c + a2 + l2 = T ∧
      l1 ≤ c + l2 ∧ l2 ≤ b + l1 := by
  let lower := max (a + c - T) ((a - b + 1) / 2)
  refine ⟨lower, a - lower, T - b - lower, T - c - (a - lower), ?_⟩
  have hlowerA : lower ≤ a := by
    simp only [lower]
    apply max_le
    · omega
    · omega
  have hlowerTB : lower ≤ T - b := by
    simp only [lower]
    apply max_le
    · omega
    · omega
  have hlowerHalf : lower ≤ (a + c) / 2 := by
    simp only [lower]
    apply max_le
    · omega
    · omega
  have hlowerLeft : a + c - T ≤ lower := by
    simp only [lower]
    exact Nat.le_max_left _ _
  have hlowerRight : (a - b + 1) / 2 ≤ lower := by
    simp only [lower]
    exact Nat.le_max_right _ _
  omega

/-- The preceding split is available from the exact pair-deficiency bounds in
source Case 3.1, with `T = ⌊(m + 1) / 4⌋`. -/
theorem existsM2CrossSplit_of_pairBounds (a b c f q remainder : ℕ)
    (hm : a + b + c + f = 4 * q + remainder) (hremainder : remainder < 4)
    (hpair : 4 * q + remainder < 2 * f)
    (hb : 4 * b ≤ 4 * q + remainder) (hc : 4 * c ≤ 4 * q + remainder)
    (hcross : 0 < b + c) :
    ∃ a1 a2 l1 l2 : ℕ,
      a1 + a2 = a ∧
      l1 + l2 = 2 * ((4 * q + remainder + 1) / 4) - a - b - c ∧
      b + a1 + l1 = (4 * q + remainder + 1) / 4 ∧
      c + a2 + l2 = (4 * q + remainder + 1) / 4 ∧
      l1 ≤ c + l2 ∧ l2 ≤ b + l1 := by
  interval_cases remainder
  · obtain ⟨a1, a2, l1, l2, ha, hl, hb, hc, hleft, hright⟩ :=
      existsM2CrossSplit a b c q (by omega) (by omega) (by omega) (by omega) hcross
    refine ⟨a1, a2, l1, l2, ha, ?_, ?_, ?_, hleft, hright⟩ <;> simp [Nat.add_div] at *
    all_goals assumption
  · obtain ⟨a1, a2, l1, l2, ha, hl, hb, hc, hleft, hright⟩ :=
      existsM2CrossSplit a b c q (by omega) (by omega) (by omega) (by omega) hcross
    refine ⟨a1, a2, l1, l2, ha, ?_, ?_, ?_, hleft, hright⟩ <;> simp [Nat.add_div] at *
    all_goals assumption
  · obtain ⟨a1, a2, l1, l2, ha, hl, hb, hc, hleft, hright⟩ :=
      existsM2CrossSplit a b c q (by omega) (by omega) (by omega) (by omega) hcross
    refine ⟨a1, a2, l1, l2, ha, ?_, ?_, ?_, hleft, hright⟩ <;> simp [Nat.add_div] at *
    all_goals assumption
  · obtain ⟨a1, a2, l1, l2, ha, hl, hb, hc, hleft, hright⟩ :=
      existsM2CrossSplit a b c (q + 1) (by omega) (by omega) (by omega) (by omega) hcross
    refine ⟨a1, a2, l1, l2, ha, ?_, ?_, ?_, hleft, hright⟩ <;> simp [Nat.add_div] at *
    all_goals assumption

/-- The cardinality calculation used after the Case 3.1 split.  Once the
`12` and `34` shares assigned to agents `0,1` have total size
`2T-a-b-c`, the two equal-as-possible residual `34` quotas are both at least
`T-1`, differ by at most one, and are no more than `T+1`.  This is the
four-remainder calculation stated in the source immediately before its EFX
verification. -/
theorem m2Case31_outsideQuota_bounds
    (a b c f q remainder firstOutside secondOutside : ℕ)
    (hm : a + b + c + f = 4 * q + remainder) (hremainder : remainder < 4)
    (hpair : 4 * q + remainder < 2 * f)
    (hshares : firstOutside + secondOutside =
      2 * ((4 * q + remainder + 1) / 4) - a - b - c) :
    let target := (4 * q + remainder + 1) / 4
    let remaining := f - firstOutside - secondOutside
    firstOutside + secondOutside ≤ f ∧
    target - 1 ≤ remaining / 2 ∧
      target - 1 ≤ remaining - remaining / 2 ∧
      remaining / 2 ≤ target + 1 ∧
      remaining - remaining / 2 ≤ target + 1 ∧
      remaining / 2 ≤ remaining - remaining / 2 + 1 ∧
      remaining - remaining / 2 ≤ remaining / 2 + 1 := by
  dsimp
  interval_cases remainder <;> simp [Nat.add_div] at * <;> omega

/-- In source Case 3.1, if one pair agent receives no own-small chore, then
the two complementary bundles both have at least that agent's target size
outside the corrected residue-three case. -/
theorem m2Case31_outsideCards_at_least_target_of_no_small
    (a b c f q remainder firstOutside secondOutside : ℕ)
    (hm : a + b + c + f = 4 * q + remainder) (hremainder : remainder < 4)
    (ha : a = 0) (hb : b = 0)
    (hfirst : b + firstOutside = (4 * q + remainder + 1) / 4)
    (hsecond : c + secondOutside = (4 * q + remainder + 1) / 4)
    (hremainderNeThree : remainder ≠ 3) :
    let target := (4 * q + remainder + 1) / 4
    let remaining := f - firstOutside - secondOutside
    target ≤ remaining / 2 ∧ target ≤ remaining - remaining / 2 := by
  dsimp
  interval_cases remainder <;> simp [Nat.add_div] at * <;> omega

/-- In the displayed Case 3.1 split, an all-large bundle of agent `0` cannot
contain a common-small chore or a `0`-incident cross chore. -/
private theorem m2PairSplitAllocation_zero_allLarge_forces_empty_smallParts
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (hr : 1 < r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (hallLarge : ∀ item ∈ m2PairSplitAllocation cost chores coreAllocation outsideAllocation 0,
      IsLargeChore cost r 0 item) :
    coreAllocation 0 = ∅ ∧ m2PairCrossFibre cost chores 0 1 = ∅ := by
  constructor
  · by_contra hcore
    obtain ⟨item, hitem⟩ := Finset.nonempty_iff_ne_empty.mpr hcore
    have hitemAllocation : item ∈ m2PairSplitAllocation cost chores coreAllocation outsideAllocation 0 := by
      simp [m2PairSplitAllocation, hitem]
    have hpool : item ∈ m2PairCoreFibre cost chores 0 1 := hcoreAllocation.1 0 item hitem
    have hsmall : IsSmallChore cost 0 item :=
      isSmallChore_of_mem_smallAgentSet cost 0 item (Finset.mem_filter.mp hpool).2.1
    have hlarge : cost 0 item = r := by
      simpa [IsLargeChore] using hallLarge item hitemAllocation
    rw [IsSmallChore] at hsmall
    linarith
  · by_contra hcross
    obtain ⟨item, hitem⟩ := Finset.nonempty_iff_ne_empty.mpr hcross
    have hitemAllocation : item ∈ m2PairSplitAllocation cost chores coreAllocation outsideAllocation 0 := by
      simp [m2PairSplitAllocation, allocateAllTo, hitem]
    have hsmall : IsSmallChore cost 0 item :=
      isSmallChore_of_mem_smallAgentSet cost 0 item (Finset.mem_filter.mp hitem).2.1
    have hlarge : cost 0 item = r := by
      simpa [IsLargeChore] using hallLarge item hitemAllocation
    rw [IsSmallChore] at hsmall
    linarith

/-- The symmetric Case 3.1 fact for agent `1`: an all-large bundle has no
common-small chore and no `1`-incident cross chore. -/
private theorem m2PairSplitAllocation_one_allLarge_forces_empty_smallParts
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (hr : 1 < r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (hallLarge : ∀ item ∈ m2PairSplitAllocation cost chores coreAllocation outsideAllocation 1,
      IsLargeChore cost r 1 item) :
    coreAllocation 1 = ∅ ∧ m2PairCrossFibre cost chores 1 0 = ∅ := by
  constructor
  · by_contra hcore
    obtain ⟨item, hitem⟩ := Finset.nonempty_iff_ne_empty.mpr hcore
    have hitemAllocation : item ∈ m2PairSplitAllocation cost chores coreAllocation outsideAllocation 1 := by
      simp [m2PairSplitAllocation, hitem]
    have hpool : item ∈ m2PairCoreFibre cost chores 0 1 := hcoreAllocation.1 1 item hitem
    have hsmall : IsSmallChore cost 1 item :=
      isSmallChore_of_mem_smallAgentSet cost 1 item (Finset.mem_filter.mp hpool).2.2
    have hlarge : cost 1 item = r := by
      simpa [IsLargeChore] using hallLarge item hitemAllocation
    rw [IsSmallChore] at hsmall
    linarith
  · by_contra hcross
    obtain ⟨item, hitem⟩ := Finset.nonempty_iff_ne_empty.mpr hcross
    have hitemAllocation : item ∈ m2PairSplitAllocation cost chores coreAllocation outsideAllocation 1 := by
      simp [m2PairSplitAllocation, allocateAllTo, hitem]
    have hsmall : IsSmallChore cost 1 item :=
      isSmallChore_of_mem_smallAgentSet cost 1 item (Finset.mem_filter.mp hitem).2.1
    have hlarge : cost 1 item = r := by
      simpa [IsLargeChore] using hallLarge item hitemAllocation
    rw [IsSmallChore] at hsmall
    linarith

/-- The nonexceptional Case 3.1 split has the two M2-properties fairness
certificates.  The only missing cardinal lower bound in the source proof is
the residue-three situation handled by the corrected cross-fiber allocation. -/
private theorem m2Case31SplitCertificates_of_remainder_ne_three
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (q remainder firstCore secondCore firstOutside secondOutside : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (hcoreCard : ∀ agent, (coreAllocation agent).card =
      m2PairCoreQuota 0 1 firstCore secondCore agent)
    (houtsideAllocation : IsAllocationOf outsideAllocation (m2PairOutsideFibre cost chores 0 1))
    (houtsideCard : ∀ agent, (outsideAllocation agent).card =
      m2PairOutsideQuota firstOutside secondOutside (m2PairOutsideFibre cost chores 0 1).card agent)
    (hm : (m2PairCoreFibre cost chores 0 1).card +
      (m2PairCrossFibre cost chores 0 1).card +
      (m2PairCrossFibre cost chores 1 0).card +
      (m2PairOutsideFibre cost chores 0 1).card = 4 * q + remainder)
    (hremainder : remainder < 4)
    (hcoreShares : firstCore + secondCore = (m2PairCoreFibre cost chores 0 1).card)
    (hfirstTarget : (m2PairCrossFibre cost chores 0 1).card + firstCore + firstOutside =
      (4 * q + remainder + 1) / 4)
    (hsecondTarget : (m2PairCrossFibre cost chores 1 0).card + secondCore + secondOutside =
      (4 * q + remainder + 1) / 4)
    (hzeroToOne : firstOutside ≤ (m2PairCrossFibre cost chores 1 0).card + secondOutside)
    (honeToZero : secondOutside ≤ (m2PairCrossFibre cost chores 0 1).card + firstOutside)
    (hefx : EFXForChores (additiveChoreCost cost)
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation))
    (hzeroSafe : remainder ≠ 3 ∨ 0 < (m2PairCoreFibre cost chores 0 1).card ∨
      0 < (m2PairCrossFibre cost chores 0 1).card)
    (honeSafe : remainder ≠ 3 ∨ 0 < (m2PairCoreFibre cost chores 0 1).card ∨
      0 < (m2PairCrossFibre cost chores 1 0).card) :
    (∀ i, (∃ item ∈ m2PairSplitAllocation cost chores coreAllocation outsideAllocation i,
      IsSmallChore cost i item) → ∀ j,
      additiveChoreCost cost i (m2PairSplitAllocation cost chores coreAllocation outsideAllocation i) - 1 ≤
        additiveChoreCost cost i (m2PairSplitAllocation cost chores coreAllocation outsideAllocation j)) ∧
    (∀ i, (∀ item ∈ m2PairSplitAllocation cost chores coreAllocation outsideAllocation i,
      IsLargeChore cost r i item) → ∀ j,
      additiveChoreCost cost i (m2PairSplitAllocation cost chores coreAllocation outsideAllocation i) ≤
        additiveChoreCost cost i (m2PairSplitAllocation cost chores coreAllocation outsideAllocation j)) := by
  let allocation := m2PairSplitAllocation cost chores coreAllocation outsideAllocation
  let target := (4 * q + remainder + 1) / 4
  let a := (m2PairCoreFibre cost chores 0 1).card
  let b := (m2PairCrossFibre cost chores 0 1).card
  let c := (m2PairCrossFibre cost chores 1 0).card
  let f := (m2PairOutsideFibre cost chores 0 1).card
  have hcoreZero : (coreAllocation 0).card = firstCore := by
    simpa [m2PairCoreQuota] using hcoreCard 0
  have hcoreOne : (coreAllocation 1).card = secondCore := by
    simpa [m2PairCoreQuota] using hcoreCard 1
  have hcoreTwo : coreAllocation 2 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 2
  have hcoreThree : coreAllocation 3 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 3
  have houtsideZero : (outsideAllocation 0).card = firstOutside := by
    simpa [m2PairOutsideQuota] using houtsideCard 0
  have houtsideOne : (outsideAllocation 1).card = secondOutside := by
    simpa [m2PairOutsideQuota] using houtsideCard 1
  have hcardZero : (allocation 0).card = target := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0).card = target
    rw [m2PairSplitAllocation_zero_card cost chores coreAllocation outsideAllocation
      firstCore firstOutside hcoreAllocation houtsideAllocation hcoreZero houtsideZero]
    dsimp [b, target]
    omega
  have hcardOne : (allocation 1).card = target := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1).card = target
    rw [m2PairSplitAllocation_one_card cost chores coreAllocation outsideAllocation
      secondCore secondOutside hcoreAllocation houtsideAllocation hcoreOne houtsideOne]
    dsimp [c, target]
    omega
  have hcardTwo : (allocation 2).card = (f - firstOutside - secondOutside) / 2 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 2).card = (f - firstOutside - secondOutside) / 2
    rw [m2PairSplitAllocation_two_eq_outside cost chores coreAllocation outsideAllocation hcoreTwo,
      houtsideCard 2]
    simp [m2PairOutsideQuota, f]
  have hcardThree : (allocation 3).card =
      f - firstOutside - secondOutside - (f - firstOutside - secondOutside) / 2 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 3).card =
        f - firstOutside - secondOutside - (f - firstOutside - secondOutside) / 2
    rw [m2PairSplitAllocation_three_eq_outside cost chores coreAllocation outsideAllocation hcoreThree,
      houtsideCard 3]
    simp [m2PairOutsideQuota, f]
  have htwoSmall : ∀ item ∈ allocation 2, IsSmallChore cost 2 item := by
    change ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 2,
      IsSmallChore cost 2 item
    exact m2PairSplitAllocation_two_ownSmall cost chores coreAllocation outsideAllocation
      hcoreTwo houtsideAllocation htwo
  have hthreeSmall : ∀ item ∈ allocation 3, IsSmallChore cost 3 item := by
    change ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 3,
      IsSmallChore cost 3 item
    exact m2PairSplitAllocation_three_ownSmall cost chores coreAllocation outsideAllocation
      hcoreThree houtsideAllocation htwo
  constructor
  · intro i hsmall
    exact smallItemCertificate_of_efx Item cost allocation hefx i hsmall
  · intro i hallLarge
    fin_cases i
    · obtain ⟨hzeroCoreEmpty, hzeroCrossEmpty⟩ :=
        m2PairSplitAllocation_zero_allLarge_forces_empty_smallParts r cost chores
          coreAllocation outsideAllocation (by linarith) hcoreAllocation hallLarge
      have hfirstCoreZero : firstCore = 0 := by
        rw [← hcoreZero, hzeroCoreEmpty]
        simp
      have hzeroCrossCard : b = 0 := by
        dsimp [b]
        rw [hzeroCrossEmpty]
        simp
      have hsecondCoreZero : secondCore = 0 := by
        dsimp [b, c, target] at hfirstTarget hsecondTarget hzeroToOne ⊢
        omega
      have hcoreOneEmpty : coreAllocation 1 = ∅ := by
        apply Finset.card_eq_zero.mp
        rw [hcoreOne, hsecondCoreZero]
      have hfirst : b + firstOutside = target := by
        dsimp [b, target] at hfirstTarget ⊢
        omega
      have hsecond : c + secondOutside = target := by
        dsimp [c, target] at hsecondTarget ⊢
        omega
      have hcoreZeroCard : a = 0 := by
        dsimp [a]
        rw [← hcoreShares, hfirstCoreZero, hsecondCoreZero]
      have hremainderNeThree : remainder ≠ 3 := by
        intro hthree
        rcases hzeroSafe with hne | hpositive | hpositive
        · exact hne hthree
        · have hzero : (m2PairCoreFibre cost chores 0 1).card = 0 := by
            simpa [a] using hcoreZeroCard
          omega
        · have hzero : (m2PairCrossFibre cost chores 0 1).card = 0 := by
            simpa [b] using hzeroCrossCard
          omega
      have htwoLower := m2Case31_outsideCards_at_least_target_of_no_small
        a b c f q remainder firstOutside secondOutside (by simpa [a, b, c, f] using hm)
          hremainder hcoreZeroCard hzeroCrossCard hfirst hsecond hremainderNeThree
      have hcardLower : ∀ other, target ≤ (allocation other).card := by
        intro other
        fin_cases other
        · exact Nat.le_of_eq hcardZero.symm
        · exact Nat.le_of_eq hcardOne.symm
        · change target ≤ (allocation 2).card
          rw [hcardTwo]
          exact htwoLower.1
        · change target ≤ (allocation 3).card
          rw [hcardThree]
          exact htwoLower.2
      have hotherLarge : ∀ other item, other ≠ 0 → item ∈ allocation other →
          IsLargeChore cost r 0 item := by
        intro other item hother hitem
        fin_cases other
        · exact (hother rfl).elim
        · change item ∈ coreAllocation 1 ∪
            (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) 1 ∪
              ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) 1 ∪
                outsideAllocation 1) at hitem
          simp [allocateAllTo, hcoreOneEmpty, hzeroCrossEmpty] at hitem
          rcases hitem with hcross | hout
          · exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 0 item
              (Finset.mem_filter.mp hcross).2.2
          · exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 0 item
              (Finset.mem_filter.mp (houtsideAllocation.1 1 item hout)).2.1
        · exact m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation
            0 2 (by linarith) hcost hcoreAllocation houtsideAllocation (Or.inl rfl) (Or.inl rfl)
              hcoreTwo item hitem
        · exact m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation
            0 3 (by linarith) hcost hcoreAllocation houtsideAllocation (Or.inl rfl) (Or.inr rfl)
              hcoreThree item hitem
      exact envyFreeForChores_single_special_of_all_large cost r allocation 0 target hcost
        (by linarith) hcardZero hcardLower hotherLarge hallLarge
    · obtain ⟨honeCoreEmpty, honeCrossEmpty⟩ :=
        m2PairSplitAllocation_one_allLarge_forces_empty_smallParts r cost chores
          coreAllocation outsideAllocation (by linarith) hcoreAllocation hallLarge
      have hsecondCoreZero : secondCore = 0 := by
        rw [← hcoreOne, honeCoreEmpty]
        simp
      have honeCrossCard : c = 0 := by
        dsimp [c]
        rw [honeCrossEmpty]
        simp
      have hfirstCoreZero : firstCore = 0 := by
        dsimp [b, c, target] at hfirstTarget hsecondTarget honeToZero ⊢
        omega
      have hcoreZeroEmpty : coreAllocation 0 = ∅ := by
        apply Finset.card_eq_zero.mp
        rw [hcoreZero, hfirstCoreZero]
      have hfirst : c + secondOutside = target := by
        dsimp [c, target] at hsecondTarget ⊢
        omega
      have hsecond : b + firstOutside = target := by
        dsimp [b, target] at hfirstTarget ⊢
        omega
      have hcoreZeroCard : a = 0 := by
        dsimp [a]
        rw [← hcoreShares, hfirstCoreZero, hsecondCoreZero]
      have hremainderNeThree : remainder ≠ 3 := by
        intro hthree
        rcases honeSafe with hne | hpositive | hpositive
        · exact hne hthree
        · have hzero : (m2PairCoreFibre cost chores 0 1).card = 0 := by
            simpa [a] using hcoreZeroCard
          omega
        · have hzero : (m2PairCrossFibre cost chores 1 0).card = 0 := by
            simpa [c] using honeCrossCard
          omega
      have htotalSwap : a + c + b + f = 4 * q + remainder := by
        simpa [a, b, c, f, add_comm, add_left_comm, add_assoc] using hm
      have htwoLower := m2Case31_outsideCards_at_least_target_of_no_small
        a c b f q remainder secondOutside firstOutside htotalSwap hremainder hcoreZeroCard
          honeCrossCard hfirst hsecond hremainderNeThree
      have hremainingSwap : f - firstOutside - secondOutside =
          f - secondOutside - firstOutside := by omega
      have hcardLower : ∀ other, target ≤ (allocation other).card := by
        intro other
        fin_cases other
        · exact Nat.le_of_eq hcardZero.symm
        · exact Nat.le_of_eq hcardOne.symm
        · change target ≤ (allocation 2).card
          rw [hcardTwo, hremainingSwap]
          exact htwoLower.1
        · change target ≤ (allocation 3).card
          rw [hcardThree, hremainingSwap]
          exact htwoLower.2
      have hotherLarge : ∀ other item, other ≠ 1 → item ∈ allocation other →
          IsLargeChore cost r 1 item := by
        intro other item hother hitem
        fin_cases other
        · change item ∈ coreAllocation 0 ∪
            (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) 0 ∪
              ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) 0 ∪
                outsideAllocation 0) at hitem
          simp [allocateAllTo, hcoreZeroEmpty, honeCrossEmpty] at hitem
          rcases hitem with hcross | hout
          · exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 1 item
              (Finset.mem_filter.mp hcross).2.2
          · exact isLargeChore_of_not_mem_smallAgentSet r cost hcost 1 item
              (Finset.mem_filter.mp (houtsideAllocation.1 0 item hout)).2.2
        · exact (hother rfl).elim
        · exact m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation
            1 2 (by linarith) hcost hcoreAllocation houtsideAllocation (Or.inr rfl) (Or.inl rfl)
              hcoreTwo item hitem
        · exact m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation
            1 3 (by linarith) hcost hcoreAllocation houtsideAllocation (Or.inr rfl) (Or.inr rfl)
              hcoreThree item hitem
      exact envyFreeForChores_single_special_of_all_large cost r allocation 1 target hcost
        (by linarith) hcardOne hcardLower hotherLarge hallLarge
    · have hempty : allocation 2 = ∅ := by
        by_contra hnotempty
        obtain ⟨item, hitem⟩ := Finset.nonempty_iff_ne_empty.mpr hnotempty
        have hsmall := htwoSmall item hitem
        have hlarge : cost 2 item = r := by simpa [IsLargeChore] using hallLarge item hitem
        rw [IsSmallChore] at hsmall
        linarith
      intro other
      change additiveChoreCost cost 2 (allocation 2) ≤ additiveChoreCost cost 2 (allocation other)
      rw [hempty]
      simp only [additiveChoreCost, Finset.sum_empty]
      exact additiveChoreCost_nonneg cost
        (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 2 (allocation other)
    · have hempty : allocation 3 = ∅ := by
        by_contra hnotempty
        obtain ⟨item, hitem⟩ := Finset.nonempty_iff_ne_empty.mpr hnotempty
        have hsmall := hthreeSmall item hitem
        have hlarge : cost 3 item = r := by simpa [IsLargeChore] using hallLarge item hitem
        rw [IsSmallChore] at hsmall
        linarith
      intro other
      change additiveChoreCost cost 3 (allocation 3) ≤ additiveChoreCost cost 3 (allocation other)
      rw [hempty]
      simp only [additiveChoreCost, Finset.sum_empty]
      exact additiveChoreCost_nonneg cost
        (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 3 (allocation other)

/-- The four-case integer check in source Case 3.2.2.  For `f = 4p+t`, the
unique common-small chore goes to agent `0`, agents `0,1` receive respectively
`ℓ₁=p` and `ℓ₂=p+⌊t/2⌋` outside-fiber chores, and the residual outside fiber
is split evenly between agents `2,3`.  The three displayed inequalities are
exactly equation (tcheck) in the source. -/
theorem m2Case322_tcheck (p t : ℕ) (ht : t < 4) :
    let firstOutside := p
    let secondOutside := p + t / 2
    let remaining := 4 * p + t - firstOutside - secondOutside
    firstOutside ≤ remaining / 2 ∧
      secondOutside - 1 ≤ remaining / 2 ∧
      remaining - remaining / 2 - 1 ≤ secondOutside ∧
      remaining / 2 ≤ remaining - remaining / 2 ∧
      remaining - remaining / 2 ≤ remaining / 2 + 1 := by
  dsimp
  interval_cases t <;> norm_num at * <;> omega

/-- The last numerical comparison used for agents `2,3` in Case 3.2.2:
their cost for agent `0`'s core-plus-outside bundle, `r+p`, dominates the
second outside share `ℓ₂`. -/
theorem m2Case322_secondOutside_le_coreCost (p t : ℕ) (r : ℝ)
    (hr : 1 ≤ r) (ht : t < 4) :
    ((p + t / 2 : ℕ) : ℝ) ≤ r + p := by
  interval_cases t <;> norm_num at * <;> linarith

/-- The two outside shares in Case 3.2.2 differ by at most one.  This is the
comparison between agents `0` and `1` used after their respective deletions. -/
theorem m2Case322_secondOutside_le_firstOutside_one (p t : ℕ) (ht : t < 4) :
    p + t / 2 ≤ p + 1 := by
  interval_cases t <;> norm_num at *

/-- The integer choice behind source Case 3.2.3.  The displayed witness is
the floor of the upper endpoint of the source interval for `L`.  Its two
inequalities say respectively that the residual even split is large enough
for the pair agents and not too large for the complementary agents.  The
second bound is stated with `2p⁻`, which is sufficient because the paper
assumes `r>2`. -/
theorem m2Case323_exists_outsideShare (a f : ℕ) (ha : 2 ≤ a) (hfa : a < f) :
    let pminus := a / 2
    let pplus := (a + 1) / 2
    ∃ L : ℕ,
      4 * L ≤ f - 2 * pplus + 2 ∧
      f - 2 * L - (f - 2 * L) / 2 ≤ L + 2 * pminus + 1 := by
  dsimp
  refine ⟨(f - 2 * ((a + 1) / 2) + 2) / 4, ?_, ?_⟩ <;> omega

/-- In the Case 3.2.2 split, agent `0` does not strongly envy agent `1`.
After deleting a chore from agent `0`'s core-plus-`p` outside bundle, the
large-count upper bound is at most the cost of agent `1`'s `ℓ₂` all-large
outside bundle. -/
private theorem m2Case322_zero_to_one_efx
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (p t : ℕ) (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1))
    (hcoreCard : ∀ agent, (coreAllocation agent).card = m2PairCoreQuota 0 1 1 0 agent)
    (houtsideCard : ∀ agent, (outsideAllocation agent).card =
      m2PairOutsideQuota p (p + t / 2) (m2PairOutsideFibre cost chores 0 1).card agent)
    (hcrossFirstEmpty : m2PairCrossFibre cost chores 0 1 = ∅)
    (hcrossSecondEmpty : m2PairCrossFibre cost chores 1 0 = ∅) :
    ∀ item ∈ m2PairSplitAllocation cost chores coreAllocation outsideAllocation 0,
      additiveChoreCost cost 0
        (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 0 \ {item}) ≤
        additiveChoreCost cost 0
          (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 1) := by
  let allocation := m2PairSplitAllocation cost chores coreAllocation outsideAllocation
  have hcoreZero : (coreAllocation 0).card = 1 := by
    simpa [m2PairCoreQuota] using hcoreCard 0
  have houtsideZero : (outsideAllocation 0).card = p := by
    simpa [m2PairOutsideQuota] using houtsideCard 0
  have houtsideOne : (outsideAllocation 1).card = p + t / 2 := by
    simpa [m2PairOutsideQuota] using houtsideCard 1
  have hcardZero : (allocation 0).card = p + 1 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0).card = p + 1
    rw [m2PairSplitAllocation_zero_card cost chores coreAllocation outsideAllocation 1 p
      hcoreAllocation houtsideAllocation hcoreZero houtsideZero, hcrossFirstEmpty]
    simp
    omega
  have hcoreOneEmpty : coreAllocation 1 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 1
  have hcardOne : (allocation 1).card = p + t / 2 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1).card = p + t / 2
    simp [allocateAllTo, hcoreOneEmpty, hcrossSecondEmpty, houtsideOne]
  have hlargeZero : (largeChoreSet cost r 0 (allocation 0)).card = p := by
    change (largeChoreSet cost r 0
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0)).card = p
    rw [m2PairSplitAllocation_zero_largeSet r cost chores coreAllocation outsideAllocation
      hr hcost hcoreAllocation houtsideAllocation, houtsideZero]
  have hlargeOne : (largeChoreSet cost r 0 (allocation 1)).card = p + t / 2 := by
    change (largeChoreSet cost r 0
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1)).card = p + t / 2
    rw [m2PairSplitAllocation_one_largeSet_for_zero r cost chores coreAllocation outsideAllocation
      hr hcost hcoreAllocation houtsideAllocation, hcrossSecondEmpty]
    simp [houtsideOne]
  have hshare : p ≤ p + t / 2 := Nat.le_add_right _ _
  have hshareReal : (p : ℝ) ≤ ((p + t / 2 : ℕ) : ℝ) := by exact_mod_cast hshare
  have hfactor : 0 ≤ r - 1 := by linarith
  have hbound : (((p + 1 - 1 : ℕ) : ℝ) + (r - 1) * p) ≤
      ((p + t / 2 : ℕ) : ℝ) + (r - 1) * ((p + t / 2 : ℕ) : ℝ) := by
    norm_num
    nlinarith [mul_nonneg hfactor (sub_nonneg.mpr hshareReal)]
  change ∀ item ∈ allocation 0,
    additiveChoreCost cost 0 (allocation 0 \ {item}) ≤ additiveChoreCost cost 0 (allocation 1)
  exact additiveChoreCost_erase_le_of_card_largeCard_upper cost r allocation 0 1
    (p + 1) (p + t / 2) p (p + t / 2) hcost (by linarith)
    hcardZero hcardOne hlargeZero hlargeOne hbound

/-- In the Case 3.2.2 split, agent `1` does not strongly envy agent `0`.
Agent `1`'s bundle is all large, while agent `0` has `p` large outside chores
and one small core chore from agent `1`'s perspective.  The elementary bound
`ℓ₂ ≤ p+1` is enough after deleting one all-large chore. -/
private theorem m2Case322_one_to_zero_efx
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (p t : ℕ) (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1))
    (hcoreCard : ∀ agent, (coreAllocation agent).card = m2PairCoreQuota 0 1 1 0 agent)
    (houtsideCard : ∀ agent, (outsideAllocation agent).card =
      m2PairOutsideQuota p (p + t / 2) (m2PairOutsideFibre cost chores 0 1).card agent)
    (hcrossFirstEmpty : m2PairCrossFibre cost chores 0 1 = ∅)
    (hcrossSecondEmpty : m2PairCrossFibre cost chores 1 0 = ∅)
    (ht : t < 4) :
    ∀ item ∈ m2PairSplitAllocation cost chores coreAllocation outsideAllocation 1,
      additiveChoreCost cost 1
        (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 1 \ {item}) ≤
        additiveChoreCost cost 1
          (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 0) := by
  let allocation := m2PairSplitAllocation cost chores coreAllocation outsideAllocation
  have hcoreZero : (coreAllocation 0).card = 1 := by
    simpa [m2PairCoreQuota] using hcoreCard 0
  have hcoreOneEmpty : coreAllocation 1 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 1
  have houtsideZero : (outsideAllocation 0).card = p := by
    simpa [m2PairOutsideQuota] using houtsideCard 0
  have houtsideOne : (outsideAllocation 1).card = p + t / 2 := by
    simpa [m2PairOutsideQuota] using houtsideCard 1
  have hcardZero : (allocation 0).card = p + 1 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0).card = p + 1
    rw [m2PairSplitAllocation_zero_card cost chores coreAllocation outsideAllocation 1 p
      hcoreAllocation houtsideAllocation hcoreZero houtsideZero, hcrossFirstEmpty]
    simp
    omega
  have hcardOne : (allocation 1).card = p + t / 2 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1).card = p + t / 2
    simp [allocateAllTo, hcoreOneEmpty, hcrossSecondEmpty, houtsideOne]
  have hallLargeOne : ∀ item ∈ allocation 1, IsLargeChore cost r 1 item := by
    change ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1,
      IsLargeChore cost r 1 item
    exact m2PairSplitAllocation_one_allLarge_of_crossSecondEmpty r cost chores coreAllocation
      outsideAllocation hcost hcoreOneEmpty hcrossSecondEmpty houtsideAllocation
  have hlargeZero : (largeChoreSet cost r 1 (allocation 0)).card = p := by
    change (largeChoreSet cost r 1
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0)).card = p
    rw [m2PairSplitAllocation_zero_largeSet_for_one r cost chores coreAllocation outsideAllocation
      hr hcost hcoreAllocation houtsideAllocation, hcrossFirstEmpty]
    simp [houtsideZero]
  have hshare : p + t / 2 - 1 ≤ p := by
    have hbound := m2Case322_secondOutside_le_firstOutside_one p t ht
    omega
  have hshareReal : ((p + t / 2 - 1 : ℕ) : ℝ) ≤ p := by
    exact_mod_cast hshare
  have hrnonneg : 0 ≤ r := by linarith
  have hscale : ((p + t / 2 - 1 : ℕ) : ℝ) * r ≤ (p : ℝ) * r :=
    mul_le_mul_of_nonneg_right hshareReal hrnonneg
  have hright : (p : ℝ) * r ≤
      ((p + 1 : ℕ) : ℝ) + (r - 1) * (p : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_one]
    ring_nf
    linarith
  have hbound : (((p + t / 2 - 1 : ℕ) : ℝ) * r) ≤
      ((p + 1 : ℕ) : ℝ) + (r - 1) * (p : ℝ) := by
    exact hscale.trans hright
  change ∀ item ∈ allocation 1,
    additiveChoreCost cost 1 (allocation 1 \ {item}) ≤ additiveChoreCost cost 1 (allocation 0)
  exact additiveChoreCost_erase_le_of_allLarge_first cost r allocation 1 0
    (p + t / 2) (p + 1) p hcost hcardOne hcardZero hallLargeOne hlargeZero hbound

/-- The complete EFX check for the labelled Case 3.2.2 split.  This follows
the source comparison table: the pair agents use large-count estimates, the
complementary agents have own-small bundles, and their comparison with agent
`0` uses the exact value `r+p` of that bundle. -/
private theorem efxOfM2PairCase322Split
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (p t : ℕ) (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1))
    (hcoreCard : ∀ agent, (coreAllocation agent).card = m2PairCoreQuota 0 1 1 0 agent)
    (houtsideCard : ∀ agent, (outsideAllocation agent).card =
      m2PairOutsideQuota p (p + t / 2) (m2PairOutsideFibre cost chores 0 1).card agent)
    (hcrossFirstEmpty : m2PairCrossFibre cost chores 0 1 = ∅)
    (hcrossSecondEmpty : m2PairCrossFibre cost chores 1 0 = ∅)
    (houtsideFibreCard : (m2PairOutsideFibre cost chores 0 1).card = 4 * p + t)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item) (ht : t < 4) :
    EFXForChores (additiveChoreCost cost)
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation) := by
  let allocation := m2PairSplitAllocation cost chores coreAllocation outsideAllocation
  let remaining := 4 * p + t - p - (p + t / 2)
  have hrOne : 1 ≤ r := by linarith
  have hrZero : 0 ≤ r := by linarith
  have htcheck : p ≤ remaining / 2 ∧
      p + t / 2 - 1 ≤ remaining / 2 ∧
      remaining - remaining / 2 - 1 ≤ p + t / 2 ∧
      remaining / 2 ≤ remaining - remaining / 2 ∧
      remaining - remaining / 2 ≤ remaining / 2 + 1 := by
    simpa [remaining] using m2Case322_tcheck p t ht
  rcases htcheck with ⟨hfirstOutside, hsecondOutside, hlastOutside,
    hlowHigh, hhighLow⟩
  have hcoreZero : (coreAllocation 0).card = 1 := by
    simpa [m2PairCoreQuota] using hcoreCard 0
  have hcoreOneCard : (coreAllocation 1).card = 0 := by
    simpa [m2PairCoreQuota] using hcoreCard 1
  have hcoreTwoCard : (coreAllocation 2).card = 0 := by
    simpa [m2PairCoreQuota] using hcoreCard 2
  have hcoreThreeCard : (coreAllocation 3).card = 0 := by
    simpa [m2PairCoreQuota] using hcoreCard 3
  have hcoreOneEmpty : coreAllocation 1 = ∅ := Finset.card_eq_zero.mp hcoreOneCard
  have hcoreTwoEmpty : coreAllocation 2 = ∅ := Finset.card_eq_zero.mp hcoreTwoCard
  have hcoreThreeEmpty : coreAllocation 3 = ∅ := Finset.card_eq_zero.mp hcoreThreeCard
  have houtsideZero : (outsideAllocation 0).card = p := by
    simpa [m2PairOutsideQuota] using houtsideCard 0
  have houtsideOne : (outsideAllocation 1).card = p + t / 2 := by
    simpa [m2PairOutsideQuota] using houtsideCard 1
  have houtsideTwo : (outsideAllocation 2).card = remaining / 2 := by
    calc
      (outsideAllocation 2).card =
          ((m2PairOutsideFibre cost chores 0 1).card - p - (p + t / 2)) / 2 := by
        simpa [m2PairOutsideQuota] using houtsideCard 2
      _ = remaining / 2 := by simp [houtsideFibreCard, remaining]
  have houtsideThree : (outsideAllocation 3).card = remaining - remaining / 2 := by
    calc
      (outsideAllocation 3).card =
          (m2PairOutsideFibre cost chores 0 1).card - p - (p + t / 2) -
            ((m2PairOutsideFibre cost chores 0 1).card - p - (p + t / 2)) / 2 := by
        simpa [m2PairOutsideQuota] using houtsideCard 3
      _ = remaining - remaining / 2 := by simp [houtsideFibreCard, remaining]
  have hcardZero : (allocation 0).card = p + 1 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0).card = p + 1
    rw [m2PairSplitAllocation_zero_card cost chores coreAllocation outsideAllocation 1 p
      hcoreAllocation houtsideAllocation hcoreZero houtsideZero, hcrossFirstEmpty]
    simp
    omega
  have hcardOne : (allocation 1).card = p + t / 2 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1).card = p + t / 2
    simp [allocateAllTo, hcoreOneEmpty, hcrossSecondEmpty, houtsideOne]
  have hcardTwo : (allocation 2).card = remaining / 2 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 2).card = remaining / 2
    rw [m2PairSplitAllocation_two_eq_outside cost chores coreAllocation outsideAllocation
      hcoreTwoEmpty]
    exact houtsideTwo
  have hcardThree : (allocation 3).card = remaining - remaining / 2 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 3).card = remaining - remaining / 2
    rw [m2PairSplitAllocation_three_eq_outside cost chores coreAllocation outsideAllocation
      hcoreThreeEmpty]
    exact houtsideThree
  have hlargeZero : (largeChoreSet cost r 0 (allocation 0)).card = p := by
    change (largeChoreSet cost r 0
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0)).card = p
    rw [m2PairSplitAllocation_zero_largeSet r cost chores coreAllocation outsideAllocation
      hr hcost hcoreAllocation houtsideAllocation, houtsideZero]
  have hlargeOne : (largeChoreSet cost r 1 (allocation 1)).card = p + t / 2 := by
    change (largeChoreSet cost r 1
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1)).card = p + t / 2
    rw [m2PairSplitAllocation_one_largeSet r cost chores coreAllocation outsideAllocation
      hr hcost hcoreAllocation houtsideAllocation, houtsideOne]
  have htwoSmall : ∀ item ∈ allocation 2, IsSmallChore cost 2 item := by
    change ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 2,
      IsSmallChore cost 2 item
    exact m2PairSplitAllocation_two_ownSmall cost chores coreAllocation outsideAllocation
      hcoreTwoEmpty houtsideAllocation htwo
  have hthreeSmall : ∀ item ∈ allocation 3, IsSmallChore cost 3 item := by
    change ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 3,
      IsSmallChore cost 3 item
    exact m2PairSplitAllocation_three_ownSmall cost chores coreAllocation outsideAllocation
      hcoreThreeEmpty houtsideAllocation htwo
  have hzeroToTwoLarge : ∀ item ∈ allocation 2, IsLargeChore cost r 0 item := by
    change ∀ item ∈ m2PairSplitAllocation cost chores coreAllocation outsideAllocation 2,
      IsLargeChore cost r 0 item
    exact m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 0 2
      hr hcost hcoreAllocation houtsideAllocation (Or.inl rfl) (Or.inl rfl) hcoreTwoEmpty
  have hzeroToThreeLarge : ∀ item ∈ allocation 3, IsLargeChore cost r 0 item := by
    change ∀ item ∈ m2PairSplitAllocation cost chores coreAllocation outsideAllocation 3,
      IsLargeChore cost r 0 item
    exact m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 0 3
      hr hcost hcoreAllocation houtsideAllocation (Or.inl rfl) (Or.inr rfl) hcoreThreeEmpty
  have honeToTwoLarge : ∀ item ∈ allocation 2, IsLargeChore cost r 1 item := by
    change ∀ item ∈ m2PairSplitAllocation cost chores coreAllocation outsideAllocation 2,
      IsLargeChore cost r 1 item
    exact m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 1 2
      hr hcost hcoreAllocation houtsideAllocation (Or.inr rfl) (Or.inl rfl) hcoreTwoEmpty
  have honeToThreeLarge : ∀ item ∈ allocation 3, IsLargeChore cost r 1 item := by
    change ∀ item ∈ m2PairSplitAllocation cost chores coreAllocation outsideAllocation 3,
      IsLargeChore cost r 1 item
    exact m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 1 3
      hr hcost hcoreAllocation houtsideAllocation (Or.inr rfl) (Or.inr rfl) hcoreThreeEmpty
  have hcoreTwoLarge : ∀ item ∈ coreAllocation 0, IsLargeChore cost r 2 item := by
    intro item hitem
    have hpool : item ∈ m2PairCoreFibre cost chores 0 1 := hcoreAllocation.1 0 item hitem
    exact m2PairCoreFibre_large_for_two r cost chores item hcost
      (htwo item (Finset.mem_filter.mp hpool).1) hpool
  have houtsideTwoSmall : ∀ item ∈ outsideAllocation 0, IsSmallChore cost 2 item := by
    intro item hitem
    have hpool : item ∈ m2PairOutsideFibre cost chores 0 1 :=
      houtsideAllocation.1 0 item hitem
    exact m2PairOutsideFibre_small_for_two cost chores item
      (htwo item (Finset.mem_filter.mp hpool).1) hpool
  have hcoreThreeLarge : ∀ item ∈ coreAllocation 0, IsLargeChore cost r 3 item := by
    intro item hitem
    have hpool : item ∈ m2PairCoreFibre cost chores 0 1 := hcoreAllocation.1 0 item hitem
    exact m2PairCoreFibre_large_for_three r cost chores item hcost
      (htwo item (Finset.mem_filter.mp hpool).1) hpool
  have houtsideThreeSmall : ∀ item ∈ outsideAllocation 0, IsSmallChore cost 3 item := by
    intro item hitem
    have hpool : item ∈ m2PairOutsideFibre cost chores 0 1 :=
      houtsideAllocation.1 0 item hitem
    exact m2PairOutsideFibre_small_for_three cost chores item
      (htwo item (Finset.mem_filter.mp hpool).1) hpool
  have hzeroCostTwo : additiveChoreCost cost 2 (allocation 0) = r + p := by
    change additiveChoreCost cost 2
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0) = r + p
    exact m2PairSplitAllocation_zero_cost_of_coreLarge_outsideSmall r cost chores
      coreAllocation outsideAllocation 2 p hr hcost hcoreAllocation houtsideAllocation
      hcrossFirstEmpty hcoreZero houtsideZero hcoreTwoLarge houtsideTwoSmall
  have hzeroCostThree : additiveChoreCost cost 3 (allocation 0) = r + p := by
    change additiveChoreCost cost 3
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0) = r + p
    exact m2PairSplitAllocation_zero_cost_of_coreLarge_outsideSmall r cost chores
      coreAllocation outsideAllocation 3 p hr hcost hcoreAllocation houtsideAllocation
      hcrossFirstEmpty hcoreZero houtsideZero hcoreThreeLarge houtsideThreeSmall
  have hzeroToTwoCard : p + 1 - 1 ≤ (allocation 2).card := by
    rw [hcardTwo]
    omega
  have hzeroToThreeCard : p + 1 - 1 ≤ (allocation 3).card := by
    rw [hcardThree]
    omega
  have honeToTwoCard : p + t / 2 - 1 ≤ (allocation 2).card := by
    rw [hcardTwo]
    exact hsecondOutside
  have honeToThreeCard : p + t / 2 - 1 ≤ (allocation 3).card := by
    rw [hcardThree]
    omega
  have htwoToOneCard : (allocation 2).card ≤ (allocation 1).card + 1 := by
    rw [hcardTwo, hcardOne]
    omega
  have hthreeToOneCard : (allocation 3).card ≤ (allocation 1).card + 1 := by
    rw [hcardThree, hcardOne]
    omega
  have htwoToThreeCard : (allocation 2).card ≤ (allocation 3).card + 1 := by
    rw [hcardTwo, hcardThree]
    omega
  have hthreeToTwoCard : (allocation 3).card ≤ (allocation 2).card + 1 := by
    rw [hcardThree, hcardTwo]
    exact hhighLow
  have htwoToZeroBound : (((allocation 2).card - 1 : ℕ) : ℝ) ≤
      additiveChoreCost cost 2 (allocation 0) := by
    rw [hcardTwo, hzeroCostTwo]
    have hlowLast : remaining / 2 - 1 ≤ p + t / 2 := by omega
    have hlowLastReal : ((remaining / 2 - 1 : ℕ) : ℝ) ≤ ((p + t / 2 : ℕ) : ℝ) := by
      exact_mod_cast hlowLast
    exact hlowLastReal.trans (m2Case322_secondOutside_le_coreCost p t r hrOne ht)
  have hthreeToZeroBound : (((allocation 3).card - 1 : ℕ) : ℝ) ≤
      additiveChoreCost cost 3 (allocation 0) := by
    rw [hcardThree, hzeroCostThree]
    have hlastReal : ((remaining - remaining / 2 - 1 : ℕ) : ℝ) ≤ ((p + t / 2 : ℕ) : ℝ) := by
      exact_mod_cast hlastOutside
    exact hlastReal.trans (m2Case322_secondOutside_le_coreCost p t r hrOne ht)
  rw [efxForChores_iff_forall_doesNotStronglyEnvy]
  intro i j
  fin_cases i <;> fin_cases j
  · exact doesNotStronglyEnvyForChores_self_of_nonneg cost allocation 0
      (fun item => IsOneOrRChoreCost.nonneg cost r hcost hrZero 0 item)
  · exact Or.inr (m2Case322_zero_to_one_efx r cost chores coreAllocation outsideAllocation
      p t hr hcost hcoreAllocation houtsideAllocation hcoreCard houtsideCard
      hcrossFirstEmpty hcrossSecondEmpty)
  · exact Or.inr (additiveChoreCost_erase_le_of_allLarge_comparison cost r allocation 0 2
      (p + 1) p hcost hrOne hcardZero hlargeZero hzeroToTwoLarge hzeroToTwoCard)
  · exact Or.inr (additiveChoreCost_erase_le_of_allLarge_comparison cost r allocation 0 3
      (p + 1) p hcost hrOne hcardZero hlargeZero hzeroToThreeLarge hzeroToThreeCard)
  · exact Or.inr (m2Case322_one_to_zero_efx r cost chores coreAllocation outsideAllocation
      p t hr hcost hcoreAllocation houtsideAllocation hcoreCard houtsideCard
      hcrossFirstEmpty hcrossSecondEmpty ht)
  · exact doesNotStronglyEnvyForChores_self_of_nonneg cost allocation 1
      (fun item => IsOneOrRChoreCost.nonneg cost r hcost hrZero 1 item)
  · exact Or.inr (additiveChoreCost_erase_le_of_allLarge_comparison cost r allocation 1 2
      (p + t / 2) (p + t / 2) hcost hrOne hcardOne hlargeOne honeToTwoLarge
      honeToTwoCard)
  · exact Or.inr (additiveChoreCost_erase_le_of_allLarge_comparison cost r allocation 1 3
      (p + t / 2) (p + t / 2) hcost hrOne hcardOne hlargeOne honeToThreeLarge
      honeToThreeCard)
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_costLower cost allocation 2 0
      htwoSmall htwoToZeroBound
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 2 1 hcost
      hrOne htwoSmall htwoToOneCard
  · exact doesNotStronglyEnvyForChores_self_of_nonneg cost allocation 2
      (fun item => IsOneOrRChoreCost.nonneg cost r hcost hrZero 2 item)
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 2 3 hcost
      hrOne htwoSmall htwoToThreeCard
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_costLower cost allocation 3 0
      hthreeSmall hthreeToZeroBound
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 3 1 hcost
      hrOne hthreeSmall hthreeToOneCard
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 3 2 hcost
      hrOne hthreeSmall hthreeToTwoCard
  · exact doesNotStronglyEnvyForChores_self_of_nonneg cost allocation 3
      (fun item => IsOneOrRChoreCost.nonneg cost r hcost hrZero 3 item)

/-- The finite allocation selected in source Case 3.2.2, before its EFX
verification.  The sole common-small chore goes to agent `0`; the two
specified outside-fiber shares are `p` and `p + ⌊t/2⌋`, and the rest is split
evenly between agents `2,3`. -/
theorem existsM2Case322Allocation
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (p t : ℕ)
    (hcore : (m2PairCoreFibre cost chores 0 1).card = 1)
    (houtside : (m2PairOutsideFibre cost chores 0 1).card = 4 * p + t)
    (ht : t < 4) :
    ∃ coreAllocation outsideAllocation : Allocation (Fin 4) Item,
      IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1) ∧
      (∀ agent, (coreAllocation agent).card = m2PairCoreQuota 0 1 1 0 agent) ∧
      IsAllocationOf outsideAllocation (m2PairOutsideFibre cost chores 0 1) ∧
      (∀ agent, (outsideAllocation agent).card =
        m2PairOutsideQuota p (p + t / 2)
          (m2PairOutsideFibre cost chores 0 1).card agent) ∧
      IsAllocationOf
        (fun agent => coreAllocation agent ∪
          (allocateAllTo (Fin 4) Item 0
            (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1
            (m2PairCrossFibre cost chores 1 0)) agent ∪ outsideAllocation agent))
        chores := by
  apply existsM2PairSplitAllocation Item cost chores 1 0 p (p + t / 2)
  · omega
  · rw [houtside]
    omega

/-- Source Case 3.2.2 in its displayed labelling.  When the `12` core fiber
has one chore, both cross fibers are empty, and the `34` fiber has size
`4p+t`, the paper's prescribed allocation is feasible and EFX. -/
theorem existsEfxOfM2PairCase322Labelled
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (p t : ℕ)
    (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcore : (m2PairCoreFibre cost chores 0 1).card = 1)
    (hcrossFirst : (m2PairCrossFibre cost chores 0 1).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores 1 0).card = 0)
    (houtside : (m2PairOutsideFibre cost chores 0 1).card = 4 * p + t)
    (ht : t < 4) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  classical
  have hcrossFirstEmpty : m2PairCrossFibre cost chores 0 1 = ∅ :=
    Finset.card_eq_zero.mp hcrossFirst
  have hcrossSecondEmpty : m2PairCrossFibre cost chores 1 0 = ∅ :=
    Finset.card_eq_zero.mp hcrossSecond
  obtain ⟨coreAllocation, outsideAllocation, hcoreAllocation, hcoreCard,
    houtsideAllocation, houtsideCard, hallocation⟩ :=
    existsM2Case322Allocation Item cost chores p t hcore houtside ht
  refine ⟨m2PairSplitAllocation cost chores coreAllocation outsideAllocation, ?_, ?_⟩
  · change IsAllocationOf
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) chores
    exact hallocation
  · exact efxOfM2PairCase322Split r cost chores coreAllocation outsideAllocation p t hr hcost
      hcoreAllocation houtsideAllocation hcoreCard houtsideCard hcrossFirstEmpty hcrossSecondEmpty
      houtside htwo ht

/-- Case 3.2.2 for an arbitrary ordered deficient pair, obtained by moving
that pair to the source labels `0,1`, applying the labelled construction, and
transporting the resulting EFX allocation back. -/
theorem existsEfxOfM2PairCase322
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4) (p t : ℕ)
    (hdistinct : first ≠ second) (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcore : (m2PairCoreFibre cost chores first second).card = 1)
    (hcrossFirst : (m2PairCrossFibre cost chores first second).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores second first).card = 0)
    (houtside : (m2PairOutsideFibre cost chores first second).card = 4 * p + t)
    (ht : t < 4) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  classical
  obtain ⟨labels, hzero, hone⟩ := existsFin4Equiv_map_zero_one first second hdistinct
  apply exists_efx_relabel_back labels cost chores
  apply existsEfxOfM2PairCase322Labelled Item r (relabelChoreCost labels cost) chores p t hr
    (IsOneOrRChoreCost.relabel labels cost r hcost)
  · intro item hitem
    exact IsSmallForExactlyTwo.relabel labels cost item (htwo item hitem)
  · rw [m2PairCoreFibre_relabel_zero_one labels cost chores first second hzero hone]
    exact hcore
  · obtain ⟨hfirst, hsecond⟩ :=
      m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
    rw [hfirst]
    exact hcrossFirst
  · obtain ⟨hfirst, hsecond⟩ :=
      m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
    rw [hsecond]
    exact hcrossSecond
  · rw [m2PairOutsideFibre_relabel_zero_one labels cost chores first second hzero hone]
    exact houtside
  · exact ht

/-- The finite allocation used in source Case 3.2.3 once an outside share
`L` has been chosen.  The common-small fiber is split as evenly as possible
between agents `0,1`, both receive `L` outside chores, and the residual is
split evenly between agents `2,3`. -/
theorem existsM2Case323Allocation
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a f L : ℕ)
    (hcore : (m2PairCoreFibre cost chores 0 1).card = a)
    (houtside : (m2PairOutsideFibre cost chores 0 1).card = f)
    (houtsideSplit : 2 * L ≤ f) :
    ∃ coreAllocation outsideAllocation : Allocation (Fin 4) Item,
      IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1) ∧
      (∀ agent, (coreAllocation agent).card =
        m2PairCoreQuota 0 1 ((a + 1) / 2) (a / 2) agent) ∧
      IsAllocationOf outsideAllocation (m2PairOutsideFibre cost chores 0 1) ∧
      (∀ agent, (outsideAllocation agent).card =
        m2PairOutsideQuota L L (m2PairOutsideFibre cost chores 0 1).card agent) ∧
      IsAllocationOf
        (fun agent => coreAllocation agent ∪
          (allocateAllTo (Fin 4) Item 0
            (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1
            (m2PairCrossFibre cost chores 1 0)) agent ∪ outsideAllocation agent))
        chores := by
  apply existsM2PairSplitAllocation Item cost chores ((a + 1) / 2) (a / 2) L L
  · rw [hcore]
    omega
  · rw [houtside]
    omega

private theorem efxOfM2PairCase323Split
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (a f L : ℕ) (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation
      (m2PairOutsideFibre cost chores 0 1))
    (hcoreCard : ∀ agent, (coreAllocation agent).card =
      m2PairCoreQuota 0 1 ((a + 1) / 2) (a / 2) agent)
    (houtsideCard : ∀ agent, (outsideAllocation agent).card =
      m2PairOutsideQuota L L (m2PairOutsideFibre cost chores 0 1).card agent)
    (hcrossFirstEmpty : m2PairCrossFibre cost chores 0 1 = ∅)
    (hcrossSecondEmpty : m2PairCrossFibre cost chores 1 0 = ∅)
    (houtsideFibreCard : (m2PairOutsideFibre cost chores 0 1).card = f)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hfa : a < f)
    (hupper : 4 * L ≤ f - 2 * ((a + 1) / 2) + 2)
    (hlower : f - 2 * L - (f - 2 * L) / 2 ≤ L + 2 * (a / 2) + 1) :
    EFXForChores (additiveChoreCost cost)
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation) := by
  let allocation := m2PairSplitAllocation cost chores coreAllocation outsideAllocation
  let pminus := a / 2
  let pplus := (a + 1) / 2
  let remaining := f - L - L
  have hrStrict : 1 < r := by linarith
  have hrOne : 1 ≤ r := by linarith
  have hrTwo : 2 ≤ r := by linarith
  have hrZero : 0 ≤ r := by linarith
  have hremaining : remaining = f - 2 * L := by
    simp [remaining, Nat.sub_sub, two_mul]
  have hlower' : remaining - remaining / 2 ≤ L + 2 * pminus + 1 := by
    simpa [hremaining, pminus] using hlower
  have hupper' : 4 * L ≤ f - 2 * pplus + 2 := by
    simpa [pplus] using hupper
  have hcoreZero : (coreAllocation 0).card = pplus := by
    simpa [pplus, m2PairCoreQuota] using hcoreCard 0
  have hcoreOne : (coreAllocation 1).card = pminus := by
    simpa [pminus, m2PairCoreQuota] using hcoreCard 1
  have hcoreTwoEmpty : coreAllocation 2 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 2
  have hcoreThreeEmpty : coreAllocation 3 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 3
  have houtsideZero : (outsideAllocation 0).card = L := by
    simpa [m2PairOutsideQuota] using houtsideCard 0
  have houtsideOne : (outsideAllocation 1).card = L := by
    simpa [m2PairOutsideQuota] using houtsideCard 1
  have houtsideTwo : (outsideAllocation 2).card = remaining / 2 := by
    calc
      (outsideAllocation 2).card =
          ((m2PairOutsideFibre cost chores 0 1).card - L - L) / 2 := by
        simpa [m2PairOutsideQuota] using houtsideCard 2
      _ = remaining / 2 := by simp [houtsideFibreCard, remaining]
  have houtsideThree : (outsideAllocation 3).card = remaining - remaining / 2 := by
    calc
      (outsideAllocation 3).card =
          (m2PairOutsideFibre cost chores 0 1).card - L - L -
            ((m2PairOutsideFibre cost chores 0 1).card - L - L) / 2 := by
        simpa [m2PairOutsideQuota] using houtsideCard 3
      _ = remaining - remaining / 2 := by simp [houtsideFibreCard, remaining]
  have hcardZero : (allocation 0).card = pplus + L := by
    change ((fun agent => coreAllocation agent ∪
      (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
        ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
          outsideAllocation agent)) 0).card = pplus + L
    rw [m2PairSplitAllocation_zero_card cost chores coreAllocation outsideAllocation pplus L
      hcoreAllocation houtsideAllocation hcoreZero houtsideZero, hcrossFirstEmpty]
    simp
  have hcardOne : (allocation 1).card = pminus + L := by
    change ((fun agent => coreAllocation agent ∪
      (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
        ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
          outsideAllocation agent)) 1).card = pminus + L
    rw [m2PairSplitAllocation_one_card cost chores coreAllocation outsideAllocation pminus L
      hcoreAllocation houtsideAllocation hcoreOne houtsideOne, hcrossSecondEmpty]
    simp
  have hcardTwo : (allocation 2).card = remaining / 2 := by
    change ((fun agent => coreAllocation agent ∪
      (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
        ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
          outsideAllocation agent)) 2).card = remaining / 2
    rw [m2PairSplitAllocation_two_eq_outside cost chores coreAllocation outsideAllocation hcoreTwoEmpty]
    exact houtsideTwo
  have hcardThree : (allocation 3).card = remaining - remaining / 2 := by
    change ((fun agent => coreAllocation agent ∪
      (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
        ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
          outsideAllocation agent)) 3).card = remaining - remaining / 2
    rw [m2PairSplitAllocation_three_eq_outside cost chores coreAllocation outsideAllocation
      hcoreThreeEmpty]
    exact houtsideThree
  have hlargeZero : (largeChoreSet cost r 0 (allocation 0)).card = L := by
    change (largeChoreSet cost r 0
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0)).card = L
    rw [m2PairSplitAllocation_zero_largeSet r cost chores coreAllocation outsideAllocation
      hrStrict hcost hcoreAllocation houtsideAllocation, houtsideZero]
  have hlargeOne : (largeChoreSet cost r 1 (allocation 1)).card = L := by
    change (largeChoreSet cost r 1
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1)).card = L
    rw [m2PairSplitAllocation_one_largeSet r cost chores coreAllocation outsideAllocation
      hrStrict hcost hcoreAllocation houtsideAllocation, houtsideOne]
  have hpplusMinus : pplus - 1 ≤ pminus := by dsimp [pminus, pplus]; omega
  have hpminusPlus : pminus ≤ pplus := by dsimp [pminus, pplus]; omega
  have hpairOutside : pplus + L - 1 ≤ remaining / 2 := by
    rw [hremaining]
    dsimp [pplus]
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    omega
  have hpairOutsideOne : pminus + L - 1 ≤ remaining / 2 := by
    calc
      pminus + L - 1 ≤ pplus + L - 1 :=
        Nat.sub_le_sub_right (Nat.add_le_add_right hpminusPlus L) 1
      _ ≤ remaining / 2 := hpairOutside
  have hlowHigh : remaining / 2 ≤ remaining - remaining / 2 := by omega
  have hlowBound : remaining / 2 - 1 ≤ L + 2 * pminus := by omega
  have hhighBound : remaining - remaining / 2 - 1 ≤ L + 2 * pminus := by omega
  have htwoSmall : ∀ item ∈ allocation 2, IsSmallChore cost 2 item := by
    change ∀ item ∈ m2PairSplitAllocation cost chores coreAllocation outsideAllocation 2,
      IsSmallChore cost 2 item
    exact m2PairSplitAllocation_two_ownSmall cost chores coreAllocation outsideAllocation
      hcoreTwoEmpty houtsideAllocation htwo
  have hthreeSmall : ∀ item ∈ allocation 3, IsSmallChore cost 3 item := by
    change ∀ item ∈ m2PairSplitAllocation cost chores coreAllocation outsideAllocation 3,
      IsSmallChore cost 3 item
    exact m2PairSplitAllocation_three_ownSmall cost chores coreAllocation outsideAllocation
      hcoreThreeEmpty houtsideAllocation htwo
  have hzeroToTwoLarge : ∀ item ∈ allocation 2, IsLargeChore cost r 0 item := by
    exact m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 0 2
      hrStrict hcost hcoreAllocation houtsideAllocation (Or.inl rfl) (Or.inl rfl) hcoreTwoEmpty
  have hzeroToThreeLarge : ∀ item ∈ allocation 3, IsLargeChore cost r 0 item := by
    exact m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 0 3
      hrStrict hcost hcoreAllocation houtsideAllocation (Or.inl rfl) (Or.inr rfl) hcoreThreeEmpty
  have honeToTwoLarge : ∀ item ∈ allocation 2, IsLargeChore cost r 1 item := by
    exact m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 1 2
      hrStrict hcost hcoreAllocation houtsideAllocation (Or.inr rfl) (Or.inl rfl) hcoreTwoEmpty
  have honeToThreeLarge : ∀ item ∈ allocation 3, IsLargeChore cost r 1 item := by
    exact m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 1 3
      hrStrict hcost hcoreAllocation houtsideAllocation (Or.inr rfl) (Or.inr rfl) hcoreThreeEmpty
  have hcoreTwoLarge : ∀ agent item, item ∈ coreAllocation agent → IsLargeChore cost r 2 item := by
    intro agent item hitem
    have hpool := hcoreAllocation.1 agent item hitem
    exact m2PairCoreFibre_large_for_two r cost chores item hcost
      (htwo item (Finset.mem_filter.mp hpool).1) hpool
  have hcoreThreeLarge : ∀ agent item, item ∈ coreAllocation agent → IsLargeChore cost r 3 item := by
    intro agent item hitem
    have hpool := hcoreAllocation.1 agent item hitem
    exact m2PairCoreFibre_large_for_three r cost chores item hcost
      (htwo item (Finset.mem_filter.mp hpool).1) hpool
  have houtsideTwoSmall : ∀ agent item, item ∈ outsideAllocation agent → IsSmallChore cost 2 item := by
    intro agent item hitem
    have hpool := houtsideAllocation.1 agent item hitem
    exact m2PairOutsideFibre_small_for_two cost chores item
      (htwo item (Finset.mem_filter.mp hpool).1) hpool
  have houtsideThreeSmall : ∀ agent item, item ∈ outsideAllocation agent → IsSmallChore cost 3 item := by
    intro agent item hitem
    have hpool := houtsideAllocation.1 agent item hitem
    exact m2PairOutsideFibre_small_for_three cost chores item
      (htwo item (Finset.mem_filter.mp hpool).1) hpool
  have hzeroCostTwo : additiveChoreCost cost 2 (allocation 0) = (pplus : ℝ) * r + L := by
    exact m2PairSplitAllocation_zero_cost_of_coreLarge_outsideSmall_general r cost chores
      coreAllocation outsideAllocation 2 pplus L hrStrict hcost hcoreAllocation
      houtsideAllocation hcrossFirstEmpty hcoreZero houtsideZero
      (fun item hitem => hcoreTwoLarge 0 item hitem)
      (fun item hitem => houtsideTwoSmall 0 item hitem)
  have honeCostTwo : additiveChoreCost cost 2 (allocation 1) = (pminus : ℝ) * r + L := by
    exact m2PairSplitAllocation_one_cost_of_coreLarge_outsideSmall_general r cost chores
      coreAllocation outsideAllocation 2 pminus L hrStrict hcost hcoreAllocation
      houtsideAllocation hcrossSecondEmpty hcoreOne houtsideOne
      (fun item hitem => hcoreTwoLarge 1 item hitem)
      (fun item hitem => houtsideTwoSmall 1 item hitem)
  have hzeroCostThree : additiveChoreCost cost 3 (allocation 0) = (pplus : ℝ) * r + L := by
    exact m2PairSplitAllocation_zero_cost_of_coreLarge_outsideSmall_general r cost chores
      coreAllocation outsideAllocation 3 pplus L hrStrict hcost hcoreAllocation
      houtsideAllocation hcrossFirstEmpty hcoreZero houtsideZero
      (fun item hitem => hcoreThreeLarge 0 item hitem)
      (fun item hitem => houtsideThreeSmall 0 item hitem)
  have honeCostThree : additiveChoreCost cost 3 (allocation 1) = (pminus : ℝ) * r + L := by
    exact m2PairSplitAllocation_one_cost_of_coreLarge_outsideSmall_general r cost chores
      coreAllocation outsideAllocation 3 pminus L hrStrict hcost hcoreAllocation
      houtsideAllocation hcrossSecondEmpty hcoreOne houtsideOne
      (fun item hitem => hcoreThreeLarge 1 item hitem)
      (fun item hitem => houtsideThreeSmall 1 item hitem)
  have hhighLow : remaining - remaining / 2 ≤ remaining / 2 + 1 := by omega
  have htwoScale : (2 : ℝ) * (pminus : ℝ) ≤ r * pminus :=
    mul_le_mul_of_nonneg_right hrTwo (Nat.cast_nonneg pminus)
  have hcoreScale : (pminus : ℝ) * r ≤ pplus * r := by
    have hcast : (pminus : ℝ) ≤ pplus := by exact_mod_cast hpminusPlus
    exact mul_le_mul_of_nonneg_right hcast hrZero
  have htwoToZeroBound : (((allocation 2).card - 1 : ℕ) : ℝ) ≤
      additiveChoreCost cost 2 (allocation 0) := by
    rw [hcardTwo, hzeroCostTwo]
    have hreal : ((remaining / 2 - 1 : ℕ) : ℝ) ≤ (L : ℝ) + (pminus : ℝ) * r := by
      have hnatReal : ((remaining / 2 - 1 : ℕ) : ℝ) ≤ (L : ℝ) + 2 * (pminus : ℝ) := by
        exact_mod_cast hlowBound
      calc
        ((remaining / 2 - 1 : ℕ) : ℝ) ≤ (L : ℝ) + 2 * (pminus : ℝ) := hnatReal
        _ ≤ (L : ℝ) + r * pminus := by simpa [add_comm] using add_le_add_left htwoScale L
        _ = (L : ℝ) + (pminus : ℝ) * r := by ring
    have hcostLower : (L : ℝ) + (pminus : ℝ) * r ≤ (pplus : ℝ) * r + L := by
      calc
        (L : ℝ) + (pminus : ℝ) * r = (pminus : ℝ) * r + L := by ring
        _ ≤ (pplus : ℝ) * r + L := by simpa [add_comm] using add_le_add_right hcoreScale L
    exact hreal.trans hcostLower
  have hthreeToZeroBound : (((allocation 3).card - 1 : ℕ) : ℝ) ≤
      additiveChoreCost cost 3 (allocation 0) := by
    rw [hcardThree, hzeroCostThree]
    have hreal : ((remaining - remaining / 2 - 1 : ℕ) : ℝ) ≤ (L : ℝ) + (pminus : ℝ) * r := by
      have hnatReal : ((remaining - remaining / 2 - 1 : ℕ) : ℝ) ≤ (L : ℝ) + 2 * (pminus : ℝ) := by
        exact_mod_cast hhighBound
      calc
        ((remaining - remaining / 2 - 1 : ℕ) : ℝ) ≤ (L : ℝ) + 2 * (pminus : ℝ) := hnatReal
        _ ≤ (L : ℝ) + r * pminus := by simpa [add_comm] using add_le_add_left htwoScale L
        _ = (L : ℝ) + (pminus : ℝ) * r := by ring
    have hcostLower : (L : ℝ) + (pminus : ℝ) * r ≤ (pplus : ℝ) * r + L := by
      calc
        (L : ℝ) + (pminus : ℝ) * r = (pminus : ℝ) * r + L := by ring
        _ ≤ (pplus : ℝ) * r + L := by simpa [add_comm] using add_le_add_right hcoreScale L
    exact hreal.trans hcostLower
  have htwoToOneBound : (((allocation 2).card - 1 : ℕ) : ℝ) ≤
      additiveChoreCost cost 2 (allocation 1) := by
    rw [hcardTwo, honeCostTwo]
    have hnatReal : ((remaining / 2 - 1 : ℕ) : ℝ) ≤ (L : ℝ) + 2 * (pminus : ℝ) := by
      exact_mod_cast hlowBound
    calc
      ((remaining / 2 - 1 : ℕ) : ℝ) ≤ (L : ℝ) + 2 * (pminus : ℝ) := hnatReal
      _ ≤ (L : ℝ) + r * pminus := by simpa [add_comm] using add_le_add_left htwoScale L
      _ = (pminus : ℝ) * r + L := by ring
  have hthreeToOneBound : (((allocation 3).card - 1 : ℕ) : ℝ) ≤
      additiveChoreCost cost 3 (allocation 1) := by
    rw [hcardThree, honeCostThree]
    have hnatReal : ((remaining - remaining / 2 - 1 : ℕ) : ℝ) ≤ (L : ℝ) + 2 * (pminus : ℝ) := by
      exact_mod_cast hhighBound
    calc
      ((remaining - remaining / 2 - 1 : ℕ) : ℝ) ≤ (L : ℝ) + 2 * (pminus : ℝ) := hnatReal
      _ ≤ (L : ℝ) + r * pminus := by simpa [add_comm] using add_le_add_left htwoScale L
      _ = (pminus : ℝ) * r + L := by ring
  rw [efxForChores_iff_forall_doesNotStronglyEnvy]
  intro i j
  fin_cases i <;> fin_cases j
  · exact doesNotStronglyEnvyForChores_self_of_nonneg cost allocation 0
      (fun item => IsOneOrRChoreCost.nonneg cost r hcost hrZero 0 item)
  · refine Or.inr (additiveChoreCost_erase_le_of_card_largeCard_upper cost r allocation 0 1
      (pplus + L) (pminus + L) L L hcost hrOne hcardZero hcardOne hlargeZero ?_ ?_)
    · change (largeChoreSet cost r 0
        ((fun agent => coreAllocation agent ∪
          (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
            ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
              outsideAllocation agent)) 1)).card = L
      rw [m2PairSplitAllocation_one_largeSet_for_zero r cost chores coreAllocation outsideAllocation
        (by linarith) hcost hcoreAllocation houtsideAllocation, hcrossSecondEmpty]
      simp [houtsideOne]
    · norm_num
      have hnat : pplus + L - 1 ≤ pminus + L := by omega
      exact_mod_cast hnat
  · exact Or.inr (additiveChoreCost_erase_le_of_allLarge_comparison cost r allocation 0 2
      (pplus + L) L hcost hrOne hcardZero hlargeZero hzeroToTwoLarge (by simpa [hcardTwo] using hpairOutside))
  · exact Or.inr (additiveChoreCost_erase_le_of_allLarge_comparison cost r allocation 0 3
      (pplus + L) L hcost hrOne hcardZero hlargeZero hzeroToThreeLarge (by rw [hcardThree]; omega))
  · refine Or.inr (additiveChoreCost_erase_le_of_card_largeCard_upper cost r allocation 1 0
      (pminus + L) (pplus + L) L L hcost hrOne hcardOne hcardZero hlargeOne ?_ ?_)
    · change (largeChoreSet cost r 1
        ((fun agent => coreAllocation agent ∪
          (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
            ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
              outsideAllocation agent)) 0)).card = L
      rw [m2PairSplitAllocation_zero_largeSet_for_one r cost chores coreAllocation outsideAllocation
        (by linarith) hcost hcoreAllocation houtsideAllocation, hcrossFirstEmpty]
      simp [houtsideZero]
    · norm_num
      have hnat : pminus + L - 1 ≤ pplus + L := by omega
      exact_mod_cast hnat
  · exact doesNotStronglyEnvyForChores_self_of_nonneg cost allocation 1
      (fun item => IsOneOrRChoreCost.nonneg cost r hcost hrZero 1 item)
  · exact Or.inr (additiveChoreCost_erase_le_of_allLarge_comparison cost r allocation 1 2
      (pminus + L) L hcost hrOne hcardOne hlargeOne honeToTwoLarge (by simpa [hcardTwo] using hpairOutsideOne))
  · exact Or.inr (additiveChoreCost_erase_le_of_allLarge_comparison cost r allocation 1 3
      (pminus + L) L hcost hrOne hcardOne hlargeOne honeToThreeLarge (by rw [hcardThree]; omega))
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_costLower cost allocation 2 0 htwoSmall htwoToZeroBound
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_costLower cost allocation 2 1 htwoSmall htwoToOneBound
  · exact doesNotStronglyEnvyForChores_self_of_nonneg cost allocation 2
      (fun item => IsOneOrRChoreCost.nonneg cost r hcost hrZero 2 item)
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 2 3 hcost hrOne htwoSmall (by rw [hcardTwo, hcardThree]; omega)
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_costLower cost allocation 3 0 hthreeSmall hthreeToZeroBound
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_costLower cost allocation 3 1 hthreeSmall hthreeToOneBound
  · exact doesNotStronglyEnvyForChores_of_ownSmall_and_card cost r allocation 3 2 hcost hrOne hthreeSmall (by rw [hcardThree, hcardTwo]; exact hhighLow)
  · exact doesNotStronglyEnvyForChores_self_of_nonneg cost allocation 3
      (fun item => IsOneOrRChoreCost.nonneg cost r hcost hrZero 3 item)

/-- For the nonexceptional residues of Case 3.2.2, the source assigns the
one common-small chore and exactly `p` outside chores to agent `0`, gives
agent `1` exactly `p` all-large chores, and balances the rest between `2,3`.
This is the Case 3.2.3 split specialized to one core chore; unlike the
unrestricted EFX witness, it makes the all-large agent envy-free for
`t < 3`. -/
theorem existsEfxOfM2PairCase322Labelled_certified_of_lt_three
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (p t : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcore : (m2PairCoreFibre cost chores 0 1).card = 1)
    (hcrossFirst : (m2PairCrossFibre cost chores 0 1).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores 1 0).card = 0)
    (houtside : (m2PairOutsideFibre cost chores 0 1).card = 4 * p + t)
    (ht : t < 3) (houtsideLarge : 1 < 4 * p + t) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) ∧
      ∀ item ∈ allocation 1, IsLargeChore cost r 1 item := by
  classical
  have hcrossFirstEmpty : m2PairCrossFibre cost chores 0 1 = ∅ :=
    Finset.card_eq_zero.mp hcrossFirst
  have hcrossSecondEmpty : m2PairCrossFibre cost chores 1 0 = ∅ :=
    Finset.card_eq_zero.mp hcrossSecond
  obtain ⟨coreAllocation, outsideAllocation, hcoreAllocation, hcoreCard,
    houtsideAllocation, houtsideCard, hallocation⟩ :=
    existsM2Case323Allocation Item cost chores 1 (4 * p + t) p hcore houtside (by omega)
  let allocation := m2PairSplitAllocation cost chores coreAllocation outsideAllocation
  have halloc : IsAllocationOf allocation chores := by
    change IsAllocationOf
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) chores
    exact hallocation
  have hefx : EFXForChores (additiveChoreCost cost) allocation := by
    apply efxOfM2PairCase323Split r cost chores coreAllocation outsideAllocation 1 (4 * p + t) p
      hr hcost hcoreAllocation houtsideAllocation hcoreCard houtsideCard hcrossFirstEmpty
      hcrossSecondEmpty houtside htwo houtsideLarge
    · omega
    · omega
  have hcoreZero : (coreAllocation 0).card = 1 := by
    simpa [m2PairCoreQuota] using hcoreCard 0
  have hcoreOneEmpty : coreAllocation 1 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 1
  have hcoreTwoEmpty : coreAllocation 2 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 2
  have hcoreThreeEmpty : coreAllocation 3 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 3
  have houtsideZero : (outsideAllocation 0).card = p := by
    simpa [m2PairOutsideQuota] using houtsideCard 0
  have houtsideOne : (outsideAllocation 1).card = p := by
    simpa [m2PairOutsideQuota] using houtsideCard 1
  have hcardZero : (allocation 0).card = p + 1 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0).card = p + 1
    rw [m2PairSplitAllocation_zero_card cost chores coreAllocation outsideAllocation 1 p
      hcoreAllocation houtsideAllocation hcoreZero houtsideZero, hcrossFirstEmpty]
    simp
    omega
  have hcardOne : (allocation 1).card = p := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1).card = p
    simp [allocateAllTo, hcoreOneEmpty, hcrossSecondEmpty, houtsideOne]
  have hcardTwo : p ≤ (allocation 2).card := by
    change p ≤
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 2).card
    rw [m2PairSplitAllocation_two_eq_outside cost chores coreAllocation outsideAllocation
      hcoreTwoEmpty, houtsideCard 2]
    simp [m2PairOutsideQuota, houtside]
    omega
  have hcardThree : p ≤ (allocation 3).card := by
    change p ≤
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 3).card
    rw [m2PairSplitAllocation_three_eq_outside cost chores coreAllocation outsideAllocation
      hcoreThreeEmpty, houtsideCard 3]
    simp [m2PairOutsideQuota, houtside]
    omega
  have honeAllLarge : ∀ item ∈ allocation 1, IsLargeChore cost r 1 item := by
    change ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1,
      IsLargeChore cost r 1 item
    exact m2PairSplitAllocation_one_allLarge_of_crossSecondEmpty r cost chores coreAllocation
      outsideAllocation hcost hcoreOneEmpty hcrossSecondEmpty houtsideAllocation
  have hzeroLargeForOne : (largeChoreSet cost r 1 (allocation 0)).card = p := by
    change (largeChoreSet cost r 1
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0)).card = p
    rw [m2PairSplitAllocation_zero_largeSet_for_one r cost chores coreAllocation outsideAllocation
      (by linarith) hcost hcoreAllocation houtsideAllocation, hcrossFirstEmpty]
    simp [houtsideZero]
  have honeToTwoLarge : ∀ item ∈ allocation 2, IsLargeChore cost r 1 item :=
    m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 1 2
      (by linarith) hcost hcoreAllocation houtsideAllocation (Or.inr rfl) (Or.inl rfl) hcoreTwoEmpty
  have honeToThreeLarge : ∀ item ∈ allocation 3, IsLargeChore cost r 1 item :=
    m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 1 3
      (by linarith) hcost hcoreAllocation houtsideAllocation (Or.inr rfl) (Or.inr rfl) hcoreThreeEmpty
  have htwoSmall : ∀ item ∈ allocation 2, IsSmallChore cost 2 item := by
    change ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 2,
      IsSmallChore cost 2 item
    exact m2PairSplitAllocation_two_ownSmall cost chores coreAllocation outsideAllocation
      hcoreTwoEmpty houtsideAllocation htwo
  have hthreeSmall : ∀ item ∈ allocation 3, IsSmallChore cost 3 item := by
    change ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 3,
      IsSmallChore cost 3 item
    exact m2PairSplitAllocation_three_ownSmall cost chores coreAllocation outsideAllocation
      hcoreThreeEmpty houtsideAllocation htwo
  refine ⟨allocation, halloc, hefx, ?_, ?_, honeAllLarge⟩
  · intro i hsmall
    exact smallItemCertificate_of_efx Item cost allocation hefx i hsmall
  · intro i hallLarge j
    fin_cases i
    · exfalso
      obtain ⟨item, hitem⟩ := Finset.card_pos.mp (by omega : 0 < (coreAllocation 0).card)
      have hitemAllocation : item ∈ allocation 0 := by
        simp [allocation, m2PairSplitAllocation, hitem]
      have hsmall : IsSmallChore cost 0 item := by
        have hpool : item ∈ m2PairCoreFibre cost chores 0 1 := hcoreAllocation.1 0 item hitem
        exact isSmallChore_of_mem_smallAgentSet cost 0 item (Finset.mem_filter.mp hpool).2.1
      have hlarge : cost 0 item = r := by
        simpa [IsLargeChore] using hallLarge item hitemAllocation
      rw [IsSmallChore] at hsmall
      linarith
    · have honeCost : additiveChoreCost cost 1 (allocation 1) = (p : ℝ) * r := by
        rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 (allocation 1) r honeAllLarge,
          hcardOne]
        simp only [nsmul_eq_mul]
      have hzeroCost : additiveChoreCost cost 1 (allocation 0) =
          ((p + 1 : ℕ) : ℝ) + (r - 1) * p := by
        rw [additiveChoreCost_eq_card_add_largeCard cost r 1 (allocation 0) hcost,
          hcardZero, hzeroLargeForOne]
      fin_cases j
      · change additiveChoreCost cost 1 (allocation 1) ≤ additiveChoreCost cost 1 (allocation 0)
        rw [honeCost, hzeroCost]
        push_cast
        ring_nf
        linarith
      · change additiveChoreCost cost 1 (allocation 1) ≤ additiveChoreCost cost 1 (allocation 1)
        exact le_rfl
      · change additiveChoreCost cost 1 (allocation 1) ≤ additiveChoreCost cost 1 (allocation 2)
        rw [honeCost, additiveChoreCost_eq_card_nsmul_of_constant cost 1 (allocation 2) r
          honeToTwoLarge]
        simp only [nsmul_eq_mul]
        have hcardReal : (p : ℝ) ≤ (allocation 2).card := by exact_mod_cast hcardTwo
        exact mul_le_mul_of_nonneg_right hcardReal (by linarith)
      · change additiveChoreCost cost 1 (allocation 1) ≤ additiveChoreCost cost 1 (allocation 3)
        rw [honeCost, additiveChoreCost_eq_card_nsmul_of_constant cost 1 (allocation 3) r
          honeToThreeLarge]
        simp only [nsmul_eq_mul]
        have hcardReal : (p : ℝ) ≤ (allocation 3).card := by exact_mod_cast hcardThree
        exact mul_le_mul_of_nonneg_right hcardReal (by linarith)
    · have hempty : allocation 2 = ∅ := by
        by_contra hnotempty
        obtain ⟨item, hitem⟩ := Finset.nonempty_iff_ne_empty.mpr hnotempty
        have hsmall := htwoSmall item hitem
        have hlarge : cost 2 item = r := by
          simpa [IsLargeChore] using hallLarge item hitem
        rw [IsSmallChore] at hsmall
        linarith
      change additiveChoreCost cost 2 (allocation 2) ≤ additiveChoreCost cost 2 (allocation j)
      rw [hempty]
      simp only [additiveChoreCost, Finset.sum_empty]
      exact additiveChoreCost_nonneg cost
        (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 2 (allocation j)
    · have hempty : allocation 3 = ∅ := by
        by_contra hnotempty
        obtain ⟨item, hitem⟩ := Finset.nonempty_iff_ne_empty.mpr hnotempty
        have hsmall := hthreeSmall item hitem
        have hlarge : cost 3 item = r := by
          simpa [IsLargeChore] using hallLarge item hitem
        rw [IsSmallChore] at hsmall
        linarith
      change additiveChoreCost cost 3 (allocation 3) ≤ additiveChoreCost cost 3 (allocation j)
      rw [hempty]
      simp only [additiveChoreCost, Finset.sum_empty]
      exact additiveChoreCost_nonneg cost
        (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 3 (allocation j)

/-- In the `a = 1`, nonexceptional residue cases, the endpoint with no
common-small chore has only large chores and is the prescribed envy-free
agent in the source construction. -/
theorem existsEfxOfM2PairCase322Labelled_preferredOne_of_lt_three
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (p t : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcore : (m2PairCoreFibre cost chores 0 1).card = 1)
    (hcrossFirst : (m2PairCrossFibre cost chores 0 1).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores 1 0).card = 0)
    (houtside : (m2PairOutsideFibre cost chores 0 1).card = 4 * p + t)
    (ht : t < 3) (houtsideLarge : 1 < 4 * p + t) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) ∧
      ∀ other, additiveChoreCost cost 1 (allocation 1) ≤
        additiveChoreCost cost 1 (allocation other) := by
  obtain ⟨allocation, halloc, hefx, hsmallCertificate, hallLargeCertificate, honeAllLarge⟩ :=
    existsEfxOfM2PairCase322Labelled_certified_of_lt_three Item r cost chores p t hr hcost
      htwo hcore hcrossFirst hcrossSecond houtside ht houtsideLarge
  exact ⟨allocation, halloc, hefx, hsmallCertificate, hallLargeCertificate,
    hallLargeCertificate 1 honeAllLarge⟩

/-- In the residue-three `a = 1` configuration, the source instead gives
agent `0` the common-small chore and `p` outside chores.  The direct cost
calculation makes that chosen endpoint envy-free. -/
theorem existsEfxOfM2PairCase322Labelled_preferredZero_three
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (p : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcore : (m2PairCoreFibre cost chores 0 1).card = 1)
    (hcrossFirst : (m2PairCrossFibre cost chores 0 1).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores 1 0).card = 0)
    (houtside : (m2PairOutsideFibre cost chores 0 1).card = 4 * p + 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      ∀ other, additiveChoreCost cost 0 (allocation 0) ≤
        additiveChoreCost cost 0 (allocation other) := by
  classical
  have hcrossFirstEmpty : m2PairCrossFibre cost chores 0 1 = ∅ :=
    Finset.card_eq_zero.mp hcrossFirst
  have hcrossSecondEmpty : m2PairCrossFibre cost chores 1 0 = ∅ :=
    Finset.card_eq_zero.mp hcrossSecond
  obtain ⟨coreAllocation, outsideAllocation, hcoreAllocation, hcoreCard,
    houtsideAllocation, houtsideCard, hallocation⟩ :=
    existsM2Case322Allocation Item cost chores p 3 hcore houtside (by omega)
  let allocation := m2PairSplitAllocation cost chores coreAllocation outsideAllocation
  have halloc : IsAllocationOf allocation chores := by
    change IsAllocationOf
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) chores
    exact hallocation
  have hefx : EFXForChores (additiveChoreCost cost) allocation := by
    exact efxOfM2PairCase322Split r cost chores coreAllocation outsideAllocation p 3 (by linarith) hcost
      hcoreAllocation houtsideAllocation hcoreCard houtsideCard hcrossFirstEmpty hcrossSecondEmpty
      houtside htwo (by omega)
  have hcoreZero : (coreAllocation 0).card = 1 := by
    simpa [m2PairCoreQuota] using hcoreCard 0
  have hcoreOneEmpty : coreAllocation 1 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 1
  have hcoreTwoEmpty : coreAllocation 2 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 2
  have hcoreThreeEmpty : coreAllocation 3 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 3
  have houtsideZero : (outsideAllocation 0).card = p := by
    simpa [m2PairOutsideQuota] using houtsideCard 0
  have houtsideOne : (outsideAllocation 1).card = p + 1 := by
    simpa [m2PairOutsideQuota] using houtsideCard 1
  have hcardZero : (allocation 0).card = p + 1 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0).card = p + 1
    rw [m2PairSplitAllocation_zero_card cost chores coreAllocation outsideAllocation 1 p
      hcoreAllocation houtsideAllocation hcoreZero houtsideZero, hcrossFirstEmpty]
    simp
    omega
  have hcardOne : (allocation 1).card = p + 1 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1).card = p + 1
    rw [m2PairSplitAllocation_one_card cost chores coreAllocation outsideAllocation 0 (p + 1)
      hcoreAllocation houtsideAllocation (by simp [hcoreOneEmpty]) houtsideOne,
      hcrossSecondEmpty]
    simp
  have hcardTwo : (allocation 2).card = p + 1 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 2).card = p + 1
    rw [m2PairSplitAllocation_two_eq_outside cost chores coreAllocation outsideAllocation hcoreTwoEmpty,
      houtsideCard 2]
    simp [m2PairOutsideQuota, houtside]
    omega
  have hcardThree : (allocation 3).card = p + 1 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 3).card = p + 1
    rw [m2PairSplitAllocation_three_eq_outside cost chores coreAllocation outsideAllocation
      hcoreThreeEmpty, houtsideCard 3]
    simp [m2PairOutsideQuota, houtside]
    omega
  have hzeroLargeCard : (largeChoreSet cost r 0 (allocation 0)).card = p := by
    change (largeChoreSet cost r 0
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0)).card = p
    exact m2PairSplitAllocation_zero_largeCard r cost chores coreAllocation outsideAllocation p
      (by linarith) hcost hcoreAllocation houtsideAllocation houtsideZero
  have honeLargeCardForZero : (largeChoreSet cost r 0 (allocation 1)).card = p + 1 := by
    change (largeChoreSet cost r 0
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1)).card = p + 1
    rw [m2PairSplitAllocation_one_largeSet_for_zero r cost chores coreAllocation outsideAllocation
      (by linarith) hcost hcoreAllocation houtsideAllocation, hcrossSecondEmpty]
    simp [houtsideOne]
  have hzeroToTwoLarge : ∀ item ∈ allocation 2, IsLargeChore cost r 0 item :=
    m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 0 2
      (by linarith) hcost hcoreAllocation houtsideAllocation (Or.inl rfl) (Or.inl rfl)
        hcoreTwoEmpty
  have hzeroToThreeLarge : ∀ item ∈ allocation 3, IsLargeChore cost r 0 item :=
    m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 0 3
      (by linarith) hcost hcoreAllocation houtsideAllocation (Or.inl rfl) (Or.inr rfl)
        hcoreThreeEmpty
  have hzeroCost : additiveChoreCost cost 0 (allocation 0) = 1 + (p : ℝ) * r := by
    rw [additiveChoreCost_eq_card_add_largeCard cost r 0 (allocation 0) hcost,
      hcardZero, hzeroLargeCard]
    push_cast
    ring
  have honeCost : additiveChoreCost cost 0 (allocation 1) = ((p + 1 : ℕ) : ℝ) * r := by
    rw [additiveChoreCost_eq_card_add_largeCard cost r 0 (allocation 1) hcost,
      hcardOne, honeLargeCardForZero]
    push_cast
    ring
  have htwoCost : additiveChoreCost cost 0 (allocation 2) = ((p + 1 : ℕ) : ℝ) * r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 (allocation 2) r hzeroToTwoLarge,
      hcardTwo]
    simp only [nsmul_eq_mul]
  have hthreeCost : additiveChoreCost cost 0 (allocation 3) = ((p + 1 : ℕ) : ℝ) * r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 (allocation 3) r hzeroToThreeLarge,
      hcardThree]
    simp only [nsmul_eq_mul]
  refine ⟨allocation, halloc, hefx, ?_⟩
  intro other
  fin_cases other
  · exact le_rfl
  · change additiveChoreCost cost 0 (allocation 0) ≤ additiveChoreCost cost 0 (allocation 1)
    rw [hzeroCost, honeCost]
    push_cast
    nlinarith
  · change additiveChoreCost cost 0 (allocation 0) ≤ additiveChoreCost cost 0 (allocation 2)
    rw [hzeroCost, htwoCost]
    push_cast
    nlinarith
  · change additiveChoreCost cost 0 (allocation 0) ≤ additiveChoreCost cost 0 (allocation 3)
    rw [hzeroCost, hthreeCost]
    push_cast
    nlinarith

/-- An EFX allocation whose every nonempty bundle contains an own-small chore
has both nonexceptional M₂ certificates.  Empty bundles are envy-free by
nonnegativity, while a nonempty own-small bundle rules out the all-large
antecedent of the second certificate. -/
private theorem m2Certificates_of_efx_ownSmall_or_empty
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (allocation : Allocation (Fin 4) Item)
    (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hefx : EFXForChores (additiveChoreCost cost) allocation)
    (hsmallOrEmpty : ∀ agent,
      (∃ item ∈ allocation agent, IsSmallChore cost agent item) ∨ allocation agent = ∅) :
    (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
      additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
    (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
      additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) := by
  constructor
  · intro i hsmall j
    exact smallItemCertificate_of_efx Item cost allocation hefx i hsmall j
  · intro i hallLarge j
    rcases hsmallOrEmpty i with hsmall | hempty
    · obtain ⟨item, hitem, hitemSmall⟩ := hsmall
      have hitemLarge := hallLarge item hitem
      rw [IsSmallChore] at hitemSmall
      rw [IsLargeChore] at hitemLarge
      linarith
    · rw [hempty]
      simp only [additiveChoreCost, Finset.sum_empty]
      exact additiveChoreCost_nonneg cost
        (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) i (allocation j)

/-- In a Case 3.2.3 split, positive core shares give agents `0` and `1`
own-small chores.  Agents `2` and `3` receive only their own-small outside
fiber when nonempty.  This structural fact supplies the M₂ certificates for
the preferred orientations used in Lemma `M2properties`(iii). -/
private theorem m2PairSplitAllocation_certificates_of_positive_core
    {Item : Type} [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (coreAllocation outsideAllocation : Allocation (Fin 4) Item)
    (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcoreAllocation : IsAllocationOf coreAllocation (m2PairCoreFibre cost chores 0 1))
    (houtsideAllocation : IsAllocationOf outsideAllocation (m2PairOutsideFibre cost chores 0 1))
    (hcoreZero : 0 < (coreAllocation 0).card)
    (hcoreOne : 0 < (coreAllocation 1).card)
    (hcoreTwoEmpty : coreAllocation 2 = ∅)
    (hcoreThreeEmpty : coreAllocation 3 = ∅)
    (hefx : EFXForChores (additiveChoreCost cost)
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation)) :
    (∀ i, (∃ item ∈ m2PairSplitAllocation cost chores coreAllocation outsideAllocation i,
        IsSmallChore cost i item) → ∀ j,
      additiveChoreCost cost i
          (m2PairSplitAllocation cost chores coreAllocation outsideAllocation i) - 1 ≤
        additiveChoreCost cost i
          (m2PairSplitAllocation cost chores coreAllocation outsideAllocation j)) ∧
    (∀ i, (∀ item ∈ m2PairSplitAllocation cost chores coreAllocation outsideAllocation i,
        IsLargeChore cost r i item) → ∀ j,
      additiveChoreCost cost i
          (m2PairSplitAllocation cost chores coreAllocation outsideAllocation i) ≤
        additiveChoreCost cost i
          (m2PairSplitAllocation cost chores coreAllocation outsideAllocation j)) := by
  apply m2Certificates_of_efx_ownSmall_or_empty r cost
    (m2PairSplitAllocation cost chores coreAllocation outsideAllocation) hr hcost hefx
  intro agent
  fin_cases agent
  · obtain ⟨item, hitem⟩ := Finset.card_pos.mp hcoreZero
    left
    refine ⟨item, ?_, ?_⟩
    · simp [m2PairSplitAllocation, hitem]
    · have hpool := hcoreAllocation.1 0 item hitem
      exact isSmallChore_of_mem_smallAgentSet cost 0 item (Finset.mem_filter.mp hpool).2.1
  · obtain ⟨item, hitem⟩ := Finset.card_pos.mp hcoreOne
    left
    refine ⟨item, ?_, ?_⟩
    · simp [m2PairSplitAllocation, hitem]
    · have hpool := hcoreAllocation.1 1 item hitem
      exact isSmallChore_of_mem_smallAgentSet cost 1 item (Finset.mem_filter.mp hpool).2.2
  · by_cases hempty : m2PairSplitAllocation cost chores coreAllocation outsideAllocation 2 = ∅
    · exact Or.inr hempty
    · left
      obtain ⟨item, hitem⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      refine ⟨item, hitem, ?_⟩
      exact m2PairSplitAllocation_two_ownSmall cost chores coreAllocation outsideAllocation
        hcoreTwoEmpty houtsideAllocation htwo item hitem
  · by_cases hempty : m2PairSplitAllocation cost chores coreAllocation outsideAllocation 3 = ∅
    · exact Or.inr hempty
    · left
      obtain ⟨item, hitem⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      refine ⟨item, hitem, ?_⟩
      exact m2PairSplitAllocation_three_ownSmall cost chores coreAllocation outsideAllocation
        hcoreThreeEmpty houtsideAllocation htwo item hitem

/-- For a core fiber of size at least three, the Case 3.2.3 interval witness
can be oriented so that label `1`, which receives the lower core half, is
envy-free as required by the prescribed-agent part of the source proof. -/
theorem existsEfxOfM2PairCase323Labelled_preferredOne_of_three_le
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a f : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcore : (m2PairCoreFibre cost chores 0 1).card = a)
    (hcrossFirst : (m2PairCrossFibre cost chores 0 1).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores 1 0).card = 0)
    (houtside : (m2PairOutsideFibre cost chores 0 1).card = f)
    (ha : 3 ≤ a) (hfa : a < f) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) ∧
      ∀ other, additiveChoreCost cost 1 (allocation 1) ≤
        additiveChoreCost cost 1 (allocation other) := by
  classical
  obtain ⟨L, hupper, hlower⟩ := m2Case323_exists_outsideShare a f (by omega) hfa
  let pminus := a / 2
  let pplus := (a + 1) / 2
  let remaining := f - L - L
  have hremaining : remaining = f - 2 * L := by
    simp [remaining, Nat.sub_sub, two_mul]
  have houtsideSplit : 2 * L ≤ f := by
    have hplusPos : 1 ≤ pplus := by dsimp [pplus]; omega
    omega
  have hcrossFirstEmpty : m2PairCrossFibre cost chores 0 1 = ∅ :=
    Finset.card_eq_zero.mp hcrossFirst
  have hcrossSecondEmpty : m2PairCrossFibre cost chores 1 0 = ∅ :=
    Finset.card_eq_zero.mp hcrossSecond
  obtain ⟨coreAllocation, outsideAllocation, hcoreAllocation, hcoreCard,
    houtsideAllocation, houtsideCard, hallocation⟩ :=
    existsM2Case323Allocation Item cost chores a f L hcore houtside houtsideSplit
  let allocation := m2PairSplitAllocation cost chores coreAllocation outsideAllocation
  have halloc : IsAllocationOf allocation chores := by
    change IsAllocationOf
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) chores
    exact hallocation
  have hefx : EFXForChores (additiveChoreCost cost) allocation := by
    exact efxOfM2PairCase323Split r cost chores coreAllocation outsideAllocation a f L hr hcost
      hcoreAllocation houtsideAllocation hcoreCard houtsideCard hcrossFirstEmpty hcrossSecondEmpty
      houtside htwo hfa hupper hlower
  have hcoreZero : (coreAllocation 0).card = pplus := by
    simpa [pplus, m2PairCoreQuota] using hcoreCard 0
  have hcoreOne : (coreAllocation 1).card = pminus := by
    simpa [pminus, m2PairCoreQuota] using hcoreCard 1
  have hcoreTwoEmpty : coreAllocation 2 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 2
  have hcoreThreeEmpty : coreAllocation 3 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 3
  have houtsideZero : (outsideAllocation 0).card = L := by
    simpa [m2PairOutsideQuota] using houtsideCard 0
  have houtsideOne : (outsideAllocation 1).card = L := by
    simpa [m2PairOutsideQuota] using houtsideCard 1
  have hcardZero : (allocation 0).card = pplus + L := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0).card = pplus + L
    rw [m2PairSplitAllocation_zero_card cost chores coreAllocation outsideAllocation pplus L
      hcoreAllocation houtsideAllocation hcoreZero houtsideZero, hcrossFirstEmpty]
    simp
  have hcardOne : (allocation 1).card = pminus + L := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1).card = pminus + L
    rw [m2PairSplitAllocation_one_card cost chores coreAllocation outsideAllocation pminus L
      hcoreAllocation houtsideAllocation hcoreOne houtsideOne, hcrossSecondEmpty]
    simp
  have hcardTwo : (allocation 2).card = remaining / 2 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 2).card = remaining / 2
    rw [m2PairSplitAllocation_two_eq_outside cost chores coreAllocation outsideAllocation hcoreTwoEmpty,
      houtsideCard 2]
    simp [m2PairOutsideQuota, houtside, remaining]
  have hcardThree : (allocation 3).card = remaining - remaining / 2 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 3).card = remaining - remaining / 2
    rw [m2PairSplitAllocation_three_eq_outside cost chores coreAllocation outsideAllocation
      hcoreThreeEmpty, houtsideCard 3]
    simp [m2PairOutsideQuota, houtside, remaining]
  have hlargeOne : (largeChoreSet cost r 1 (allocation 1)).card = L := by
    change (largeChoreSet cost r 1
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1)).card = L
    rw [m2PairSplitAllocation_one_largeSet r cost chores coreAllocation outsideAllocation
      (by linarith) hcost hcoreAllocation houtsideAllocation, houtsideOne]
  have hlargeZeroForOne : (largeChoreSet cost r 1 (allocation 0)).card = L := by
    change (largeChoreSet cost r 1
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0)).card = L
    rw [m2PairSplitAllocation_zero_largeSet_for_one r cost chores coreAllocation outsideAllocation
      (by linarith) hcost hcoreAllocation houtsideAllocation, hcrossFirstEmpty]
    simp [houtsideZero]
  have honeToTwoLarge : ∀ item ∈ allocation 2, IsLargeChore cost r 1 item :=
    m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 1 2
      (by linarith) hcost hcoreAllocation houtsideAllocation (Or.inr rfl) (Or.inl rfl)
        hcoreTwoEmpty
  have honeToThreeLarge : ∀ item ∈ allocation 3, IsLargeChore cost r 1 item :=
    m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 1 3
      (by linarith) hcost hcoreAllocation houtsideAllocation (Or.inr rfl) (Or.inr rfl)
        hcoreThreeEmpty
  have honeCost : additiveChoreCost cost 1 (allocation 1) = (pminus : ℝ) + r * L := by
    rw [additiveChoreCost_eq_card_add_largeCard cost r 1 (allocation 1) hcost,
      hcardOne, hlargeOne]
    push_cast
    ring
  have hzeroCost : additiveChoreCost cost 1 (allocation 0) = (pplus : ℝ) + r * L := by
    rw [additiveChoreCost_eq_card_add_largeCard cost r 1 (allocation 0) hcost,
      hcardZero, hlargeZeroForOne]
    push_cast
    ring
  have htwoCost : additiveChoreCost cost 1 (allocation 2) = ((remaining / 2 : ℕ) : ℝ) * r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 (allocation 2) r honeToTwoLarge,
      hcardTwo]
    simp only [nsmul_eq_mul]
  have hthreeCost : additiveChoreCost cost 1 (allocation 3) =
      ((remaining - remaining / 2 : ℕ) : ℝ) * r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 (allocation 3) r honeToThreeLarge,
      hcardThree]
    simp only [nsmul_eq_mul]
  have hpairOutside : pplus + L - 1 ≤ remaining / 2 := by
    rw [hremaining]
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    omega
  have hscale : (pminus : ℝ) ≤ r * ((pplus - 1 : ℕ) : ℝ) := by
    have hnat : pminus ≤ 2 * (pplus - 1) := by
      dsimp [pminus, pplus]
      omega
    have hnatReal : (pminus : ℝ) ≤ ((2 * (pplus - 1) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at hnatReal
    nlinarith
  have houtsideBound : (pminus : ℝ) + r * L ≤ r * ((remaining / 2 : ℕ) : ℝ) := by
    have hpairReal : ((pplus + L - 1 : ℕ) : ℝ) ≤ ((remaining / 2 : ℕ) : ℝ) := by
      exact_mod_cast hpairOutside
    have hmul := mul_le_mul_of_nonneg_left hpairReal (by linarith : 0 ≤ r)
    have hsum : pplus - 1 + L = pplus + L - 1 := by omega
    calc
      (pminus : ℝ) + r * L ≤ r * ((pplus - 1 : ℕ) : ℝ) + r * L :=
        by simpa [add_comm] using add_le_add_right hscale (r * L)
      _ = r * ((pplus + L - 1 : ℕ) : ℝ) := by
        rw [← hsum]
        push_cast
        ring
      _ ≤ r * ((remaining / 2 : ℕ) : ℝ) := hmul
  have hpminusPlus : pminus ≤ pplus := by
    dsimp [pminus, pplus]
    omega
  have hhalf : remaining / 2 ≤ remaining - remaining / 2 := by omega
  have hcoreZeroPos : 0 < (coreAllocation 0).card := by
    rw [hcoreZero]
    dsimp [pplus]
    omega
  have hcoreOnePos : 0 < (coreAllocation 1).card := by
    rw [hcoreOne]
    dsimp [pminus]
    omega
  have hcertificates := m2PairSplitAllocation_certificates_of_positive_core r cost chores
    coreAllocation outsideAllocation (by linarith) hcost htwo hcoreAllocation houtsideAllocation
    hcoreZeroPos hcoreOnePos hcoreTwoEmpty hcoreThreeEmpty (by simpa [allocation] using hefx)
  refine ⟨allocation, halloc, hefx, hcertificates.1, hcertificates.2, ?_⟩
  · intro other
    fin_cases other
    · change additiveChoreCost cost 1 (allocation 1) ≤ additiveChoreCost cost 1 (allocation 0)
      rw [honeCost, hzeroCost]
      have hcast : (pminus : ℝ) ≤ (pplus : ℝ) := by exact_mod_cast hpminusPlus
      linarith
    · exact le_rfl
    · change additiveChoreCost cost 1 (allocation 1) ≤ additiveChoreCost cost 1 (allocation 2)
      rw [honeCost, htwoCost]
      simpa [mul_comm] using houtsideBound
    · change additiveChoreCost cost 1 (allocation 1) ≤ additiveChoreCost cost 1 (allocation 3)
      rw [honeCost, hthreeCost]
      have hhalfReal : ((remaining / 2 : ℕ) : ℝ) ≤
          ((remaining - remaining / 2 : ℕ) : ℝ) := by
        exact_mod_cast hhalf
      calc
        (pminus : ℝ) + r * L ≤ r * ((remaining / 2 : ℕ) : ℝ) := houtsideBound
        _ ≤ r * ((remaining - remaining / 2 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hhalfReal (by linarith)
        _ = ((remaining - remaining / 2 : ℕ) : ℝ) * r := by ring

/-- The `a = 2` preferred-endpoint construction uses the source's special
share `⌊(f-2)/4⌋`; its even remainder split gives the required extra outside
chore to each complementary endpoint. -/
theorem existsEfxOfM2PairCase323Labelled_preferredOne_two
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (f : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcore : (m2PairCoreFibre cost chores 0 1).card = 2)
    (hcrossFirst : (m2PairCrossFibre cost chores 0 1).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores 1 0).card = 0)
    (houtside : (m2PairOutsideFibre cost chores 0 1).card = f)
    (hfa : 2 < f) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) ∧
      ∀ other, additiveChoreCost cost 1 (allocation 1) ≤
        additiveChoreCost cost 1 (allocation other) := by
  classical
  let L := (f - 2) / 4
  let remaining := f - L - L
  have hremaining : remaining = f - 2 * L := by simp [remaining, Nat.sub_sub, two_mul]
  have hsplit : 2 * L ≤ f := by dsimp [L]; omega
  have hupper : 4 * L ≤ f - 2 * ((2 + 1) / 2) + 2 := by dsimp [L]; omega
  have hlower : f - 2 * L - (f - 2 * L) / 2 ≤ L + 2 * (2 / 2) + 1 := by
    dsimp [L]
    omega
  have hcrossFirstEmpty : m2PairCrossFibre cost chores 0 1 = ∅ :=
    Finset.card_eq_zero.mp hcrossFirst
  have hcrossSecondEmpty : m2PairCrossFibre cost chores 1 0 = ∅ :=
    Finset.card_eq_zero.mp hcrossSecond
  obtain ⟨coreAllocation, outsideAllocation, hcoreAllocation, hcoreCard,
    houtsideAllocation, houtsideCard, hallocation⟩ :=
    existsM2Case323Allocation Item cost chores 2 f L hcore houtside hsplit
  let allocation := m2PairSplitAllocation cost chores coreAllocation outsideAllocation
  have halloc : IsAllocationOf allocation chores := by
    change IsAllocationOf
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) chores
    exact hallocation
  have hefx : EFXForChores (additiveChoreCost cost) allocation := by
    exact efxOfM2PairCase323Split r cost chores coreAllocation outsideAllocation 2 f L hr hcost
      hcoreAllocation houtsideAllocation hcoreCard houtsideCard hcrossFirstEmpty hcrossSecondEmpty
      houtside htwo hfa hupper hlower
  have hcoreZero : (coreAllocation 0).card = 1 := by
    simpa [m2PairCoreQuota] using hcoreCard 0
  have hcoreOne : (coreAllocation 1).card = 1 := by
    simpa [m2PairCoreQuota] using hcoreCard 1
  have hcoreTwoEmpty : coreAllocation 2 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 2
  have hcoreThreeEmpty : coreAllocation 3 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 3
  have houtsideZero : (outsideAllocation 0).card = L := by
    simpa [m2PairOutsideQuota] using houtsideCard 0
  have houtsideOne : (outsideAllocation 1).card = L := by
    simpa [m2PairOutsideQuota] using houtsideCard 1
  have hcardZero : (allocation 0).card = 1 + L := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0).card = 1 + L
    rw [m2PairSplitAllocation_zero_card cost chores coreAllocation outsideAllocation 1 L
      hcoreAllocation houtsideAllocation hcoreZero houtsideZero, hcrossFirstEmpty]
    simp
  have hcardOne : (allocation 1).card = 1 + L := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1).card = 1 + L
    rw [m2PairSplitAllocation_one_card cost chores coreAllocation outsideAllocation 1 L
      hcoreAllocation houtsideAllocation hcoreOne houtsideOne, hcrossSecondEmpty]
    simp
  have hcardTwo : (allocation 2).card = remaining / 2 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 2).card = remaining / 2
    rw [m2PairSplitAllocation_two_eq_outside cost chores coreAllocation outsideAllocation hcoreTwoEmpty,
      houtsideCard 2]
    simp [m2PairOutsideQuota, houtside, remaining]
  have hcardThree : (allocation 3).card = remaining - remaining / 2 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 3).card = remaining - remaining / 2
    rw [m2PairSplitAllocation_three_eq_outside cost chores coreAllocation outsideAllocation
      hcoreThreeEmpty, houtsideCard 3]
    simp [m2PairOutsideQuota, houtside, remaining]
  have hlargeOne : (largeChoreSet cost r 1 (allocation 1)).card = L := by
    change (largeChoreSet cost r 1
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1)).card = L
    rw [m2PairSplitAllocation_one_largeSet r cost chores coreAllocation outsideAllocation
      (by linarith) hcost hcoreAllocation houtsideAllocation, houtsideOne]
  have hlargeZeroForOne : (largeChoreSet cost r 1 (allocation 0)).card = L := by
    change (largeChoreSet cost r 1
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0)).card = L
    rw [m2PairSplitAllocation_zero_largeSet_for_one r cost chores coreAllocation outsideAllocation
      (by linarith) hcost hcoreAllocation houtsideAllocation, hcrossFirstEmpty]
    simp [houtsideZero]
  have honeToTwoLarge : ∀ item ∈ allocation 2, IsLargeChore cost r 1 item :=
    m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 1 2
      (by linarith) hcost hcoreAllocation houtsideAllocation (Or.inr rfl) (Or.inl rfl)
        hcoreTwoEmpty
  have honeToThreeLarge : ∀ item ∈ allocation 3, IsLargeChore cost r 1 item :=
    m2PairSplitAllocation_outside_allLarge r cost chores coreAllocation outsideAllocation 1 3
      (by linarith) hcost hcoreAllocation houtsideAllocation (Or.inr rfl) (Or.inr rfl)
        hcoreThreeEmpty
  have honeCost : additiveChoreCost cost 1 (allocation 1) = 1 + r * L := by
    rw [additiveChoreCost_eq_card_add_largeCard cost r 1 (allocation 1) hcost,
      hcardOne, hlargeOne]
    push_cast
    ring
  have hzeroCost : additiveChoreCost cost 1 (allocation 0) = 1 + r * L := by
    rw [additiveChoreCost_eq_card_add_largeCard cost r 1 (allocation 0) hcost,
      hcardZero, hlargeZeroForOne]
    push_cast
    ring
  have htwoCost : additiveChoreCost cost 1 (allocation 2) = ((remaining / 2 : ℕ) : ℝ) * r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 (allocation 2) r honeToTwoLarge,
      hcardTwo]
    simp only [nsmul_eq_mul]
  have hthreeCost : additiveChoreCost cost 1 (allocation 3) =
      ((remaining - remaining / 2 : ℕ) : ℝ) * r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 (allocation 3) r honeToThreeLarge,
      hcardThree]
    simp only [nsmul_eq_mul]
  have houtsideLower : L + 1 ≤ remaining / 2 := by
    rw [hremaining]
    dsimp [L]
    omega
  have hhalf : remaining / 2 ≤ remaining - remaining / 2 := by omega
  have hcoreZeroPos : 0 < (coreAllocation 0).card := by rw [hcoreZero]; omega
  have hcoreOnePos : 0 < (coreAllocation 1).card := by rw [hcoreOne]; omega
  have hcertificates := m2PairSplitAllocation_certificates_of_positive_core r cost chores
    coreAllocation outsideAllocation (by linarith) hcost htwo hcoreAllocation houtsideAllocation
    hcoreZeroPos hcoreOnePos hcoreTwoEmpty hcoreThreeEmpty (by simpa [allocation] using hefx)
  refine ⟨allocation, halloc, hefx, hcertificates.1, hcertificates.2, ?_⟩
  · intro other
    fin_cases other
    · change additiveChoreCost cost 1 (allocation 1) ≤ additiveChoreCost cost 1 (allocation 0)
      rw [honeCost, hzeroCost]
    · exact le_rfl
    · change additiveChoreCost cost 1 (allocation 1) ≤ additiveChoreCost cost 1 (allocation 2)
      rw [honeCost, htwoCost]
      have hlowerReal : ((L + 1 : ℕ) : ℝ) ≤ ((remaining / 2 : ℕ) : ℝ) := by
        exact_mod_cast houtsideLower
      push_cast at hlowerReal
      nlinarith
    · change additiveChoreCost cost 1 (allocation 1) ≤ additiveChoreCost cost 1 (allocation 3)
      rw [honeCost, hthreeCost]
      have hlowerReal : ((L + 1 : ℕ) : ℝ) ≤ ((remaining / 2 : ℕ) : ℝ) := by
        exact_mod_cast houtsideLower
      have hhalfReal : ((remaining / 2 : ℕ) : ℝ) ≤
          ((remaining - remaining / 2 : ℕ) : ℝ) := by
        exact_mod_cast hhalf
      push_cast at hlowerReal
      nlinarith

/-- A preferred-agent EFX witness transports back through a finite relabelling
of the four agents. -/
private theorem existsEfxPreferred_relabel_back
    {Item : Type} [DecidableEq Item] (labels : Fin 4 ≃ Fin 4)
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) (preferred : Fin 4)
    (h : ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧
      EFXForChores (additiveChoreCost (relabelChoreCost labels cost)) allocation ∧
      ∀ other, additiveChoreCost (relabelChoreCost labels cost) preferred (allocation preferred) ≤
        additiveChoreCost (relabelChoreCost labels cost) preferred (allocation other)) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      ∀ other, additiveChoreCost cost (labels preferred) (allocation (labels preferred)) ≤
        additiveChoreCost cost (labels preferred) (allocation other) := by
  obtain ⟨labelledAllocation, hlabelledAllocation, hlabelledEfx, hcomparison⟩ := h
  let allocation := relabelAllocation labels.symm labelledAllocation
  have halloc : IsAllocationOf allocation chores := hlabelledAllocation.relabel labels.symm
  have hefx : EFXForChores (additiveChoreCost cost) allocation := by
    have htransport := hlabelledEfx.relabel labels.symm
    have hcostEq : relabelChoreCost labels.symm (relabelChoreCost labels cost) = cost := by
      funext agent item
      simp [relabelChoreCost]
    rw [hcostEq] at htransport
    exact htransport
  refine ⟨allocation, halloc, hefx, ?_⟩
  intro other
  have hsource := hcomparison (labels.symm other)
  simpa [allocation, relabelAllocation, relabelChoreCost, additiveChoreCost] using hsource

/-- The preferred endpoint and both nonexceptional M₂ certificates transport
back through a finite relabelling.  This keeps the Case 3.2 source witnesses
as a single allocation when they are used by the B.4.2(a) concatenation. -/
private theorem existsEfxPreferredCertified_relabel_back
    {Item : Type} [DecidableEq Item] (labels : Fin 4 ≃ Fin 4)
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) (preferred : Fin 4)
    (h : ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧
      EFXForChores (additiveChoreCost (relabelChoreCost labels cost)) allocation ∧
      (∀ i, (∃ item ∈ allocation i,
          IsSmallChore (relabelChoreCost labels cost) i item) → ∀ j,
        additiveChoreCost (relabelChoreCost labels cost) i (allocation i) - 1 ≤
          additiveChoreCost (relabelChoreCost labels cost) i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i,
          IsLargeChore (relabelChoreCost labels cost) r i item) → ∀ j,
        additiveChoreCost (relabelChoreCost labels cost) i (allocation i) ≤
          additiveChoreCost (relabelChoreCost labels cost) i (allocation j)) ∧
      ∀ other, additiveChoreCost (relabelChoreCost labels cost) preferred (allocation preferred) ≤
        additiveChoreCost (relabelChoreCost labels cost) preferred (allocation other)) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) ∧
      ∀ other, additiveChoreCost cost (labels preferred) (allocation (labels preferred)) ≤
        additiveChoreCost cost (labels preferred) (allocation other) := by
  obtain ⟨labelledAllocation, hlabelledAllocation, hlabelledEfx, hsmallCertificate,
    hlargeCertificate, hcomparison⟩ := h
  let allocation := relabelAllocation labels.symm labelledAllocation
  have halloc : IsAllocationOf allocation chores := hlabelledAllocation.relabel labels.symm
  have hefx : EFXForChores (additiveChoreCost cost) allocation := by
    have htransport := hlabelledEfx.relabel labels.symm
    have hcostEq : relabelChoreCost labels.symm (relabelChoreCost labels cost) = cost := by
      funext agent item
      simp [relabelChoreCost]
    rw [hcostEq] at htransport
    exact htransport
  refine ⟨allocation, halloc, hefx, ?_, ?_, ?_⟩
  · intro i hsmall j
    rcases hsmall with ⟨item, hitem, hitemSmall⟩
    have hlabelledSmall : ∃ item ∈ labelledAllocation (labels.symm i),
        IsSmallChore (relabelChoreCost labels cost) (labels.symm i) item := by
      refine ⟨item, ?_, ?_⟩
      · simpa [allocation, relabelAllocation] using hitem
      · simpa [relabelChoreCost, IsSmallChore] using hitemSmall
    have hsource := hsmallCertificate (labels.symm i) hlabelledSmall (labels.symm j)
    simpa [allocation, relabelAllocation, relabelChoreCost, additiveChoreCost] using hsource
  · intro i hallLarge j
    have hlabelledLarge : ∀ item ∈ labelledAllocation (labels.symm i),
        IsLargeChore (relabelChoreCost labels cost) r (labels.symm i) item := by
      intro item hitem
      have hitemOriginal : item ∈ allocation i := by
        simpa [allocation, relabelAllocation] using hitem
      have hlarge := hallLarge item hitemOriginal
      simpa [relabelChoreCost, IsLargeChore] using hlarge
    have hsource := hlargeCertificate (labels.symm i) hlabelledLarge (labels.symm j)
    simpa [allocation, relabelAllocation, relabelChoreCost, additiveChoreCost] using hsource
  · intro other
    have hsource := hcomparison (labels.symm other)
    simpa [allocation, relabelAllocation, relabelChoreCost, additiveChoreCost] using hsource

/-- The four fiber-cardinality hypotheses for a named pair transport to the
displayed labels used by the source constructions. -/
private theorem m2PairData_relabel_zero_one
    {Item : Type} [DecidableEq Item] (labels : Fin 4 ≃ Fin 4)
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item) (first second : Fin 4)
    (hzero : labels 0 = first) (hone : labels 1 = second)
    (a f : ℕ)
    (hcore : (m2PairCoreFibre cost chores first second).card = a)
    (hcrossFirst : (m2PairCrossFibre cost chores first second).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores second first).card = 0)
    (houtside : (m2PairOutsideFibre cost chores first second).card = f) :
    (m2PairCoreFibre (relabelChoreCost labels cost) chores 0 1).card = a ∧
    (m2PairCrossFibre (relabelChoreCost labels cost) chores 0 1).card = 0 ∧
    (m2PairCrossFibre (relabelChoreCost labels cost) chores 1 0).card = 0 ∧
    (m2PairOutsideFibre (relabelChoreCost labels cost) chores 0 1).card = f := by
  constructor
  · rw [m2PairCoreFibre_relabel_zero_one labels cost chores first second hzero hone]
    exact hcore
  constructor
  · obtain ⟨hfirst, _⟩ :=
      m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
    rw [hfirst]
    exact hcrossFirst
  constructor
  · obtain ⟨_, hsecond⟩ :=
      m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
    rw [hsecond]
    exact hcrossSecond
  · rw [m2PairOutsideFibre_relabel_zero_one labels cost chores first second hzero hone]
    exact houtside

/-- The prescribed-agent clause of Lemma `M2properties`(iii): for two
disjoint small-agent types whose second fiber is at least as large as the
first, every specified endpoint of the first type can be made envy-free. -/
theorem existsEfxOfM2TwoDisjointTypes_preferred
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (firstType secondType : Finset (Fin 4)) (agent : Fin 4)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hfirstCard : firstType.card = 2) (hsecondCard : secondType.card = 2)
    (hdisjoint : Disjoint firstType secondType)
    (htypes : ∀ item ∈ chores, smallAgentSet cost item = firstType ∨
      smallAgentSet cost item = secondType)
    (hcount : (chores.filter fun item => smallAgentSet cost item = firstType).card ≤
      (chores.filter fun item => smallAgentSet cost item = secondType).card)
    (hagent : agent ∈ firstType) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      ∀ other, additiveChoreCost cost agent (allocation agent) ≤
        additiveChoreCost cost agent (allocation other) := by
  classical
  let a := (chores.filter fun item => smallAgentSet cost item = firstType).card
  let f := (chores.filter fun item => smallAgentSet cost item = secondType).card
  by_cases haZero : a = 0
  · exact existsEfxOfM2TwoTypes_preferred_of_firstCount_zero Item r cost chores firstType
      secondType agent hr hcost hfirstCard hsecondCard hdisjoint htypes (by simpa [a] using haZero)
      hagent
  obtain ⟨partner, hpartnerNe, hfirstPair⟩ :
      ∃ partner, agent ≠ partner ∧ firstType = ({agent, partner} : Finset (Fin 4)) := by
    obtain ⟨x, y, hxy, htype⟩ := Finset.card_eq_two.mp hfirstCard
    rw [htype] at hagent
    simp only [Finset.mem_insert, Finset.mem_singleton] at hagent
    rcases hagent with rfl | rfl
    · exact ⟨y, hxy, htype⟩
    · refine ⟨x, hxy.symm, ?_⟩
      rw [htype]
      ext z
      simp [or_comm]
  obtain ⟨hcoreEq, hcrossFirstEq, hcrossSecondEq, houtsideEq⟩ :=
    m2PairFibres_of_two_disjoint_smallTypes cost chores firstType secondType agent partner
      hagent (by simpa [hfirstPair]) hdisjoint htypes
  have hcore : (m2PairCoreFibre cost chores agent partner).card = a := by
    simp [a, hcoreEq]
  have hcrossFirst : (m2PairCrossFibre cost chores agent partner).card = 0 := by
    rw [hcrossFirstEq]
    simp
  have hcrossSecond : (m2PairCrossFibre cost chores partner agent).card = 0 := by
    rw [hcrossSecondEq]
    simp
  have houtside : (m2PairOutsideFibre cost chores agent partner).card = f := by
    simp [f, houtsideEq]
  have hle : a ≤ f := by simpa [a, f] using hcount
  have htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item := by
    intro item hitem
    rcases htypes item hitem with htype | htype
    · rw [IsSmallForExactlyTwo, htype, hfirstCard]
    · rw [IsSmallForExactlyTwo, htype, hsecondCard]
  by_cases heq : a = f
  · obtain ⟨labels, hzero, hone⟩ := existsFin4Equiv_map_zero_one agent partner hpartnerNe
    obtain ⟨hcoreL, hcrossFirstL, hcrossSecondL, houtsideL⟩ :=
      m2PairData_relabel_zero_one labels cost chores agent partner hzero hone a f
        hcore hcrossFirst hcrossSecond houtside
    have hresult := existsEfxPreferred_relabel_back labels cost chores 0 (by
      obtain ⟨allocation, halloc, hefx, hsmallCertificate, hlargeCertificate, hpreferred⟩ :=
        existsEfxOfM2PairEqualFibres_preferredZero Item r (relabelChoreCost labels cost) chores a
          hr (IsOneOrRChoreCost.relabel labels cost r hcost)
          (fun item hitem => IsSmallForExactlyTwo.relabel labels cost item (htwo item hitem))
          hcoreL hcrossFirstL hcrossSecondL (by simpa [heq] using houtsideL)
      exact ⟨allocation, halloc, hefx, hpreferred⟩)
    simpa [hzero] using hresult
  have hlt : a < f := lt_of_le_of_ne hle heq
  have haPos : 0 < a := Nat.pos_of_ne_zero haZero
  by_cases haOne : a = 1
  · let p := f / 4
    let t := f % 4
    have hfdecompose : f = 4 * p + t := by
      dsimp [p, t]
      have hmod := Nat.mod_add_div f 4
      omega
    have ht : t < 4 := by
      dsimp [t]
      exact Nat.mod_lt _ (by omega)
    have houtsideLarge : 1 < 4 * p + t := by
      rw [← hfdecompose]
      omega
    by_cases htThree : t < 3
    · obtain ⟨labels, hzero, hone⟩ := existsFin4Equiv_map_zero_one partner agent hpartnerNe.symm
      have hcoreSwap : (m2PairCoreFibre cost chores partner agent).card = 1 := by
        rw [← m2PairCoreFibre_swap cost chores partner agent]
        simpa [haOne] using hcore
      have houtsideSwap : (m2PairOutsideFibre cost chores partner agent).card = f := by
        rw [← m2PairOutsideFibre_swap cost chores partner agent]
        exact houtside
      obtain ⟨hcoreL, hcrossFirstL, hcrossSecondL, houtsideL⟩ :=
        m2PairData_relabel_zero_one labels cost chores partner agent hzero hone 1 f
          hcoreSwap hcrossSecond hcrossFirst houtsideSwap
      have hresult := existsEfxPreferred_relabel_back labels cost chores 1 (by
        obtain ⟨allocation, halloc, hefx, hsmallCertificate, hlargeCertificate, hpreferred⟩ :=
          existsEfxOfM2PairCase322Labelled_preferredOne_of_lt_three Item r
            (relabelChoreCost labels cost) chores p t hr
            (IsOneOrRChoreCost.relabel labels cost r hcost)
            (fun item hitem => IsSmallForExactlyTwo.relabel labels cost item (htwo item hitem))
            hcoreL hcrossFirstL hcrossSecondL (by simpa [hfdecompose] using houtsideL)
            htThree houtsideLarge
        exact ⟨allocation, halloc, hefx, hpreferred⟩)
      simpa [hone] using hresult
    · have htEq : t = 3 := by omega
      obtain ⟨labels, hzero, hone⟩ := existsFin4Equiv_map_zero_one agent partner hpartnerNe
      obtain ⟨hcoreL, hcrossFirstL, hcrossSecondL, houtsideL⟩ :=
        m2PairData_relabel_zero_one labels cost chores agent partner hzero hone 1 f
          (by simpa [haOne] using hcore) hcrossFirst hcrossSecond houtside
      have hresult := existsEfxPreferred_relabel_back labels cost chores 0
        (existsEfxOfM2PairCase322Labelled_preferredZero_three Item r
          (relabelChoreCost labels cost) chores p hr
          (IsOneOrRChoreCost.relabel labels cost r hcost)
          (fun item hitem => IsSmallForExactlyTwo.relabel labels cost item (htwo item hitem))
          hcoreL hcrossFirstL hcrossSecondL (by simpa [hfdecompose, htEq] using houtsideL))
      simpa [hzero] using hresult
  obtain ⟨labels, hzero, hone⟩ := existsFin4Equiv_map_zero_one partner agent hpartnerNe.symm
  have hcoreSwap : (m2PairCoreFibre cost chores partner agent).card = a := by
    rw [← m2PairCoreFibre_swap cost chores partner agent]
    exact hcore
  have houtsideSwap : (m2PairOutsideFibre cost chores partner agent).card = f := by
    rw [← m2PairOutsideFibre_swap cost chores partner agent]
    exact houtside
  obtain ⟨hcoreL, hcrossFirstL, hcrossSecondL, houtsideL⟩ :=
    m2PairData_relabel_zero_one labels cost chores partner agent hzero hone a f
      hcoreSwap hcrossSecond hcrossFirst houtsideSwap
  by_cases haTwo : a = 2
  · have hresult := existsEfxPreferred_relabel_back labels cost chores 1 (by
      obtain ⟨allocation, halloc, hefx, hsmallCertificate, hlargeCertificate, hpreferred⟩ :=
        existsEfxOfM2PairCase323Labelled_preferredOne_two Item r
          (relabelChoreCost labels cost) chores f hr
          (IsOneOrRChoreCost.relabel labels cost r hcost)
          (fun item hitem => IsSmallForExactlyTwo.relabel labels cost item (htwo item hitem))
          (by simpa [haTwo] using hcoreL) hcrossFirstL hcrossSecondL houtsideL
          (by simpa [haTwo] using hlt)
      exact ⟨allocation, halloc, hefx, hpreferred⟩)
    simpa [hone] using hresult
  · have haThree : 3 ≤ a := by omega
    have hresult := existsEfxPreferred_relabel_back labels cost chores 1 (by
      obtain ⟨allocation, halloc, hefx, hsmallCertificate, hlargeCertificate, hpreferred⟩ :=
        existsEfxOfM2PairCase323Labelled_preferredOne_of_three_le Item r
          (relabelChoreCost labels cost) chores a f hr
          (IsOneOrRChoreCost.relabel labels cost r hcost)
          (fun item hitem => IsSmallForExactlyTwo.relabel labels cost item (htwo item hitem))
          hcoreL hcrossFirstL hcrossSecondL houtsideL haThree hlt
      exact ⟨allocation, halloc, hefx, hpreferred⟩)
    simpa [hone] using hresult

/-- The preferred-endpoint clause of `M2properties`(iii) can use the same
explicit M₂ allocation as clause (i) whenever the residue is not exceptional.
This strengthened interface is required in source Case B.4.2(a), where the
short prefix endpoint must be residual-favorite while every other comparison
still uses the small-removal certificate. -/
theorem existsEfxOfM2TwoDisjointTypes_preferred_certified_of_notExceptional
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (firstType secondType : Finset (Fin 4)) (agent : Fin 4)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hfirstCard : firstType.card = 2) (hsecondCard : secondType.card = 2)
    (hdisjoint : Disjoint firstType secondType)
    (htypes : ∀ item ∈ chores, smallAgentSet cost item = firstType ∨
      smallAgentSet cost item = secondType)
    (hcount : (chores.filter fun item => smallAgentSet cost item = firstType).card ≤
      (chores.filter fun item => smallAgentSet cost item = secondType).card)
    (hagent : agent ∈ firstType) (hnotExceptional : ¬ IsM2Exceptional cost chores) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) ∧
      ∀ other, additiveChoreCost cost agent (allocation agent) ≤
        additiveChoreCost cost agent (allocation other) := by
  classical
  let a := (chores.filter fun item => smallAgentSet cost item = firstType).card
  let f := (chores.filter fun item => smallAgentSet cost item = secondType).card
  have htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item := by
    intro item hitem
    rcases htypes item hitem with htype | htype
    · rw [IsSmallForExactlyTwo, htype, hfirstCard]
    · rw [IsSmallForExactlyTwo, htype, hsecondCard]
  have hle : a ≤ f := by simpa [a, f] using hcount
  by_cases haZero : a = 0
  · have hsmallType : ∀ item ∈ chores, smallAgentSet cost item = secondType := by
      intro item hitem
      rcases htypes item hitem with hfirst | hsecond
      · have hmember : item ∈ chores.filter fun item => smallAgentSet cost item = firstType :=
          Finset.mem_filter.mpr ⟨hitem, hfirst⟩
        have hempty : chores.filter fun item => smallAgentSet cost item = firstType = ∅ := by
          apply Finset.card_eq_zero.mp
          simpa [a] using haZero
        have hfalse : False := by simpa [hempty] using hmember
        exact hfalse.elim
      · exact hsecond
    let q := chores.card / 4
    let remainder := chores.card % 4
    have hdecompose : chores.card = 4 * q + remainder := by
      dsimp [q, remainder]
      omega
    have hremainder : remainder < 4 := by
      dsimp [remainder]
      exact Nat.mod_lt _ (by omega)
    have hremainderNeThree : remainder ≠ 3 := by
      intro hthree
      apply hnotExceptional
      apply isM2Exceptional_of_fixedSmallType Item cost chores secondType q htwo hsmallType
      rw [hdecompose, hthree]
    have hagentNotSecond : agent ∉ secondType := by
      intro hagentSecond
      exact Finset.disjoint_left.mp hdisjoint hagent hagentSecond
    exact existsEfxOfM2SingleSmallType_preferred_largeAgent_certified_of_remainder_ne_three
      Item r cost chores q remainder secondType agent hr hcost htwo hsmallType hdecompose hremainder
      hremainderNeThree hagentNotSecond
  obtain ⟨partner, hpartnerNe, hfirstPair⟩ :
      ∃ partner, agent ≠ partner ∧ firstType = ({agent, partner} : Finset (Fin 4)) := by
    obtain ⟨x, y, hxy, htype⟩ := Finset.card_eq_two.mp hfirstCard
    rw [htype] at hagent
    simp only [Finset.mem_insert, Finset.mem_singleton] at hagent
    rcases hagent with rfl | rfl
    · exact ⟨y, hxy, htype⟩
    · refine ⟨x, hxy.symm, ?_⟩
      rw [htype]
      ext z
      simp [or_comm]
  obtain ⟨hcoreEq, hcrossFirstEq, hcrossSecondEq, houtsideEq⟩ :=
    m2PairFibres_of_two_disjoint_smallTypes cost chores firstType secondType agent partner
      hagent (by simpa [hfirstPair]) hdisjoint htypes
  have hcore : (m2PairCoreFibre cost chores agent partner).card = a := by
    simp [a, hcoreEq]
  have hcrossFirst : (m2PairCrossFibre cost chores agent partner).card = 0 := by
    rw [hcrossFirstEq]
    simp
  have hcrossSecond : (m2PairCrossFibre cost chores partner agent).card = 0 := by
    rw [hcrossSecondEq]
    simp
  have houtside : (m2PairOutsideFibre cost chores agent partner).card = f := by
    simp [f, houtsideEq]
  by_cases heq : a = f
  · obtain ⟨labels, hzero, hone⟩ := existsFin4Equiv_map_zero_one agent partner hpartnerNe
    obtain ⟨hcoreL, hcrossFirstL, hcrossSecondL, houtsideL⟩ :=
      m2PairData_relabel_zero_one labels cost chores agent partner hzero hone a f
        hcore hcrossFirst hcrossSecond houtside
    have hresult := existsEfxPreferredCertified_relabel_back labels cost chores 0
      (existsEfxOfM2PairEqualFibres_preferredZero Item r (relabelChoreCost labels cost) chores a
        hr (IsOneOrRChoreCost.relabel labels cost r hcost)
        (fun item hitem => IsSmallForExactlyTwo.relabel labels cost item (htwo item hitem))
        hcoreL hcrossFirstL hcrossSecondL (by simpa [heq] using houtsideL))
    simpa [hzero] using hresult
  have hlt : a < f := lt_of_le_of_ne hle heq
  have haPos : 0 < a := Nat.pos_of_ne_zero haZero
  by_cases haOne : a = 1
  · let p := f / 4
    let t := f % 4
    have hfdecompose : f = 4 * p + t := by
      dsimp [p, t]
      omega
    have ht : t < 4 := by
      dsimp [t]
      exact Nat.mod_lt _ (by omega)
    have houtsideLarge : 1 < 4 * p + t := by
      rw [← hfdecompose]
      omega
    by_cases htThree : t < 3
    · obtain ⟨labels, hzero, hone⟩ := existsFin4Equiv_map_zero_one partner agent hpartnerNe.symm
      have hcoreSwap : (m2PairCoreFibre cost chores partner agent).card = 1 := by
        rw [← m2PairCoreFibre_swap cost chores partner agent]
        simpa [haOne] using hcore
      have houtsideSwap : (m2PairOutsideFibre cost chores partner agent).card = f := by
        rw [← m2PairOutsideFibre_swap cost chores partner agent]
        exact houtside
      obtain ⟨hcoreL, hcrossFirstL, hcrossSecondL, houtsideL⟩ :=
        m2PairData_relabel_zero_one labels cost chores partner agent hzero hone 1 f
          hcoreSwap hcrossSecond hcrossFirst houtsideSwap
      have hresult := existsEfxPreferredCertified_relabel_back labels cost chores 1
        (existsEfxOfM2PairCase322Labelled_preferredOne_of_lt_three Item r
          (relabelChoreCost labels cost) chores p t hr
          (IsOneOrRChoreCost.relabel labels cost r hcost)
          (fun item hitem => IsSmallForExactlyTwo.relabel labels cost item (htwo item hitem))
          hcoreL hcrossFirstL hcrossSecondL (by simpa [hfdecompose] using houtsideL)
          htThree houtsideLarge)
      simpa [hone] using hresult
    · have htEq : t = 3 := by omega
      apply False.elim
      apply hnotExceptional
      apply isM2Exceptional_of_oneCoreFibre Item cost chores agent partner (f / 4) hpartnerNe
        htwo (by simpa [haOne] using hcore) hcrossFirst hcrossSecond
      rw [houtside, hfdecompose, htEq]
      have hdiv : (4 * p + 3) / 4 = p := by
        apply Nat.div_eq_of_lt_le <;> omega
      omega
  obtain ⟨labels, hzero, hone⟩ := existsFin4Equiv_map_zero_one partner agent hpartnerNe.symm
  have hcoreSwap : (m2PairCoreFibre cost chores partner agent).card = a := by
    rw [← m2PairCoreFibre_swap cost chores partner agent]
    exact hcore
  have houtsideSwap : (m2PairOutsideFibre cost chores partner agent).card = f := by
    rw [← m2PairOutsideFibre_swap cost chores partner agent]
    exact houtside
  obtain ⟨hcoreL, hcrossFirstL, hcrossSecondL, houtsideL⟩ :=
    m2PairData_relabel_zero_one labels cost chores partner agent hzero hone a f
      hcoreSwap hcrossSecond hcrossFirst houtsideSwap
  by_cases haTwo : a = 2
  · have hresult := existsEfxPreferredCertified_relabel_back labels cost chores 1
      (existsEfxOfM2PairCase323Labelled_preferredOne_two Item r
        (relabelChoreCost labels cost) chores f hr
        (IsOneOrRChoreCost.relabel labels cost r hcost)
        (fun item hitem => IsSmallForExactlyTwo.relabel labels cost item (htwo item hitem))
        (by simpa [haTwo] using hcoreL) hcrossFirstL hcrossSecondL houtsideL
        (by simpa [haTwo] using hlt))
    simpa [hone] using hresult
  · have haThree : 3 ≤ a := by omega
    have hresult := existsEfxPreferredCertified_relabel_back labels cost chores 1
      (existsEfxOfM2PairCase323Labelled_preferredOne_of_three_le Item r
        (relabelChoreCost labels cost) chores a f hr
        (IsOneOrRChoreCost.relabel labels cost r hcost)
        (fun item hitem => IsSmallForExactlyTwo.relabel labels cost item (htwo item hitem))
        hcoreL hcrossFirstL hcrossSecondL houtsideL haThree hlt)
    simpa [hone] using hresult

/-- The nonexceptional Case 3.2.2 certificates transport from the displayed
pair to any ordered deficient pair. -/
theorem existsEfxOfM2PairCase322_certified_of_lt_three
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4) (p t : ℕ)
    (hdistinct : first ≠ second) (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcore : (m2PairCoreFibre cost chores first second).card = 1)
    (hcrossFirst : (m2PairCrossFibre cost chores first second).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores second first).card = 0)
    (houtside : (m2PairOutsideFibre cost chores first second).card = 4 * p + t)
    (ht : t < 3) (houtsideLarge : 1 < 4 * p + t) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) := by
  classical
  obtain ⟨labels, hzero, hone⟩ := existsFin4Equiv_map_zero_one first second hdistinct
  obtain ⟨labelledAllocation, hlabelledAllocation, hlabelledEfx, hsmallCertificate,
    hlargeCertificate, _⟩ :=
    existsEfxOfM2PairCase322Labelled_certified_of_lt_three Item r
      (relabelChoreCost labels cost) chores p t hr
      (IsOneOrRChoreCost.relabel labels cost r hcost)
      (by
        intro item hitem
        exact IsSmallForExactlyTwo.relabel labels cost item (htwo item hitem))
      (by
        rw [m2PairCoreFibre_relabel_zero_one labels cost chores first second hzero hone]
        exact hcore)
      (by
        obtain ⟨hfirst, hsecond⟩ :=
          m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
        rw [hfirst]
        exact hcrossFirst)
      (by
        obtain ⟨hfirst, hsecond⟩ :=
          m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
        rw [hsecond]
        exact hcrossSecond)
      (by
        rw [m2PairOutsideFibre_relabel_zero_one labels cost chores first second hzero hone]
        exact houtside)
      ht houtsideLarge
  let allocation := relabelAllocation labels.symm labelledAllocation
  have halloc : IsAllocationOf allocation chores := hlabelledAllocation.relabel labels.symm
  have hefx : EFXForChores (additiveChoreCost cost) allocation := by
    have htransport := hlabelledEfx.relabel labels.symm
    have hcostEq : relabelChoreCost labels.symm (relabelChoreCost labels cost) = cost := by
      funext agent item
      simp [relabelChoreCost]
    rw [hcostEq] at htransport
    exact htransport
  refine ⟨allocation, halloc, hefx, ?_, ?_⟩
  · intro i hsmall j
    rcases hsmall with ⟨item, hitem, hitemSmall⟩
    have hlabelledSmall : ∃ item ∈ labelledAllocation (labels.symm i),
        IsSmallChore (relabelChoreCost labels cost) (labels.symm i) item := by
      refine ⟨item, ?_, ?_⟩
      · simpa [allocation, relabelAllocation] using hitem
      · simpa [relabelChoreCost, IsSmallChore] using hitemSmall
    have hcomparison := hsmallCertificate (labels.symm i) hlabelledSmall (labels.symm j)
    simpa [allocation, relabelAllocation, relabelChoreCost, additiveChoreCost] using hcomparison
  · intro i hallLarge j
    have hlabelledLarge : ∀ item ∈ labelledAllocation (labels.symm i),
        IsLargeChore (relabelChoreCost labels cost) r (labels.symm i) item := by
      intro item hitem
      have hitemOriginal : item ∈ allocation i := by
        simpa [allocation, relabelAllocation] using hitem
      have hlarge := hallLarge item hitemOriginal
      simpa [relabelChoreCost, IsLargeChore] using hlarge
    have hcomparison := hlargeCertificate (labels.symm i) hlabelledLarge (labels.symm j)
    simpa [allocation, relabelAllocation, relabelChoreCost, additiveChoreCost] using hcomparison

/-- Source Case 3.2.3 in its displayed labelling.  With at least two common
small chores, no cross-fiber chores, and a larger outside fiber, the source
floor witness for `L` yields a feasible EFX allocation. -/
theorem existsEfxOfM2PairCase323Labelled_certified
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a f : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcore : (m2PairCoreFibre cost chores 0 1).card = a)
    (hcrossFirst : (m2PairCrossFibre cost chores 0 1).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores 1 0).card = 0)
    (houtside : (m2PairOutsideFibre cost chores 0 1).card = f)
    (ha : 2 ≤ a) (hfa : a < f) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) := by
  classical
  obtain ⟨L, hupper, hlower⟩ := m2Case323_exists_outsideShare a f ha hfa
  have houtsideSplit : 2 * L ≤ f := by
    have hplusPos : 1 ≤ (a + 1) / 2 := by omega
    omega
  have hcrossFirstEmpty : m2PairCrossFibre cost chores 0 1 = ∅ :=
    Finset.card_eq_zero.mp hcrossFirst
  have hcrossSecondEmpty : m2PairCrossFibre cost chores 1 0 = ∅ :=
    Finset.card_eq_zero.mp hcrossSecond
  obtain ⟨coreAllocation, outsideAllocation, hcoreAllocation, hcoreCard,
    houtsideAllocation, houtsideCard, hallocation⟩ :=
    existsM2Case323Allocation Item cost chores a f L hcore houtside houtsideSplit
  let allocation := m2PairSplitAllocation cost chores coreAllocation outsideAllocation
  have halloc : IsAllocationOf allocation chores := by
    change IsAllocationOf
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) chores
    exact hallocation
  have hefx : EFXForChores (additiveChoreCost cost) allocation := by
    exact efxOfM2PairCase323Split r cost chores coreAllocation outsideAllocation a f L hr hcost
      hcoreAllocation houtsideAllocation hcoreCard houtsideCard hcrossFirstEmpty hcrossSecondEmpty
      houtside htwo hfa hupper hlower
  have hcoreTwoEmpty : coreAllocation 2 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 2
  have hcoreThreeEmpty : coreAllocation 3 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 3
  have htwoSmall : ∀ item ∈ allocation 2, IsSmallChore cost 2 item := by
    change ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 2,
      IsSmallChore cost 2 item
    exact m2PairSplitAllocation_two_ownSmall cost chores coreAllocation outsideAllocation
      hcoreTwoEmpty houtsideAllocation htwo
  have hthreeSmall : ∀ item ∈ allocation 3, IsSmallChore cost 3 item := by
    change ∀ item ∈
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 3,
      IsSmallChore cost 3 item
    exact m2PairSplitAllocation_three_ownSmall cost chores coreAllocation outsideAllocation
      hcoreThreeEmpty houtsideAllocation htwo
  refine ⟨allocation, halloc, hefx, ?_, ?_⟩
  · intro i hsmall
    exact smallItemCertificate_of_efx Item cost allocation hefx i hsmall
  · intro i hallLarge j
    fin_cases i
    · exfalso
      have hcoreZeroCard : (coreAllocation 0).card = (a + 1) / 2 := by
        simpa [m2PairCoreQuota] using hcoreCard 0
      have hcoreZeroPos : 0 < (coreAllocation 0).card := by omega
      obtain ⟨item, hitem⟩ := Finset.card_pos.mp hcoreZeroPos
      have hitemAllocation : item ∈ allocation 0 := by
        simp [allocation, m2PairSplitAllocation, hitem]
      have hsmall : IsSmallChore cost 0 item := by
        have hpool : item ∈ m2PairCoreFibre cost chores 0 1 := hcoreAllocation.1 0 item hitem
        exact isSmallChore_of_mem_smallAgentSet cost 0 item (Finset.mem_filter.mp hpool).2.1
      have hlarge : cost 0 item = r := by
        simpa [IsLargeChore] using hallLarge item hitemAllocation
      rw [IsSmallChore] at hsmall
      linarith
    · exfalso
      have hcoreOneCard : (coreAllocation 1).card = a / 2 := by
        simpa [m2PairCoreQuota] using hcoreCard 1
      have hcoreOnePos : 0 < (coreAllocation 1).card := by omega
      obtain ⟨item, hitem⟩ := Finset.card_pos.mp hcoreOnePos
      have hitemAllocation : item ∈ allocation 1 := by
        simp [allocation, m2PairSplitAllocation, hitem]
      have hsmall : IsSmallChore cost 1 item := by
        have hpool : item ∈ m2PairCoreFibre cost chores 0 1 := hcoreAllocation.1 1 item hitem
        exact isSmallChore_of_mem_smallAgentSet cost 1 item (Finset.mem_filter.mp hpool).2.2
      have hlarge : cost 1 item = r := by
        simpa [IsLargeChore] using hallLarge item hitemAllocation
      rw [IsSmallChore] at hsmall
      linarith
    · have hempty : allocation 2 = ∅ := by
        by_contra hnotempty
        obtain ⟨item, hitem⟩ := Finset.nonempty_iff_ne_empty.mpr hnotempty
        have hsmall := htwoSmall item hitem
        have hlarge : cost 2 item = r := by
          simpa [IsLargeChore] using hallLarge item hitem
        rw [IsSmallChore] at hsmall
        linarith
      change additiveChoreCost cost 2 (allocation 2) ≤ additiveChoreCost cost 2 (allocation j)
      rw [hempty]
      simp only [additiveChoreCost, Finset.sum_empty]
      exact additiveChoreCost_nonneg cost
        (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 2 (allocation j)
    · have hempty : allocation 3 = ∅ := by
        by_contra hnotempty
        obtain ⟨item, hitem⟩ := Finset.nonempty_iff_ne_empty.mpr hnotempty
        have hsmall := hthreeSmall item hitem
        have hlarge : cost 3 item = r := by
          simpa [IsLargeChore] using hallLarge item hitem
        rw [IsSmallChore] at hsmall
        linarith
      change additiveChoreCost cost 3 (allocation 3) ≤ additiveChoreCost cost 3 (allocation j)
      rw [hempty]
      simp only [additiveChoreCost, Finset.sum_empty]
      exact additiveChoreCost_nonneg cost
        (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 3 (allocation j)

/-- Case 3.2.3 at the basic EFX-existence interface. -/
theorem existsEfxOfM2PairCase323Labelled
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a f : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcore : (m2PairCoreFibre cost chores 0 1).card = a)
    (hcrossFirst : (m2PairCrossFibre cost chores 0 1).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores 1 0).card = 0)
    (houtside : (m2PairOutsideFibre cost chores 0 1).card = f)
    (ha : 2 ≤ a) (hfa : a < f) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨allocation, halloc, hefx, _, _⟩ :=
    existsEfxOfM2PairCase323Labelled_certified Item r cost chores a f hr hcost htwo hcore
      hcrossFirst hcrossSecond houtside ha hfa
  exact ⟨allocation, halloc, hefx⟩

/-- Case 3.2.3 for an arbitrary ordered deficient pair, transported through
the finite relabelling that maps that pair to the source labels `0,1`. -/
theorem existsEfxOfM2PairCase323
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4) (a f : ℕ)
    (hdistinct : first ≠ second) (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcore : (m2PairCoreFibre cost chores first second).card = a)
    (hcrossFirst : (m2PairCrossFibre cost chores first second).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores second first).card = 0)
    (houtside : (m2PairOutsideFibre cost chores first second).card = f)
    (ha : 2 ≤ a) (hfa : a < f) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  classical
  obtain ⟨labels, hzero, hone⟩ := existsFin4Equiv_map_zero_one first second hdistinct
  apply exists_efx_relabel_back labels cost chores
  apply existsEfxOfM2PairCase323Labelled Item r (relabelChoreCost labels cost) chores a f hr
    (IsOneOrRChoreCost.relabel labels cost r hcost)
  · intro item hitem
    exact IsSmallForExactlyTwo.relabel labels cost item (htwo item hitem)
  · rw [m2PairCoreFibre_relabel_zero_one labels cost chores first second hzero hone]
    exact hcore
  · obtain ⟨hfirst, hsecond⟩ :=
      m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
    rw [hfirst]
    exact hcrossFirst
  · obtain ⟨hfirst, hsecond⟩ :=
      m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
    rw [hsecond]
    exact hcrossSecond
  · rw [m2PairOutsideFibre_relabel_zero_one labels cost chores first second hzero hone]
    exact houtside
  · exact ha
  · exact hfa

/-- The nonexceptional certificates for Case 3.2.3 are invariant under the
finite relabelling used to present an arbitrary deficient pair as `0,1`. -/
theorem existsEfxOfM2PairCase323_certified
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4) (a f : ℕ)
    (hdistinct : first ≠ second) (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hcore : (m2PairCoreFibre cost chores first second).card = a)
    (hcrossFirst : (m2PairCrossFibre cost chores first second).card = 0)
    (hcrossSecond : (m2PairCrossFibre cost chores second first).card = 0)
    (houtside : (m2PairOutsideFibre cost chores first second).card = f)
    (ha : 2 ≤ a) (hfa : a < f) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) := by
  classical
  obtain ⟨labels, hzero, hone⟩ := existsFin4Equiv_map_zero_one first second hdistinct
  obtain ⟨labelledAllocation, hlabelledAllocation, hlabelledEfx, hsmallCertificate,
    hlargeCertificate⟩ :=
    existsEfxOfM2PairCase323Labelled_certified Item r (relabelChoreCost labels cost) chores a f
      hr (IsOneOrRChoreCost.relabel labels cost r hcost)
      (by
        intro item hitem
        exact IsSmallForExactlyTwo.relabel labels cost item (htwo item hitem))
      (by
        rw [m2PairCoreFibre_relabel_zero_one labels cost chores first second hzero hone]
        exact hcore)
      (by
        obtain ⟨hfirst, hsecond⟩ :=
          m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
        rw [hfirst]
        exact hcrossFirst)
      (by
        obtain ⟨hfirst, hsecond⟩ :=
          m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
        rw [hsecond]
        exact hcrossSecond)
      (by
        rw [m2PairOutsideFibre_relabel_zero_one labels cost chores first second hzero hone]
        exact houtside)
      ha hfa
  let allocation := relabelAllocation labels.symm labelledAllocation
  have halloc : IsAllocationOf allocation chores := hlabelledAllocation.relabel labels.symm
  have hefx : EFXForChores (additiveChoreCost cost) allocation := by
    have htransport := hlabelledEfx.relabel labels.symm
    have hcostEq : relabelChoreCost labels.symm (relabelChoreCost labels cost) = cost := by
      funext agent item
      simp [relabelChoreCost]
    rw [hcostEq] at htransport
    exact htransport
  refine ⟨allocation, halloc, hefx, ?_, ?_⟩
  · intro i hsmall j
    rcases hsmall with ⟨item, hitem, hitemSmall⟩
    have hlabelledSmall : ∃ item ∈ labelledAllocation (labels.symm i),
        IsSmallChore (relabelChoreCost labels cost) (labels.symm i) item := by
      refine ⟨item, ?_, ?_⟩
      · simpa [allocation, relabelAllocation] using hitem
      · simpa [relabelChoreCost, IsSmallChore] using hitemSmall
    have hcomparison := hsmallCertificate (labels.symm i) hlabelledSmall (labels.symm j)
    simpa [allocation, relabelAllocation, relabelChoreCost, additiveChoreCost] using hcomparison
  · intro i hallLarge j
    have hlabelledLarge : ∀ item ∈ labelledAllocation (labels.symm i),
        IsLargeChore (relabelChoreCost labels cost) r (labels.symm i) item := by
      intro item hitem
      have hitemOriginal : item ∈ allocation i := by
        simpa [allocation, relabelAllocation] using hitem
      have hlarge := hallLarge item hitemOriginal
      simpa [relabelChoreCost, IsLargeChore] using hlarge
    have hcomparison := hlargeCertificate (labels.symm i) hlabelledLarge (labels.symm j)
    simpa [allocation, relabelAllocation, relabelChoreCost, additiveChoreCost] using hcomparison

/-- Source Case 3.1 in its displayed labelling: when `{0,1}` is the positive
maximum-deficiency pair, the cross fibers are present, and the two source
quarter-size bounds hold, there is a feasible EFX allocation.  This combines
the exact finite-fiber allocation, the interval split, and the full EFX
verification above.  Relabelling an arbitrary maximum pair is deliberately
left to the outer M2 case theorem. -/
theorem existsEfxOfM2PairCase31Labelled
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q remainder : ℕ)
    (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hdecompose : chores.card = 4 * q + remainder) (hremainder : remainder < 4)
    (hpairPositive : chores.card < 2 * (m2PairOutsideFibre cost chores 0 1).card)
    (hfirstCrossBound : 4 * (m2PairCrossFibre cost chores 0 1).card ≤ chores.card)
    (hsecondCrossBound : 4 * (m2PairCrossFibre cost chores 1 0).card ≤ chores.card)
    (hcrossPresent : 0 < (m2PairCrossFibre cost chores 0 1).card +
      (m2PairCrossFibre cost chores 1 0).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  let a := (m2PairCoreFibre cost chores 0 1).card
  let b := (m2PairCrossFibre cost chores 0 1).card
  let c := (m2PairCrossFibre cost chores 1 0).card
  let f := (m2PairOutsideFibre cost chores 0 1).card
  let target := (4 * q + remainder + 1) / 4
  have hm : a + b + c + f = 4 * q + remainder := by
    change (m2PairCoreFibre cost chores 0 1).card +
        (m2PairCrossFibre cost chores 0 1).card +
        (m2PairCrossFibre cost chores 1 0).card +
        (m2PairOutsideFibre cost chores 0 1).card = 4 * q + remainder
    rw [m2PairFibres_card_sum, ← hdecompose]
  have hpair : 4 * q + remainder < 2 * f := by
    simpa [f, hdecompose] using hpairPositive
  have hfirstBound : 4 * b ≤ 4 * q + remainder := by
    simpa [b, hdecompose] using hfirstCrossBound
  have hsecondBound : 4 * c ≤ 4 * q + remainder := by
    simpa [c, hdecompose] using hsecondCrossBound
  have hcross : 0 < b + c := by simpa [b, c] using hcrossPresent
  obtain ⟨firstCore, secondCore, firstOutside, secondOutside, hcoreShares,
      houtsideShares, hfirstTarget, hsecondTarget, hzeroToOne, honeToZero⟩ :=
    existsM2CrossSplit_of_pairBounds a b c f q remainder hm hremainder hpair
      hfirstBound hsecondBound hcross
  obtain ⟨houtsideSharesLe, htwoLower, hthreeLower, htwoUpper, hthreeUpper,
      htwoThree, hthreeTwo⟩ :=
    m2Case31_outsideQuota_bounds a b c f q remainder firstOutside secondOutside
      hm hremainder hpair houtsideShares
  obtain ⟨coreAllocation, outsideAllocation, hcoreAllocation, hcoreCard,
      houtsideAllocation, houtsideCard, hfull⟩ :=
    existsM2PairSplitAllocation Item cost chores firstCore secondCore firstOutside secondOutside
      (by simpa [a] using hcoreShares) (by simpa [f] using houtsideSharesLe)
  have hcoreZero : (coreAllocation 0).card = firstCore := by
    simpa [m2PairCoreQuota] using hcoreCard 0
  have hcoreOne : (coreAllocation 1).card = secondCore := by
    simpa [m2PairCoreQuota] using hcoreCard 1
  have hcoreTwo : coreAllocation 2 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 2
  have hcoreThree : coreAllocation 3 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 3
  have houtsideZero : (outsideAllocation 0).card = firstOutside := by
    simpa [m2PairOutsideQuota] using houtsideCard 0
  have houtsideOne : (outsideAllocation 1).card = secondOutside := by
    simpa [m2PairOutsideQuota] using houtsideCard 1
  let allocation := m2PairSplitAllocation cost chores coreAllocation outsideAllocation
  have hcardZero : (allocation 0).card = target := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0).card = target
    rw [m2PairSplitAllocation_zero_card cost chores coreAllocation outsideAllocation
      firstCore firstOutside hcoreAllocation houtsideAllocation hcoreZero houtsideZero]
    dsimp [b, target]
    omega
  have hcardOne : (allocation 1).card = target := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1).card = target
    rw [m2PairSplitAllocation_one_card cost chores coreAllocation outsideAllocation
      secondCore secondOutside hcoreAllocation houtsideAllocation hcoreOne houtsideOne]
    dsimp [c, target]
    omega
  have hcardTwo : (allocation 2).card = (f - firstOutside - secondOutside) / 2 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 2).card = (f - firstOutside - secondOutside) / 2
    rw [m2PairSplitAllocation_two_eq_outside cost chores coreAllocation outsideAllocation hcoreTwo,
      houtsideCard 2]
    simp [m2PairOutsideQuota, f]
  have hcardThree : (allocation 3).card =
      f - firstOutside - secondOutside - (f - firstOutside - secondOutside) / 2 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 3).card =
        f - firstOutside - secondOutside - (f - firstOutside - secondOutside) / 2
    rw [m2PairSplitAllocation_three_eq_outside cost chores coreAllocation outsideAllocation hcoreThree,
      houtsideCard 3]
    simp [m2PairOutsideQuota, f]
  have hcompTwoZero :
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 2).card ≤
        (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 0).card + 1 := by
    change (allocation 2).card ≤ (allocation 0).card + 1
    rw [hcardTwo, hcardZero]
    simpa [target] using htwoUpper
  have hcompTwoOne :
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 2).card ≤
        (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 1).card + 1 := by
    change (allocation 2).card ≤ (allocation 1).card + 1
    rw [hcardTwo, hcardOne]
    simpa [target] using htwoUpper
  have hcompTwoThree :
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 2).card ≤
        (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 3).card + 1 := by
    change (allocation 2).card ≤ (allocation 3).card + 1
    rw [hcardTwo, hcardThree]
    simpa using htwoThree
  have hcompThreeZero :
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 3).card ≤
        (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 0).card + 1 := by
    change (allocation 3).card ≤ (allocation 0).card + 1
    rw [hcardThree, hcardZero]
    simpa [target] using hthreeUpper
  have hcompThreeOne :
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 3).card ≤
        (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 1).card + 1 := by
    change (allocation 3).card ≤ (allocation 1).card + 1
    rw [hcardThree, hcardOne]
    simpa [target] using hthreeUpper
  have hcompThreeTwo :
      (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 3).card ≤
        (m2PairSplitAllocation cost chores coreAllocation outsideAllocation 2).card + 1 := by
    change (allocation 3).card ≤ (allocation 2).card + 1
    rw [hcardThree, hcardTwo]
    simpa using hthreeTwo
  have hallocationShape : m2PairSplitAllocation cost chores coreAllocation outsideAllocation =
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) := by
    funext agent
    simp only [m2PairSplitAllocation, Finset.union_assoc]
  refine ⟨allocation, ?_, ?_⟩
  · rw [show allocation = m2PairSplitAllocation cost chores coreAllocation outsideAllocation by rfl,
      hallocationShape]
    exact hfull
  · apply efxOfM2PairSplitOfCardBounds r cost chores coreAllocation outsideAllocation
      firstCore secondCore firstOutside secondOutside target (by linarith) hcost hcoreAllocation
      houtsideAllocation hcoreCard houtsideCard htwo
    · simpa [b, target] using hfirstTarget
    · simpa [c, target] using hsecondTarget
    · simpa [c] using hzeroToOne
    · simpa [b] using honeToZero
    · rw [houtsideCard 2]
      simpa [m2PairOutsideQuota, f, target] using htwoLower
    · rw [houtsideCard 3]
      simpa [m2PairOutsideQuota, f, target] using hthreeLower
    · intro i j hi
      fin_cases i
      · exact False.elim (by simpa using hi)
      · exact False.elim (by simpa using hi)
      · fin_cases j
        · exact hcompTwoZero
        · exact hcompTwoOne
        · omega
        · exact hcompTwoThree
      · fin_cases j
        · exact hcompThreeZero
        · exact hcompThreeOne
        · exact hcompThreeTwo
        · omega

/-- The displayed Case 3.1 construction has the M2-properties certificates
whenever a residue-three all-large endpoint would contain a positive incident
cross fiber. -/
theorem existsEfxOfM2PairCase31Labelled_certified_of_safe_endpoint_fibres
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q remainder : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hdecompose : chores.card = 4 * q + remainder) (hremainder : remainder < 4)
    (hpairPositive : chores.card < 2 * (m2PairOutsideFibre cost chores 0 1).card)
    (hfirstCrossBound : 4 * (m2PairCrossFibre cost chores 0 1).card ≤ chores.card)
    (hsecondCrossBound : 4 * (m2PairCrossFibre cost chores 1 0).card ≤ chores.card)
    (hcrossPresent : 0 < (m2PairCrossFibre cost chores 0 1).card +
      (m2PairCrossFibre cost chores 1 0).card)
    (hzeroSafe : remainder ≠ 3 ∨ 0 < (m2PairCoreFibre cost chores 0 1).card ∨
      0 < (m2PairCrossFibre cost chores 0 1).card)
    (honeSafe : remainder ≠ 3 ∨ 0 < (m2PairCoreFibre cost chores 0 1).card ∨
      0 < (m2PairCrossFibre cost chores 1 0).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) := by
  let a := (m2PairCoreFibre cost chores 0 1).card
  let b := (m2PairCrossFibre cost chores 0 1).card
  let c := (m2PairCrossFibre cost chores 1 0).card
  let f := (m2PairOutsideFibre cost chores 0 1).card
  let target := (4 * q + remainder + 1) / 4
  have hm : a + b + c + f = 4 * q + remainder := by
    change (m2PairCoreFibre cost chores 0 1).card +
        (m2PairCrossFibre cost chores 0 1).card +
        (m2PairCrossFibre cost chores 1 0).card +
        (m2PairOutsideFibre cost chores 0 1).card = 4 * q + remainder
    rw [m2PairFibres_card_sum, ← hdecompose]
  have hpair : 4 * q + remainder < 2 * f := by
    simpa [f, hdecompose] using hpairPositive
  have hfirstBound : 4 * b ≤ 4 * q + remainder := by
    simpa [b, hdecompose] using hfirstCrossBound
  have hsecondBound : 4 * c ≤ 4 * q + remainder := by
    simpa [c, hdecompose] using hsecondCrossBound
  have hcross : 0 < b + c := by simpa [b, c] using hcrossPresent
  obtain ⟨firstCore, secondCore, firstOutside, secondOutside, hcoreShares,
      houtsideShares, hfirstTarget, hsecondTarget, hzeroToOne, honeToZero⟩ :=
    existsM2CrossSplit_of_pairBounds a b c f q remainder hm hremainder hpair
      hfirstBound hsecondBound hcross
  obtain ⟨houtsideSharesLe, htwoLower, hthreeLower, htwoUpper, hthreeUpper,
      htwoThree, hthreeTwo⟩ :=
    m2Case31_outsideQuota_bounds a b c f q remainder firstOutside secondOutside
      hm hremainder hpair houtsideShares
  obtain ⟨coreAllocation, outsideAllocation, hcoreAllocation, hcoreCard,
      houtsideAllocation, houtsideCard, hfull⟩ :=
    existsM2PairSplitAllocation Item cost chores firstCore secondCore firstOutside secondOutside
      (by simpa [a] using hcoreShares) (by simpa [f] using houtsideSharesLe)
  have hcoreZero : (coreAllocation 0).card = firstCore := by
    simpa [m2PairCoreQuota] using hcoreCard 0
  have hcoreOne : (coreAllocation 1).card = secondCore := by
    simpa [m2PairCoreQuota] using hcoreCard 1
  have hcoreTwo : coreAllocation 2 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 2
  have hcoreThree : coreAllocation 3 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [m2PairCoreQuota] using hcoreCard 3
  have houtsideZero : (outsideAllocation 0).card = firstOutside := by
    simpa [m2PairOutsideQuota] using houtsideCard 0
  have houtsideOne : (outsideAllocation 1).card = secondOutside := by
    simpa [m2PairOutsideQuota] using houtsideCard 1
  let allocation := m2PairSplitAllocation cost chores coreAllocation outsideAllocation
  have hcardZero : (allocation 0).card = target := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 0).card = target
    rw [m2PairSplitAllocation_zero_card cost chores coreAllocation outsideAllocation
      firstCore firstOutside hcoreAllocation houtsideAllocation hcoreZero houtsideZero]
    dsimp [b, target]
    omega
  have hcardOne : (allocation 1).card = target := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 1).card = target
    rw [m2PairSplitAllocation_one_card cost chores coreAllocation outsideAllocation
      secondCore secondOutside hcoreAllocation houtsideAllocation hcoreOne houtsideOne]
    dsimp [c, target]
    omega
  have hcardTwo : (allocation 2).card = (f - firstOutside - secondOutside) / 2 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 2).card = (f - firstOutside - secondOutside) / 2
    rw [m2PairSplitAllocation_two_eq_outside cost chores coreAllocation outsideAllocation hcoreTwo,
      houtsideCard 2]
    simp [m2PairOutsideQuota, f]
  have hcardThree : (allocation 3).card =
      f - firstOutside - secondOutside - (f - firstOutside - secondOutside) / 2 := by
    change
      ((fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) 3).card =
        f - firstOutside - secondOutside - (f - firstOutside - secondOutside) / 2
    rw [m2PairSplitAllocation_three_eq_outside cost chores coreAllocation outsideAllocation hcoreThree,
      houtsideCard 3]
    simp [m2PairOutsideQuota, f]
  have hcompTwoZero : (allocation 2).card ≤ (allocation 0).card + 1 := by
    rw [hcardTwo, hcardZero]
    simpa [target] using htwoUpper
  have hcompTwoOne : (allocation 2).card ≤ (allocation 1).card + 1 := by
    rw [hcardTwo, hcardOne]
    simpa [target] using htwoUpper
  have hcompTwoThree : (allocation 2).card ≤ (allocation 3).card + 1 := by
    rw [hcardTwo, hcardThree]
    simpa using htwoThree
  have hcompThreeZero : (allocation 3).card ≤ (allocation 0).card + 1 := by
    rw [hcardThree, hcardZero]
    simpa [target] using hthreeUpper
  have hcompThreeOne : (allocation 3).card ≤ (allocation 1).card + 1 := by
    rw [hcardThree, hcardOne]
    simpa [target] using hthreeUpper
  have hcompThreeTwo : (allocation 3).card ≤ (allocation 2).card + 1 := by
    rw [hcardThree, hcardTwo]
    simpa using hthreeTwo
  have halloc : IsAllocationOf allocation chores := by
    change IsAllocationOf
      (fun agent => coreAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 (m2PairCrossFibre cost chores 0 1)) agent ∪
          ((allocateAllTo (Fin 4) Item 1 (m2PairCrossFibre cost chores 1 0)) agent ∪
            outsideAllocation agent)) chores
    exact hfull
  have hefx : EFXForChores (additiveChoreCost cost) allocation := by
    apply efxOfM2PairSplitOfCardBounds r cost chores coreAllocation outsideAllocation
      firstCore secondCore firstOutside secondOutside target (by linarith) hcost hcoreAllocation
      houtsideAllocation hcoreCard houtsideCard htwo
    · simpa [b, target] using hfirstTarget
    · simpa [c, target] using hsecondTarget
    · simpa [c] using hzeroToOne
    · simpa [b] using honeToZero
    · rw [houtsideCard 2]
      simpa [m2PairOutsideQuota, f, target] using htwoLower
    · rw [houtsideCard 3]
      simpa [m2PairOutsideQuota, f, target] using hthreeLower
    · intro i j hi
      fin_cases i
      · exact False.elim (by simpa using hi)
      · exact False.elim (by simpa using hi)
      · fin_cases j
        · exact hcompTwoZero
        · exact hcompTwoOne
        · omega
        · exact hcompTwoThree
      · fin_cases j
        · exact hcompThreeZero
        · exact hcompThreeOne
        · exact hcompThreeTwo
        · omega
  refine ⟨allocation, halloc, hefx, ?_⟩
  exact m2Case31SplitCertificates_of_remainder_ne_three r cost chores coreAllocation
    outsideAllocation q remainder firstCore secondCore firstOutside secondOutside hr hcost htwo
    hcoreAllocation hcoreCard houtsideAllocation houtsideCard (by simpa [a, b, c, f] using hm)
    hremainder (by simpa [a] using hcoreShares) (by simpa [b, target] using hfirstTarget)
    (by simpa [c, target] using hsecondTarget) (by simpa [c] using hzeroToOne)
    (by simpa [b] using honeToZero) hefx hzeroSafe honeSafe

/-- The safe-endpoint construction specializes to every non-residue-three
Case 3.1 instance. -/
theorem existsEfxOfM2PairCase31Labelled_certified_of_remainder_ne_three
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q remainder : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hdecompose : chores.card = 4 * q + remainder) (hremainder : remainder < 4)
    (hpairPositive : chores.card < 2 * (m2PairOutsideFibre cost chores 0 1).card)
    (hfirstCrossBound : 4 * (m2PairCrossFibre cost chores 0 1).card ≤ chores.card)
    (hsecondCrossBound : 4 * (m2PairCrossFibre cost chores 1 0).card ≤ chores.card)
    (hcrossPresent : 0 < (m2PairCrossFibre cost chores 0 1).card +
      (m2PairCrossFibre cost chores 1 0).card)
    (hremainderNeThree : remainder ≠ 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) := by
  exact existsEfxOfM2PairCase31Labelled_certified_of_safe_endpoint_fibres Item r cost chores
    q remainder hr hcost htwo hdecompose hremainder hpairPositive hfirstCrossBound hsecondCrossBound
    hcrossPresent (Or.inl hremainderNeThree) (Or.inl hremainderNeThree)

/-- Case 3.1 for an arbitrary ordered deficient pair, obtained by relabelling
the pair to the source labels `0,1` and transporting the labelled EFX split
back to the original agents. -/
theorem existsEfxOfM2PairCase31
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4) (q remainder : ℕ)
    (hdistinct : first ≠ second) (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hdecompose : chores.card = 4 * q + remainder) (hremainder : remainder < 4)
    (hpairPositive : chores.card < 2 * (m2PairOutsideFibre cost chores first second).card)
    (hfirstCrossBound : 4 * (m2PairCrossFibre cost chores first second).card ≤ chores.card)
    (hsecondCrossBound : 4 * (m2PairCrossFibre cost chores second first).card ≤ chores.card)
    (hcrossPresent : 0 < (m2PairCrossFibre cost chores first second).card +
      (m2PairCrossFibre cost chores second first).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  classical
  obtain ⟨labels, hzero, hone⟩ := existsFin4Equiv_map_zero_one first second hdistinct
  apply exists_efx_relabel_back labels cost chores
  apply existsEfxOfM2PairCase31Labelled Item r (relabelChoreCost labels cost) chores q remainder hr
    (IsOneOrRChoreCost.relabel labels cost r hcost)
  · intro item hitem
    exact IsSmallForExactlyTwo.relabel labels cost item (htwo item hitem)
  · exact hdecompose
  · exact hremainder
  · rw [m2PairOutsideFibre_relabel_zero_one labels cost chores first second hzero hone]
    exact hpairPositive
  · obtain ⟨hfirst, hsecond⟩ :=
      m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
    rw [hfirst]
    exact hfirstCrossBound
  · obtain ⟨hfirst, hsecond⟩ :=
      m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
    rw [hsecond]
    exact hsecondCrossBound
  · obtain ⟨hfirst, hsecond⟩ :=
      m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
    rw [hfirst, hsecond]
    exact hcrossPresent

/-- The non-residue Case 3.1 certificates transport from the source labels
to any ordered maximally deficient pair. -/
theorem existsEfxOfM2PairCase31_certified_of_remainder_ne_three
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4) (q remainder : ℕ)
    (hdistinct : first ≠ second) (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hdecompose : chores.card = 4 * q + remainder) (hremainder : remainder < 4)
    (hpairPositive : chores.card < 2 * (m2PairOutsideFibre cost chores first second).card)
    (hfirstCrossBound : 4 * (m2PairCrossFibre cost chores first second).card ≤ chores.card)
    (hsecondCrossBound : 4 * (m2PairCrossFibre cost chores second first).card ≤ chores.card)
    (hcrossPresent : 0 < (m2PairCrossFibre cost chores first second).card +
      (m2PairCrossFibre cost chores second first).card)
    (hremainderNeThree : remainder ≠ 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) := by
  classical
  obtain ⟨labels, hzero, hone⟩ := existsFin4Equiv_map_zero_one first second hdistinct
  obtain ⟨labelledAllocation, hlabelledAllocation, hlabelledEfx, hsmallCertificate,
    hlargeCertificate⟩ :=
    existsEfxOfM2PairCase31Labelled_certified_of_remainder_ne_three Item r
      (relabelChoreCost labels cost) chores q remainder hr
      (IsOneOrRChoreCost.relabel labels cost r hcost)
      (by
        intro item hitem
        exact IsSmallForExactlyTwo.relabel labels cost item (htwo item hitem))
      hdecompose hremainder
      (by
        rw [m2PairOutsideFibre_relabel_zero_one labels cost chores first second hzero hone]
        exact hpairPositive)
      (by
        obtain ⟨hfirst, hsecond⟩ :=
          m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
        rw [hfirst]
        exact hfirstCrossBound)
      (by
        obtain ⟨hfirst, hsecond⟩ :=
          m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
        rw [hsecond]
        exact hsecondCrossBound)
      (by
        obtain ⟨hfirst, hsecond⟩ :=
          m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
        rw [hfirst, hsecond]
        exact hcrossPresent)
      hremainderNeThree
  let allocation := relabelAllocation labels.symm labelledAllocation
  have halloc : IsAllocationOf allocation chores := hlabelledAllocation.relabel labels.symm
  have hefx : EFXForChores (additiveChoreCost cost) allocation := by
    have htransport := hlabelledEfx.relabel labels.symm
    have hcostEq : relabelChoreCost labels.symm (relabelChoreCost labels cost) = cost := by
      funext agent item
      simp [relabelChoreCost]
    rw [hcostEq] at htransport
    exact htransport
  refine ⟨allocation, halloc, hefx, ?_, ?_⟩
  · intro i hsmall j
    rcases hsmall with ⟨item, hitem, hitemSmall⟩
    have hlabelledSmall : ∃ item ∈ labelledAllocation (labels.symm i),
        IsSmallChore (relabelChoreCost labels cost) (labels.symm i) item := by
      refine ⟨item, ?_, ?_⟩
      · simpa [allocation, relabelAllocation] using hitem
      · simpa [relabelChoreCost, IsSmallChore] using hitemSmall
    have hcomparison := hsmallCertificate (labels.symm i) hlabelledSmall (labels.symm j)
    simpa [allocation, relabelAllocation, relabelChoreCost, additiveChoreCost] using hcomparison
  · intro i hallLarge j
    have hlabelledLarge : ∀ item ∈ labelledAllocation (labels.symm i),
        IsLargeChore (relabelChoreCost labels cost) r (labels.symm i) item := by
      intro item hitem
      have hitemOriginal : item ∈ allocation i := by
        simpa [allocation, relabelAllocation] using hitem
      have hlarge := hallLarge item hitemOriginal
      simpa [relabelChoreCost, IsLargeChore] using hlarge
    have hcomparison := hlargeCertificate (labels.symm i) hlabelledLarge (labels.symm j)
    simpa [allocation, relabelAllocation, relabelChoreCost, additiveChoreCost] using hcomparison

/-- The safe-endpoint form of the Case 3.1 certificates transports to any
ordered maximally deficient pair. -/
theorem existsEfxOfM2PairCase31_certified_of_safe_endpoint_fibres
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4) (q remainder : ℕ)
    (hdistinct : first ≠ second) (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hdecompose : chores.card = 4 * q + remainder) (hremainder : remainder < 4)
    (hpairPositive : chores.card < 2 * (m2PairOutsideFibre cost chores first second).card)
    (hfirstCrossBound : 4 * (m2PairCrossFibre cost chores first second).card ≤ chores.card)
    (hsecondCrossBound : 4 * (m2PairCrossFibre cost chores second first).card ≤ chores.card)
    (hcrossPresent : 0 < (m2PairCrossFibre cost chores first second).card +
      (m2PairCrossFibre cost chores second first).card)
    (hzeroSafe : remainder ≠ 3 ∨ 0 < (m2PairCoreFibre cost chores first second).card ∨
      0 < (m2PairCrossFibre cost chores first second).card)
    (honeSafe : remainder ≠ 3 ∨ 0 < (m2PairCoreFibre cost chores first second).card ∨
      0 < (m2PairCrossFibre cost chores second first).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) := by
  classical
  obtain ⟨labels, hzero, hone⟩ := existsFin4Equiv_map_zero_one first second hdistinct
  obtain ⟨labelledAllocation, hlabelledAllocation, hlabelledEfx, hsmallCertificate,
    hlargeCertificate⟩ :=
    existsEfxOfM2PairCase31Labelled_certified_of_safe_endpoint_fibres Item r
      (relabelChoreCost labels cost) chores q remainder hr
      (IsOneOrRChoreCost.relabel labels cost r hcost)
      (by
        intro item hitem
        exact IsSmallForExactlyTwo.relabel labels cost item (htwo item hitem))
      hdecompose hremainder
      (by
        rw [m2PairOutsideFibre_relabel_zero_one labels cost chores first second hzero hone]
        exact hpairPositive)
      (by
        obtain ⟨hfirst, hsecond⟩ :=
          m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
        rw [hfirst]
        exact hfirstCrossBound)
      (by
        obtain ⟨hfirst, hsecond⟩ :=
          m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
        rw [hsecond]
        exact hsecondCrossBound)
      (by
        obtain ⟨hfirst, hsecond⟩ :=
          m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
        rw [hfirst, hsecond]
        exact hcrossPresent)
      (by
        rcases hzeroSafe with hne | hcore | hcross
        · exact Or.inl hne
        · right; left
          rw [m2PairCoreFibre_relabel_zero_one labels cost chores first second hzero hone]
          exact hcore
        · right; right
          obtain ⟨hfirst, _⟩ :=
            m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
          rw [hfirst]
          exact hcross)
      (by
        rcases honeSafe with hne | hcore | hcross
        · exact Or.inl hne
        · right; left
          rw [m2PairCoreFibre_relabel_zero_one labels cost chores first second hzero hone]
          exact hcore
        · right; right
          obtain ⟨_, hsecond⟩ :=
            m2PairCrossFibre_relabel_zero_one labels cost chores first second hzero hone
          rw [hsecond]
          exact hcross)
  let allocation := relabelAllocation labels.symm labelledAllocation
  have halloc : IsAllocationOf allocation chores := hlabelledAllocation.relabel labels.symm
  have hefx : EFXForChores (additiveChoreCost cost) allocation := by
    have htransport := hlabelledEfx.relabel labels.symm
    have hcostEq : relabelChoreCost labels.symm (relabelChoreCost labels cost) = cost := by
      funext agent item
      simp [relabelChoreCost]
    rw [hcostEq] at htransport
    exact htransport
  refine ⟨allocation, halloc, hefx, ?_, ?_⟩
  · intro i hsmall j
    rcases hsmall with ⟨item, hitem, hitemSmall⟩
    have hlabelledSmall : ∃ item ∈ labelledAllocation (labels.symm i),
        IsSmallChore (relabelChoreCost labels cost) (labels.symm i) item := by
      refine ⟨item, ?_, ?_⟩
      · simpa [allocation, relabelAllocation] using hitem
      · simpa [relabelChoreCost, IsSmallChore] using hitemSmall
    have hcomparison := hsmallCertificate (labels.symm i) hlabelledSmall (labels.symm j)
    simpa [allocation, relabelAllocation, relabelChoreCost, additiveChoreCost] using hcomparison
  · intro i hallLarge j
    have hlabelledLarge : ∀ item ∈ labelledAllocation (labels.symm i),
        IsLargeChore (relabelChoreCost labels cost) r (labels.symm i) item := by
      intro item hitem
      have hitemOriginal : item ∈ allocation i := by
        simpa [allocation, relabelAllocation] using hitem
      have hlarge := hallLarge item hitemOriginal
      simpa [relabelChoreCost, IsLargeChore] using hlarge
    have hcomparison := hlargeCertificate (labels.symm i) hlabelledLarge (labels.symm j)
    simpa [allocation, relabelAllocation, relabelChoreCost, additiveChoreCost] using hcomparison

/-- The complete Case 3.1 certificate dispatch.  In residue three, the only
one-sided cross-fiber configurations use the corrected allocation; every
other split is covered by the all-large endpoint argument. -/
theorem existsEfxOfM2PairCase31_certified
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4) (q remainder : ℕ)
    (hdistinct : first ≠ second) (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (htwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hdecompose : chores.card = 4 * q + remainder) (hremainder : remainder < 4)
    (hpairPositive : chores.card < 2 * (m2PairOutsideFibre cost chores first second).card)
    (hfirstCrossBound : 4 * (m2PairCrossFibre cost chores first second).card ≤ chores.card)
    (hsecondCrossBound : 4 * (m2PairCrossFibre cost chores second first).card ≤ chores.card)
    (hcrossPresent : 0 < (m2PairCrossFibre cost chores first second).card +
      (m2PairCrossFibre cost chores second first).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) := by
  let a := (m2PairCoreFibre cost chores first second).card
  let b := (m2PairCrossFibre cost chores first second).card
  let c := (m2PairCrossFibre cost chores second first).card
  by_cases hthree : remainder = 3
  · by_cases hcore : a = 0
    · by_cases hfirstCross : b = 0
      · exact existsEfxOfM2PairCase31CrossResidueThree_certified Item r cost chores first second q
          hdistinct hr hcost htwo (by simpa [a] using hcore) (by simpa [b] using hfirstCross)
          (by simpa [hthree] using hdecompose) hsecondCrossBound hcrossPresent
      · by_cases hsecondCross : c = 0
        · have hcoreSwap : (m2PairCoreFibre cost chores second first).card = 0 := by
            rw [m2PairCoreFibre_swap]
            simpa [a] using hcore
          have hcrossSwap : 0 < (m2PairCrossFibre cost chores second first).card +
              (m2PairCrossFibre cost chores first second).card := by
            simpa [add_comm] using hcrossPresent
          exact existsEfxOfM2PairCase31CrossResidueThree_certified Item r cost chores second first q
            hdistinct.symm hr hcost htwo hcoreSwap (by simpa [c] using hsecondCross)
            (by simpa [hthree] using hdecompose) hfirstCrossBound hcrossSwap
        · exact existsEfxOfM2PairCase31_certified_of_safe_endpoint_fibres Item r cost chores
            first second q remainder hdistinct hr hcost htwo hdecompose hremainder hpairPositive
            hfirstCrossBound hsecondCrossBound hcrossPresent
            (Or.inr (Or.inr (by simpa [b] using Nat.pos_of_ne_zero hfirstCross)))
            (Or.inr (Or.inr (by simpa [c] using Nat.pos_of_ne_zero hsecondCross)))
    · have hcorePos : 0 < (m2PairCoreFibre cost chores first second).card := by
        simpa [a] using Nat.pos_of_ne_zero hcore
      exact existsEfxOfM2PairCase31_certified_of_safe_endpoint_fibres Item r cost chores
        first second q remainder hdistinct hr hcost htwo hdecompose hremainder hpairPositive
        hfirstCrossBound hsecondCrossBound hcrossPresent (Or.inr (Or.inl hcorePos))
        (Or.inr (Or.inl hcorePos))
  · exact existsEfxOfM2PairCase31_certified_of_safe_endpoint_fibres Item r cost chores
      first second q remainder hdistinct hr hcost htwo hdecompose hremainder hpairPositive
      hfirstCrossBound hsecondCrossBound hcrossPresent (Or.inl hthree) (Or.inl hthree)

/-- Case 2 of the source M2 proof.  A positively and maximally deficient
singleton receives all of its incident chores and the fallback triangle
chores; the other three agents obtain a Hall-oriented small triangle bundle. -/
theorem existsEfxOfM2SingletonMaxDeficiency_certified
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q remainder : ℕ) (special : Fin 4)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hsmall : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hdecompose : chores.card = 4 * q + remainder) (hremainder : remainder < 4)
    (hmaximum : ∀ agents, m2ScaledDeficiency cost chores agents ≤
      m2ScaledDeficiency cost chores {special})
    (hpositive : 0 < m2ScaledDeficiency cost chores {special}) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) := by
  classical
  obtain ⟨longAgents, hlongSubset, hlongCard⟩ :=
    exists_m2SingletonLongAgents special remainder hremainder
  let triangle := m2SingletonTriangle cost chores special
  let quota := m2SingletonQuota special q longAgents
  have hdeficient : 4 * m2Incidence cost chores {special} < chores.card := by
    have hdeficient' := (m2ScaledDeficiency_pos_iff cost chores {special}).mp hpositive
    simpa using hdeficient'
  have hincidentLe : m2Incidence cost chores {special} ≤ q :=
    m2SingletonDeficient_incidence_le_quotient cost chores {special} q remainder
      hdecompose hremainder (by simp) (by simpa using hdeficient)
  have htriangleLarge : chores.card - q ≤ triangle.card := by
    rw [show triangle = m2SingletonTriangle cost chores special by rfl,
      m2SingletonTriangle_card]
    omega
  have hsumOther : ∑ agent ∈ Finset.univ.erase special, quota agent = chores.card - q := by
    change ∑ agent ∈ Finset.univ.erase special,
      m2SingletonQuota special q longAgents agent = chores.card - q
    rw [m2SingletonQuota_sum_other special q longAgents hlongSubset, hlongCard, hdecompose]
    omega
  have hquotaRange : ∀ agent, agent ≠ special → q ≤ quota agent ∧ quota agent ≤ q + 1 := by
    simpa only [quota] using m2SingletonQuota_range special q longAgents
  have hdegree : ∀ agent, agent ≠ special → quota agent ≤
      (triangle.filter fun item => agent ∈ smallAgentSet cost item).card := by
    intro agent hagent
    have hdegreeLower := m2SingletonMax_triangleDegree_lower cost chores special agent
      hmaximum hagent
    change m2SingletonQuota special q longAgents agent ≤
      ((m2SingletonTriangle cost chores special).filter fun item =>
        agent ∈ smallAgentSet cost item).card
    by_cases hlong : agent ∈ longAgents
    · have hremPositive : 0 < remainder := by
        by_contra hzero
        have hlongEmpty : longAgents = ∅ := by
          apply Finset.card_eq_zero.mp
          omega
        simp [hlongEmpty] at hlong
      simp [m2SingletonQuota, hagent, hlong]
      omega
    · have htarget : q ≤ ((m2SingletonTriangle cost chores special).filter fun item =>
        agent ∈ smallAgentSet cost item).card := by
        omega
      simpa [m2SingletonQuota, hagent, hlong] using htarget
  have hhall : ∀ vertices : Finset (Fin 4), vertices.sum quota ≤
      (triangle.filter fun item => (smallAgentSet cost item ∩ vertices).Nonempty).card :=
    singletonTriangleHall triangle (smallAgentSet cost) special quota
      (by simp [quota, m2SingletonQuota])
      (by
        intro item hitem
        exact hsmall item (Finset.mem_filter.mp hitem).1)
      (by
        intro item hitem
        exact (Finset.mem_filter.mp hitem).2)
      hdegree
      (by rw [hsumOther]; exact htriangleLarge)
  apply existsEfxOfM2SingletonPartialOrientation_certified Item r cost chores triangle special q
    (smallAgentSet cost) quota hr hcost
  · exact (by intro item hitem; exact (Finset.mem_filter.mp hitem).1)
  · exact hhall
  · exact hsumOther
  · omega
  · exact hquotaRange
  · intro agent item _ _ hendpoint
    simpa [smallAgentSet, IsSmallChore] using hendpoint
  · intro _ item _ hitem _
    have hnotSpecial : special ∉ smallAgentSet cost item := (Finset.mem_filter.mp hitem).2
    have hnotSmall : ¬ IsSmallChore cost special item := by
      intro hsmallSpecial
      apply hnotSpecial
      simpa [smallAgentSet, IsSmallChore] using hsmallSpecial
    rcases hcost special item with hsmallSpecial | hlargeSpecial
    · exact (hnotSmall (by simpa [IsSmallChore] using hsmallSpecial)).elim
    · exact hlargeSpecial

/-- The maximal-singleton M2 branch at its basic EFX-existence interface.
The richer certificate conclusion is available from
`existsEfxOfM2SingletonMaxDeficiency_certified`. -/
theorem existsEfxOfM2SingletonMaxDeficiency
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q remainder : ℕ) (special : Fin 4)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hsmall : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hdecompose : chores.card = 4 * q + remainder) (hremainder : remainder < 4)
    (hmaximum : ∀ agents, m2ScaledDeficiency cost chores agents ≤
      m2ScaledDeficiency cost chores {special})
    (hpositive : 0 < m2ScaledDeficiency cost chores {special}) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨allocation, halloc, hefx, _, _⟩ :=
    existsEfxOfM2SingletonMaxDeficiency_certified Item r cost chores q remainder special hr hcost
      hsmall hdecompose hremainder hmaximum hpositive
  exact ⟨allocation, halloc, hefx⟩

theorem existsEfxOfM2HallQuotasWithSmall
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (quota : Fin 4 → ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hsmallTwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hsum : Finset.univ.sum quota = chores.card)
    (hhall : ∀ agents : Finset (Fin 4), agents.sum quota ≤
      (chores.filter fun item => (smallAgentSet cost item ∩ agents).Nonempty).card)
    (hbalanced : ∀ i j, quota i ≤ quota j + 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
        ∀ agent item, item ∈ allocation agent → IsSmallChore cost agent item := by
  have hends : ∀ item ∈ chores, (smallAgentSet cost item).card = 2 := hsmallTwo
  obtain ⟨owner, howner, hcard⟩ :=
    (balancedOrientationIff (Fin 4) Item chores (smallAgentSet cost) quota hends hsum).mpr hhall
  have htotal : ∀ item ∈ chores, ∃ agent, owner item = some agent := by
    intro item hitem
    obtain ⟨agent, hownerEq, _⟩ := howner item hitem
    exact ⟨agent, hownerEq⟩
  have hsmall : ∀ agent item, item ∈ chores → owner item = some agent →
      IsSmallChore cost agent item := by
    intro agent item hitem hownerEq
    obtain ⟨other, hotherEq, hotherSmall⟩ := howner item hitem
    have hotherAgent : other = agent :=
      Option.some.inj (hotherEq.symm.trans hownerEq)
    have hsmallOther : IsSmallChore cost other item := by
      simpa [smallAgentSet] using hotherSmall
    simpa [hotherAgent] using hsmallOther
  have hcardBalanced : ∀ i j,
      (allocationOfOwner chores owner i).card ≤ (allocationOfOwner chores owner j).card + 1 := by
    intro i j
    have hcardI : (allocationOfOwner chores owner i).card = quota i := by
      rw [← hcard i]
      apply congrArg Finset.card
      ext item
      simp [allocationOfOwner]
    have hcardJ : (allocationOfOwner chores owner j).card = quota j := by
      rw [← hcard j]
      apply congrArg Finset.card
      ext item
      simp [allocationOfOwner]
    simpa [hcardI, hcardJ] using hbalanced i j
  refine ⟨allocationOfOwner chores owner,
    isAllocationOf_allocationOfOwner chores owner htotal,
    efxForChores_allocationOfOwner_of_small_balanced cost r chores owner hcost
      (by linarith) hsmall hcardBalanced, ?_⟩
  intro agent item hitem
  have hfilter : item ∈ chores ∧ owner item = some agent := by
    simpa [allocationOfOwner] using hitem
  exact hsmall agent item hfilter.1 hfilter.2

/-- The all-small Hall-orientation branch, with the small-owner invariant
discarded when only EFX existence is required. -/
theorem existsEfxOfM2HallQuotas
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (quota : Fin 4 → ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hsmallTwo : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hsum : Finset.univ.sum quota = chores.card)
    (hhall : ∀ agents : Finset (Fin 4), agents.sum quota ≤
      (chores.filter fun item => (smallAgentSet cost item ∩ agents).Nonempty).card)
    (hbalanced : ∀ i j, quota i ≤ quota j + 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨allocation, halloc, hefx, _⟩ :=
    existsEfxOfM2HallQuotasWithSmall Item r cost chores quota hr hcost hsmallTwo hsum hhall
      hbalanced
  exact ⟨allocation, halloc, hefx⟩

private theorem existsEfxOfM2NoDeficiency_withLongAgentsWithSmall
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q remainder : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hsmall : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hdecompose : chores.card = 4 * q + remainder) (hremainder : remainder < 4)
    (hdeficiency : ∀ agents : Finset (Fin 4),
      agents.card * chores.card ≤ 4 * m2Incidence cost chores agents)
    (longAgents : Finset (Fin 4)) (hlongCard : longAgents.card = remainder)
    (hnotTight : remainder = 2 → longAgents ∉ m2TightPairs cost chores q) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
        ∀ agent item, item ∈ allocation agent → IsSmallChore cost agent item := by
  apply existsEfxOfM2HallQuotasWithSmall Item r cost chores (m2Quota q longAgents) hr hcost hsmall
  · rw [m2Quota_sum, hlongCard, ← hdecompose]
  · intro agents
    rw [m2Quota_sum_on]
    have hvertexBound : agents.card ≤ 4 := by
      simpa using Finset.card_le_univ agents
    have hlongVertex : (agents ∩ longAgents).card ≤ agents.card :=
      Finset.card_le_card Finset.inter_subset_left
    by_cases htwo : remainder = 2
    · apply m2HallArithmeticRemainderTwoOfNonTight chores.card q
        (m2Incidence cost chores agents) agents.card (agents ∩ longAgents).card
      · omega
      · exact hvertexBound
      · exact hdeficiency agents
      · exact hlongVertex
      · calc
          (agents ∩ longAgents).card ≤ longAgents.card :=
            Finset.card_le_card Finset.inter_subset_right
          _ = remainder := hlongCard
          _ = 2 := htwo
      · intro hagentCard hinterCard
        have hlongTwo : longAgents.card = 2 := by omega
        have hagentsLong : agents = longAgents :=
          m2Pair_eq_of_inter_card_two agents longAgents hagentCard hlongTwo hinterCard
        subst agents
        have hincidenceLower := hdeficiency longAgents
        have hchoresTwo : chores.card = 4 * q + 2 := by omega
        rw [hlongTwo, hchoresTwo] at hincidenceLower
        have hincidenceNe : m2Incidence cost chores longAgents ≠ 2 * q + 1 := by
          intro hincidenceEq
          apply hnotTight htwo
          simp only [m2TightPairs, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hlongTwo, hincidenceEq⟩
        omega
    · apply m2HallArithmeticOfNoDeficiency chores.card q remainder
        (m2Incidence cost chores agents) agents.card (agents ∩ longAgents).card
      · exact hdecompose
      · exact hremainder
      · exact htwo
      · exact hvertexBound
      · exact hdeficiency agents
      · exact hlongVertex
      · rw [← hlongCard]
        exact Finset.card_le_card Finset.inter_subset_right
  · exact m2Quota_balanced q longAgents

/-- Case 1 of the source M2 proof: if the two-small-agent incidence graph has
no deficient vertex set, then balanced endpoint orientation yields EFX.  The
remainder-two branch uses the source's tight-pair avoidance construction. -/
theorem existsEfxOfM2NoDeficiencyWithSmall
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q remainder : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hsmall : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hdecompose : chores.card = 4 * q + remainder) (hremainder : remainder < 4)
    (hdeficiency : ∀ agents : Finset (Fin 4),
      agents.card * chores.card ≤ 4 * m2Incidence cost chores agents) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
        ∀ agent item, item ∈ allocation agent → IsSmallChore cost agent item := by
  classical
  interval_cases remainder
  · exact existsEfxOfM2NoDeficiency_withLongAgentsWithSmall Item r cost chores q 0 hr hcost hsmall
      hdecompose hremainder hdeficiency ∅ (by decide) (by omega)
  · exact existsEfxOfM2NoDeficiency_withLongAgentsWithSmall Item r cost chores q 1 hr hcost hsmall
      hdecompose hremainder hdeficiency {0} (by decide) (by omega)
  · obtain ⟨longAgents, hlongCard, hnotTight⟩ :=
      existsPairAvoidingAtMostTwo (m2TightPairs cost chores q)
        (m2TightPairs_card_le_two cost chores q hsmall (by omega))
    exact existsEfxOfM2NoDeficiency_withLongAgentsWithSmall Item r cost chores q 2 hr hcost hsmall
      hdecompose hremainder hdeficiency longAgents hlongCard (by intro _; exact hnotTight)
  · exact existsEfxOfM2NoDeficiency_withLongAgentsWithSmall Item r cost chores q 3 hr hcost hsmall
      hdecompose hremainder hdeficiency {0, 1, 2} (by decide) (by omega)

/-- Case 1 of the source M2 proof, stated at its basic EFX-existence
interface. The stronger all-small-owner invariant is available from
`existsEfxOfM2NoDeficiencyWithSmall`. -/
theorem existsEfxOfM2NoDeficiency
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q remainder : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hsmall : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hdecompose : chores.card = 4 * q + remainder) (hremainder : remainder < 4)
    (hdeficiency : ∀ agents : Finset (Fin 4),
      agents.card * chores.card ≤ 4 * m2Incidence cost chores agents) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨allocation, halloc, hefx, _⟩ :=
    existsEfxOfM2NoDeficiencyWithSmall Item r cost chores q remainder hr hcost hsmall
      hdecompose hremainder hdeficiency
  exact ⟨allocation, halloc, hefx⟩

/-- In the no-deficiency M2 branch, endpoint orientation supplies all of the
nonexceptional certificates required by Lemma `M2properties`(i). -/
theorem existsEfxOfM2NoDeficiency_certified
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (q remainder : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hsmall : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hdecompose : chores.card = 4 * q + remainder) (hremainder : remainder < 4)
    (hdeficiency : ∀ agents : Finset (Fin 4),
      agents.card * chores.card ≤ 4 * m2Incidence cost chores agents) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) := by
  obtain ⟨allocation, halloc, hefx, hownerSmall⟩ :=
    existsEfxOfM2NoDeficiencyWithSmall Item r cost chores q remainder hr hcost hsmall
      hdecompose hremainder hdeficiency
  exact ⟨allocation, halloc, hefx,
    allSmallOwner_efx_certificates Item r cost allocation hr hcost hefx hownerSmall⟩

/-- Source-faithful assembly of the three cases in the proof of the M2 lemma.
The finite maximum-deficiency set is selected first; a nonpositive maximum
uses balanced orientation, while a positive maximum is a singleton or pair.
For a pair, the incidence bridge turns its positive deficiency into the
outside-fiber inequality that dispatches Cases 3.1 and 3.2. -/
theorem existsEfxOfM2
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hsmall : ∀ item ∈ chores, IsSmallForExactlyTwo cost item) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  classical
  let q := chores.card / 4
  let remainder := chores.card % 4
  have hdecompose : chores.card = 4 * q + remainder := by
    have hmod := Nat.mod_add_div chores.card 4
    dsimp [q, remainder]
    omega
  have hremainder : remainder < 4 := by
    dsimp [remainder]
    exact Nat.mod_lt _ (by omega)
  obtain ⟨maximum, hmaximum, _⟩ :=
    exists_m2ScaledDeficiency_maximizer_min_card cost chores
  by_cases hpositive : 0 < m2ScaledDeficiency cost chores maximum
  · rcases m2PositiveMaximizer_card_one_or_two cost chores maximum hpositive hsmall with
      hsingleton | hpair
    · obtain ⟨special, hmaximumEq⟩ := Finset.card_eq_one.mp hsingleton
      subst maximum
      exact existsEfxOfM2SingletonMaxDeficiency Item r cost chores q remainder special hr hcost
        hsmall hdecompose hremainder hmaximum hpositive
    · obtain ⟨first, second, hdistinct, hmaximumEq⟩ := Finset.card_eq_two.mp hpair
      subst maximum
      let a := (m2PairCoreFibre cost chores first second).card
      let b := (m2PairCrossFibre cost chores first second).card
      let c := (m2PairCrossFibre cost chores second first).card
      let f := (m2PairOutsideFibre cost chores first second).card
      have hpairPositive : 4 * m2Incidence cost chores {first, second} < 2 * chores.card := by
        have hpositive' := (m2ScaledDeficiency_pos_iff cost chores {first, second}).mp hpositive
        rw [hpair] at hpositive'
        exact hpositive'
      have houtsideGt : a + b + c < f := by
        simpa [a, b, c, f] using
          m2PairPositive_outside_gt_nonOutside cost chores first second hpairPositive
      have hfirstCrossBound :
          4 * (m2PairCrossFibre cost chores first second).card ≤ chores.card :=
        m2PairMax_crossFibre_upper cost chores {first, second} first second hmaximum rfl hdistinct
      have hpairReverse : ({first, second} : Finset (Fin 4)) = insert second {first} := by
        ext agent
        simp [or_comm]
      have hsecondCrossBound :
          4 * (m2PairCrossFibre cost chores second first).card ≤ chores.card :=
        m2PairMax_crossFibre_upper cost chores {first, second} second first hmaximum
          hpairReverse hdistinct.symm
      by_cases hcross : 0 < b + c
      · have hpairOutside : chores.card < 2 * (m2PairOutsideFibre cost chores first second).card := by
          rw [← m2PairFibres_card_sum cost chores first second]
          dsimp [a, b, c, f] at houtsideGt hcross ⊢
          omega
        exact existsEfxOfM2PairCase31 Item r cost chores first second q remainder hdistinct
          (by linarith) hcost hsmall hdecompose hremainder hpairOutside hfirstCrossBound
          hsecondCrossBound (by simpa [b, c] using hcross)
      · have hcrossZero : b + c = 0 := by omega
        have hfirstCrossZero : (m2PairCrossFibre cost chores first second).card = 0 := by
          dsimp [b] at hcrossZero
          omega
        have hsecondCrossZero : (m2PairCrossFibre cost chores second first).card = 0 := by
          dsimp [c] at hcrossZero
          omega
        by_cases hcoreZero : a = 0
        · have hcoreCard : (m2PairCoreFibre cost chores first second).card = 0 := by
            simpa [a] using hcoreZero
          have houtsideAll : m2PairOutsideFibre cost chores first second = chores := by
            apply Finset.eq_of_subset_of_card_le
            · intro item hitem
              exact (Finset.mem_filter.mp hitem).1
            rw [← m2PairFibres_card_sum cost chores first second]
            omega
          apply existsEfxOfM2SingleSmallType Item r cost chores q remainder
            ({first, second} : Finset (Fin 4))ᶜ hr hcost ?_ hdecompose hremainder
          intro item hitem
          apply (not_m2Incident_iff_smallSet_eq_compl cost item {first, second}
            (hsmall item hitem) (by simp [hdistinct])).mp
          rintro ⟨agent, hagent⟩
          rcases Finset.mem_inter.mp hagent with ⟨hagentSmall, hagentPair⟩
          have houtsideMem : item ∈ m2PairOutsideFibre cost chores first second := by
            rw [houtsideAll]
            exact hitem
          rcases Finset.mem_filter.mp houtsideMem with ⟨_, hnotFirst, hnotSecond⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hagentPair
          rcases hagentPair with rfl | rfl
          · exact hnotFirst hagentSmall
          · exact hnotSecond hagentSmall
        · by_cases hcoreOne : a = 1
          · exact existsEfxOfM2PairCase322 Item r cost chores first second (f / 4) (f % 4)
              hdistinct (by linarith) hcost hsmall
              (by simpa [a] using hcoreOne)
              hfirstCrossZero hsecondCrossZero
              (by
                change f = 4 * (f / 4) + f % 4
                have hmod := Nat.mod_add_div f 4
                omega)
              (by exact Nat.mod_lt _ (by omega))
          · have hcoreLarge : 2 ≤ a := by omega
            exact existsEfxOfM2PairCase323 Item r cost chores first second a f hdistinct hr hcost
              hsmall (by rfl) hfirstCrossZero hsecondCrossZero (by rfl) hcoreLarge
              (by
                dsimp [b, c] at houtsideGt hcrossZero
                omega)
  · apply existsEfxOfM2NoDeficiency Item r cost chores q remainder hr hcost hsmall
      hdecompose hremainder
    intro agents
    have hupper := hmaximum agents
    have hmaximumNonpositive : m2ScaledDeficiency cost chores maximum ≤ 0 := by omega
    unfold m2ScaledDeficiency at hupper hmaximumNonpositive
    omega

/-- Under the negation of the two exceptional residue configurations, the
source M2 case dispatch produces an allocation with both certificates from
Lemma `M2properties`(i). -/
theorem existsEfxOfM2_certified_of_notExceptional
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hsmall : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (hnotExceptional : ¬ IsM2Exceptional cost chores) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
        additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
      (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
        additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j)) := by
  classical
  let q := chores.card / 4
  let remainder := chores.card % 4
  have hdecompose : chores.card = 4 * q + remainder := by
    have hmod := Nat.mod_add_div chores.card 4
    dsimp [q, remainder]
    omega
  have hremainder : remainder < 4 := by
    dsimp [remainder]
    exact Nat.mod_lt _ (by omega)
  obtain ⟨maximum, hmaximum, _⟩ :=
    exists_m2ScaledDeficiency_maximizer_min_card cost chores
  by_cases hpositive : 0 < m2ScaledDeficiency cost chores maximum
  · rcases m2PositiveMaximizer_card_one_or_two cost chores maximum hpositive hsmall with
      hsingleton | hpair
    · obtain ⟨special, hmaximumEq⟩ := Finset.card_eq_one.mp hsingleton
      subst maximum
      exact existsEfxOfM2SingletonMaxDeficiency_certified Item r cost chores q remainder special hr
        hcost hsmall hdecompose hremainder hmaximum hpositive
    · obtain ⟨first, second, hdistinct, hmaximumEq⟩ := Finset.card_eq_two.mp hpair
      subst maximum
      let a := (m2PairCoreFibre cost chores first second).card
      let b := (m2PairCrossFibre cost chores first second).card
      let c := (m2PairCrossFibre cost chores second first).card
      let f := (m2PairOutsideFibre cost chores first second).card
      have hpairPositive : 4 * m2Incidence cost chores {first, second} < 2 * chores.card := by
        have hpositive' := (m2ScaledDeficiency_pos_iff cost chores {first, second}).mp hpositive
        rw [hpair] at hpositive'
        exact hpositive'
      have houtsideGt : a + b + c < f := by
        simpa [a, b, c, f] using
          m2PairPositive_outside_gt_nonOutside cost chores first second hpairPositive
      have hfirstCrossBound :
          4 * (m2PairCrossFibre cost chores first second).card ≤ chores.card :=
        m2PairMax_crossFibre_upper cost chores {first, second} first second hmaximum rfl hdistinct
      have hpairReverse : ({first, second} : Finset (Fin 4)) = insert second {first} := by
        ext agent
        simp [or_comm]
      have hsecondCrossBound :
          4 * (m2PairCrossFibre cost chores second first).card ≤ chores.card :=
        m2PairMax_crossFibre_upper cost chores {first, second} second first hmaximum
          hpairReverse hdistinct.symm
      by_cases hcross : 0 < b + c
      · have hpairOutside : chores.card < 2 * (m2PairOutsideFibre cost chores first second).card := by
          rw [← m2PairFibres_card_sum cost chores first second]
          dsimp [a, b, c, f] at houtsideGt hcross ⊢
          omega
        exact existsEfxOfM2PairCase31_certified Item r cost chores first second q remainder hdistinct
          hr hcost hsmall hdecompose hremainder hpairOutside hfirstCrossBound hsecondCrossBound
          (by simpa [b, c] using hcross)
      · have hcrossZero : b + c = 0 := by omega
        have hfirstCrossZero : (m2PairCrossFibre cost chores first second).card = 0 := by
          dsimp [b] at hcrossZero
          omega
        have hsecondCrossZero : (m2PairCrossFibre cost chores second first).card = 0 := by
          dsimp [c] at hcrossZero
          omega
        by_cases hcoreZero : a = 0
        · have hcoreCard : (m2PairCoreFibre cost chores first second).card = 0 := by
            simpa [a] using hcoreZero
          have houtsideAll : m2PairOutsideFibre cost chores first second = chores := by
            apply Finset.eq_of_subset_of_card_le
            · intro item hitem
              exact (Finset.mem_filter.mp hitem).1
            rw [← m2PairFibres_card_sum cost chores first second]
            omega
          have hsmallType : ∀ item ∈ chores,
              smallAgentSet cost item = ({first, second} : Finset (Fin 4))ᶜ := by
            intro item hitem
            apply (not_m2Incident_iff_smallSet_eq_compl cost item {first, second}
              (hsmall item hitem) (by simp [hdistinct])).mp
            rintro ⟨agent, hagent⟩
            rcases Finset.mem_inter.mp hagent with ⟨hagentSmall, hagentPair⟩
            have houtsideMem : item ∈ m2PairOutsideFibre cost chores first second := by
              rw [houtsideAll]
              exact hitem
            rcases Finset.mem_filter.mp houtsideMem with ⟨_, hnotFirst, hnotSecond⟩
            simp only [Finset.mem_insert, Finset.mem_singleton] at hagentPair
            rcases hagentPair with rfl | rfl
            · exact hnotFirst hagentSmall
            · exact hnotSecond hagentSmall
          have hremainderNeThree : remainder ≠ 3 := by
            intro hthree
            apply hnotExceptional
            exact isM2Exceptional_of_fixedSmallType Item cost chores
              ({first, second} : Finset (Fin 4))ᶜ q hsmall hsmallType (by rw [hdecompose, hthree])
          obtain ⟨allocation, halloc, hefx, hsmallCertificate, hlargeCertificate,
            houtsideFavorite⟩ :=
            existsEfxOfM2SingleSmallType_certified_of_remainder_ne_three Item r cost chores q
              remainder ({first, second} : Finset (Fin 4))ᶜ hr hcost hsmall hsmallType hdecompose
              hremainder hremainderNeThree
          exact ⟨allocation, halloc, hefx, hsmallCertificate, hlargeCertificate⟩
        · by_cases hcoreOne : a = 1
          · have hfdecompose : f = 4 * (f / 4) + f % 4 := by
              have hmod := Nat.mod_add_div f 4
              omega
            have hfLarge : 1 < f := by
              dsimp [a, b, c] at houtsideGt hcrossZero
              omega
            have hmodNeThree : f % 4 ≠ 3 := by
              intro hthree
              apply hnotExceptional
              apply isM2Exceptional_of_oneCoreFibre Item cost chores first second (f / 4)
                hdistinct hsmall (by simpa [a] using hcoreOne) hfirstCrossZero hsecondCrossZero
              change f = 4 * (f / 4) + 3
              rw [hfdecompose, hthree]
              omega
            have hmodLtThree : f % 4 < 3 := by
              have hmodLt : f % 4 < 4 := Nat.mod_lt _ (by omega)
              omega
            exact existsEfxOfM2PairCase322_certified_of_lt_three Item r cost chores first second
              (f / 4) (f % 4) hdistinct hr hcost hsmall (by simpa [a] using hcoreOne)
              hfirstCrossZero hsecondCrossZero hfdecompose hmodLtThree (by rw [← hfdecompose]; exact hfLarge)
          · have hcoreLarge : 2 ≤ a := by omega
            exact existsEfxOfM2PairCase323_certified Item r cost chores first second a f hdistinct hr
              hcost hsmall (by rfl) hfirstCrossZero hsecondCrossZero (by rfl) hcoreLarge
              (by
                dsimp [b, c] at houtsideGt hcrossZero
                omega)
  · apply existsEfxOfM2NoDeficiency_certified Item r cost chores q remainder hr hcost hsmall
      hdecompose hremainder
    intro agents
    have hupper := hmaximum agents
    have hmaximumNonpositive : m2ScaledDeficiency cost chores maximum ≤ 0 := by omega
    unfold m2ScaledDeficiency at hupper hmaximumNonpositive
    omega

/-- The source M2 construction always has EFX, and it has both certificates
outside exactly the two exceptional residue configurations. -/
theorem existsEfxOfM2_with_conditionalCertificates
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hsmall : ∀ item ∈ chores, IsSmallForExactlyTwo cost item) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation ∧
      (¬ IsM2Exceptional cost chores →
        (∀ i, (∃ item ∈ allocation i, IsSmallChore cost i item) → ∀ j,
          additiveChoreCost cost i (allocation i) - 1 ≤ additiveChoreCost cost i (allocation j)) ∧
        (∀ i, (∀ item ∈ allocation i, IsLargeChore cost r i item) → ∀ j,
          additiveChoreCost cost i (allocation i) ≤ additiveChoreCost cost i (allocation j))) := by
  by_cases hexceptional : IsM2Exceptional cost chores
  · obtain ⟨allocation, halloc, hefx⟩ := existsEfxOfM2 Item r cost chores hr hcost hsmall
    refine ⟨allocation, halloc, hefx, ?_⟩
    intro hnot
    exact (hnot hexceptional).elim
  · obtain ⟨allocation, halloc, hefx, hsmallCertificate, hlargeCertificate⟩ :=
      existsEfxOfM2_certified_of_notExceptional Item r cost chores hr hcost hsmall hexceptional
    exact ⟨allocation, halloc, hefx, fun _ => ⟨hsmallCertificate, hlargeCertificate⟩⟩

end HT26EFXChores
