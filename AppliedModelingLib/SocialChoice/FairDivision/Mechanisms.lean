import AppliedModelingLib.SocialChoice.FairDivision.IndivisibleGoods
import AppliedModelingLib.Foundations.Probability.FiniteExpectation

namespace AppliedModelingLib
namespace FairDivision

variable {Agent Item : Type*}

/--
A direct fair-division report assigns a value to every bundle for every agent.
This is intentionally proof-free: admissibility conditions such as monotonicity,
additivity, or normalization should be separate predicates.
-/
abbrev FairDivisionReport (Agent Item : Type*) :=
  Agent → Bundle Item → ℝ

/--
A direct fair-division mechanism without transfers.  The allocation can depend
on all reported bundle values.
-/
structure DirectFairDivisionMechanism (Agent Item : Type*) where
  allocation : FairDivisionReport Agent Item → Allocation Agent Item

namespace DirectFairDivisionMechanism

/-- Utility is the true value of the bundle assigned to the agent. -/
def utility (M : DirectFairDivisionMechanism Agent Item)
    (values reports : FairDivisionReport Agent Item) (i : Agent) : ℝ :=
  values i (M.allocation reports i)

/-- Dominant-strategy truthfulness for direct fair-division mechanisms. -/
def Truthful [DecidableEq Agent]
    (M : DirectFairDivisionMechanism Agent Item) : Prop :=
  ∀ (values : FairDivisionReport Agent Item)
      (i : Agent) (report : Bundle Item → ℝ),
    M.utility values (Function.update values i report) i ≤
      M.utility values values i

/-- The allocation rule is independent of reports. -/
def ReportIndependent (M : DirectFairDivisionMechanism Agent Item) : Prop :=
  ∀ reports reports', M.allocation reports = M.allocation reports'

/--
Any report-independent no-transfer allocation rule is truthful: no report can
change the assigned bundle.
-/
theorem truthful_of_reportIndependent [DecidableEq Agent]
    (M : DirectFairDivisionMechanism Agent Item)
    (hind : M.ReportIndependent) :
    M.Truthful := by
  intro values i report
  have halloc := congrFun (hind (Function.update values i report) values) i
  simp [utility, halloc]

/-- A concrete profitable deviation from truthful reporting. -/
structure ProfitableDeviation [DecidableEq Agent]
    (M : DirectFairDivisionMechanism Agent Item) where
  values : FairDivisionReport Agent Item
  agent : Agent
  report : Bundle Item → ℝ
  improves :
    M.utility values (Function.update values agent report) agent >
      M.utility values values agent

/-- A mechanism with a profitable deviation is not truthful. -/
theorem not_truthful_of_profitableDeviation [DecidableEq Agent]
    (M : DirectFairDivisionMechanism Agent Item)
    (w : M.ProfitableDeviation) :
    ¬ M.Truthful := by
  intro htruth
  exact not_lt_of_ge (htruth w.values w.agent w.report) w.improves

end DirectFairDivisionMechanism

/--
A randomized direct fair-division mechanism without transfers.  The allocation
law can depend on all reported bundle values.
-/
structure RandomizedDirectFairDivisionMechanism (Agent Item : Type*) where
  allocationLaw :
    FairDivisionReport Agent Item → PMF (Allocation Agent Item)

namespace RandomizedDirectFairDivisionMechanism

/-- Expected utility is expected true value of the assigned random bundle. -/
noncomputable def expectedUtility
    [Fintype (Allocation Agent Item)] [DecidableEq (Allocation Agent Item)]
    (M : RandomizedDirectFairDivisionMechanism Agent Item)
    (values reports : FairDivisionReport Agent Item) (i : Agent) : ℝ :=
  AppliedModelingLib.pmfExp (M.allocationLaw reports)
    (fun A => values i (A i))

/-- Dominant-strategy truthfulness in expected utility. -/
def Truthful
    [Fintype (Allocation Agent Item)] [DecidableEq (Allocation Agent Item)]
    [DecidableEq Agent]
    (M : RandomizedDirectFairDivisionMechanism Agent Item) : Prop :=
  ∀ (values : FairDivisionReport Agent Item)
      (i : Agent) (report : Bundle Item → ℝ),
    M.expectedUtility values (Function.update values i report) i ≤
      M.expectedUtility values values i

/-- The allocation law is independent of reports. -/
def ReportIndependent
    (M : RandomizedDirectFairDivisionMechanism Agent Item) : Prop :=
  ∀ reports reports', M.allocationLaw reports = M.allocationLaw reports'

/--
Any report-independent no-transfer randomized allocation rule is truthful in
expected utility.
-/
theorem truthful_of_reportIndependent
    [Fintype (Allocation Agent Item)] [DecidableEq (Allocation Agent Item)]
    [DecidableEq Agent]
    (M : RandomizedDirectFairDivisionMechanism Agent Item)
    (hind : M.ReportIndependent) :
    M.Truthful := by
  intro values i report
  have halloc := hind (Function.update values i report) values
  simp [expectedUtility, halloc]

end RandomizedDirectFairDivisionMechanism

/-- Envy computed from raw reported bundle values. -/
def reportEnvy (values : FairDivisionReport Agent Item)
    (A : Allocation Agent Item) (i j : Agent) : ℝ :=
  max 0 (values i (A j) - values i (A i))

/-- Reported envy-freeness for a raw bundle-value profile. -/
def ReportEnvyFree (values : FairDivisionReport Agent Item)
    (A : Allocation Agent Item) : Prop :=
  ∀ i j, values i (A j) ≤ values i (A i)

theorem reportEnvy_nonneg (values : FairDivisionReport Agent Item)
    (A : Allocation Agent Item) (i j : Agent) :
    0 ≤ reportEnvy values A i j := by
  exact le_max_left 0 (values i (A j) - values i (A i))

theorem reportEnvy_eq_zero_iff (values : FairDivisionReport Agent Item)
    (A : Allocation Agent Item) (i j : Agent) :
    reportEnvy values A i j = 0 ↔ values i (A j) ≤ values i (A i) := by
  constructor
  · intro h
    have hgap : values i (A j) - values i (A i) ≤ 0 := by
      have hright :
          values i (A j) - values i (A i) ≤ reportEnvy values A i j := by
        exact le_max_right 0 (values i (A j) - values i (A i))
      simpa [h] using hright
    linarith
  · intro h
    have hgap : values i (A j) - values i (A i) ≤ 0 := by
      linarith
    exact max_eq_left hgap

/-- Maximum reported pairwise envy over finite agents. -/
noncomputable def maxReportEnvy [Fintype Agent] [Nonempty Agent]
    (values : FairDivisionReport Agent Item) (A : Allocation Agent Item) : ℝ :=
  ((Finset.univ : Finset Agent).product (Finset.univ : Finset Agent)).sup'
    (by
      obtain ⟨i⟩ := (inferInstance : Nonempty Agent)
      exact ⟨(i, i), by simp⟩)
    (fun p => reportEnvy values A p.1 p.2)

theorem maxReportEnvy_le_iff [Fintype Agent] [Nonempty Agent]
    (values : FairDivisionReport Agent Item) (A : Allocation Agent Item) (x : ℝ) :
    maxReportEnvy values A ≤ x ↔
      ∀ i j, reportEnvy values A i j ≤ x := by
  classical
  simp [maxReportEnvy, Finset.sup'_le_iff]

theorem reportEnvy_le_maxReportEnvy [Fintype Agent] [Nonempty Agent]
    (values : FairDivisionReport Agent Item)
    (A : Allocation Agent Item) (i j : Agent) :
    reportEnvy values A i j ≤ maxReportEnvy values A := by
  classical
  unfold maxReportEnvy
  exact Finset.le_sup'
    (s := (Finset.univ : Finset Agent).product (Finset.univ : Finset Agent))
    (f := fun p : Agent × Agent => reportEnvy values A p.1 p.2)
    (b := (i, j))
    (by simp)

theorem maxReportEnvy_nonneg [Fintype Agent] [Nonempty Agent]
    (values : FairDivisionReport Agent Item) (A : Allocation Agent Item) :
    0 ≤ maxReportEnvy values A := by
  obtain ⟨i⟩ := (inferInstance : Nonempty Agent)
  exact le_trans (reportEnvy_nonneg values A i i)
    (reportEnvy_le_maxReportEnvy values A i i)

theorem maxReportEnvy_eq_zero_of_reportEnvyFree [Fintype Agent] [Nonempty Agent]
    (values : FairDivisionReport Agent Item) (A : Allocation Agent Item)
    (hfree : ReportEnvyFree values A) :
    maxReportEnvy values A = 0 := by
  apply le_antisymm
  · rw [maxReportEnvy_le_iff]
    intro i j
    have hzero : reportEnvy values A i j = 0 :=
      (reportEnvy_eq_zero_iff values A i j).mpr (hfree i j)
    simp [hzero]
  · exact maxReportEnvy_nonneg values A

theorem reportEnvyFree_of_maxReportEnvy_le_zero
    [Fintype Agent] [Nonempty Agent]
    (values : FairDivisionReport Agent Item) (A : Allocation Agent Item)
    (hle : maxReportEnvy values A ≤ 0) :
    ReportEnvyFree values A := by
  intro i j
  have henvy_nonneg : 0 ≤ reportEnvy values A i j :=
    reportEnvy_nonneg values A i j
  have henvy_le_zero : reportEnvy values A i j ≤ 0 :=
    le_trans (reportEnvy_le_maxReportEnvy values A i j) hle
  have hzero : reportEnvy values A i j = 0 :=
    le_antisymm henvy_le_zero henvy_nonneg
  exact (reportEnvy_eq_zero_iff values A i j).mp hzero

/-- A target-goods allocation whose maximum reported envy is minimal. -/
def MinimumReportEnvyAllocation [Fintype Agent] [Nonempty Agent] [DecidableEq Item]
    (values : FairDivisionReport Agent Item) (goods : Finset Item)
    (A : Allocation Agent Item) : Prop :=
  IsAllocationOf A goods ∧
    ∀ B : Allocation Agent Item,
      IsAllocationOf B goods →
        maxReportEnvy values A ≤ maxReportEnvy values B

theorem reportEnvyFree_of_minimumReportEnvyAllocation_of_exists
    [Fintype Agent] [Nonempty Agent] [DecidableEq Item]
    {values : FairDivisionReport Agent Item} {goods : Finset Item}
    {A : Allocation Agent Item}
    (hmin : MinimumReportEnvyAllocation values goods A)
    (hexists : ∃ B : Allocation Agent Item,
      IsAllocationOf B goods ∧ ReportEnvyFree values B) :
    ReportEnvyFree values A := by
  obtain ⟨B, hBalloc, hBfree⟩ := hexists
  have hBmax : maxReportEnvy values B = 0 :=
    maxReportEnvy_eq_zero_of_reportEnvyFree values B hBfree
  have hle : maxReportEnvy values A ≤ 0 := by
    simpa [hBmax] using hmin.2 B hBalloc
  exact reportEnvyFree_of_maxReportEnvy_le_zero values A hle

/--
A mechanism returns an envy-free allocation whenever one exists for the reported
profile and target goods.
-/
def ReturnsEnvyFreeWheneverExists [DecidableEq Item]
    (M : DirectFairDivisionMechanism Agent Item) (goods : Finset Item) : Prop :=
  ∀ values : FairDivisionReport Agent Item,
    (∃ A : Allocation Agent Item, IsAllocationOf A goods ∧ ReportEnvyFree values A) →
      ReportEnvyFree values (M.allocation values)

/-- The mechanism always returns an allocation of the target goods. -/
def ReturnsAllocationOf [DecidableEq Item]
    (M : DirectFairDivisionMechanism Agent Item) (goods : Finset Item) : Prop :=
  ∀ values : FairDivisionReport Agent Item,
    IsAllocationOf (M.allocation values) goods

/-- The mechanism always returns a minimum-envy allocation of the target goods. -/
def ReturnsMinimumReportEnvy [Fintype Agent] [Nonempty Agent] [DecidableEq Item]
    (M : DirectFairDivisionMechanism Agent Item) (goods : Finset Item) : Prop :=
  ∀ values : FairDivisionReport Agent Item,
    MinimumReportEnvyAllocation values goods (M.allocation values)

theorem returnsAllocationOf_of_returnsMinimumReportEnvy
    [Fintype Agent] [Nonempty Agent] [DecidableEq Item]
    (M : DirectFairDivisionMechanism Agent Item) {goods : Finset Item}
    (hmin : ReturnsMinimumReportEnvy M goods) :
    ReturnsAllocationOf M goods := by
  intro values
  exact (hmin values).1

theorem returnsEnvyFreeWheneverExists_of_returnsMinimumReportEnvy
    [Fintype Agent] [Nonempty Agent] [DecidableEq Item]
    (M : DirectFairDivisionMechanism Agent Item) {goods : Finset Item}
    (hmin : ReturnsMinimumReportEnvy M goods) :
    ReturnsEnvyFreeWheneverExists M goods := by
  intro values hexists
  exact reportEnvyFree_of_minimumReportEnvyAllocation_of_exists
    (hmin values) hexists

/--
A certificate for the source proof pattern behind impossibility of truthful
minimum-envy fair division: every admissible envy-free output after one
deviation gives the deviating agent strictly more true utility than every
admissible envy-free output at the truthful profile.
-/
structure EnvyFreeManipulationCertificate [DecidableEq Agent] [DecidableEq Item]
    (goods : Finset Item) where
  values : FairDivisionReport Agent Item
  agent : Agent
  report : Bundle Item → ℝ
  truthful_exists :
    ∃ A : Allocation Agent Item, IsAllocationOf A goods ∧ ReportEnvyFree values A
  deviated_exists :
    ∃ A : Allocation Agent Item,
      IsAllocationOf A goods ∧
        ReportEnvyFree (Function.update values agent report) A
  deviated_better :
    ∀ A B : Allocation Agent Item,
      IsAllocationOf A goods →
      ReportEnvyFree values A →
      IsAllocationOf B goods →
      ReportEnvyFree (Function.update values agent report) B →
        values agent (A agent) < values agent (B agent)

/--
An envy-free manipulation certificate refutes dominant-strategy truthfulness
for any mechanism that always allocates the target goods and returns an
envy-free allocation whenever one exists.
-/
theorem not_truthful_of_envyFreeManipulationCertificate
    [DecidableEq Agent] [DecidableEq Item]
    (M : DirectFairDivisionMechanism Agent Item) {goods : Finset Item}
    (halloc : ReturnsAllocationOf M goods)
    (hef : ReturnsEnvyFreeWheneverExists M goods)
    (cert : EnvyFreeManipulationCertificate (Agent := Agent) (Item := Item) goods) :
    ¬ M.Truthful := by
  intro htruth
  have htruthful_alloc : IsAllocationOf (M.allocation cert.values) goods :=
    halloc cert.values
  have htruthful_ef : ReportEnvyFree cert.values (M.allocation cert.values) :=
    hef cert.values cert.truthful_exists
  have hdeviated_alloc :
      IsAllocationOf
        (M.allocation (Function.update cert.values cert.agent cert.report))
        goods :=
    halloc (Function.update cert.values cert.agent cert.report)
  have hdeviated_ef :
      ReportEnvyFree (Function.update cert.values cert.agent cert.report)
        (M.allocation (Function.update cert.values cert.agent cert.report)) :=
    hef (Function.update cert.values cert.agent cert.report) cert.deviated_exists
  have hbetter :
      M.utility cert.values cert.values cert.agent <
        M.utility cert.values
          (Function.update cert.values cert.agent cert.report) cert.agent := by
    simpa [DirectFairDivisionMechanism.utility] using
      cert.deviated_better
        (M.allocation cert.values)
        (M.allocation (Function.update cert.values cert.agent cert.report))
        htruthful_alloc htruthful_ef hdeviated_alloc hdeviated_ef
  exact not_lt_of_ge (htruth cert.values cert.agent cert.report) hbetter

end FairDivision
end AppliedModelingLib
