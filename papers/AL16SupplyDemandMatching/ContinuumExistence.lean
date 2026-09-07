import AL16SupplyDemandMatching.ContinuumModel
import Mathlib.Order.FixedPoints

/-!
# Concrete Continuum Existence for Azevedo--Leshno

This module proves nonempty Definition-2 clearing directly for the literal
continuum carrier. For each college, it takes the least own cutoff that makes
that college weakly feasible with every other cutoff fixed. Assumption 1 makes
aggregate demand continuous, so a positive threshold fills capacity. Gross
substitutes makes the resulting best-response map monotone, and
Knaster--Tarski supplies a fixed point.

This is a direct proof of the source existence consequence at
`docs/source_microsoft_2013.txt:1930-1983`, not a supplied deferred-acceptance
or market-clearing witness.
-/

namespace AL16SupplyDemandMatching

open scoped Topology
open AppliedModelingLib.Matching
open Filter
open MeasureTheory Set

universe v

variable {College : Type v} [Fintype College]

/-- Replace one coordinate of a source cutoff vector. -/
noncomputable def al16SourceUpdateCutoff
    (P : AL16Cutoff College) (c : College) (x : Set.Icc (0 : ℝ) 1) :
    AL16Cutoff College := by
  classical
  exact Function.update P c x

/-- Coordinate replacement is continuous in the new cutoff value. -/
theorem al16SourceUpdateCutoff_continuous
    (P : AL16Cutoff College) (c : College) :
    Continuous (fun x : Set.Icc (0 : ℝ) 1 => al16SourceUpdateCutoff P c x) := by
  classical
  have hpair : Continuous (fun x : Set.Icc (0 : ℝ) 1 => (P, x)) :=
    continuous_const.prodMk continuous_id
  simpa only [al16SourceUpdateCutoff, Function.comp_apply] using
    (continuous_update c).comp hpair

/--
Sequential continuity of favorite-affordable demand when only the demanded
college's cutoff coordinate changes.  Constant coordinates do not need
score-level nullity; only the moving coordinate's target boundary can change
choice membership.
-/
theorem al16FavoriteAffordableAggregateDemand_tendsto_of_updateTendsto
    {Student : Type*} [MeasurableSpace Student]
    (mu : Measure Student) [IsProbabilityMeasure mu]
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    (hscore_measurable :
      ∀ c : College, Measurable (fun theta => al16ScoreValue score theta c))
    (hrank_measurable : ∀ c : College, Measurable (fun theta => rank theta c))
    (hrank_injective : ∀ theta : Student, Function.Injective (rank theta))
    (P : AL16Cutoff College) (c : College)
    (xseq : ℕ -> Set.Icc (0 : ℝ) 1) (x : Set.Icc (0 : ℝ) 1)
    (hboundary_null :
      mu {theta | al16ScoreValue score theta c = (x : ℝ)} = 0)
    (hxseq : Tendsto (fun n => (xseq n : ℝ)) atTop (𝓝 (x : ℝ))) :
    Tendsto
      (fun n => mu.real
        (al16DemandChoiceSet (al16FavoriteAffordableChoice score rank)
          (al16SourceUpdateCutoff P c (xseq n)) c))
      atTop
      (𝓝 (mu.real
        (al16DemandChoiceSet (al16FavoriteAffordableChoice score rank)
          (al16SourceUpdateCutoff P c x) c))) := by
  classical
  have hboundary :
      ∀ᵐ theta ∂mu, al16ScoreValue score theta c ≠ (x : ℝ) := by
    apply ae_iff.mpr
    simpa only [not_not] using hboundary_null
  have hchoice :
      ∀ᵐ theta ∂mu, ∀ᶠ n in atTop,
        al16FavoriteAffordableChoice score rank
            (al16SourceUpdateCutoff P c (xseq n)) theta =
          al16FavoriteAffordableChoice score rank
            (al16SourceUpdateCutoff P c x) theta := by
    filter_upwards [hboundary] with theta htheta
    have haffordable : ∀ d : College, ∀ᶠ n in atTop,
        al16Affordable score (al16SourceUpdateCutoff P c (xseq n)) theta d ↔
          al16Affordable score (al16SourceUpdateCutoff P c x) theta d := by
      intro d
      by_cases hdc : d = c
      · subst d
        rcases lt_or_gt_of_ne htheta with hscore_lt | hcutoff_lt
        · filter_upwards [hxseq.eventually_const_lt hscore_lt] with n hn
          simpa [al16Affordable, al16CutoffValue, al16ScoreValue,
            al16SourceUpdateCutoff] using
            (iff_of_false (not_le_of_gt hn) (not_le_of_gt hscore_lt))
        · filter_upwards [hxseq.eventually_lt_const hcutoff_lt] with n hn
          simpa [al16Affordable, al16CutoffValue, al16ScoreValue,
            al16SourceUpdateCutoff] using
            (iff_of_true (le_of_lt hn) (le_of_lt hcutoff_lt))
      · exact Filter.Eventually.of_forall fun n => by
          simp [al16Affordable, al16CutoffValue,
            al16SourceUpdateCutoff, hdc]
    have hall : ∀ᶠ n in atTop, ∀ d : College,
        al16Affordable score (al16SourceUpdateCutoff P c (xseq n)) theta d ↔
          al16Affordable score (al16SourceUpdateCutoff P c x) theta d :=
      Filter.eventually_all.2 haffordable
    filter_upwards [hall] with n hn
    exact al16FavoriteAffordableChoice_eq_of_affordability score rank
      (al16SourceUpdateCutoff P c (xseq n)) (al16SourceUpdateCutoff P c x)
      theta (hrank_injective theta) hn
  have hmembership :
      ∀ᵐ theta ∂mu, ∀ᶠ n in atTop,
        theta ∈
            al16DemandChoiceSet (al16FavoriteAffordableChoice score rank)
              (al16SourceUpdateCutoff P c (xseq n)) c ↔
          theta ∈
            al16DemandChoiceSet (al16FavoriteAffordableChoice score rank)
              (al16SourceUpdateCutoff P c x) c := by
    filter_upwards [hchoice] with theta hchoice
    filter_upwards [hchoice] with n hn
    simp only [al16DemandChoiceSet, Set.mem_setOf_eq]
    rw [hn]
  have hmeasurableQ :
      MeasurableSet
        (al16DemandChoiceSet (al16FavoriteAffordableChoice score rank)
          (al16SourceUpdateCutoff P c x) c) := by
    change MeasurableSet
      ((al16FavoriteAffordableChoice score rank
          (al16SourceUpdateCutoff P c x)) ⁻¹'
        ({some c} : Set (Option College)))
    exact al16FavoriteAffordableChoice_fiber_measurable
      score rank hscore_measurable hrank_measurable hrank_injective
      (al16SourceUpdateCutoff P c x) (some c)
  have hmeasurableP : ∀ n : ℕ,
      MeasurableSet
        (al16DemandChoiceSet (al16FavoriteAffordableChoice score rank)
          (al16SourceUpdateCutoff P c (xseq n)) c) := by
    intro n
    change MeasurableSet
      ((al16FavoriteAffordableChoice score rank
          (al16SourceUpdateCutoff P c (xseq n))) ⁻¹'
        ({some c} : Set (Option College)))
    exact al16FavoriteAffordableChoice_fiber_measurable
      score rank hscore_measurable hrank_measurable hrank_injective
      (al16SourceUpdateCutoff P c (xseq n)) (some c)
  have hmeasure :
      Tendsto
        (fun n => mu
          (al16DemandChoiceSet (al16FavoriteAffordableChoice score rank)
            (al16SourceUpdateCutoff P c (xseq n)) c))
        atTop
        (𝓝 (mu
          (al16DemandChoiceSet (al16FavoriteAffordableChoice score rank)
            (al16SourceUpdateCutoff P c x) c))) :=
    tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
      hmeasurableQ hmeasurableP hmembership
  have hreal :=
    (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure
  simpa only [Function.comp_apply, measureReal_def] using hreal

/-- Replacing the same cutoff coordinate leaves the other coordinates unchanged. -/
theorem al16SourceUpdateCutoff_apply_of_ne
    (P : AL16Cutoff College) (c d : College) (x : Set.Icc (0 : ℝ) 1)
    (h : d ≠ c) :
    al16SourceUpdateCutoff P c x d = P d := by
  classical
  simp [al16SourceUpdateCutoff, h]

/-- Replacing the selected coordinate gives the supplied value. -/
theorem al16SourceUpdateCutoff_apply_self
    (P : AL16Cutoff College) (c : College) (x : Set.Icc (0 : ℝ) 1) :
    al16SourceUpdateCutoff P c x c = x := by
  classical
  simp [al16SourceUpdateCutoff]

/-- Assumption 1 gives topological continuity of each aggregate-demand component. -/
theorem al16SourceAggregateDemand_continuous
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (hstrict : al16SourceStrictPreferences mu) (c : College) :
    Continuous (fun P : AL16Cutoff College => al16SourceAggregateDemand mu P c) := by
  rw [continuous_iff_seqContinuous]
  intro P Q hPQ
  apply al16SourceAggregateDemand_tendsto_of_coordinatewiseTendsto mu hstrict P Q
  intro d
  exact ((continuous_subtype_val.comp (continuous_apply d)).tendsto Q).comp hPQ

/-- At a unit cutoff, Assumption 1 makes a college's aggregate demand zero. -/
theorem al16SourceAggregateDemand_eq_zero_of_cutoff_eq_one
    (mu : Measure (AL16SourceStudent College))
    (hstrict : al16SourceStrictPreferences mu)
    (P : AL16Cutoff College) (c : College)
    (hP : al16CutoffValue P c = 1) :
    al16SourceAggregateDemand mu P c = 0 := by
  have hsubset : al16DemandChoiceSet al16SourceChoice P c ⊆
      {theta | al16ScoreValue al16SourceScore theta c = 1} := by
    intro theta htheta
    change al16SourceChoice P theta = some c at htheta
    have hsemantics := al16SourceChoice_semantics P theta
    rw [htheta] at hsemantics
    apply le_antisymm
    · exact (al16SourceScore theta c).property.2
    · simpa [hP] using hsemantics.1
  have hzero : mu (al16DemandChoiceSet al16SourceChoice P c) = 0 :=
    measure_mono_null hsubset (hstrict c 1)
  rw [al16SourceAggregateDemand, measureReal_def, hzero]
  rfl

/--
Raising every source cutoff coordinate weakly increases outside-option mass.
This is the source monotonicity step used in Proposition 7's capacity-perturbation
argument.
-/
theorem al16SourceOutsideDemand_le_of_cutoffLe
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    {P Q : AL16Cutoff College}
    (hPQ : ∀ c : College, al16CutoffValue P c ≤ al16CutoffValue Q c) :
    al16SourceOutsideDemand mu P ≤ al16SourceOutsideDemand mu Q := by
  have hsup : Q ⊔ P = Q := by
    funext c
    apply Subtype.ext
    change max ((Q c : Set.Icc (0 : ℝ) 1) : ℝ)
        ((P c : Set.Icc (0 : ℝ) 1) : ℝ) =
      ((Q c : Set.Icc (0 : ℝ) 1) : ℝ)
    exact max_eq_left (hPQ c)
  have h :=
    al16Outside_le_sup_of_choice_semantics
      (al16SourceOutsideDemand mu) mu.real al16SourceScore
      al16SourcePrefers al16SourceChoice
      (fun {A B} hAB => al16MeasureMass_mono mu hAB)
      (fun _ => rfl) al16SourceChoice_semantics Q P
  simpa [hsup] using h

/--
Raising every source cutoff coordinate weakly decreases total college demand.
This is the total-demand comparison in Proposition 7's proof.
-/
theorem al16SourceAggregateDemand_sum_le_of_cutoffLe
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    {P Q : AL16Cutoff College}
    (hPQ : ∀ c : College, al16CutoffValue P c ≤ al16CutoffValue Q c) :
    (∑ c : College, al16SourceAggregateDemand mu Q c) ≤
      ∑ c : College, al16SourceAggregateDemand mu P c := by
  have houtside : al16SourceOutsideDemand mu P ≤ al16SourceOutsideDemand mu Q :=
    al16SourceOutsideDemand_le_of_cutoffLe mu hPQ
  have hpartitionP :
      al16SourceOutsideDemand mu P +
          ∑ c : College, al16SourceAggregateDemand mu P c = 1 := by
    simpa [al16SourceOutsideDemand, al16SourceAggregateDemand] using
      (al16UnitMassPartition_of_measure_choice
        mu al16SourceChoice al16SourceChoice_fiber_measurable P)
  have hpartitionQ :
      al16SourceOutsideDemand mu Q +
          ∑ c : College, al16SourceAggregateDemand mu Q c = 1 := by
    simpa [al16SourceOutsideDemand, al16SourceAggregateDemand] using
      (al16UnitMassPartition_of_measure_choice
          mu al16SourceChoice al16SourceChoice_fiber_measurable Q)
  nlinarith

/--
Proposition 7, source-shaped upward-capacity cutoff exclusion.

If the perturbed capacity vector has larger total capacity than the old one
but still has total capacity below the unit student mass, no weakly higher
cutoff vector can clear the perturbed economy above an old clearing cutoff.
This is the contradiction in `docs/source_microsoft_2013.txt:1791-1812`,
written with the neighborhood condition exposed as `Pminus <= P`.
-/
theorem al16Source_no_marketClearing_weaklyAbove_of_capacity_sum_increase_lt_one
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity capacity' : College -> ℝ)
    {Pminus P : AL16Cutoff College}
    (hPminus :
      al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity Pminus)
    (hcutoff_le :
      ∀ c : College, al16CutoffValue Pminus c ≤ al16CutoffValue P c)
    (hcapacity_sum_lt :
      (∑ c : College, capacity c) < ∑ c : College, capacity' c)
    (hcapacity'_sum_lt_one : (∑ c : College, capacity' c) < 1)
    (hP :
      al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity' P) :
    False := by
  have hdemand_sum_le :
      (∑ c : College, al16SourceAggregateDemand mu P c) ≤
        ∑ c : College, al16SourceAggregateDemand mu Pminus c :=
    al16SourceAggregateDemand_sum_le_of_cutoffLe mu hcutoff_le
  have hold_capacity :
      (∑ c : College, al16SourceAggregateDemand mu Pminus c) ≤
        ∑ c : College, capacity c := by
    exact Finset.sum_le_sum fun c _ => hPminus.1 c
  have hnew_exact :
      ∀ c : College, al16SourceAggregateDemand mu P c = capacity' c :=
    al16SourceMarketClearing_exactFill_of_capacity_sum_lt_one
      mu capacity' hP hcapacity'_sum_lt_one
  have hnew_capacity :
      (∑ c : College, al16SourceAggregateDemand mu P c) =
        ∑ c : College, capacity' c := by
    exact Finset.sum_congr rfl fun c _ => hnew_exact c
  have hchain :
      (∑ c : College, capacity' c) ≤ ∑ c : College, capacity c := by
    calc
      (∑ c : College, capacity' c) =
          ∑ c : College, al16SourceAggregateDemand mu P c := hnew_capacity.symm
      _ ≤ ∑ c : College, al16SourceAggregateDemand mu Pminus c := hdemand_sum_le
      _ ≤ ∑ c : College, capacity c := hold_capacity
  exact (not_lt_of_ge hchain) hcapacity_sum_lt

/--
Proposition 7, source-shaped downward-capacity cutoff exclusion.

If total capacity is perturbed downward while the original economy has total
capacity below the unit student mass, no weakly lower cutoff vector can clear
the perturbed economy below an old clearing cutoff. This is the case the
source proof calls analogous at `docs/source_microsoft_2013.txt:1788-1812`.
-/
theorem al16Source_no_marketClearing_weaklyBelow_of_capacity_sum_decrease_lt_one
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity capacity' : College -> ℝ)
    {Pplus P : AL16Cutoff College}
    (hPplus :
      al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity Pplus)
    (hcutoff_le :
      ∀ c : College, al16CutoffValue P c ≤ al16CutoffValue Pplus c)
    (hcapacity'_sum_lt :
      (∑ c : College, capacity' c) < ∑ c : College, capacity c)
    (hcapacity_sum_lt_one : (∑ c : College, capacity c) < 1)
    (hP :
      al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity' P) :
    False := by
  have hcapacity'_sum_lt_one : (∑ c : College, capacity' c) < 1 :=
    lt_trans hcapacity'_sum_lt hcapacity_sum_lt_one
  have hdemand_sum_le :
      (∑ c : College, al16SourceAggregateDemand mu Pplus c) ≤
        ∑ c : College, al16SourceAggregateDemand mu P c :=
    al16SourceAggregateDemand_sum_le_of_cutoffLe mu hcutoff_le
  have hold_exact :
      ∀ c : College, al16SourceAggregateDemand mu Pplus c = capacity c :=
    al16SourceMarketClearing_exactFill_of_capacity_sum_lt_one
      mu capacity hPplus hcapacity_sum_lt_one
  have hnew_exact :
      ∀ c : College, al16SourceAggregateDemand mu P c = capacity' c :=
    al16SourceMarketClearing_exactFill_of_capacity_sum_lt_one
      mu capacity' hP hcapacity'_sum_lt_one
  have hold_capacity :
      (∑ c : College, al16SourceAggregateDemand mu Pplus c) =
        ∑ c : College, capacity c := by
    exact Finset.sum_congr rfl fun c _ => hold_exact c
  have hnew_capacity :
      (∑ c : College, al16SourceAggregateDemand mu P c) =
        ∑ c : College, capacity' c := by
    exact Finset.sum_congr rfl fun c _ => hnew_exact c
  have hchain :
      (∑ c : College, capacity c) ≤ ∑ c : College, capacity' c := by
    calc
      (∑ c : College, capacity c) =
          ∑ c : College, al16SourceAggregateDemand mu Pplus c := hold_capacity.symm
      _ ≤ ∑ c : College, al16SourceAggregateDemand mu P c := hdemand_sum_le
      _ = ∑ c : College, capacity' c := hnew_capacity
  exact (not_lt_of_ge hchain) hcapacity'_sum_lt

/--
Proposition 7, source-shaped upward sequence/neighborhood exclusion.

If a sequence of perturbed capacities converges back to the original capacities,
has strictly larger total capacity eventually, and remains below total student
mass eventually, then no Definition-2 clearing cutoff in any set lying weakly
above the old lower clearing cutoff can occur eventually. The convergence
premise records the source's `E_k -> E` condition; the contradiction itself is
the visible total-capacity argument at
`docs/source_microsoft_2013.txt:1791-1812`.
-/
theorem al16Source_eventually_no_marketClearing_in_weaklyAbove_neighborhood
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (capacitySeq : ℕ -> College -> ℝ)
    (N : Set (AL16Cutoff College))
    {Pminus : AL16Cutoff College}
    (hPminus :
      al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity Pminus)
    (hN :
      ∀ P : AL16Cutoff College, P ∈ N ->
        ∀ c : College, al16CutoffValue Pminus c ≤ al16CutoffValue P c)
    (_hcapacity_tendsto :
      ∀ c : College, Tendsto (fun k : ℕ => capacitySeq k c) atTop
        (𝓝 (capacity c)))
    (hcapacity_sum_increase :
      ∀ᶠ k : ℕ in atTop,
        (∑ c : College, capacity c) < ∑ c : College, capacitySeq k c)
    (hcapacity_sum_lt_one :
      ∀ᶠ k : ℕ in atTop, (∑ c : College, capacitySeq k c) < 1) :
    ∀ᶠ k : ℕ in atTop,
      ∀ P : AL16Cutoff College, P ∈ N ->
        al16SourceMarketClearing (al16SourceAggregateDemand mu) (capacitySeq k) P ->
          False := by
  filter_upwards [hcapacity_sum_increase, hcapacity_sum_lt_one] with k hsum hsum_one
  intro P hPN hP
  exact al16Source_no_marketClearing_weaklyAbove_of_capacity_sum_increase_lt_one
    mu capacity (capacitySeq k) hPminus (hN P hPN) hsum hsum_one hP

/--
Proposition 7, source-shaped downward sequence/neighborhood exclusion.

If a sequence of perturbed capacities converges back to the original capacities
and has strictly smaller total capacity eventually, while the original total
capacity is below total student mass, then no Definition-2 clearing cutoff in
any set lying weakly below the old upper clearing cutoff can occur eventually.
The convergence premise records the source's `E_k -> E` condition; the
contradiction is the symmetric capacity argument at
`docs/source_microsoft_2013.txt:1788-1812`.
-/
theorem al16Source_eventually_no_marketClearing_in_weaklyBelow_neighborhood
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (capacitySeq : ℕ -> College -> ℝ)
    (N : Set (AL16Cutoff College))
    {Pplus : AL16Cutoff College}
    (hPplus :
      al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity Pplus)
    (hN :
      ∀ P : AL16Cutoff College, P ∈ N ->
        ∀ c : College, al16CutoffValue P c ≤ al16CutoffValue Pplus c)
    (_hcapacity_tendsto :
      ∀ c : College, Tendsto (fun k : ℕ => capacitySeq k c) atTop
        (𝓝 (capacity c)))
    (hcapacity_sum_decrease :
      ∀ᶠ k : ℕ in atTop,
        (∑ c : College, capacitySeq k c) < ∑ c : College, capacity c)
    (hcapacity_sum_lt_one : (∑ c : College, capacity c) < 1) :
    ∀ᶠ k : ℕ in atTop,
      ∀ P : AL16Cutoff College, P ∈ N ->
        al16SourceMarketClearing (al16SourceAggregateDemand mu) (capacitySeq k) P ->
          False := by
  filter_upwards [hcapacity_sum_decrease] with k hsum
  intro P hPN hP
  exact al16Source_no_marketClearing_weaklyBelow_of_capacity_sum_decrease_lt_one
    mu capacity (capacitySeq k) hPplus (hN P hPN) hsum hcapacity_sum_lt_one hP

/--
If `P` is coordinatewise strictly above `Pminus`, then the source proof's
weakly-above-`Pminus` region is a neighborhood of `P`.
-/
theorem al16Source_weaklyAbove_region_mem_nhds
    {Pminus P : AL16Cutoff College}
    (hstrict : ∀ c : College, al16CutoffValue Pminus c < al16CutoffValue P c) :
    {Q : AL16Cutoff College |
      ∀ c : College, al16CutoffValue Pminus c ≤ al16CutoffValue Q c} ∈ 𝓝 P := by
  have hcoord : ∀ c : College, ∀ᶠ Q : AL16Cutoff College in 𝓝 P,
      al16CutoffValue Pminus c ≤ al16CutoffValue Q c := by
    intro c
    have hcont : ContinuousAt (fun Q : AL16Cutoff College => al16CutoffValue Q c) P := by
      simpa [al16CutoffValue] using
        ((continuous_subtype_val.comp (continuous_apply c)).continuousAt :
          ContinuousAt (fun Q : AL16Cutoff College => ((Q c : Set.Icc (0 : ℝ) 1) : ℝ)) P)
    exact (hcont.eventually (Ioi_mem_nhds (hstrict c))).mono fun Q hQ => hQ.le
  simpa only [Set.mem_setOf_eq] using Filter.eventually_all.2 hcoord

/--
If `P` is coordinatewise strictly below `Pplus`, then the source proof's
weakly-below-`Pplus` region is a neighborhood of `P`.
-/
theorem al16Source_weaklyBelow_region_mem_nhds
    {P Pplus : AL16Cutoff College}
    (hstrict : ∀ c : College, al16CutoffValue P c < al16CutoffValue Pplus c) :
    {Q : AL16Cutoff College |
      ∀ c : College, al16CutoffValue Q c ≤ al16CutoffValue Pplus c} ∈ 𝓝 P := by
  have hcoord : ∀ c : College, ∀ᶠ Q : AL16Cutoff College in 𝓝 P,
      al16CutoffValue Q c ≤ al16CutoffValue Pplus c := by
    intro c
    have hcont : ContinuousAt (fun Q : AL16Cutoff College => al16CutoffValue Q c) P := by
      simpa [al16CutoffValue] using
        ((continuous_subtype_val.comp (continuous_apply c)).continuousAt :
          ContinuousAt (fun Q : AL16Cutoff College => ((Q c : Set.Icc (0 : ℝ) 1) : ℝ)) P)
    exact (hcont.eventually (Iio_mem_nhds (hstrict c))).mono fun Q hQ => hQ.le
  simpa only [Set.mem_setOf_eq] using Filter.eventually_all.2 hcoord

/--
Proposition 7, strict-above neighborhood exclusion.

If the reviewed cutoff `P` is coordinatewise strictly above an old lower
clearing cutoff, the weakly-above region used in the proof contains a
neighborhood of `P`; the existing total-capacity contradiction therefore rules
out all clearing cutoffs in that actual neighborhood eventually.
-/
theorem al16Source_eventually_no_marketClearing_in_strictAbove_nhds
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (capacitySeq : ℕ -> College -> ℝ)
    {Pminus P : AL16Cutoff College}
    (hPminus :
      al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity Pminus)
    (hstrict : ∀ c : College, al16CutoffValue Pminus c < al16CutoffValue P c)
    (hcapacity_tendsto :
      ∀ c : College, Tendsto (fun k : ℕ => capacitySeq k c) atTop
        (𝓝 (capacity c)))
    (hcapacity_sum_increase :
      ∀ᶠ k : ℕ in atTop,
        (∑ c : College, capacity c) < ∑ c : College, capacitySeq k c)
    (hcapacity_sum_lt_one :
      ∀ᶠ k : ℕ in atTop, (∑ c : College, capacitySeq k c) < 1) :
    ∃ N : Set (AL16Cutoff College), N ∈ 𝓝 P ∧
      ∀ᶠ k : ℕ in atTop,
        ∀ Q : AL16Cutoff College, Q ∈ N ->
          al16SourceMarketClearing (al16SourceAggregateDemand mu) (capacitySeq k) Q ->
            False := by
  let N : Set (AL16Cutoff College) :=
    {Q | ∀ c : College, al16CutoffValue Pminus c ≤ al16CutoffValue Q c}
  refine ⟨N, ?_, ?_⟩
  · exact al16Source_weaklyAbove_region_mem_nhds hstrict
  · exact al16Source_eventually_no_marketClearing_in_weaklyAbove_neighborhood
      mu capacity capacitySeq N hPminus (fun Q hQ => hQ)
      hcapacity_tendsto hcapacity_sum_increase hcapacity_sum_lt_one

/--
Proposition 7, strict-below neighborhood exclusion.

If the reviewed cutoff `P` is coordinatewise strictly below an old upper
clearing cutoff, the weakly-below region used in the proof contains a
neighborhood of `P`; the symmetric total-capacity contradiction rules out all
clearing cutoffs in that actual neighborhood eventually.
-/
theorem al16Source_eventually_no_marketClearing_in_strictBelow_nhds
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (capacitySeq : ℕ -> College -> ℝ)
    {P Pplus : AL16Cutoff College}
    (hPplus :
      al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity Pplus)
    (hstrict : ∀ c : College, al16CutoffValue P c < al16CutoffValue Pplus c)
    (hcapacity_tendsto :
      ∀ c : College, Tendsto (fun k : ℕ => capacitySeq k c) atTop
        (𝓝 (capacity c)))
    (hcapacity_sum_decrease :
      ∀ᶠ k : ℕ in atTop,
        (∑ c : College, capacitySeq k c) < ∑ c : College, capacity c)
    (hcapacity_sum_lt_one : (∑ c : College, capacity c) < 1) :
    ∃ N : Set (AL16Cutoff College), N ∈ 𝓝 P ∧
      ∀ᶠ k : ℕ in atTop,
        ∀ Q : AL16Cutoff College, Q ∈ N ->
          al16SourceMarketClearing (al16SourceAggregateDemand mu) (capacitySeq k) Q ->
            False := by
  let N : Set (AL16Cutoff College) :=
    {Q | ∀ c : College, al16CutoffValue Q c ≤ al16CutoffValue Pplus c}
  refine ⟨N, ?_, ?_⟩
  · exact al16Source_weaklyBelow_region_mem_nhds hstrict
  · exact al16Source_eventually_no_marketClearing_in_weaklyBelow_neighborhood
      mu capacity capacitySeq N hPplus (fun Q hQ => hQ)
      hcapacity_tendsto hcapacity_sum_decrease hcapacity_sum_lt_one

/--
Proposition 7, constructed upward perturbation sequence.

Given a cutoff strictly above an old lower clearing cutoff and total old
capacity below the unit source mass, this constructs an explicit capacity
sequence converging back to the old capacity vector.  Eventually every
perturbed capacity vector is strictly positive, has larger total capacity but
still total capacity below one, and has no clearing cutoff in a neighborhood of
the reviewed cutoff.  The old lower clearing anchor remains visible.
-/
theorem al16Source_exists_upward_capacity_sequence_no_marketClearing_in_strictAbove_nhds
    [Nonempty College]
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    {Pminus P : AL16Cutoff College}
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (hcapacity_sum_lt_one : (∑ c : College, capacity c) < 1)
    (hPminus :
      al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity Pminus)
    (hstrict : ∀ c : College, al16CutoffValue Pminus c < al16CutoffValue P c) :
    ∃ capacitySeq : ℕ -> College -> ℝ,
      (∀ c : College,
        Tendsto (fun k : ℕ => capacitySeq k c) atTop (𝓝 (capacity c))) ∧
        (∀ᶠ k : ℕ in atTop, ∀ c : College, 0 < capacitySeq k c) ∧
        ∃ N : Set (AL16Cutoff College), N ∈ 𝓝 P ∧
          ∀ᶠ k : ℕ in atTop,
            ∀ Q : AL16Cutoff College, Q ∈ N ->
              al16SourceMarketClearing
                (al16SourceAggregateDemand mu) (capacitySeq k) Q ->
                False := by
  classical
  let c0 : College := Classical.choice (inferInstance : Nonempty College)
  let gap : ℝ := 1 - ∑ c : College, capacity c
  let eps : ℕ -> ℝ := fun k => gap / (2 * ((k : ℝ) + 1))
  let capacitySeq : ℕ -> College -> ℝ :=
    fun k c => capacity c + if c = c0 then eps k else 0
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    linarith
  have heps_tendsto : Tendsto eps atTop (𝓝 0) := by
    have hbase :
        Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hmul := (tendsto_const_nhds (x := gap / 2)).mul hbase
    simpa [eps, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  have heps_pos : ∀ k : ℕ, 0 < eps k := by
    intro k
    have hden : 0 < 2 * ((k : ℝ) + 1) := by positivity
    exact div_pos hgap_pos hden
  have heps_lt_gap : ∀ k : ℕ, eps k < gap := by
    intro k
    have hden_gt_one : 1 < 2 * ((k : ℝ) + 1) := by
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith
    exact div_lt_self hgap_pos hden_gt_one
  have hsum_seq : ∀ k : ℕ,
      (∑ c : College, capacitySeq k c) =
        (∑ c : College, capacity c) + eps k := by
    intro k
    simp [capacitySeq, Finset.sum_add_distrib]
  have htendsto : ∀ c : College,
      Tendsto (fun k : ℕ => capacitySeq k c) atTop (𝓝 (capacity c)) := by
    intro c
    by_cases hc : c = c0
    · subst c
      simpa [capacitySeq] using
        (tendsto_const_nhds (x := capacity c0)).add heps_tendsto
    · simpa [capacitySeq, hc] using tendsto_const_nhds (x := capacity c)
  have hpos_eventually :
      ∀ᶠ k : ℕ in atTop, ∀ c : College, 0 < capacitySeq k c :=
    Filter.Eventually.of_forall fun k c => by
      by_cases hc : c = c0
      · subst c
        have hnonneg : 0 ≤ eps k := (heps_pos k).le
        have hcap := hcapacity_pos c0
        dsimp [capacitySeq]
        rw [if_pos rfl]
        linarith
      · dsimp [capacitySeq]
        rw [if_neg hc]
        simpa using hcapacity_pos c
  have hsum_increase :
      ∀ᶠ k : ℕ in atTop,
        (∑ c : College, capacity c) < ∑ c : College, capacitySeq k c :=
    Filter.Eventually.of_forall fun k => by
      rw [hsum_seq k]
      exact lt_add_of_pos_right _ (heps_pos k)
  have hsum_lt_one :
      ∀ᶠ k : ℕ in atTop, (∑ c : College, capacitySeq k c) < 1 :=
    Filter.Eventually.of_forall fun k => by
      rw [hsum_seq k]
      have hlt := heps_lt_gap k
      dsimp [gap] at hlt
      linarith
  refine ⟨capacitySeq, htendsto, hpos_eventually, ?_⟩
  exact al16Source_eventually_no_marketClearing_in_strictAbove_nhds
    mu capacity capacitySeq hPminus hstrict htendsto hsum_increase hsum_lt_one

/--
Proposition 7, constructed downward perturbation sequence.

Given a cutoff strictly below an old upper clearing cutoff and total old
capacity below the unit source mass, this constructs an explicit capacity
sequence converging back to the old capacity vector.  Eventually every
perturbed capacity vector is strictly positive and has lower total capacity,
and no clearing cutoff lies in a neighborhood of the reviewed cutoff.  The old
upper clearing anchor remains visible.
-/
theorem al16Source_exists_downward_capacity_sequence_no_marketClearing_in_strictBelow_nhds
    [Nonempty College]
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    {P Pplus : AL16Cutoff College}
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (hcapacity_sum_lt_one : (∑ c : College, capacity c) < 1)
    (hPplus :
      al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity Pplus)
    (hstrict : ∀ c : College, al16CutoffValue P c < al16CutoffValue Pplus c) :
    ∃ capacitySeq : ℕ -> College -> ℝ,
      (∀ c : College,
        Tendsto (fun k : ℕ => capacitySeq k c) atTop (𝓝 (capacity c))) ∧
        (∀ᶠ k : ℕ in atTop, ∀ c : College, 0 < capacitySeq k c) ∧
        ∃ N : Set (AL16Cutoff College), N ∈ 𝓝 P ∧
          ∀ᶠ k : ℕ in atTop,
            ∀ Q : AL16Cutoff College, Q ∈ N ->
              al16SourceMarketClearing
                (al16SourceAggregateDemand mu) (capacitySeq k) Q ->
                False := by
  classical
  let c0 : College := Classical.choice (inferInstance : Nonempty College)
  let gap : ℝ := capacity c0
  let eps : ℕ -> ℝ := fun k => gap / (2 * ((k : ℝ) + 1))
  let capacitySeq : ℕ -> College -> ℝ :=
    fun k c => capacity c - if c = c0 then eps k else 0
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    exact hcapacity_pos c0
  have heps_tendsto : Tendsto eps atTop (𝓝 0) := by
    have hbase :
        Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hmul := (tendsto_const_nhds (x := gap / 2)).mul hbase
    simpa [eps, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  have heps_pos : ∀ k : ℕ, 0 < eps k := by
    intro k
    have hden : 0 < 2 * ((k : ℝ) + 1) := by positivity
    exact div_pos hgap_pos hden
  have heps_lt_gap : ∀ k : ℕ, eps k < gap := by
    intro k
    have hden_gt_one : 1 < 2 * ((k : ℝ) + 1) := by
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith
    exact div_lt_self hgap_pos hden_gt_one
  have hsum_seq : ∀ k : ℕ,
      (∑ c : College, capacitySeq k c) =
        (∑ c : College, capacity c) - eps k := by
    intro k
    simp [capacitySeq, Finset.sum_sub_distrib]
  have htendsto : ∀ c : College,
      Tendsto (fun k : ℕ => capacitySeq k c) atTop (𝓝 (capacity c)) := by
    intro c
    by_cases hc : c = c0
    · subst c
      simpa [capacitySeq] using
        (tendsto_const_nhds (x := capacity c0)).sub heps_tendsto
    · simpa [capacitySeq, hc] using tendsto_const_nhds (x := capacity c)
  have hpos_eventually :
      ∀ᶠ k : ℕ in atTop, ∀ c : College, 0 < capacitySeq k c :=
    Filter.Eventually.of_forall fun k c => by
      by_cases hc : c = c0
      · subst c
        have hlt := heps_lt_gap k
        dsimp [capacitySeq, gap] at hlt ⊢
        rw [if_pos rfl]
        linarith
      · dsimp [capacitySeq]
        rw [if_neg hc]
        simpa using hcapacity_pos c
  have hsum_decrease :
      ∀ᶠ k : ℕ in atTop,
        (∑ c : College, capacitySeq k c) < ∑ c : College, capacity c :=
    Filter.Eventually.of_forall fun k => by
      rw [hsum_seq k]
      exact sub_lt_self _ (heps_pos k)
  refine ⟨capacitySeq, htendsto, hpos_eventually, ?_⟩
  exact al16Source_eventually_no_marketClearing_in_strictBelow_nhds
    mu capacity capacitySeq hPplus hstrict htendsto hsum_decrease
    hcapacity_sum_lt_one

/--
Proposition 7, upward-capacity cutoff exclusion step.

If capacities are perturbed upward in total, then no cutoff vector strictly
above an old clearing cutoff can clear the perturbed capacity vector. The proof
uses only Definition 2's exact-fill-at-positive-cutoffs clause, the old weak
capacity inequalities, and the source total-demand monotonicity under higher
cutoffs. Source: `docs/source_microsoft_2013.txt:1774-1812`.
-/
theorem al16Source_no_marketClearing_strictAbove_of_capacity_sum_increase
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity capacity' : College -> ℝ)
    {Pminus P : AL16Cutoff College}
    (hPminus :
      al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity Pminus)
    (hstrictAbove :
      ∀ c : College, al16CutoffValue Pminus c < al16CutoffValue P c)
    (hcapacity_sum_lt :
      (∑ c : College, capacity c) < ∑ c : College, capacity' c)
    (hP :
      al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity' P) :
    False := by
  have hle_cutoff :
      ∀ c : College, al16CutoffValue Pminus c ≤ al16CutoffValue P c :=
    fun c => (hstrictAbove c).le
  have hdemand_sum_le :
      (∑ c : College, al16SourceAggregateDemand mu P c) ≤
        ∑ c : College, al16SourceAggregateDemand mu Pminus c :=
    al16SourceAggregateDemand_sum_le_of_cutoffLe mu hle_cutoff
  have hold_capacity :
      (∑ c : College, al16SourceAggregateDemand mu Pminus c) ≤
        ∑ c : College, capacity c := by
    exact Finset.sum_le_sum fun c _ => hPminus.1 c
  have hP_pos : ∀ c : College, 0 < al16CutoffValue P c := by
    intro c
    exact lt_of_le_of_lt (Pminus c).property.1 (hstrictAbove c)
  have hnew_capacity :
      (∑ c : College, al16SourceAggregateDemand mu P c) =
        ∑ c : College, capacity' c := by
    exact Finset.sum_congr rfl fun c _ => hP.2 c (hP_pos c)
  have hnot_lt :
      ¬ (∑ c : College, capacity c) < ∑ c : College, capacity' c := by
    intro hlt
    have hchain :
        (∑ c : College, capacity' c) ≤ ∑ c : College, capacity c := by
      calc
        (∑ c : College, capacity' c) =
            ∑ c : College, al16SourceAggregateDemand mu P c := hnew_capacity.symm
        _ ≤ ∑ c : College, al16SourceAggregateDemand mu Pminus c := hdemand_sum_le
        _ ≤ ∑ c : College, capacity c := hold_capacity
    exact (not_lt_of_ge hchain) hlt
  exact hnot_lt hcapacity_sum_lt

/-- Own-cutoff values that make one college weakly capacity feasible. -/
noncomputable def al16SourceCapacityFeasibleCutoffs
    (mu : Measure (AL16SourceStudent College))
    (capacity : College -> ℝ)
    (P : AL16Cutoff College) (c : College) : Set (Set.Icc (0 : ℝ) 1) :=
  {x | al16SourceAggregateDemand mu (al16SourceUpdateCutoff P c x) c ≤ capacity c}

/-- The capacity-feasible own-cutoff set is closed. -/
theorem al16SourceCapacityFeasibleCutoffs_closed
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (hstrict : al16SourceStrictPreferences mu)
    (P : AL16Cutoff College) (c : College) :
    IsClosed (al16SourceCapacityFeasibleCutoffs mu capacity P c) := by
  exact isClosed_le
    ((al16SourceAggregateDemand_continuous mu hstrict c).comp
      (al16SourceUpdateCutoff_continuous P c)) continuous_const

/-- Positive capacities make the capacity-feasible own-cutoff set nonempty. -/
theorem al16SourceCapacityFeasibleCutoffs_nonempty
    (mu : Measure (AL16SourceStudent College))
    (capacity : College -> ℝ)
    (hstrict : al16SourceStrictPreferences mu)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (P : AL16Cutoff College) (c : College) :
    (al16SourceCapacityFeasibleCutoffs mu capacity P c).Nonempty := by
  refine ⟨1, ?_⟩
  change al16SourceAggregateDemand mu
      (al16SourceUpdateCutoff P c (1 : Set.Icc (0 : ℝ) 1)) c ≤ capacity c
  rw [al16SourceAggregateDemand_eq_zero_of_cutoff_eq_one mu hstrict
    (al16SourceUpdateCutoff P c (1 : Set.Icc (0 : ℝ) 1)) c]
  · exact (hcapacity_pos c).le
  · simp [al16CutoffValue, al16SourceUpdateCutoff]

/-- The least own cutoff that makes a college weakly capacity feasible. -/
noncomputable def al16SourceCapacityThreshold
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (hstrict : al16SourceStrictPreferences mu)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (P : AL16Cutoff College) (c : College) : Set.Icc (0 : ℝ) 1 :=
  ((al16SourceCapacityFeasibleCutoffs_closed mu capacity hstrict P c).isCompact.exists_isLeast
    (al16SourceCapacityFeasibleCutoffs_nonempty mu capacity hstrict hcapacity_pos P c)).choose

/-- The capacity threshold is the least feasible own-cutoff value. -/
theorem al16SourceCapacityThreshold_isLeast
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (hstrict : al16SourceStrictPreferences mu)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (P : AL16Cutoff College) (c : College) :
    IsLeast (al16SourceCapacityFeasibleCutoffs mu capacity P c)
      (al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos P c) := by
  simp only [al16SourceCapacityThreshold]
  exact
    ((al16SourceCapacityFeasibleCutoffs_closed mu capacity hstrict P c).isCompact.exists_isLeast
      (al16SourceCapacityFeasibleCutoffs_nonempty mu capacity hstrict hcapacity_pos P c)).choose_spec

/-- The capacity threshold itself is weakly capacity feasible. -/
theorem al16SourceCapacityThreshold_feasible
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (hstrict : al16SourceStrictPreferences mu)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (P : AL16Cutoff College) (c : College) :
    al16SourceAggregateDemand mu
      (al16SourceUpdateCutoff P c
        (al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos P c)) c ≤ capacity c :=
  (al16SourceCapacityThreshold_isLeast mu capacity hstrict hcapacity_pos P c).1

/-- A positive least feasible threshold fills the college by continuity. -/
theorem al16SourceCapacityThreshold_eq_capacity_of_pos
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (hstrict : al16SourceStrictPreferences mu)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (P : AL16Cutoff College) (c : College)
    (hpos : 0 < (al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos P c : ℝ)) :
    al16SourceAggregateDemand mu
      (al16SourceUpdateCutoff P c
        (al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos P c)) c = capacity c := by
  let f : Set.Icc (0 : ℝ) 1 -> ℝ :=
    fun x => al16SourceAggregateDemand mu (al16SourceUpdateCutoff P c x) c
  have hf : Continuous f :=
    (al16SourceAggregateDemand_continuous mu hstrict c).comp
      (al16SourceUpdateCutoff_continuous P c)
  have hfeasible : f (al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos P c) ≤
      capacity c :=
    al16SourceCapacityThreshold_feasible mu capacity hstrict hcapacity_pos P c
  apply le_antisymm hfeasible
  apply le_of_not_gt
  intro hlt
  have hopen : IsOpen {x : Set.Icc (0 : ℝ) 1 | f x < capacity c} :=
    isOpen_lt hf continuous_const
  have hnotmin : ¬ IsMin (al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos P c) := by
    apply (isMin_iff_eq_bot.not).mpr
    have hbpos : (0 : Set.Icc (0 : ℝ) 1) <
        al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos P c := by
      change (0 : ℝ) < (al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos P c : ℝ)
      exact hpos
    exact ne_of_gt hbpos
  obtain ⟨x, hxopen, hxlt⟩ :=
    nonempty_nhds_inter_Iio (hopen.mem_nhds hlt) hnotmin
  have hxfeasible : x ∈ al16SourceCapacityFeasibleCutoffs mu capacity P c := by
    change f x ≤ capacity c
    exact le_of_lt hxopen
  exact (not_lt_of_ge
    ((al16SourceCapacityThreshold_isLeast mu capacity hstrict hcapacity_pos P c).2 hxfeasible)) hxlt

/-- Updating comparable cutoff vectors with the same own coordinate preserves order. -/
theorem al16SourceUpdateCutoff_le_of_le
    {P Q : AL16Cutoff College} (hPQ : P ≤ Q)
    (c : College) (x : Set.Icc (0 : ℝ) 1) :
    al16SourceUpdateCutoff P c x ≤ al16SourceUpdateCutoff Q c x := by
  classical
  intro d
  by_cases hdc : d = c
  · subst d
    simp [al16SourceUpdateCutoff]
  · simp [al16SourceUpdateCutoff, hdc, hPQ d]

/-- Raising only other colleges' cutoffs weakly raises a college's demand. -/
theorem al16SourceAggregateDemand_le_of_le_same_coordinate
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    {P Q : AL16Cutoff College} {c : College}
    (hPQ : P ≤ Q)
    (hcoordinate : al16CutoffValue P c = al16CutoffValue Q c) :
    al16SourceAggregateDemand mu P c ≤ al16SourceAggregateDemand mu Q c := by
  have htotal : ∀ theta : AL16SourceStudent College, ∀ a b : College,
      a = b ∨ al16SourcePrefers theta (some a) (some b) ∨
        al16SourcePrefers theta (some b) (some a) :=
    al16RankPrefers_total al16SourceRank al16SourceRank_injective
  have hcomp := al16AggregateDemand_le_sup_of_choice_semantics
    (demand := al16SourceAggregateDemand mu) (mass := mu.real)
    (score := al16SourceScore) (prefers := al16SourcePrefers)
    (choice := al16SourceChoice)
    (fun {A B} hAB => al16MeasureMass_mono mu hAB)
    (fun _ _ => rfl) al16SourceChoice_semantics htotal
    (P := Q) (Q := P) (c := c) hcoordinate.ge
  have hsup : Q ⊔ P = Q := sup_eq_left.mpr hPQ
  simpa only [hsup] using hcomp

/-- Least feasible own cutoffs are monotone in all other cutoff coordinates. -/
theorem al16SourceCapacityThreshold_mono
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (hstrict : al16SourceStrictPreferences mu)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    {P Q : AL16Cutoff College} (hPQ : P ≤ Q) (c : College) :
    al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos P c ≤
      al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos Q c := by
  apply (al16SourceCapacityThreshold_isLeast mu capacity hstrict hcapacity_pos P c).2
  change al16SourceAggregateDemand mu
      (al16SourceUpdateCutoff P c
        (al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos Q c)) c ≤ capacity c
  have hupdate : al16SourceUpdateCutoff P c
      (al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos Q c) ≤
      al16SourceUpdateCutoff Q c
        (al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos Q c) :=
    al16SourceUpdateCutoff_le_of_le hPQ c _
  have hcoordinate :
      al16CutoffValue
        (al16SourceUpdateCutoff P c
          (al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos Q c)) c =
      al16CutoffValue
        (al16SourceUpdateCutoff Q c
          (al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos Q c)) c := by
    classical
    simp [al16CutoffValue, al16SourceUpdateCutoff]
  calc
    al16SourceAggregateDemand mu
        (al16SourceUpdateCutoff P c
          (al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos Q c)) c ≤
      al16SourceAggregateDemand mu
        (al16SourceUpdateCutoff Q c
          (al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos Q c)) c :=
      al16SourceAggregateDemand_le_of_le_same_coordinate mu hupdate hcoordinate
    _ ≤ capacity c :=
      al16SourceCapacityThreshold_feasible mu capacity hstrict hcapacity_pos Q c

/-- The monotone vector of least capacity-feasible own cutoffs. -/
noncomputable def al16SourceCapacityBestResponse
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (hstrict : al16SourceStrictPreferences mu)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (P : AL16Cutoff College) : AL16Cutoff College :=
  fun c => al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos P c

/-- The source capacity best-response map is monotone. -/
theorem al16SourceCapacityBestResponse_monotone
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (hstrict : al16SourceStrictPreferences mu)
    (hcapacity_pos : ∀ c : College, 0 < capacity c) :
    Monotone (al16SourceCapacityBestResponse mu capacity hstrict hcapacity_pos) := by
  intro P Q hPQ c
  exact al16SourceCapacityThreshold_mono mu capacity hstrict hcapacity_pos hPQ c

/--
Generic A-L best-response existence shell.  A paper-specific development may
supply its own least capacity-feasible threshold operator; once that operator is
monotone, weakly feasible, and exact-filling at positive coordinates, the
Knaster--Tarski fixed point is a Definition 2 clearing cutoff.
-/
theorem al16SourceMarketClearing_nonempty_of_capacity_threshold_primitives
    (demand : AL16Cutoff College -> College -> ℝ)
    (capacity : College -> ℝ)
    (threshold : AL16Cutoff College -> College -> Set.Icc (0 : ℝ) 1)
    (hthreshold_mono :
      ∀ {P Q : AL16Cutoff College}, P ≤ Q ->
        ∀ c : College, threshold P c ≤ threshold Q c)
    (hthreshold_feasible :
      ∀ P : AL16Cutoff College, ∀ c : College,
        demand (al16SourceUpdateCutoff P c (threshold P c)) c ≤ capacity c)
    (hthreshold_eq_capacity_of_pos :
      ∀ P : AL16Cutoff College, ∀ c : College,
        0 < (threshold P c : ℝ) ->
          demand (al16SourceUpdateCutoff P c (threshold P c)) c = capacity c) :
    ∃ P : AL16Cutoff College,
      al16SourceMarketClearing demand capacity P := by
  let bestResponse : AL16Cutoff College -> AL16Cutoff College :=
    fun P c => threshold P c
  have hbest_mono : Monotone bestResponse := by
    intro P Q hPQ c
    exact hthreshold_mono hPQ c
  let F : AL16Cutoff College →o AL16Cutoff College :=
    ⟨bestResponse, hbest_mono⟩
  let P : AL16Cutoff College := F.lfp
  have hfixed : bestResponse P = P := F.map_lfp
  have hcoordinate (c : College) : threshold P c = P c := by
    simpa [bestResponse] using congr_fun hfixed c
  have hupdate (c : College) :
      al16SourceUpdateCutoff P c (threshold P c) = P := by
    funext d
    by_cases hdc : d = c
    · subst d
      simpa [al16SourceUpdateCutoff] using hcoordinate c
    · rw [al16SourceUpdateCutoff_apply_of_ne P c d _ hdc]
  refine ⟨P, ?_⟩
  constructor
  · intro c
    rw [← hupdate c]
    exact hthreshold_feasible P c
  · intro c hpos
    have hthreshold_pos : 0 < (threshold P c : ℝ) := by
      rw [hcoordinate c]
      simpa [al16CutoffValue] using hpos
    rw [← hupdate c]
    exact hthreshold_eq_capacity_of_pos P c hthreshold_pos

/-- The capacity best-response map as the order morphism used for Knaster--Tarski. -/
noncomputable def al16SourceCapacityBestResponseOrderHom
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (hstrict : al16SourceStrictPreferences mu)
    (hcapacity_pos : ∀ c : College, 0 < capacity c) :
    AL16Cutoff College →o AL16Cutoff College :=
  ⟨al16SourceCapacityBestResponse mu capacity hstrict hcapacity_pos,
    al16SourceCapacityBestResponse_monotone mu capacity hstrict hcapacity_pos⟩

/-- A concrete least fixed point of the source capacity best-response map. -/
noncomputable def al16SourceMarketClearingWitness
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (hstrict : al16SourceStrictPreferences mu)
    (hcapacity_pos : ∀ c : College, 0 < capacity c) : AL16Cutoff College :=
  (al16SourceCapacityBestResponseOrderHom mu capacity hstrict hcapacity_pos).lfp

/-- The clearing witness is a fixed point of the capacity best-response map. -/
theorem al16SourceMarketClearingWitness_fixed
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (hstrict : al16SourceStrictPreferences mu)
    (hcapacity_pos : ∀ c : College, 0 < capacity c) :
    al16SourceCapacityBestResponse mu capacity hstrict hcapacity_pos
      (al16SourceMarketClearingWitness mu capacity hstrict hcapacity_pos) =
      al16SourceMarketClearingWitness mu capacity hstrict hcapacity_pos := by
  exact (al16SourceCapacityBestResponseOrderHom mu capacity hstrict hcapacity_pos).map_lfp

/-- The Knaster--Tarski witness satisfies the source's Definition 2 clearing clauses. -/
theorem al16SourceMarketClearingWitness_marketClearing
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (hstrict : al16SourceStrictPreferences mu)
    (hcapacity_pos : ∀ c : College, 0 < capacity c) :
    al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity
      (al16SourceMarketClearingWitness mu capacity hstrict hcapacity_pos) := by
  let P : AL16Cutoff College :=
    al16SourceMarketClearingWitness mu capacity hstrict hcapacity_pos
  have hfixed : al16SourceCapacityBestResponse mu capacity hstrict hcapacity_pos P = P :=
    al16SourceMarketClearingWitness_fixed mu capacity hstrict hcapacity_pos
  have hcoordinate (c : College) :
      al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos P c = P c := by
    simpa only [al16SourceCapacityBestResponse] using congr_fun hfixed c
  change al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity P
  have hupdate (c : College) :
      al16SourceUpdateCutoff P c
        (al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos P c) = P := by
    funext d
    by_cases hdc : d = c
    · subst d
      simpa [al16SourceUpdateCutoff] using hcoordinate c
    · rw [al16SourceUpdateCutoff_apply_of_ne P c d _ hdc]
  constructor
  · intro c
    rw [← hupdate c]
    exact al16SourceCapacityThreshold_feasible mu capacity hstrict hcapacity_pos P c
  · intro c hpos
    have hthreshold_pos :
        0 < (al16SourceCapacityThreshold mu capacity hstrict hcapacity_pos P c : ℝ) := by
      rw [hcoordinate c]
      simpa [al16CutoffValue] using hpos
    rw [← hupdate c]
    exact al16SourceCapacityThreshold_eq_capacity_of_pos
      mu capacity hstrict hcapacity_pos P c hthreshold_pos

/-- Corollary A1's source clearing-existence consequence for the literal continuum model. -/
theorem al16SourceMarketClearing_nonempty_of_concrete_continuum_primitives
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (hstrict : al16SourceStrictPreferences mu) :
    ∃ P : AL16Cutoff College,
      al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity P :=
  ⟨al16SourceMarketClearingWitness mu capacity hstrict hcapacity_pos,
    al16SourceMarketClearingWitness_marketClearing mu capacity hstrict hcapacity_pos⟩

/-- The complete Theorem A1 conclusion for the literal continuum source model. -/
theorem al16TheoremA1_of_concrete_continuum_primitives
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (hstrict : al16SourceStrictPreferences mu) :
    (∃ P : AL16Cutoff College,
      al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity P) ∧
      CompleteLatticeOn (al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity)
        al16CutoffLe :=
by
  let hnonempty := al16SourceMarketClearing_nonempty_of_concrete_continuum_primitives
    mu capacity hcapacity_pos hstrict
  exact ⟨hnonempty,
    al16SourceMarketClearing_completeLattice_of_concrete_continuum_primitives
      mu capacity hstrict hnonempty⟩

end AL16SupplyDemandMatching
