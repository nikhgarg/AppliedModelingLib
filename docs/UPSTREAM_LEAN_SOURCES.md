# Potential Upstream Lean Sources

This note records Lean repositories that agents may scout before creating new
`AppliedModelingLib` APIs. Not every source listed here is a dependency. Treat these as
places to inspect for definitions, theorem shapes, proof patterns, and possible
small imports; only add a Lake dependency after checking toolchain
compatibility, license fit, API stability, and user approval.

If an agent uses or ports material from any upstream source, cite it. This
includes copied or translated definitions, theorem statements, proof structure,
module organization, or nontrivial proof ideas. Record the repository URL,
file/module path, commit or release when available, license status, and what
was reused. Put this provenance near the resulting Lean code or in the relevant
paper/formalization plan; also add a bibliography or documentation citation
when the reuse affects human-facing paper text.

## Current Imported Sources

- Mathlib: the main mathematical upstream, pinned in `lake-manifest.json` at
  [`5450b53e5ddc75d46418fabb605edbf36bd0beb6`](https://github.com/leanprover-community/mathlib4/tree/5450b53e5ddc75d46418fabb605edbf36bd0beb6)
  under Apache-2.0. Search it first for standard structures, algebra, order,
  topology, probability, measure, optimization, and analysis facts. The
  reusable finite-cover empirical-mean bridge in
  `AppliedModelingLib/Foundations/Probability/UniformHoeffding.lean` directly
  composes the local finite-class wrapper with Mathlib's
  [`HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/SubGaussian.html#ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun)
  from
  [`Mathlib/Probability/Moments/SubGaussian.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/Moments/SubGaussian.lean),
  imported unchanged under Mathlib's Apache-2.0 license.  No upstream proof
  text is copied or ported: the local result proves the finite-cover transfer
  from explicit empirical and population approximation hypotheses, its affine
  bounded-interval (`[a,b]`, hence `[0,B]`) IID-score normalization bridge,
  and the deterministic pointwise-to-mean cover lemmas locally.
  The non-finite pointwise-envelope layer additionally composes Mathlib's
  [`le_csSup` and `csSup_le`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean)
  at that same pinned Apache-2.0 revision.  Its boundedness and stability
  arguments are local; no upstream proof text is copied or ported.
  Its countable measurable near-maximizer selector additionally composes
  [`measurable_find`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Constructions.html#measurable_find)
  and
  [`measurable_from_prod_countable_right`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Constructions.html#measurable_from_prod_countable_right)
  from
  [`Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean),
  at that same Apache-2.0 revision.  The Mathlib APIs are imported unchanged;
  the local theorem only proves their action-valued composition, and no
  upstream proof text is copied or ported.
  Its separable-continuous selector specialization additionally uses
  [`TopologicalSpace.denseSeq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Bases.html#TopologicalSpace.denseSeq),
  [`DenseRange.exists_mem_open`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Continuous.html#DenseRange.exists_mem_open),
  and
  [`lt_csSup_iff`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/ConditionallyCompleteLattice/Basic.html#lt_csSup_iff)
  from the corresponding
  [`Topology/Bases.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/Bases.lean),
  [`Topology/Continuous.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/Continuous.lean),
  and conditional-complete-order Mathlib files at the same Apache-2.0 pin.
  The dense-sequence near-maximizer proof is local; no upstream proof text is
  copied or ported.  Its penalty-convexity extension uses Mathlib's
  [`ConvexOn`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Convex/Function.lean#L54)
  and [`convex_Ici`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Convex/Basic.lean#L251)
  from `Mathlib/Analysis/Convex/Function.lean` and
  `Mathlib/Analysis/Convex/Basic.lean` at the same pinned Apache-2.0 revision.
  Those APIs are imported unchanged; the local affine pointwise-supremum proof
  is new and copies no upstream proof text.
  The SNVD17 zero-neighborhood penalty bridge additionally composes
  [`exists_nat_one_div_lt`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/Archimedean/Basic.lean#L213),
  [`tendsto_atTop_ciSup`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/Order/MonotoneConvergence.lean#L116),
  and
  [`integral_tendsto_of_tendsto_of_monotone`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L782)
  from the cited Mathlib revision, under the same Apache-2.0 license.  These
  APIs are imported unchanged; the inverse-penalty construction, pointwise
  envelope argument, and finite-parameter concentration bracket are local and
  copy no upstream proof text.
  The SNVD17 positive-interval floor grid directly uses
  [`Nat.floor_le`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/Floor/Semiring.lean#L47),
  [`Nat.lt_floor_add_one`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/Floor/Semiring.lean#L65),
  and
  [`Nat.floor_le_floor`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/Floor/Semiring.lean#L95),
  again at that pinned Apache-2.0 revision.  The finite interval grid and its
  concentration specialization are local and copy no upstream proof text.
  The real-cost weak-DRO transport bridge in
  `AppliedModelingLib/Foundations/Probability/MeasureTransport.lean` directly
  uses [`exists_lt_of_csInf_lt`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean)
  and [`le_of_forall_pos_le_add`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/Field/Basic.lean),
  together with `integral_mono`, `integral_add`, and `integral_const_mul` from
  [`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean)
  and `Integrable.of_bound` from
  [`Mathlib/MeasureTheory/Integral/IntegrableOn.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/IntegrableOn.lean).
  These Apache-2.0 primitives are imported unchanged; the real-cost coupling
  interface, epsilon argument, and paper application are local and copy no
  upstream proof text.
  Its selector-to-coupling and penalized-supremum extension additionally uses
  [`integral_map`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean)
  and
  [`integrable_map_measure`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean)
  at the same pinned Apache-2.0 revision.  Those unchanged Mathlib APIs only
  transfer integration and integrability through a measurable map; the local
  reversed-graph, finite-cost-coupling, and selector/upper-envelope proofs are
  new and no upstream proof text is copied or ported.
  Its unrestricted zero-penalty value additionally composes
  [`integral_dirac'`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner/Basic.html#MeasureTheory.integral_dirac')
  and `le_csSup`/`csSup_le` from the same pinned Mathlib files.  These
  Apache-2.0 APIs are imported unchanged; the local zero-penalty convention
  and expected-loss supremum proof are new and copy no upstream proof text.
  Its constrained real-transport-ball value and diagonal feasibility bridge
  additionally use the same `csSup_le`, plus
  [`integrable_map_measure`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean)
  and
  [`integral_map`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean)
  at that pinned Apache-2.0 revision.  The transport-ball supremum,
  finite-domain condition, diagonal coupling, and weak-duality argument are
  local; no external Lean proof text is copied or ported.
  The
  LBG22 Strategic Ranking Proposition B.2 source-family check directly reuses
  `strictConvexOn_pow` from
  [`Mathlib/Analysis/Convex/SpecificFunctions/Deriv.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Convex/SpecificFunctions/Deriv.lean#L43)
  ([API documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convex/SpecificFunctions/Deriv.html#strictConvexOn_pow))
  and `integral_id` from
  [`Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean#L201)
  ([API documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.html#integral_id));
  both are imported unchanged under Mathlib's Apache-2.0 license. The
  Fournier--Guillin compact-confidence schedule directly imports
  [`Mathlib/Analysis/Complex/ExponentialBounds.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Complex/ExponentialBounds.lean)
  for `Real.exp_one_gt_two`; its noncompact transport bridge directly uses
  `ProbabilityMeasure.map`/`ProbabilityMeasure.toMeasure_map` from
  [`Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean)
  and `Measure.map_map` from
  [`Mathlib/MeasureTheory/Measure/Map.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Map.lean),
  plus `ENNReal.mul_iInf` and `lintegral_const_mul` from
  [`Mathlib/Data/ENNReal/Inv.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/ENNReal/Inv.lean)
  and
  [`Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean).
  The reusable independent-residual transport bound additionally uses that
  same `lintegral_add_left` together with the local coupling-marginal
  integration lemmas; it bounds the product-coupling cost by its two radial
  first moments without importing an additional upstream project.
  The Euclidean truncation instance additionally uses `PiLp.norm_apply_le`
  and `PiLp.smul_apply` from
  [`Mathlib/Analysis/Normed/Lp/PiLp.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Normed/Lp/PiLp.lean),
  `LipschitzWith.of_dist_le_mul` from
  [`Mathlib/Topology/EMetricSpace/Lipschitz.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/EMetricSpace/Lipschitz.lean),
  and `lintegral_indicator` from
  [`Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean).
  Its exponential outer-tail lift directly uses `integral_indicator` from
  [`Mathlib/MeasureTheory/Integral/Bochner/Set.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Set.lean),
  `integral_const_mul`, `integral_mono_ae`, and
  `ofReal_integral_eq_lintegral_ofReal` from
  [`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean),
  and `Integrable.indicator` from
  [`Mathlib/MeasureTheory/Integral/IntegrableOn.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/IntegrableOn.lean).
  The strict-tail probability conversion additionally uses
  `ENNReal.toReal_mono` from
  [`Mathlib/Data/ENNReal/Real.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/ENNReal/Real.lean)
  and `ENNReal.toReal_ofReal` from
  [`Mathlib/Data/ENNReal/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/ENNReal/Basic.lean).
  Empirical-law pushforwards directly reuse `PMF.map_comp` and
  `PMF.toMeasure_map` from
  [`Mathlib/Probability/ProbabilityMassFunction/Constructions.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean).
  The Fournier--Guillin sharp-shell geometry directly reuses
  `FiniteMeasure.restrict` from
  [`Mathlib/MeasureTheory/Measure/FiniteMeasure.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean)
  and `FiniteMeasure.normalize` with
  `toMeasure_normalize_eq_of_nonzero` and
  `self_eq_mass_smul_normalize` from
  [`Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean),
  retaining its zero-mass totalization explicitly rather than treating it as
  a conditional-law certificate. The latter resynthesis lemma gives the
  checked countable identity that each normalized source shell, weighted by
  its actual mass, reconstructs the original law. Its per-shell radial-tail bound directly
  uses `measureReal_mono` from
  [`Mathlib/MeasureTheory/Measure/Real.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Real.lean).
  The exact half-open cube-shell geometry additionally uses
  `measurableSet_Ioc`, `MeasurableSet.iInter`, and `Measurable.subtype_mk`
  from, respectively,
  [`Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean),
  [`Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/MeasurableSpace/Defs.lean),
  and
  [`Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean).
  Its countable source-shell decomposition directly reuses
  `Measure.restrict_iUnion` from
  [`Mathlib/MeasureTheory/Measure/Restrict.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Restrict.lean).
  The positive-mass shell first-moment bound additionally uses
  `ae_restrict_mem` from that Restrict module and `lintegral_mono_ae` with
  `lintegral_const` from the already credited
  [`Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean).
  The associated shell-mass normalization directly uses `Measure.sum_apply`
  from
  [`Mathlib/MeasureTheory/Measure/MeasureSpace.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/MeasureSpace.lean).
  The reusable countable mixture layer directly uses that same
  `Measure.sum_apply`, along with `Measure.map_sum` from
  [`Mathlib/MeasureTheory/Measure/AEMeasurable.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/AEMeasurable.lean)
  and `Measure.map_smul` from the already credited
  [`Mathlib/MeasureTheory/Measure/Map.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Map.lean).
  Its one-residual/countable-family normalization additionally uses
  `ENNReal.tsum_sigma'`, `ENNReal.tsum_mul_left`, and `ENNReal.tsum_add` from
  [`Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean),
  together with `ENNReal.inv_mul_cancel` and `ENNReal.mul_div_cancel` from
  [`Mathlib/Data/ENNReal/Inv.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/ENNReal/Inv.lean).
  Its finite empirical-component selection layer additionally uses
  `ENNReal.iInf_sum` from
  [`Mathlib/Data/ENNReal/BigOperators.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/ENNReal/BigOperators.lean),
  `ENNReal.mul_iInf` from the already credited
  [`Mathlib/Data/ENNReal/Inv.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/ENNReal/Inv.lean),
  `tsum_eq_sum` from
  [`Mathlib/Topology/Algebra/InfiniteSum/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean),
  `ProbabilityMeasure.apply_le_one` from the already credited
  [`Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean),
  and `Finset.sum_coe_sort` from
  [`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean).
  The empirical shell-support bridge additionally uses `Finset.image` and
  `Finset.mem_image` from
  [`Mathlib/Data/Finset/Image.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/Finset/Image.lean),
  and `Nat.find`/`Nat.find_spec` from
  [`Mathlib/Data/Nat/Find.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/Nat/Find.lean); its generic
  finite-empirical-support lemma uses `PMF.toMeasure_map` from
  [`Mathlib/Probability/ProbabilityMassFunction/Constructions.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean)
  and `Measure.map_apply` from the already credited
  [`Mathlib/MeasureTheory/Measure/Map.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Map.lean).
  The empirical-restriction/reindexing seam additionally uses
  `PMF.toMeasure_map_apply` from the already credited
  [`Mathlib/Probability/ProbabilityMassFunction/Constructions.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean),
  `PMF.toMeasure_uniformOfFintype_apply` from
  [`Mathlib/Probability/Distributions/Uniform.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/Distributions/Uniform.lean),
  `FiniteMeasure.normalize_eq_of_nonzero`, `restrict_mass`, and
  `restrict_apply` from the already credited
  [`Mathlib/MeasureTheory/Measure/FiniteMeasure.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean),
  and `Fintype.card_of_subtype` from
  [`Mathlib/Data/Fintype/Card.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/Fintype/Card.lean).
  `EmpiricalMeasure.lean` uses these exact pinned Apache-2.0 declarations to
  prove that a normalized nonempty measurable restriction of an empirical law
  is the empirical law of its selected observations. No external Lean source
  beyond Mathlib is imported, copied, or ported for this reindexing proof.
  The fixed-membership conditional-IID seam in `FiniteIID.lean` directly uses
  `ProbabilityTheory.iIndepFun.cond`, `cond_iInter`, and
  `iIndepFun_iff_map_fun_eq_pi_map` from
  [`Mathlib/Probability/Independence/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/Independence/Basic.lean),
  together with `cond_apply` and `cond_isProbabilityMeasure` from
  [`Mathlib/Probability/ConditionalProbability.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/ConditionalProbability.lean).
  These exact Mathlib declarations prove that, conditioned on any positive
  fixed in/out membership pattern, the selected coordinates have the product
  law of the source law conditioned on the selected set. The completed
  fixed-cardinality reindexing theorem additionally directly uses
  `MeasurableEquiv.piCongrLeft` and `Measure.pi_map_piCongrLeft` from
  [`Mathlib/MeasureTheory/Constructions/Pi.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Constructions/Pi.lean),
  along with `Fintype.equivFin`/`Fintype.card_coe` from
  [`Mathlib/Data/Fintype/EquivFin.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/Fintype/EquivFin.lean)
  and `finCongr` from
  [`Mathlib/Data/Fin/SuccPred.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/Fin/SuccPred.lean).
  Thus `map_finiteIIDSampleOnFinsetToFin_conditioned` gives exactly an iid
  `Fin inside.card` sample from the selected conditional law. All of these
  declarations are reused directly under the same pinned Apache-2.0 Mathlib
  license; no external Lean source is imported, copied, or ported.
  The resulting compact-shell resampling bridge additionally uses Mathlib's
  `Measure.pi_map_pi` from the already linked
  [`Mathlib/MeasureTheory/Constructions/Pi.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Constructions/Pi.lean),
  `Fintype.card_of_subtype`/`Fintype.card_congr` from
  [`Mathlib/Data/Fintype/Card.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/Fintype/Card.lean),
  and `Equiv.subtypeEquiv` from
  [`Mathlib/Logic/Equiv/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Logic/Equiv/Basic.lean).
  The shell normalization identification directly uses `ProbabilityTheory.cond`
  from the already linked
  [`Mathlib/Probability/ConditionalProbability.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/ConditionalProbability.lean)
  and `FiniteMeasure.toMeasure_normalize_eq_of_nonzero` from the already linked
  [`Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean).
  These pinned Apache-2.0 APIs establish that a positive fixed cube-shell
  membership pattern maps to the exact fixed-length iid compact-shell law;
  no external Lean source is imported, copied, or ported. The deterministic
  companion `empiricalCompactShellSample_eq_compactLaw` combines that local
  reindexing infrastructure with the already credited empirical-measure map
  and normalized-restriction declarations; it introduces no additional
  external Lean dependency or source material.
  The exact compact-coordinate shell law uses
  `MeasurableEmbedding.exists_measurable_extend` from
  [`Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean)
  and `FiniteMeasure.map` from the already credited
  [`Mathlib/MeasureTheory/Measure/FiniteMeasure.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean).
  Its scale-back contraction directly uses `LipschitzWith.of_dist_le_mul` from
  [`Mathlib/Topology/EMetricSpace/Lipschitz.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/EMetricSpace/Lipschitz.lean).
  Its exact normalized shell-law reconstruction additionally uses
  `Measure.map_congr` and `Measure.map_id` from the already credited
  [`Mathlib/MeasureTheory/Measure/Map.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Map.lean).
  Its exhaustive-cover proof directly uses
  `tendsto_pow_atTop_atTop_of_one_lt` and `PiLp.norm_apply_le` from
  [`Mathlib/Analysis/SpecificLimits/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecificLimits/Basic.lean)
  and
  [`Mathlib/Analysis/Normed/Lp/PiLp.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Normed/Lp/PiLp.lean),
  respectively.  The source-cube-to-Euclidean-radius bound additionally
  directly uses `PiLp.norm_sq_eq_of_L2` from that same Apache-2.0 PiLp module;
  it exposes the necessary `sqrt dimension` metric-convention factor.
  The reusable real-valued non-strict radial Markov tail directly uses
  `ENNReal.toReal_mono` and `ENNReal.toReal_ofReal` from
  [`Mathlib/Data/ENNReal/Real.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/ENNReal/Real.lean)
  and
  [`Mathlib/Data/ENNReal/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/ENNReal/Basic.lean).
  The explicit critical-dimensional selected-shell selector directly uses
  Mathlib's `Real.log_natCast_le_rpow_div` from
  [`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean#L896)
  ([API documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Pow/Real.html#Real.log_natCast_le_rpow_div)).
  It converts the logarithmic dyadic depth into a conservative quarter-power
  rate and hence a visible fourth-power count gate in dimension two.  The
  theorem is imported unchanged at the pinned Mathlib commit under Apache-2.0;
  the remaining depth and real-power argument is local, and no Mathlib source
  is copied or ported.
  No source text is copied or ported. This license requires preservation of
  its copyright and license notices on redistribution.
- CSLib: the current computer-science upstream dependency. See
  [`CSLIB_COMPATIBILITY_NOTES.md`](CSLIB_COMPATIBILITY_NOTES.md) for pinned
  version, import boundaries, and known useful modules.
- Optlib: scout when it exists in the workspace or Lake manifest for
  optimization-specific APIs.
- [`Hydrodynamical/Vlasov_Meanfield_Formalization`](https://github.com/Hydrodynamical/Vlasov_Meanfield_Formalization)
  is an immutable direct Lake dependency at commit
  [`b2eda09e58ceebad6cf23b8a7a6839001d4e7c15`](https://github.com/Hydrodynamical/Vlasov_Meanfield_Formalization/tree/b2eda09e58ceebad6cf23b8a7a6839001d4e7c15),
  loaded from its `Vlasov/` subpackage. `Vlasov/OT/Wasserstein.lean` and
  `Vlasov/OT/Coupling.lean` provide the W₁ Kantorovich--Rubinstein dual and
  coupling formulations and their equality. The dependency is Apache-2.0;
  its repository `LICENSE` is retained in the Lake checkout and it has no
  `NOTICE` file. Redistribution must retain the license and attribution;
  modified upstream files would also need prominent change notices. We import
  the files unchanged, so no upstream source text is copied or modified here.
  Although upstream pins Lean 4.29.1, both files compile unchanged against this
  repository's Lean 4.30.0-rc2/Mathlib checkout. Searches found no
  `sorry`/`admit`/`axiom` in either file, and `#print axioms` for
  `Vlasov.wasserstein1_eq_coupling` and
  `Vlasov.wassersteinCost_coupling_le_dual` reports only `propext`,
  `Classical.choice`, and `Quot.sound`. The local reusable module
  `AppliedModelingLib/Foundations/Probability/MetricPartitionTransport.lean` proves
  equality between the local and upstream primal coupling infima, then invokes
  `Vlasov.wasserstein1_eq_iSup_lipschitz`,
  `Vlasov.wasserstein1_eq_coupling`, and
  `Vlasov.wassersteinCost_coupling_comm`, and
  `Vlasov.wassersteinCost_coupling_triangle` to obtain its finite-hierarchy
  W₁ bound, local primal symmetry, and the local primal triangle inequality;
  that module carries the exact declaration/file links and Mathlib provenance.
- The SNVD17 unbounded-penalty tail bridge directly uses Mathlib's
  [`ciInf_le`/`le_ciInf`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean#L181),
  [`Measurable.iInf`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean#L912),
  [`tendsto_atTop_ciInf`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/Order/MonotoneConvergence.lean#L136),
  and
  [`integral_tendsto_of_tendsto_of_antitone`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L820),
  [`Metric.tendsto_atTop`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L901),
  and
  [`Finset.le_sup`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/Finset/Lattice/Fold.lean#L118),
  all at the repository's pinned
  [`5450b53e5ddc75d46418fabb605edbf36bd0beb6`](https://github.com/leanprover-community/mathlib4/tree/5450b53e5ddc75d46418fabb605edbf36bd0beb6)
  Apache-2.0 revision.  These declarations are imported unchanged; the
  cofinal-penalty, tail-envelope, and paper-specific bracketing arguments are
  local and do not copy or port upstream proof text.
- The subsequent SNVD17 finite-family three-range composition directly uses
  Mathlib's
  [`MeasureTheory.measureReal_mono`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Real.lean#L85)
  and
  [`MeasureTheory.measureReal_union_le`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Real.lean#L134),
  at the same pinned Apache-2.0 Mathlib revision.  They are imported unchanged
  to combine paper-local penalty events; no upstream proof text or code was
  copied or ported.

## Potential Additional Sources

- [`SamuelSchlesinger/complexitylib`](https://github.com/SamuelSchlesinger/complexitylib)
  was inspected at commit
  [`58198f347a7700856b2778394da9c6b9429b729e`](https://github.com/SamuelSchlesinger/complexitylib/tree/58198f347a7700856b2778394da9c6b9429b729e)
  for the Strategic Classification 3SAT reduction. Its
  [`Complexitylib/SAT/ThreeSAT/Completeness.lean`](https://github.com/SamuelSchlesinger/complexitylib/blob/58198f347a7700856b2778394da9c6b9429b729e/Complexitylib/SAT/ThreeSAT/Completeness.lean)
  proves encoded 3SAT NP-complete on a concrete machine model. The project is
  Apache-2.0, but this revision pins Lean/Mathlib `v4.30.0` while AppliedModelingLib is
  pinned to `v4.30.0-rc2`; it is therefore not currently imported. The local
  typed `ThreeCNF` semantic layer was written independently and does not copy
  or port upstream material. A future direct dependency must first pass a full
  repository pin-upgrade regression and preserve the upstream license notice.
- [`PierreSenellart/descriptive-complexity`](https://github.com/PierreSenellart/descriptive-complexity)
  was inspected at commit
  [`2bfbb33703f10fed7350459769c1aaf03f7991e0`](https://github.com/PierreSenellart/descriptive-complexity/tree/2bfbb33703f10fed7350459769c1aaf03f7991e0).
  Its documented `ThreeSAT` completeness route uses first-order reductions on
  Mathlib model theory. It is Apache-2.0, but its available releases target
  Lean/Mathlib `v4.33.0`, so it is neither imported nor ported here.
- <https://github.com/elazarg/GameTheory>: candidate source for game-theory
  definitions, equilibrium-style theorem statements, and proof organization.
- <https://github.com/alexfleetcommander/lean-proofs>: candidate source for
  Lean proof examples and reusable proof patterns.
- <https://github.com/gametheoryinlean/EconCSLib>: independent Economics and
  Computation concept-library project. This is the preferred additional source
  for reusable Economics-and-Computation definitions and closed proofs. Search
  its relevant domain modules before introducing a new local API; reuse or port
  a compatible definition or proof when it fits. Record the exact upstream
  module, commit, Apache-2.0 license status, and any local adaptation. Its
  current Lean toolchain must still be compatible before adding it as a direct
  Lake dependency.

## Agent Workflow

Before creating a paper-local wrapper or reusable `AppliedModelingLib/` primitive for a
common proof seam:

1. Search Mathlib, CSLib, Optlib when present, and existing `AppliedModelingLib/`
   modules.
2. For overlapping game-theory, EC, social-choice, mechanism-design,
   optimization, or proof-pattern seams, also scout the potential additional
   sources above.
3. Record inspected modules, APIs chosen, near misses, and citation/provenance
   for any material used or ported in the paper's formalization plan.
4. Prefer thin bridge lemmas around existing upstream APIs when they fit. If an
   upstream source almost fits but cannot be used directly, record why before
   adding a local primitive.
