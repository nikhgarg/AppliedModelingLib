import AppliedModelingLib.Foundations.Probability.Bernoulli
import AppliedModelingLib.Foundations.Probability.Conditional
import AppliedModelingLib.Foundations.Probability.FiniteAdaptiveMGF
import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import AppliedModelingLib.Foundations.Probability.FiniteDistributionalRobustness
import AppliedModelingLib.Foundations.Probability.FiniteConstrainedDistributionalRobustness
import AppliedModelingLib.Foundations.Probability.FiniteTransportMatrix
import AppliedModelingLib.Foundations.Probability.FiniteIID
import AppliedModelingLib.Foundations.Probability.FiniteIidUniformLaw
import AppliedModelingLib.Foundations.Probability.FiniteKernelProduct
import AppliedModelingLib.Foundations.Probability.FiniteKLDataProcessing
import AppliedModelingLib.Foundations.Probability.FiniteMixture
import AppliedModelingLib.Foundations.Probability.FiniteSimplex
import AppliedModelingLib.Foundations.Probability.Kernel
import AppliedModelingLib.Foundations.Probability.MeasureAtoms

/-!
# Finite probability

Curated entrypoint for finite probability spaces, finite expectations and
mixtures, finite iid samples, finite kernels, simplex representations, and
finite transport/distributionally robust optimization. This includes compact
real finite-coupling and fixed-nominal kernel polytopes with scalar Lagrange
strong duality. Import a leaf module instead when only one of these APIs is
needed.
-/
