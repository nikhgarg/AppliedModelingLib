import AppliedModelingLib.Foundations.Probability.Gaussian

/-!
# Gaussian Hazard Inverse Interface

Small interface for papers that use the inverse normal hazard rate.

## Main declarations

- `GaussianHazardInverseCertificate`
-/

namespace AppliedModelingLib
namespace Probability

/--
Analytic certificate for an inverse of the standard-normal hazard rate.

The base `GaussianHazardCertificate` already exposes the hazard rate and its
monotonicity.  This extension adds exactly the order-theoretic inverse fact
used by admissions/testing papers that write thresholds with `HR⁻¹`.

The inverse law is restricted to positive right-hand sides.  A real-valued
hazard rate is positive, so a global equivalence
`hazard z ≤ y ↔ z ≤ hazardInv y` cannot hold for arbitrary nonpositive `y`.
-/
structure GaussianHazardInverseCertificate extends GaussianHazardCertificate where
  hazardInv : ℝ → ℝ
  hazard_le_iff_le_inv : ∀ {z y : ℝ}, 0 < y → (hazard z ≤ y ↔ z ≤ hazardInv y)

end Probability
end AppliedModelingLib
