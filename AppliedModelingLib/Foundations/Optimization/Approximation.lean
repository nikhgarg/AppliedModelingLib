import Mathlib.Data.Real.Basic

namespace AppliedModelingLib
namespace Optimization

/-!
# Approximation and Competitive-Ratio Certificates

Small algebraic certificates for primal-dual and benchmark-sandwich proofs.

## Main declarations

- `UpperBoundApproximationCertificate`: if `benchmark <= upper` and
  `ratio * upper <= achieved`, then `ratio * benchmark <= achieved`.
- `UpperBoundApproximationWithErrorCertificate`: additive-error variant.
-/

/--
A multiplicative approximation/competitive-ratio certificate.

`upper` is usually a dual objective or another explicit upper bound on the
benchmark/offline optimum.
-/
structure UpperBoundApproximationCertificate
    (benchmark achieved ratio : ℝ) where
  upper : ℝ
  benchmark_le_upper : benchmark ≤ upper
  scaled_upper_le_achieved : ratio * upper ≤ achieved

namespace UpperBoundApproximationCertificate

/-- The certificate proves the multiplicative benchmark bound. -/
theorem scaled_benchmark_le_achieved
    {benchmark achieved ratio : ℝ}
    (cert : UpperBoundApproximationCertificate benchmark achieved ratio)
    (hratio : 0 ≤ ratio) :
    ratio * benchmark ≤ achieved := by
  exact le_trans (mul_le_mul_of_nonneg_left cert.benchmark_le_upper hratio)
    cert.scaled_upper_le_achieved

end UpperBoundApproximationCertificate

/--
Additive-error approximation certificate.

This is useful for finite small-bids or discretization proofs where the clean
asymptotic ratio has an explicit finite error term.
-/
structure UpperBoundApproximationWithErrorCertificate
    (benchmark achieved ratio error : ℝ) where
  upper : ℝ
  benchmark_le_upper : benchmark ≤ upper
  scaled_upper_le_achieved_add_error : ratio * upper ≤ achieved + error

namespace UpperBoundApproximationWithErrorCertificate

/-- The certificate proves the additive-error benchmark bound. -/
theorem scaled_benchmark_le_achieved_add_error
    {benchmark achieved ratio error : ℝ}
    (cert :
      UpperBoundApproximationWithErrorCertificate benchmark achieved ratio error)
    (hratio : 0 ≤ ratio) :
    ratio * benchmark ≤ achieved + error := by
  exact le_trans (mul_le_mul_of_nonneg_left cert.benchmark_le_upper hratio)
    cert.scaled_upper_le_achieved_add_error

end UpperBoundApproximationWithErrorCertificate

end Optimization
end AppliedModelingLib
