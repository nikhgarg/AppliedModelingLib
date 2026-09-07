import AppliedModelingLib.Foundations
import AppliedModelingLib.Algorithms
import AppliedModelingLib.Learning.Statistics
import AppliedModelingLib.Learning.Bandits
import AppliedModelingLib.MechanismDesign
import AppliedModelingLib.SocialChoice
import AppliedModelingLib.Markets
import AppliedModelingLib.Applications

/-!
# AppliedModelingLib Shared Prelude

This file is a broad compatibility prelude for reusable library development and
paper-facing proofs. It centralizes common `import`s and namespace defaults for
interactive work and historical clients. New library modules and paper
interfaces should prefer the smallest documented family facade or leaf import.

## Main declarations

- `AppliedModelingLib.Basic`: imports a broad reusable surface used across the library.
- Shared namespace defaults (`open scoped BigOperators`) for concise theorem scripts.
- Curated family imports for algorithms, statistics, bandits, mechanisms,
  social choice, markets, and applications.
- Admissions policy/equilibrium surfaces used by testing, matching, and
  strategic admissions formalizations.
-/

open scoped BigOperators
