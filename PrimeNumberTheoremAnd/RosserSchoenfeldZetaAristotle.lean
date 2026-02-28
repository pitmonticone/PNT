import Mathlib
import PrimeNumberTheoremAnd.ZetaDefinitionsAristotle

/-!
# The zeta function bounds of Rosser and Schoenfeld


-/

/-!
In this section we formalize the zeta function bounds of Rosser and Schoenfeld.

TODO: Add more results and proofs here, and reorganize the blueprint
-/

namespace RS
/-- **Rosser--Schoenfeld Theorem 19**

One has a Riemann von Mangoldt estimate with parameters 0.137, 0.443, and 1.588.
-/
theorem theorem_19 : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 1.588 := by sorry


end RS
