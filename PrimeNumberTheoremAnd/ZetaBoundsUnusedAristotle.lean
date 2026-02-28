import Mathlib
import PrimeNumberTheoremAnd.ZetaBoundsAristotle

open Complex Filter Set
local notation (name := riemannzeta2) "ζ" => riemannZeta
local notation (name := derivriemannzeta2) "ζ'" => deriv riemannZeta

/-!
It would perhaps (?) be better to refactor this entire file so that we're not using explicit
constants but instead systematically using big Oh notation... The punchline would be:
-/
/-- **LogDerivZetaBndAlt**

There is an $A>0$ so that for $1-A/\log^9 |t| \le \sigma < 1$ and $|t|\to\infty$,
    $$
    |\frac {\zeta'}{\zeta} (\sigma+it)| \ll \log^9 |t|.
    $$
    (Same statement but using big-Oh and filters.)

PROVIDED SOLUTION:
Same as above.
-/
lemma LogDerivZetaBndAlt :
    ∃ A > 0, ∀ (σ) (_ : σ ∈ Ico ((1 : ℝ) / 2) (1 : ℝ)),
    (fun (t : ℝ) ↦ ζ' (σ + t * I) / ζ (σ + t * I)) =O[cocompact ℝ ⊓
      Filter.principal {t | 1 - A / Real.log |t| ^ 9 < σ}]
        fun t ↦ Real.log |t| ^ 9 := by
  admit