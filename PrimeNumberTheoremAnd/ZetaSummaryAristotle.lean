import Mathlib
import PrimeNumberTheoremAnd.ZetaDefinitionsAristotle
import PrimeNumberTheoremAnd.KLNAristotle
import PrimeNumberTheoremAnd.RosserSchoenfeldZetaAristotle
import PrimeNumberTheoremAnd.ZetaAppendixAristotle

/-!
# Summary of results
-/

/-!
Here we list some papers that we plan to incorporate into this section in the future, and list
some results that have not yet been moved into dedicated paper sections.

References to add:

MT: M. J. Mossinghoff and T. S. Trudgian, Nonnegative trigonometric polynomials and a zero-free
region for the Riemann zeta-function, J. Number Theory. 157 (2015), 329–349.

MTY: M. J. Mossinghoff, T. S. Trudgian, and A. Yang, Nonnegative trigonometric polynomials and a
zero-free region for the Riemann zeta-function, arXiv:2212.06867.
-/

-- TODO: move to separate file
/-- **Hasanalizade-Shen-Wang**

One has a Riemann von Mangoldt estimate with parameters 0.1038, 0.2573, and 9.3675.
  -
-/
theorem HSW.main_theorem : riemannZeta.Riemann_vonMangoldt_bound 0.1038 0.2573 9.3675 := sorry



-- TODO: move to separate file
/-- **MT Theorem 1**

One has a classical zero-free region with $R = 5.5666305$. (A more conservative value of $R = 5.573412$ was announced in the paper using weaker numerical verification of the Riemann hypothesis.)
-/
theorem MT_theorem_1 : riemannZeta.classicalZeroFree 5.5666305 := sorry


-- TODO: move to separate file
/-- **MTY**

One has a classical zero-free region with $R = 5.558691$.
-/
theorem MTY_theorem : riemannZeta.classicalZeroFree 5.558691 := sorry


-- TODO: move to separate file
/-- **Platt's numerical verification of RH**

The Riemann hypothesis is verified up to $H_0 = 3.061 \times 10^{10}$.
-/
theorem Platt_theorem : riemannZeta.RH_up_to 30610000000 := sorry


-- TODO: move to separate file
/-- **Gourdon-Wedeniwski**

The Riemann hypothesis is verified up to $H_0 = 2445999556030$.
-/
theorem GW_theorem : riemannZeta.RH_up_to 2445999556030 := sorry


-- TODO: move to separate file
/-- **PT Theorem 1**

The Riemann hypothesis is verified up to $H_0 = 3 \times 10^{12}$.
-/
theorem PT_theorem_1 : riemannZeta.RH_up_to 3e12 := sorry
