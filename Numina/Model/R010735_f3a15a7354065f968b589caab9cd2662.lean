import Mathlib

/-prove that
$\frac{1995}{2}-\frac{1994}{3}+\frac{1993}{4}-\cdots-\frac{2}{1995}+\frac{1}{1996}
=\frac{1}{999}+\frac{3}{1000}+\cdots+\frac{1995}{1996} .$-/
open Finset Real Nat

theorem number_theory_241558: (∑ k ∈ Icc 1 1996, (-1) ^ (k + (1: ℤ)) * (((1997:ℚ) / (k + 1)) - 1))
= (∑ k ∈ Icc 1 (998: ℤ), ( ((2 * k + 1996): ℚ) / (998 + k) - (1997: ℚ) / (998 + k) ) ) := by
  native_decide