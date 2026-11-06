import Mathlib
open Real

/-
Suppose $x$ satisfies $x^{3}+x^{2}+x+1=0$. What are all possible values of $x^{4}+2 x^{3}+$ $2 x^{2}+2 x+1$ ?
-/
theorem algebra_610898 (x:ℝ) (h: x^3 + x^2 + x + 1 = 0): x^4 + 2*x^3 + 2*x^2 + 2*x + 1 = 0 := by
  calc
    -- The 4th power can be facotorized as a product of $(x+1)*(x^3 + x^2 + x + 1)$, thus equals to 0.
    _ = (x+1)*(x^3 + x^2 + x + 1) := by ring_nf
    _ = (x+1)* 0 := by rw[h]
    _ = 0 := by ring_nf