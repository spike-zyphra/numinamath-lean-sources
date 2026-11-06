import Mathlib

/-
What is the value of
$(2^{0} − 1 + 5^{2} − 0)^{−1} \times 5$?
-/
theorem algebra_95094 : ((2^0 - 1 + 5^2 - 0 : ℝ)^(-1 : ℝ) * 5) = 1 / 5 := by
  -- Since this problem is purely numerical, we can just use
  -- the `ring` tactic from MathLib to compute it.
  ring