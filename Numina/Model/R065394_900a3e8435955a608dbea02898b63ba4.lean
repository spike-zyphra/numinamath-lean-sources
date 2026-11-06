import Mathlib

/- Given positive real numbers $a$, $b$ satisfy the system of equations $\left\{\begin{array}{c} a+b^{2}+ab=5 \\ a^{2}+b+ab=7 \end{array}\right.$, then the value of $a+b$ is ___          ___. -/
theorem algebra_8050 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
(h1 : a + b^2 + a * b = 5) (h2 : a^2 + b + a * b = 7) :
a + b = 3 := by
  have h3 : (a + b)^2 + (a + b) - 12 = 0 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]
  have h4 : (a + b - 3) * (a + b + 4) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h4) with h5 h6
  · -- Case where a + b - 3 = 0, hence a + b = 3
    linarith
  · -- Case where a + b + 4 = 0, hence a + b = -4, which contradicts a + b > 0
    nlinarith [show 0 < a + b from add_pos ha hb]