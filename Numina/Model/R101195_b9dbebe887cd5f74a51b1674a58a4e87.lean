import Mathlib

theorem algebra_182628 (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (x * y + 2 * y * z) / (x ^ 2 + y ^ 2 + z ^ 2) ≤ Real.sqrt 5 / 2 := by
  have h1 : x^2 + y^2 + z^2 > 0 := by
    have h1 : x^2 > 0 := sq_pos_of_ne_zero hx
    have h2 : y^2 > 0 := sq_pos_of_ne_zero hy
    have h3 : z^2 > 0 := sq_pos_of_ne_zero hz
    linarith
  have h3 : (x * y + 2 * y * z) ≤ Real.sqrt 5 / 2 * (x^2 + y^2 + z^2) := by
    nlinarith [sq_nonneg (x - Real.sqrt 5 * y / 5), sq_nonneg (z - 2 * Real.sqrt 5 * y / 5),
      Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num)]
  have h4 : (x * y + 2 * y * z) / (x^2 + y^2 + z^2) ≤ Real.sqrt 5 / 2 := by
    have h5 : x^2 + y^2 + z^2 > 0 := h1
    apply (div_le_iff₀' h5).mpr
    linarith
  exact h4