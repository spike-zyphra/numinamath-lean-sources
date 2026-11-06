import Mathlib

theorem inequalities_279368 (x y : ℝ) (hx : abs x < 1) (hy : abs y < 1) :
    1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) ≥ 2 / (1 - x * y) := by
  have h1 : -1 < x := by
    linarith [abs_lt.mp hx]
  have h2 : x < 1 := by
    linarith [abs_lt.mp hx]
  have h3 : -1 < y := by
    linarith [abs_lt.mp hy]
  have h4 : y < 1 := by
    linarith [abs_lt.mp hy]
  have h5 : 1 - x ^ 2 > 0 := by
    nlinarith
  have h6 : 1 - y ^ 2 > 0 := by
    nlinarith
  have h7 : 1 - x * y > 0 := by
    nlinarith [abs_lt.mp hx, abs_lt.mp hy, mul_pos (show (0 : ℝ) < 1 - x by nlinarith) (show (0 : ℝ) < 1 - y by nlinarith), sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (x - y)]
  have h8 : 1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) - 2 / (1 - x * y) ≥ 0 := by
    have pos1 : 0 < (1 - x ^ 2 : ℝ) := h5
    have pos2 : 0 < (1 - y ^ 2 : ℝ) := h6
    have pos3 : 0 < (1 - x * y : ℝ) := h7
    have h9 : (1 - y ^ 2) * (1 - x * y) + (1 - x ^ 2) * (1 - x * y) - 2 * (1 - x ^ 2) * (1 - y ^ 2) ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - x * y), sq_nonneg (x + y), sq_nonneg (x * y), mul_pos (show (0 : ℝ) < 1 - x by nlinarith) (show (0 : ℝ) < 1 - y by nlinarith), mul_pos (show (0 : ℝ) < 1 + x by nlinarith) (show (0 : ℝ) < 1 + y by nlinarith)]
    have h10 : (1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) - 2 / (1 - x * y)) =
        ((1 - y^2) * (1 - x * y) + (1 - x^2) * (1 - x * y) - 2 * (1 - x^2) * (1 - y^2)) / ((1 - x ^ 2) * (1 - y ^ 2) * (1 - x * y)) := by
      field_simp
      <;> ring
    rw [h10] at *
    apply div_nonneg
    linarith [h9]
    positivity
  linarith