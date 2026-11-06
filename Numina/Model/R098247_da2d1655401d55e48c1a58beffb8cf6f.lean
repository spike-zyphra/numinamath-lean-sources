import Mathlib

open Real

theorem inequalities_106603 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    4 / (x + y) ≤ 1 / x + 1 / y := by
  have h1 : 0 < x + y := by linarith
  have h2 : 0 < x * y := mul_pos hx hy
  have h3 : 4 * x * y ≤ (x + y) ^ 2 := by
    nlinarith [sq_nonneg (x - y)]
  have h4 : 4 / (x + y) ≤ 1 / x + 1 / y := by
    have h5 : 0 < x * y := mul_pos hx hy
    have h6 : 0 < x + y := by linarith
    have h7 : 4 * x * y ≤ (x + y) ^ 2 := h3
    have h8 : 4 / (x + y) - (1 / x + 1 / y) ≤ 0 := by
      have h9 : (4 / (x + y) - (1 / x + 1 / y)) = (4 * x * y - (x + y) ^ 2) / (x * y * (x + y)) := by
        field_simp
        ring
      rw [h9]
      have h10 : (4 * x * y - (x + y) ^ 2) ≤ 0 := by nlinarith
      have h11 : x * y * (x + y) > 0 := mul_pos h5 h6
      apply div_nonpos_of_nonpos_of_nonneg h10 (by linarith)
    linarith
  linarith