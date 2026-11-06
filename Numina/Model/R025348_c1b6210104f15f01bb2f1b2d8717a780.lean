import Mathlib

theorem inequalities_309232 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) :
    (x + 1 / x) * (y + 1 / y) ≥ 25 / 4 := by
  have h1 : 0 < x * y := by
    nlinarith
  have h2 : (x + 1 / x) * (y + 1 / y) = (x ^ 2 + 1) * (y ^ 2 + 1) / (x * y) := by
    field_simp
    <;> ring
  rw [h2] at *
  have h4 : (x ^ 2 + 1) * (y ^ 2 + 1) / (x * y) ≥ (25 / 4) := by
    have h5 : 0 < x * y := h1
    apply (le_div_iff₀ h5).mpr
    have h6 : y = 1 - x := by linarith
    rw [h6]
    nlinarith [sq_nonneg (x - (1 - x)), sq_nonneg (x * (1 - x) - 1 / 4), sq_nonneg (x - 1 / 2), sq_nonneg ((1 - x) - 1 / 2),
              mul_pos hx (show (0 : ℝ) < (1 - x) by nlinarith),
              mul_pos hx (show (0 : ℝ) < 1 / 4 by norm_num),
              mul_pos (show (0 : ℝ) < (1 - x) by nlinarith) (show (0 : ℝ) < 1 / 4 by norm_num),
              sq_nonneg ((x) * (1 - x) - 1 / 4), sq_nonneg (x - (1 - x)), mul_pos hx hy, mul_pos (show 0 < x * (1 - x) by nlinarith) (show 0 < x * (1 - x) by nlinarith)]
  linarith