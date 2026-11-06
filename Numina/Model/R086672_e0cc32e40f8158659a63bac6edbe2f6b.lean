import Mathlib

theorem algebra_242285 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : x / y = (x + y) / (x - y)) : x / y = (1 + Real.sqrt 2) := by
  have h1 : y ≠ 0 := by linarith
  have h2 : x - y ≠ 0 := by
    by_contra h3
    have h4 : x = y := by linarith
    rw [h4] at h
    field_simp [h1] at h ⊢
    all_goals linarith
  have h3 : x / y = (x + y) / (x - y) := h
  have h4 : x * (x - y) = y * (x + y) := by
    field_simp [h1, h2] at h3 ⊢
    linarith
  have h5 : x ^ 2 - 2 * x * y - y ^ 2 = 0 := by
    nlinarith [h4]
  have h6 : (x / y) ^ 2 - 2 * (x / y) - 1 = 0 := by
    have h7 : x ^ 2 - 2 * x * y - y ^ 2 = 0 := h5
    field_simp [h1] at h7 ⊢
    nlinarith
  have h7 : (x / y - (1 + Real.sqrt 2)) * (x / y - (1 - Real.sqrt 2)) = 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), h6]
  cases' (mul_eq_zero.mp h7) with h8 h9
  · -- x/y = 1 + sqrt(2)
    linarith
  · -- x/y = 1 - sqrt(2)
    have h10 : Real.sqrt 2 > (1 : ℝ) := Real.lt_sqrt_of_sq_lt (by norm_num)
    have h11 : (1 : ℝ) - Real.sqrt 2 < 0 := by linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    have h12 : x / y > 0 := by positivity
    have h13 : x / y < 0 := by linarith
    linarith