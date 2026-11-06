import Mathlib

theorem algebra_6404 (x y : ℝ)
    (h₀ : x ^ 2 - 3 * x * y + 2 * y ^ 2 + x - y = 0)
    (h₁ : x ^ 2 - 2 * x * y + y ^ 2 - 5 * x + 7 * y = 0) :
    x * y - 12 * x + 15 * y = 0 := by
  have h2 : (x - y) * (x - 2 * y + 1) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h2) with h3 h4
  · -- Case where x - y = 0, so x = y
    have h4 : x = y := by linarith
    rw [show x = y by linarith [h4]] at h₁
    have h5 : y = 0 := by nlinarith
    have h6 : x = 0 := by linarith [h4, h5]
    rw [h6, h5]
    norm_num
  · -- Case where x - 2y + 1 = 0, so x = 2y - 1
    have h5 : x = 2 * y - 1 := by linarith
    rw [h5] at h₁
    have h6 : y^2 - 5 * y + 6 = 0 := by
      nlinarith
    have h7 : (y - 2) * (y - 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h7) with h8 h9
    · -- Case where y = 2
      have hy2 : y = 2 := by linarith
      have hx3 : x = 3 := by
        linarith [h5, hy2]
      rw [hx3, hy2]
      norm_num
    · -- Case where y = 3
      have hy3 : y = 3 := by linarith
      have hx5 : x = 5 := by
        linarith [h5, hy3]
      rw [hx5, hy3]
      norm_num