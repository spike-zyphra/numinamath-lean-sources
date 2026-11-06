import Mathlib

theorem algebra_10267 {x : ℝ} (hx : (x - 4)^3 = (1 / 8 : ℝ)^(-1 : ℤ)) : x = 6 := by
  have h1 : (1 / 8 : ℝ) ^ (-1 : ℤ) = 8 := by
    norm_num
  rw [h1] at hx
  have h2 : (x - 4) ^ 3 - 8 = 0 := by linarith
  have h3 : (x - 4 - 2) * ((x - 4) ^ 2 + (x - 4) * 2 + 4) = 0 := by
    ring_nf at h2 ⊢
    <;> nlinarith
  cases' (mul_eq_zero.1 h3) with h4 h5
  · linarith
  · have h6 : (x - 4) ^ 2 + (x - 4) * 2 + 4 > 0 := by
      nlinarith [sq_nonneg (x - 4), sq_nonneg (x - 4 + 1)]
    linarith