import Mathlib

theorem algebra_10605 (x y : ℝ) (h₀ : |y| = 12) (h₁ : Real.sqrt ((x - 1)^2 + (y - 6)^2) = 10)
    (h₂ : x > 1) :
    Real.sqrt (x^2 + y^2) = 15 := by
  have h1 : (x - 1) ^ 2 + (y - 6) ^ 2 = 100 := by
    have h3 : Real.sqrt ((x - 1)^2 + (y - 6)^2) = 10 := h₁
    have h4 : (Real.sqrt ((x - 1)^2 + (y - 6)^2)) ^ 2 = (10 : ℝ) ^ 2 := by
      rw [h3]
    rw [Real.sq_sqrt (by positivity)] at h4
    nlinarith
  cases eq_or_eq_neg_of_abs_eq h₀ with
  | inl hy12 =>
    have h2 : y = 12 := hy12
    rw [h2] at h1
    have h5 : x = 9 := by
      nlinarith [sq_nonneg (x - 9), sq_nonneg (x + 7)]
    have h6 : x^2 + y^2 = 225 := by
      rw [h5, h2]
      norm_num
    have h7 : Real.sqrt (x ^ 2 + y ^ 2) = 15 := by
      rw [h6]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    exact h7
  | inr hy12 =>
    have h2 : y = -12 := by linarith
    rw [h2] at h1
    nlinarith