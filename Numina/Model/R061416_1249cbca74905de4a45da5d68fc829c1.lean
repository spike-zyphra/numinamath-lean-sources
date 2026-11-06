import Mathlib

theorem algebra_326826 (a : ℕ → ℝ) (m : ℝ) (ha1 : a 1 = 1)
    (han : ∀ n, a (n + 1) = (1 / 8) * (a n)^2 + m)
    (h : ∀ n, 0 < n → a n < 4) :
    m ≤ 2 := by 
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  have h4 := h 4 (by norm_num)
  have eq1 : a 2 = (1 / 8) * (a 1) ^ 2 + m := han 1
  have eq2 : a 3 = (1 / 8) * (a 2) ^ 2 + m := han 2
  have eq3 : a 4 = (1 / 8) * (a 3) ^ 2 + m := han 3
  rw [eq1] at h2
  rw [ha1] at h2
  rw [eq2] at h3
  rw [eq3] at h4
  nlinarith [sq_nonneg (a 1 - 4), sq_nonneg (a 2 - 4), sq_nonneg (a 3 - 4), sq_nonneg (a 4 - 4),
          h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num),
          han 1, han 2, han 3, han 0]