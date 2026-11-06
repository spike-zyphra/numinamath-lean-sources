import Mathlib

theorem algebra_9481 (a : ℕ → ℝ) (r : ℝ) (h₀ : ∀ n, 0 < a n) (h₁ : ∀ n, a n = a 0 * r ^ n)
    (h₂ : a 4 + a 3 - a 2 - a 1 = 5) :
    a 5 + a 6 ≥ 20 := by
  have ha4 : a 4 = a 0 * r ^ 4 := h₁ 4
  have ha3 : a 3 = a 0 * r ^ 3 := h₁ 3
  have ha2 : a 2 = a 0 * r ^ 2 := h₁ 2
  have ha1 : a 1 = a 0 * r ^ 1 := h₁ 1
  have ha5 : a 5 = a 0 * r ^ 5 := h₁ 5
  have ha6 : a 6 = a 0 * r ^ 6 := h₁ 6
  rw [ha4] at h₂ 
  rw [ha3] at h₂ 
  rw [ha2] at h₂ 
  rw [ha1] at h₂ 
  rw [ha5, ha6]
  have h3 : 0 < a 0 := by
    have h4 : 0 < a 0 := h₀ 0 
    linarith 
  have h4 : 0 < r := by
    have h5 : 0 < a 1 := h₀ 1
    rw [show a 1 = a 0 * r ^ 1 by exact h₁ 1] at h5 
    nlinarith [h3]
  have h6 : a 0 * r * (r - 1) * (r + 1) ^ 2 = 5 := by
    nlinarith 
  have h7 : a 0 * r ^ 5 + a 0 * r ^ 6 ≥ 20 := by
    nlinarith [sq_nonneg (a 0 * (r ^ 2 - 2) ), sq_nonneg (r ^ 2 - 4), sq_nonneg (r - 2), sq_nonneg (a 0 - 5 / 18), sq_nonneg (r * (r - 2) ), sq_nonneg ((r ^ 2 - 2) * (r - 2) ), mul_pos h3 h4, sq_nonneg (a 0 * r), mul_pos (show 0 < r by linarith) (show 0 < r by linarith)]
  linarith