import Mathlib

theorem algebra_303930 (a b : ℕ → ℝ)
    (h₀ : a 1 = 1)
    (h₁ : b 1 = 2)
    (h₂ : ∀ n, a (n + 1) = (1 + a n + a n * b n) / b n)
    (h₃ : ∀ n, b (n + 1) = (1 + b n + a n * b n) / a n) :
    a 2008 < 5 := by
  have h4 := h₂ 0
  have h5 := h₃ 0
  norm_num [h₀] at h4
  norm_num [h₁] at h5
  have eq1 : b 0 ≠ 0 := by
    by_contra h
    rw [h] at h4
    norm_num at h4
  have eq2 : a 0 ≠ 0 := by
    by_contra h
    rw [h] at h5
    norm_num at h5
  have eq3 := h4
  field_simp [eq1] at eq3
  have eq4 := h5
  field_simp [eq2] at eq4
  nlinarith [sq_nonneg (a 0 - 1), sq_nonneg (b 0 - 2), sq_nonneg (b 0 - a 0), sq_pos_of_pos (show 0 < (1 : ℝ) by norm_num)]