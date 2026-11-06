import Mathlib

theorem algebra_379 (a : ℕ → ℝ) (h₀ : ∀ n, a (n + 1) = 1 + 1 / a n) (h₁ : a 4 = 0) : a 0 = -3 / 5 := by
  have h2 : a 4 = 1 + 1 / a 3 := h₀ 3
  rw [h2] at h₁
  have h3 : a 3 ≠ 0 := by
    by_contra h
    rw [h] at h₁
    norm_num at h₁
  have ha3 : a 3 = -1 := by
    field_simp at h₁
    linarith
  have h4 : a 3 = 1 + 1 / a 2 := h₀ 2
  rw [ha3] at h4
  have h5 : a 2 ≠ 0 := by
    by_contra h
    rw [h] at h4
    norm_num at h4
  have ha2 : a 2 = -1 / 2 := by
    field_simp at h4
    linarith
  have h6 : a 2 = 1 + 1 / a 1 := h₀ 1
  rw [ha2] at h6
  have h7 : a 1 ≠ 0 := by
    by_contra h
    rw [h] at h6
    norm_num at h6
  have ha1 : a 1 = -2 / 3 := by
    field_simp at h6
    linarith
  have h8 : a 1 = 1 + 1 / a 0 := h₀ 0
  rw [ha1] at h8
  have h9 : a 0 ≠ 0 := by
    by_contra h
    rw [h] at h8
    norm_num at h8
  field_simp at h8
  linarith