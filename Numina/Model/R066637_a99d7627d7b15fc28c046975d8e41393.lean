import Mathlib

theorem algebra_188030 {x : ℚ} (hx : x ≠ 0) (h : x + x / x + x / (x + x / x) = 1) :
    x = -2 := by
  have h1 : x / x = 1 := by
    field_simp [hx]
  rw [h1] at h
  have h2 : x + 1 ≠ 0 := by
    by_contra h2'
    have h3 : x = -1 := by
      linarith
    rw [h3] at h
    norm_num [show (-1 : ℚ) ≠ 0 by norm_num] at h
  have h3 : x / (x + 1) = -x := by
    have h6 : x + 1 ≠ 0 := h2
    field_simp [h6] at h ⊢
    linarith
  have h5 : x^2 + 2 * x = 0 := by
    have h6 : x + 1 ≠ 0 := h2
    field_simp [show x + 1 ≠ 0 by exact h6] at h3
    nlinarith
  have h7 : x * (x + 2) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h7) with h8 h9
  · 
    exfalso
    exact hx (by linarith)
  · 
    linarith