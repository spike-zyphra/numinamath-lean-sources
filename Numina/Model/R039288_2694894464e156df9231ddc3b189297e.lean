import Mathlib

theorem algebra_126077 {a b c x : ℝ} (h : a * b * c ≠ 0)
    (h1 : (x * b + (1 - x) * c) / a = (x * c + (1 - x) * a) / b)
    (h2 : (x * c + (1 - x) * a) / b = (x * a + (1 - x) * b) / c) :
    a + b + c = 0 ∨ a = b ∧ b = c := by
  have h3 : a * b * c ≠ 0 := h
  have ha : a ≠ 0 := by
    by_contra h'
    rw [h'] at h3
    simp at h3
  have hb : b ≠ 0 := by
    by_contra h'
    rw [h'] at h3
    simp at h3
  have hc : c ≠ 0 := by
    by_contra h'
    rw [h'] at h3
    simp at h3
  have eq1 : b * (x * b + (1 - x) * c) = a * (x * c + (1 - x) * a) := by
    have h1' : (x * b + (1 - x) * c) / a = (x * c + (1 - x) * a) / b := h1
    field_simp [ha, hb] at h1' ⊢
    linarith
  have eq2 : c * (x * c + (1 - x) * a) = b * (x * a + (1 - x) * b) := by
    have h2' : (x * c + (1 - x) * a) / b = (x * a + (1 - x) * b) / c := h2
    field_simp [hb, hc] at h2' ⊢
    linarith
  have eq3 : c * (x * b + (1 - x) * c) = a * (x * a + (1 - x) * b) := by
    have h3 : (x * b + (1 - x) * c) / a = (x * a + (1 - x) * b) / c := by
      linarith [h1, h2]
    field_simp [ha, hc] at h3 ⊢
    linarith
  have eq4 : (a + b + c) * (a + b + c) = (a + b + c) * (a + b + c) := by
    nlinarith
  by_cases h4 : a + b + c = 0
  · left
    exact h4
  · -- Assume a + b + c ≠ 0, derive a = b ∧ b = c
    right
    have h5 : a = b := by
      apply (mul_left_inj' h4).mp
      -- Multiply both sides of eq1 by (a + b + c)
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc]
    have h6 : b = c := by
      apply (mul_left_inj' h4).mp
      -- Multiply both sides of eq2 by (a + b + c)
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc]
    exact ⟨h5, h6⟩