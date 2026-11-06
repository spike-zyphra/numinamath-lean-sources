import Mathlib

theorem algebra_273698 {a b : ℝ} (ha : a ≠ b) (h : (a + b) / (a - b) = 3) : a / b = 2 := by
  have h1 : a - b ≠ 0 := by
    intro h2
    apply ha
    linarith
  have eqn1 : a + b = 3 * (a - b) := by
    field_simp [h1] at h
    linarith
  have eqn2 : a = 2 * b := by
    linarith [eqn1]
  have hb : b ≠ 0 := by
    by_contra h2
    have ha0 : a = 0 := by
      rw [eqn2]
      rw [h2]
      norm_num
    have h3 : a = b := by
      rw [ha0, h2]
    contradiction
  field_simp [hb]
  nlinarith [eqn2]