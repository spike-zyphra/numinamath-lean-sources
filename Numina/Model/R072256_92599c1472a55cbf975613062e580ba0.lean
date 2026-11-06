import Mathlib

theorem algebra_289 {a b : ℝ} (ha : a ≠ b) (h1 : a^2 + 1 = 3 * a) (h2 : b^2 + 1 = 3 * b) :
(1 / a^2) + (1 / b^2) = 7 := by
  have ha2 : a ≠ 0 := by
    rintro rfl
    linarith
  have hb2 : b ≠ 0 := by
    rintro rfl
    linarith
  have h3 : a + b = 3 := by
    have h4 : a^2 - b^2 = 3 * (a - b) := by linarith [h1, h2]
    have h5 : a^2 - b^2 = (a - b) * (a + b) := by ring
    rw [h5] at h4
    have h6 : a - b ≠ 0 := by
      intro h
      apply ha
      linarith
    have h7 : a + b = 3 := by
      apply (mul_left_inj' h6).mp
      linarith
    exact h7
  have h8 : a * b = 1 := by
    nlinarith [h1, h2, h3]
  have h9 : a^2 + b^2 = 7 := by
    nlinarith [h1, h2, h3, h8]
  have h10 : 1 / a^2 + 1 / b^2 = (a^2 + b^2) / ((a * b)^2) := by
    field_simp [ha2, hb2]
    <;> nlinarith
  rw [h10]
  rw [h9, h8]
  all_goals norm_num