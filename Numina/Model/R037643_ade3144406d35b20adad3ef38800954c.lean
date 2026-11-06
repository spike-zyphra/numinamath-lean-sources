import Mathlib

theorem algebra_10835 {a : ℝ} (ha : 4 = a + 1 / a) :
    a ^ 4 + 1 / a ^ 4 = 194 := by
  have ha1 : a ≠ 0 := by
    by_contra h
    rw [h] at ha
    norm_num at ha
  have h1 : a + 1 / a = 4 := by linarith
  have h2 : a ^ 2 + 1 / a ^ 2 = 14 := by
    have h3 : a ^ 2 + 1 / a ^ 2 = (a + 1 / a) ^ 2 - 2 := by
      field_simp
      <;> ring
    rw [h3, h1]
    all_goals norm_num
  have h4 : a ^ 4 + 1 / a ^ 4 = 194 := by
    have h5 : a ^ 4 + 1 / a ^ 4 = (a ^ 2 + 1 / a ^ 2) ^ 2 - 2 := by
      field_simp
      <;> ring
    rw [h5, h2]
    all_goals norm_num
  exact h4