import Mathlib

theorem algebra_320962 {a b c : ℝ} (h : a * b * c ≠ 0) (h' : a + b = c) :
    (b ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c) + (c ^ 2 + a ^ 2 - b ^ 2) / (2 * c * a) +
    (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) = 1 := by
  have h1 : c = a + b := by linarith
  have ha : a ≠ 0 := by
    by_contra h11
    have : a * b * c = 0 := by
      rw [h11]
      norm_num
    contradiction
  have hb : b ≠ 0 := by
    by_contra h11
    have : a * b * c = 0 := by
      rw [h11]
      norm_num
    contradiction
  have hc : c ≠ 0 := by
    by_contra h11
    have : a * b * c = 0 := by
      rw [h11]
      norm_num
    contradiction
  have h2 : (b ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c) = 1 := by
    rw [h1]
    have h3 : 2 * b * (a + b) ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      norm_num
      exact hb
      have h5 : a + b = c := by linarith
      rw [h5] at *
      exact hc
    field_simp [h3]
    <;> nlinarith
  have h3 : (c ^ 2 + a ^ 2 - b ^ 2) / (2 * c * a) = 1 := by
    rw [h1]
    have h4 : 2 * (a + b) * a ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      norm_num
      have h5 : a + b = c := by linarith
      rw [h5] at *
      exact hc
      exact ha
    field_simp [h4]
    <;> nlinarith
    all_goals nlinarith
  have h4 : (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) = -1 := by
    rw [h1]
    have h5 : 2 * a * b ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      norm_num
      exact ha
      exact hb
    field_simp [h5]
    <;> nlinarith
    all_goals nlinarith
  rw [h2, h3, h4]
  norm_num