import Mathlib

theorem algebra_284841
    (a b : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (h : 1 / a - 1 / b - 1 / (a + b) = 0) :
    (b / a + a / b)^2 = 5 := by
  have h1' : a + b > 0 := by linarith
  have h2 : b * (a + b) - a * (a + b) - a * b = 0 := by
    have h3 : a ≠ 0 := by linarith
    have h4 : b ≠ 0 := by linarith
    have h5 : a + b ≠ 0 := by linarith
    field_simp [h3, h4, h5] at h ⊢
    nlinarith [h, mul_pos ha hb, mul_pos ha h1', mul_pos hb h1']
  have h3 : b ^ 2 - a * b - a ^ 2 = 0 := by
    nlinarith
  have h4 : b ^ 2 = a * b + a ^ 2 := by linarith
  have h5 : (b / a + a / b) ^ 2 = 5 := by
    have h7 : (b / a + a / b) ^ 2 = (b ^ 2 / a ^ 2) + 2 + (a ^ 2 / b ^ 2) := by
      field_simp
      <;> ring_nf <;> field_simp <;> ring
    have h8 : b ^ 2 / a ^ 2 = b / a + 1 := by
      have h9 : a ≠ 0 := by linarith
      have h10 : a ^ 2 > 0 := by nlinarith
      field_simp [h9]
      nlinarith [h4]
    have h9 : a ^ 2 / b ^ 2 = 1 - (a / b) := by
      have h11 : b ≠ 0 := by linarith
      have h12 : b ^ 2 > 0 := by nlinarith
      have h13 : a ^ 2 = b ^ 2 - a * b := by
        nlinarith [h4]
      rw [h13]
      field_simp [h11]
      <;> nlinarith
    rw [h7, h8, h9]
    have h10 : b / a - (a / b) = 1 := by
      have h11 : b ^ 2 = a * b + a ^ 2 := by linarith
      have h12 : b / a - (a / b) = 1 := by
        have h13 : a ≠ 0 := by linarith
        have h14 : b ≠ 0 := by linarith
        field_simp [h13, h14]
        nlinarith [h11, sq_nonneg (a - b), sq_nonneg (a + b)]
      exact h12
    nlinarith [h10, mul_pos ha hb]
  exact h5