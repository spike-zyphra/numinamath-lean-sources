import Mathlib

theorem algebra_152302 {a b c : ℝ} (ha : 0 < a) (hb : b < 0) (hc : c < b)
    (h : 1 / a + 1 / (2 * b) + 1 / (3 * c) = 1 / (a + 2 * b + 3 * c)) :
    (a + 2 * b) * (a + 3 * c) = 0 := by
  have ha1 : a ≠ 0 := by linarith
  have hb1 : b ≠ 0 := by linarith
  have hc1 : c ≠ 0 := by linarith
  have h1 : a + 2 * b + 3 * c ≠ 0 := by
    by_contra h2
    have h3 : 1 / a + 1 / (2 * b) + 1 / (3 * c) = 0 := by 
      rw [h] 
      field_simp [show a + 2 * b + 3 * c = 0 by linarith]
    field_simp [ha1, hb1, hc1] at h3
    nlinarith
  have heq : 6 * b * c * (a + 2 * b + 3 * c) + 3 * a * c * (a + 2 * b + 3 * c) + 2 * a * b * (a + 2 * b + 3 * c) = 6 * a * b * c := by
    have h2 : 1 / a + 1 / (2 * b) + 1 / (3 * c) = 1 / (a + 2 * b + 3 * c) := h
    have h4 : b * c * (a + 2 * b + 3 * c) + (a * c * (a + 2 * b + 3 * c)) / 2 + (a * b * (a + 2 * b + 3 * c)) / 3 = a * b * c := by
      field_simp [ha1, hb1, hc1, h1] at h2 ⊢
      nlinarith
    -- To clear denominator from above hypothesis
    have h5 : 6 * b * c * (a + 2 * b + 3 * c) + 3 * a * c * (a + 2 * b + 3 * c) + 2 * a * b * (a + 2 * b + 3 * c) = 6 * a * b * c := by
      have eq1 : b * c * (a + 2 * b + 3 * c) + (a * c * (a + 2 * b + 3 * c)) / 2 + (a * b * (a + 2 * b + 3 * c)) / 3 = a * b * c := h4
      field_simp at eq1 ⊢ 
      linarith
    exact h5 
  nlinarith [sq_nonneg (a + 2 * b), sq_nonneg (a + 3 * c), sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (a + 2 * b + 3 * c), mul_pos ha (show 0 < a by linarith), mul_pos (show 0 < a - b by nlinarith) (show 0 < a - c by nlinarith)]