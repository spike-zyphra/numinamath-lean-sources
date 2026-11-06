import Mathlib

open Real

theorem algebra_241746 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 9 * a + 4 * b = a * b * c) :
    a + b + c ≥ 10 := by
  have h1 : c = (9 * a + 4 * b) / (a * b) := by
    have h2 : a * b ≠ 0 := mul_ne_zero (ne_of_gt ha) (ne_of_gt hb)
    field_simp at h ⊢
    nlinarith
  rw [h1]
  have h2 : a * b > 0 := mul_pos ha hb
  have h3 : a + 4 / a ≥ 4 := by
    have h4 : a > 0 := by linarith
    have h5 : a + 4 / a - 4 ≥ 0 := by
      have h6 : a + 4 / a - 4 = (a^2 - 4 * a + 4) / a := by
        field_simp
        ring
      rw [h6]
      have h7 : a^2 - 4 * a + 4 ≥ 0 := by
        nlinarith [sq_nonneg (a - 2)]
      have h8 : (a^2 - 4 * a + 4) / a ≥ 0 := by
        apply div_nonneg
        linarith [h7]
        linarith [ha]
      linarith [h8]
    linarith [h5]
  have h4 : b + 9 / b ≥ 6 := by
    have h5 : b > 0 := by linarith
    have h6 : b + 9 / b - 6 ≥ 0 := by
      have h7 : b + 9 / b - 6 = (b^2 - 6 * b + 9) / b := by
        field_simp
        ring
      rw [h7]
      have h8 : b^2 - 6 * b + 9 ≥ 0 := by
        nlinarith [sq_nonneg (b - 3)]
      have h9 : (b^2 - 6 * b + 9) / b ≥ 0 := by
        apply div_nonneg
        linarith [h8]
        linarith [hb]
      linarith [h9]
    linarith [h6]
  have h5 : (9 * a + 4 * b) / (a * b) = 9 / b + 4 / a := by
    field_simp
    <;> ring_nf <;> field_simp <;> ring
  have h6 : a + b + (9 * a + 4 * b) / (a * b) = (a + 4 / a) + (b + 9 / b) := by
    rw [h5]
    ring
  have h7 : (a + 4 / a) + (b + 9 / b) ≥ 10 := by
    linarith [h3, h4]
  linarith [h6, h7]