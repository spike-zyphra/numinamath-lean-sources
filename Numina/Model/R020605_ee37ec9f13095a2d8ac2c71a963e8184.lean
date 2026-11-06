import Mathlib

open Real

theorem algebra_303772 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 9 * a + 4 * b = a * b * c) :
    a + b + c ≥ 10 := by

  have h1 : 0 < a * b := mul_pos ha hb

  have h2 : c = (9 * a + 4 * b) / (a * b) := by 
    have h3 : a * b ≠ 0 := by positivity
    field_simp [h3] at *
    nlinarith

  have h3_eq : a + b + c = a + b + (9 * a + 4 * b) / (a * b) := by 
    rw [h2]

  have h4 : a + b + (9 * a + 4 * b) / (a * b) ≥ 10 := by 
    have h7 : a + 4 / a ≥ 4 := by
      have h8 : a + 4 / a - 4 ≥ 0 := by
        have h9 : a + 4 / a - 4 = (a - 2) ^ 2 / a := by
          field_simp
          ring
        rw [h9]
        apply div_nonneg
        · -- Show (a - 2) ^ 2 ≥ 0
          apply pow_two_nonneg
        · -- Show 0 < (a) 
          linarith [ha]
      linarith

    have h8 : b + 9 / b ≥ 6 := by
      have h9 : b + 9 / b - 6 ≥ 0 := by
        have h10 : b + 9 / b - 6 = (b - 3) ^ 2 / b := by
          field_simp
          ring
        rw [h10]
        apply div_nonneg
        · -- Show (b - 3) ^ 2 ≥ 0
          apply pow_two_nonneg
        · -- Show 0 < (b)
          linarith [hb]
      linarith

    have h9 : a + b + (9 * a + 4 * b) / (a * b) = (a + 4 / a) + (b + 9 / b) := by
      have h10 : a * b ≠ 0 := by positivity
      field_simp at *
      <;> ring
    rw [h9]
    linarith [h7, h8]

  linarith [h3_eq, h4]