import Mathlib

theorem inequalities_79577 (a b c : ℝ) (ha : -3 / 4 ≤ a) (hb : -3 / 4 ≤ b) (hc : -3 / 4 ≤ c)
    (h : a + b + c = 1) :
    a / (1 + a ^ 2) + b / (1 + b ^ 2) + c / (1 + c ^ 2) ≤ 9 / 10 := by

  have h1 : a / (1 + a ^ 2) ≤ 18 / 25 * a + 3 / 50 := by
    have h2 : (a - 1 / 3) ^ 2 ≥ 0 := sq_nonneg (a - 1 / 3)
    have h3 : (1 + a ^ 2) > 0 := by nlinarith [sq_nonneg (a), sq_nonneg (a + 3 / 4)]
    have h4 : a / (1 + a ^ 2) - (18 / 25 * a + 3 / 50) ≤ 0 := by
      have h5 : a / (1 + a ^ 2) - (18 / 25 * a + 3 / 50) = (a - (18 / 25 * a + 3 / 50) * (1 + a ^ 2)) / (1 + a ^ 2) := by
        field_simp
        ring
      rw [h5]
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show numerator ≤ 0
        nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (a + 3 / 4), sq_nonneg (a ^ 2 - 1 / 9), sq_nonneg (a ^ 2 - 1 / 4), sq_nonneg (a - 1 / 3), sq_nonneg (a * (a - 1 / 3)), sq_nonneg ((a - 1 / 3) * (a + 3 / 4))]
      · -- Show denominator ≥ 0
        nlinarith [sq_nonneg (a), sq_nonneg (a + 3 / 4)]
    linarith

  have h2 : b / (1 + b ^ 2) ≤ 18 / 25 * b + 3 / 50 := by
    have h2 : (b - 1 / 3) ^ 2 ≥ 0 := sq_nonneg (b - 1 / 3)
    have h3 : (1 + b ^ 2) > 0 := by nlinarith [sq_nonneg (b), sq_nonneg (b + 3 / 4)]
    have h4 : b / (1 + b ^ 2) - (18 / 25 * b + 3 / 50) ≤ 0 := by
      have h5 : b / (1 + b ^ 2) - (18 / 25 * b + 3 / 50) = (b - (18 / 25 * b + 3 / 50) * (1 + b ^ 2)) / (1 + b ^ 2) := by
        field_simp
        ring
      rw [h5]
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show numerator ≤ 0
        nlinarith [sq_nonneg (b - 1 / 3), sq_nonneg (b + 3 / 4), sq_nonneg (b ^ 2 - 1 / 9), sq_nonneg (b ^ 2 - 1 / 4), sq_nonneg (b - 1 / 3), sq_nonneg (b * (b - 1 / 3)), sq_nonneg ((b - 1 / 3) * (b + 3 / 4))]
      · -- Show denominator ≥ 0
        nlinarith [sq_nonneg (b), sq_nonneg (b + 3 / 4)]
    linarith

  have h3 : c / (1 + c ^ 2) ≤ 18 / 25 * c + 3 / 50 := by
    have h2 : (c - 1 / 3) ^ 2 ≥ 0 := sq_nonneg (c - 1 / 3)
    have h3 : (1 + c ^ 2) > 0 := by nlinarith [sq_nonneg (c), sq_nonneg (c + 3 / 4)]
    have h4 : c / (1 + c ^ 2) - (18 / 25 * c + 3 / 50) ≤ 0 := by
      have h5 : c / (1 + c ^ 2) - (18 / 25 * c + 3 / 50) = (c - (18 / 25 * c + 3 / 50) * (1 + c ^ 2)) / (1 + c ^ 2) := by
        field_simp
        ring
      rw [h5]
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show numerator ≤ 0
        nlinarith [sq_nonneg (c - 1 / 3), sq_nonneg (c + 3 / 4), sq_nonneg (c ^ 2 - 1 / 9), sq_nonneg (c ^ 2 - 1 / 4), sq_nonneg (c - 1 / 3), sq_nonneg (c * (c - 1 / 3)), sq_nonneg ((c - 1 / 3) * (c + 3 / 4))]
      · -- Show denominator ≥ 0
        nlinarith [sq_nonneg (c), sq_nonneg (c + 3 / 4)]
    linarith

  have h4 : a / (1 + a ^ 2) + b / (1 + b ^ 2) + c / (1 + c ^ 2) ≤ (18 / 25 * a + 3 / 50) + (18 / 25 * b + 3 / 50) + (18 / 25 * c + 3 / 50) := by
    linarith [h1, h2, h3]

  have h5 : (18 / 25 * a + 3 / 50) + (18 / 25 * b + 3 / 50) + (18 / 25 * c + 3 / 50) = 18 / 25 * (a + b + c) + 9 / 50 := by
    ring

  rw [h5] at h4
  rw [show a + b + c = 1 by linarith] at h4
  norm_num at h4 ⊢
  linarith