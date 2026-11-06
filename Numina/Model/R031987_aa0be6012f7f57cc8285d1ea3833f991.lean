import Mathlib

theorem algebra_607354 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x + 2 / y) * (y / x + 2) ≥ 8 ∧ ((x + 2 / y) * (y / x + 2) = 8 ↔ (x = 1 ∧ y = 2)):= by
  have h3 : (x + 2 / y) * (y / x + 2) = 2 * x + 2 / x + y + 4 / y := by
    field_simp
    ring
  have h1 : 2 * x + 2 / x ≥ 4 := by
    have h2 : x > 0 := hx
    have h4 : (2 * x) * (2 / x) = 4 := by
      field_simp
      <;> linarith
    nlinarith [sq_nonneg (x - 1), sq_nonneg (2 * x - 2), mul_pos hx (show 0 < 2 by linarith), h4, mul_pos hx (show 0 < (2 / x) by positivity)]
  have h2 : y + 4 / y ≥ 4 := by
    have h3 : y > 0 := hy
    have h4 : y * (4 / y) = 4 := by
      field_simp
      <;> linarith
    nlinarith [sq_nonneg (y - 2), sq_nonneg (y * (4 / y) - 4), mul_pos hy (show (0 : ℝ) < y by linarith), mul_pos (show (0 : ℝ) < y by linarith) (show 0 < 4 by linarith), h4, mul_pos (show 0 < y by linarith) (show 0 < (4 / y) by positivity)]
  have h5 : (x + 2 / y) * (y / x + 2) ≥ 8 := by
    have eq : (x + 2 / y) * (y / x + 2) = 2 * x + 2 / x + y + 4 / y := by
      field_simp
      ring
    have h6 : 2 * x + 2 / x ≥ 4 := h1
    have h7 : y + 4 / y ≥ 4 := h2
    have h8 : 2 * x + 2 / x + y + 4 / y ≥ 8 := by
      linarith
    linarith [eq, h8]
  constructor
  · -- First part: prove the inequality.
    linarith [h5]
  · -- Second part: prove the equality condition.
    constructor
    · -- Forward direction: equality implies x = 1 and y = 2.
      intro h_eq
      have eq1 : (x + 2 / y) * (y / x + 2) = 8 := by linarith [h_eq, h5]
      have eq2 : (x + 2 / y) * (y / x + 2) = 2 * x + 2 / x + y + 4 / y := h3
      have eq3 : 2 * x + 2 / x + y + 4 / y = 8 := by
        linarith [eq1, eq2]
      have h_eq1 : 2 * x + 2 / x = 4 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (2 * x - 2), mul_pos hx (show 0 < 2 by linarith), mul_pos hx (show 0 < (2 / x) by positivity), sq_nonneg (2 / x - 2)]
      have h_eq2 : y + 4 / y = 4 := by
        nlinarith [sq_nonneg (y - 2), sq_nonneg (4 / y - 2), mul_pos hy (show (0 : ℝ) < y by linarith), mul_pos (show 0 < y by linarith) (show 0 < 4 by linarith), mul_pos (show 0 < y by linarith) (show 0 < (4 / y) by positivity), sq_nonneg (y * (4 / y) - 4)]
      have h_eq3 : x = 1 := by
        -- from 2x + 2/x = 4 
        have h4 : 2 * x + 2 / x = 4 := h_eq1
        have h5 : x > 0 := hx
        have h6 : 2 * x ^ 2 + 2 = 4 * x := by
          have eq1 : 2 * x + 2 / x = 4 := h_eq1
          field_simp at eq1
          nlinarith
        have h6' : (x - 1) ^ 2 = 0 := by
          nlinarith [sq_nonneg (x - 1), h6, h5]
        have h7 : x - 1 = 0 := by
          nlinarith
        linarith
      have h_eq4 : y = 2 := by
        -- from y + 4/y = 4
        have h7 : y + 4 / y = 4 := h_eq2
        have h8 : y > 0 := hy
        have h6 : y ^ 2 + 4 = 4 * y := by
          have eq1 : y + 4 / y = 4 := h_eq2
          field_simp at eq1
          nlinarith
        have h9 : (y - 2) ^ 2 = 0 := by
          nlinarith [sq_nonneg (y - 2), h6, h8]
        have h10 : y - 2 = 0 := by
          nlinarith
        linarith
      constructor
      · exact h_eq3
      · exact h_eq4
    · -- Backward direction: x = 1 and y = 2 implies equality.
      rintro ⟨rfl, rfl⟩
      norm_num [h3]