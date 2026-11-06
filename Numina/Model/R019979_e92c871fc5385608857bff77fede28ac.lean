import Mathlib

theorem algebra_164183 (y : ℝ) :
    y^4 - 6 * y^3 + 10 * y^2 - 4 * y = 0 ↔
    y = 2 + Real.sqrt 2 ∨ y = 2 - Real.sqrt 2 ∨ y = 0 ∨ y = 2 := by
  constructor
  · -- Forward direction: if y^4 - 6y^3 + 10y^2 - 4y = 0, then y is one of the four roots
    intro h
    have h1 : y^4 - 6 * y^3 + 10 * y^2 - 4 * y = 0 := h
    -- Factor the polynomial
    have h2 : y^4 - 6 * y^3 + 10 * y^2 - 4 * y = 
        y * (y - 2) * ((y - 2)^2 - 2) := by
      ring_nf
    rw [h2] at h1
    -- Solve the equation
    cases' (mul_eq_zero.mp h1) with h3 h4
    · cases' (mul_eq_zero.mp h3) with h5 h6
      · -- Case y = 0
        right
        right
        left
        linarith
      · -- Case y - 2 = 0 => y = 2
        right
        right
        right
        linarith
    · -- Solve ((y - 2) ^ 2 - 2) = 0
      have h7 : (y - 2) ^ 2 - 2 = 0 := by 
        linarith
      have h8 : (y - 2) ^ 2 = 2 := by linarith
      have h9 : y - 2 = Real.sqrt 2 ∨ y - 2 = -Real.sqrt 2 := by
        apply eq_or_eq_neg_of_sq_eq_sq
        norm_num
        linarith
      cases' h9 with h10 h11
      · -- Case y - 2 = √2 => y = 2 + √2
        left
        linarith
      · -- Case y - 2 = -√2 => y = 2 - √2
        right
        left
        linarith
  · -- Backward direction: the four roots satisfy the equation
    rintro (h | h | h | h)
    · -- y = 2 + √2
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2)]
    · -- y = 2 - √2
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2)]
    · -- y = 0
      rw [h]
      norm_num
    · -- y = 2
      rw [h]
      norm_num