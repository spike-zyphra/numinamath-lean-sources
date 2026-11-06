import Mathlib

theorem algebra_165788 (x : ℝ) :
    (x + 4) * (x + 1) - 3 * Real.sqrt (x ^ 2 + 5 * x + 2) = 6 ↔
    x = -7 ∨ x = 2 := by
  constructor
  · -- Forward direction: if the equation holds, then x = -7 or x = 2
    intro h
    have h1 : (x + 4) * (x + 1) - 3 * Real.sqrt (x ^ 2 + 5 * x + 2) = 6 := h
    have h2 : Real.sqrt (x ^ 2 + 5 * x + 2) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + 5 * x + 2)
    have h3 : (x + 4) * (x + 1) - 6 = 3 * Real.sqrt (x ^ 2 + 5 * x + 2) := by 
      linarith [h1]
    have h4 : ((x + 4) * (x + 1) - 6) ^ 2 = (3 * Real.sqrt (x ^ 2 + 5 * x + 2)) ^ 2 := by
      rw [h3]
    have h7 : (x ^ 2 + 5 * x - 2) ^ 2 = 9 * (x ^ 2 + 5 * x + 2) := by
      nlinarith [h4, Real.sq_sqrt (show (x ^ 2 + 5 * x + 2 : ℝ) ≥ 0 by nlinarith)]
    have h8 : (x ^ 2 + 5 * x + 1) * (x ^ 2 + 5 * x - 14) = 0 := by
      nlinarith [h7]
    cases' (mul_eq_zero.1 h8) with h9 h10
    · -- Case where x^2 + 5x + 1 = 0
      nlinarith [Real.sq_sqrt (show (x ^ 2 + 5 * x + 2 : ℝ) ≥ 0 by nlinarith), Real.sqrt_nonneg (x ^ 2 + 5 * x + 2)]
    · -- Case where x^2 + 5 x - 14 = 0
      have h11 : x ^ 2 + 5 * x - 14 = 0 := h10
      have h12 : (x - 2) * (x + 7) = 0 := by
        nlinarith [h11]
      cases' (mul_eq_zero.1 h12) with h13 h14
      · -- Case where x - 2 = 0, so x = 2
        right
        linarith
      · -- Case where x + 7 = 0, so x = -7
        left
        linarith
  · -- Backward direction
    rintro (h | h)
    · -- x = -7
      rw [h]
      have h2 : Real.sqrt ((-7 : ℝ) ^ 2 + 5 * (-7 : ℝ) + 2) = 4 := by
        rw [show (-7 : ℝ) ^ 2 + 5 * (-7 : ℝ) + 2 = (16 : ℝ) by norm_num]
        exact Real.sqrt_eq_cases.2 (by norm_num)
      nlinarith [h2]
    · -- x = 2
      rw [h]
      have h3 : Real.sqrt ((2 : ℝ) ^ 2 + 5 * (2 : ℝ) + 2) = 4 := by
        rw [show (2 : ℝ) ^ 2 + 5 * (2 : ℝ) + 2 = (16 : ℝ) by norm_num]
        exact Real.sqrt_eq_cases.2 (by norm_num)
      nlinarith [h3]