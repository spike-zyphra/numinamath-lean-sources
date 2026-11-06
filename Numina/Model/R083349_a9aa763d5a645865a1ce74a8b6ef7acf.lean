import Mathlib

theorem algebra_7128 (x : ℝ) (hx1 : x^2 - 5 * x + 1 ≥ 0) (hx2 : 8 * x - x^2 - 12 ≥ 0)
    (hx3 : 3 * x - 11 ≥ 0) :
    Real.sqrt (x^2 - 5 * x + 1) + Real.sqrt (8 * x - x^2 - 12) = Real.sqrt (3 * x - 11) ↔
    x = (5 + Real.sqrt 21) / 2 ∨ x = 6 := by 

  constructor
  · -- Assume the equation, prove the disjunction of the two roots
    intro h_eq
    have h1 : Real.sqrt (x^2 - 5 * x + 1) ≥ 0 := by positivity
    have h2 : Real.sqrt (8 * x - x^2 - 12) ≥ 0 := by positivity
    have h3 : Real.sqrt (3 * x - 11) ≥ 0 := by positivity
    have h_eq1 : (Real.sqrt (x^2 - 5 * x + 1) + Real.sqrt (8 * x - x^2 - 12)) ^ 2 = (Real.sqrt (3 * x - 11)) ^ 2 := by 
      rw [h_eq]
    have h_eq2 : (Real.sqrt (x^2 - 5 * x + 1)) ^ 2 + (Real.sqrt (8 * x - x^2 - 12)) ^ 2 + 2 * (Real.sqrt (x^2 - 5 * x + 1) * Real.sqrt (8 * x - x^2 - 12)) = (3 * x - 11) := by
      have h_eq3 : (Real.sqrt (3 * x - 11)) ^ 2 = 3 * x - 11 := by 
        rw [Real.sq_sqrt]
        linarith 
      nlinarith [h_eq1, h_eq3, Real.sq_sqrt (show x^2 - 5 * x + 1 ≥ 0 by linarith), Real.sq_sqrt (show 8 * x - x^2 - 12 ≥ 0 by linarith)]
    have h_eq3 : (Real.sqrt (x^2 - 5 * x + 1)) ^ 2 = x^2 - 5 * x + 1 := Real.sq_sqrt (by linarith)
    have h_eq4 : (Real.sqrt (8 * x - x^2 - 12)) ^ 2 = 8 * x - x^2 - 12 := Real.sq_sqrt (by linarith)
    rw [h_eq3, h_eq4] at h_eq2
    have h_eq5 : 2 * (Real.sqrt (x^2 - 5 * x + 1) * Real.sqrt (8 * x - x^2 - 12)) = 0 := by 
      nlinarith 
    have h_eq6 : Real.sqrt (x^2 - 5 * x + 1) * Real.sqrt (8 * x - x^2 - 12) = 0 := by 
      linarith [h_eq5, h1, h2, h3]
    cases' (mul_eq_zero.mp h_eq6) with h_a h_b
    · -- Case where sqrt(x^2 -5x +1) = 0 
      have h_eq7 : Real.sqrt (x^2 - 5 * x + 1) = 0 := by
        linarith 
      have h_eq8 : x^2 - 5 * x + 1 = 0 := by 
        rw [Real.sqrt_eq_zero (by linarith)] at h_eq7 
        linarith
      have h4 : x^2 - 5 * x + 1 = (x - (5 + Real.sqrt 21) / 2) * (x - (5 - Real.sqrt 21) / 2) := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (21 : ℝ) by norm_num)]
      rw [h4] at h_eq8
      cases' (mul_eq_zero.mp h_eq8) with h_a h_b
      · -- Case where x - (5 + Real.sqrt 21) / 2 = 0 
        left
        linarith
      · -- Case where x - (5 - Real.sqrt 21) / 2 = 0 
        right
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (21 : ℝ) by norm_num ), Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num ) ] 
    · -- Case where sqrt(8x -x^2 -12) = 0 
      have h_eq9 : Real.sqrt (8 * x - x^2 - 12) = 0 := by 
        linarith 
      have h_eq10 : 8 * x - x^2 - 12 = 0 := by 
        rw [Real.sqrt_eq_zero (by linarith)] at h_eq9 
        linarith
      have h5 : 8 * x - x^2 - 12 = 0 := h_eq10 
      have h6 : x^2 - 8 * x + 12 = 0 := by nlinarith
      have h7 : (x - 2) * (x - 6) = 0 := by 
        nlinarith [h6]
      cases' (mul_eq_zero.mp h7) with h8 h9
      · -- Case where x - 2 = 0 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num ) ]
      · -- Case where x - 6 = 0 
        right
        linarith
  · -- Prove that the solutions satisfy the equation
    rintro (h | h)
    · -- Case where x = (5 + Real.sqrt 21) / 2 
      have h1 : x ^ 2 - 5 * x + 1 = 0 := by 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (21 : ℝ) by norm_num ), Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num ) ]
      have h2 : Real.sqrt (x ^ 2 - 5 * x + 1) = 0 := by 
        rw [show x ^ 2 - 5 * x + 1 = (0 : ℝ) by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (21 : ℝ) by norm_num ), Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num ) ] ]
        simp
      have h3 : Real.sqrt (8 * x - x^2 - 12) = Real.sqrt (3 * x - 11) := by 
        have h4 : 8 * x - x^2 - 12 = 3 * x - 11 := by 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (21 : ℝ) by norm_num ), Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num  ) ]
        rw [h4]
      rw [h2, h3]
      all_goals linarith
    · -- Case where x = 6 
      have h4 : x = 6 := by linarith
      rw [h4]
      have h5 : Real.sqrt (6^2 - 5 * (6 : ℝ) + 1) = Real.sqrt 7 := by norm_num [Real.sqrt_eq_iff_sq_eq]
      have h6 : Real.sqrt (8 * (6 : ℝ) - 6^2 - 12) = 0 := by norm_num [Real.sqrt_eq_zero]
      have h7 : Real.sqrt (3 * (6 : ℝ) - 11) = Real.sqrt 7 := by norm_num [Real.sqrt_eq_iff_sq_eq]
      rw [h5, h6, h7]
      all_goals norm_num