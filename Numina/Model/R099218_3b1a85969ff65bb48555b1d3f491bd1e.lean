import Mathlib

theorem algebra_271579 {x : ℝ} (hx : x ≠ 0) (h : (x + 1 / x) ^ 2 = 3) :
    x^3 + 1 / x^3 = 0 := by
  have h1 : x + 1 / x = Real.sqrt 3 ∨ x + 1 / x = -Real.sqrt 3 := by
    have h2 : (x + 1 / x) ^ 2 - 3 = 0 := by linarith
    have h3 : (x + 1 / x - Real.sqrt 3) * (x + 1 / x + Real.sqrt 3) = 0 := by 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- h4 : (x + 1 / x - Real.sqrt 3) = 0
      left
      linarith
    · -- h5 : (x + 1 / x + Real.sqrt 3) = 0
      right
      linarith
  cases h1 with
  | inl h6 =>
    have h7 : x^3 + 1 / x^3 = (x + 1 / x) ^ 3 - 3 * (x + 1 / x) := by
      field_simp
      ring
    rw [h7, h6]
    have h8 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
    have h9 : (Real.sqrt 3 : ℝ) ^ 3 = 3 * Real.sqrt 3 := by
      calc
        (Real.sqrt 3) ^ 3 = (Real.sqrt 3) ^ 2 * Real.sqrt 3 := by ring
        _ = 3 * Real.sqrt 3 := by rw [h8]
    rw [h9]
    all_goals ring
  | inr h7 =>
    have h8 : x^3 + 1 / x^3 = (x + 1 / x) ^ 3 - 3 * (x + 1 / x) := by
      field_simp
      ring
    rw [h8, h7]
    have h9 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
    have h10 : (-Real.sqrt 3 : ℝ) ^ 3 = -3 * Real.sqrt 3 := by
      calc
        (-Real.sqrt 3) ^ 3 = - (Real.sqrt 3) ^ 3 := by ring
        _ = - ( (Real.sqrt 3) ^ 2 * Real.sqrt 3 ) := by ring
        _ = - ( 3 * Real.sqrt 3 ) := by rw [h9]
        _ = -3 * Real.sqrt 3 := by ring
    rw [h10]
    all_goals ring