import Mathlib

theorem algebra_165854 {x : ℝ} (hx : x^2 - 1 ≥ 0) :
    (x + Real.sqrt (x^2 - 1))^5 * (x - Real.sqrt (x^2 - 1))^3 = 1 ↔ x = 1 ∨ x = -1 := by 
  constructor
  · -- Assume (x + √(x² - 1)) ^ 5 * (x - √(x² - 1)) ^ 3 = 1, prove x = 1 ∨ x = -1
    intro h_eq
    have h1 : (x + Real.sqrt (x^2 - 1)) * (x - Real.sqrt (x^2 - 1)) = 1 := by 
      nlinarith [Real.sqrt_nonneg (x^2 - 1), Real.sq_sqrt (show x^2 - 1 ≥ 0 by linarith)]
    have h2 : (x + Real.sqrt (x^2 - 1))^5 * (x - Real.sqrt (x^2 - 1))^3 = (x + Real.sqrt (x^2 - 1)) ^ 2 := by
      calc
        (x + Real.sqrt (x^2 - 1))^5 * (x - Real.sqrt (x^2 - 1))^3
          = (x + Real.sqrt (x^2 - 1)) ^ 2 * ((x + Real.sqrt (x^2 - 1)) ^ 3 * (x - Real.sqrt (x^2 - 1)) ^ 3) := by ring
        _ = (x + Real.sqrt (x^2 - 1)) ^ 2 * (( (x + Real.sqrt (x^2 - 1)) * (x - Real.sqrt (x^2 - 1)) ) ^ 3) := by ring
        _ = (x + Real.sqrt (x^2 - 1)) ^ 2 * (1 ^ 3) := by rw [h1]
        _ = (x + Real.sqrt (x^2 - 1)) ^ 2 := by ring
    rw [h2] at h_eq
    have h3 : (x + Real.sqrt (x^2 - 1)) ^ 2 = 1 := h_eq
    have h4 : x + Real.sqrt (x^2 - 1) = 1 ∨ x + Real.sqrt (x^2 - 1) = -1 := by 
      rw [sq_eq_one_iff] at h3
      exact h3
    rcases h4 with (h4 | h4)
    · -- x + Real.sqrt (x^2 - 1) = 1
      have h5 : Real.sqrt (x^2 - 1) = 1 - x := by linarith
      have h6 : Real.sqrt (x^2 - 1) ^ 2 = (1 - x) ^ 2 := by 
        rw [h5]
      have h7 : Real.sqrt (x^2 - 1) ^ 2 = x^2 - 1 := Real.sq_sqrt (show x^2 - 1 ≥ 0 by linarith)
      have h8 : x^2 - 1 = (1 - x) ^ 2 := by 
        linarith [h6, h7]
      have h9 : x = 1 := by
        nlinarith
      left
      exact h9
    · -- x + Real.sqrt (x^2 - 1) = -1
      have h5 : Real.sqrt (x^2 - 1) = -1 - x := by linarith
      have h6 : Real.sqrt (x^2 - 1) ^ 2 = (-1 - x) ^ 2 := by 
        rw [h5]
      have h7 : Real.sqrt (x^2 - 1) ^ 2 = x^2 - 1 := Real.sq_sqrt (show x^2 - 1 ≥ 0 by linarith)
      have h8 : x^2 - 1 = (-1 - x) ^ 2 := by 
        linarith [h6, h7]
      have h9 : x = -1 := by
        nlinarith
      right
      exact h9
  · -- Assume x = 1 ∨ x = -1, prove (x + √(x² - 1)) ^ 5 * (x - √(x² - 1)) ^ 3 = 1
    rintro (h_eq | h_eq)
    · -- x = 1
      rw [show x = (1 : ℝ) by linarith [h_eq]]
      have h1 : Real.sqrt ((1:ℝ) ^ 2 - 1) = 0 := by 
        rw [show (1:ℝ) ^ 2 - 1 = (0:ℝ) by norm_num]
        simp
      rw [h1]
      norm_num
    · -- x = -1
      rw [show x = (-1 : ℝ) by linarith [h_eq]]
      have h1 : Real.sqrt ((-1:ℝ) ^ 2 - 1) = 0 := by 
        rw [show (-1:ℝ) ^ 2 - 1 = (0:ℝ) by norm_num]
        simp
      rw [h1]
      norm_num