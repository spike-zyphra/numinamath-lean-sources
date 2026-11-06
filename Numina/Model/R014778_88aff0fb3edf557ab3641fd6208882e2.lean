import Mathlib

theorem algebra_186894 (x : ℝ) (hx : x ≤ 5 ∧ x ≥ 3) :
    ((5 - x) * Real.sqrt (5 - x) + (x - 3) * Real.sqrt (x - 3)) / (Real.sqrt (5 - x) + Real.sqrt (x - 3)) = 2 ↔
    x = 5 ∨ x = 3 := by
  constructor
  · -- Assume the equation holds, prove x = 5 or x = 3
    intro h_eq
    have h1 : x ≤ 5 := hx.1
    have h2 : x ≥ 3 := hx.2
    have h3 : Real.sqrt (5 - x) ≥ 0 := by positivity
    have h4 : Real.sqrt (x - 3) ≥ 0 := by positivity
    have h5 : Real.sqrt (5 - x) + Real.sqrt (x - 3) > 0 := by
      by_contra h
      push_neg at h
      have h6 : Real.sqrt (5 - x) = 0 := by linarith [h3, h4, h]
      have h7 : Real.sqrt (x - 3) = 0 := by linarith [h3, h4, h]
      have h8 : 5 - x = 0 := by
        rw [Real.sqrt_eq_zero (by linarith)] at h6
        linarith
      have h9 : x - 3 = 0 := by
        rw [Real.sqrt_eq_zero (by linarith)] at h7
        linarith
      linarith
    have eq1 : ((5 - x) * Real.sqrt (5 - x) + (x - 3) * Real.sqrt (x - 3)) = 2 * (Real.sqrt (5 - x) + Real.sqrt (x - 3)) := by
      field_simp [h5] at h_eq ⊢
      linarith
    have eq2 : Real.sqrt (5 - x) * (3 - x) + Real.sqrt (x - 3) * (x - 5) = 0 := by
      nlinarith [eq1, sq_nonneg (Real.sqrt (5 - x) - Real.sqrt (x - 3)), sq_nonneg (x - 4), Real.sq_sqrt (show (5 - x : ℝ) ≥ 0 by linarith), Real.sq_sqrt (show (x - 3 : ℝ) ≥ 0 by linarith)]
    have h7 : Real.sqrt (5 - x) * Real.sqrt (x - 3) = 0 := by
      nlinarith [sq_nonneg (Real.sqrt (5 - x) - Real.sqrt (x - 3)), Real.sq_sqrt (show (5 - x : ℝ) ≥ 0 by linarith), Real.sq_sqrt (show (x - 3 : ℝ) ≥ 0 by linarith), sq_nonneg (x - 4), Real.sqrt_nonneg (5 - x), Real.sqrt_nonneg (x - 3)]
    cases' (mul_eq_zero.1 h7) with h8 h9
    · 
      have h10 : 5 - x = 0 := by
        rw [Real.sqrt_eq_zero (by linarith)] at h8
        linarith
      have h11 : x = 5 := by linarith
      left
      exact h11
    · 
      have h13 : x - 3 = 0 := by
        rw [Real.sqrt_eq_zero (by linarith)] at h9
        linarith
      have h14 : x = 3 := by linarith
      right
      exact h14
  · -- Assume x = 5 or x = 3, prove the equation
    rintro (h | h)
    · -- x = 5
      rw [h]
      norm_num
    · -- x = 3
      rw [h]
      norm_num