import Mathlib

theorem algebra_295129 (x : ℝ) (hx : x > 0) (h : Real.sqrt (x^2 + 4 * x + 4) / Real.sqrt (x^2 + 6 * x + 9) = 37 / 39) :
    10 * x = 165 := by

  have h1 : Real.sqrt (x^2 + 4 * x + 4) = x + 2 := by
    have h1 : x^2 + 4 * x + 4 = (x + 2) ^ 2 := by ring
    rw [h1]
    rw [Real.sqrt_sq]
    all_goals nlinarith
  
  have h2 : Real.sqrt (x^2 + 6 * x + 9) = x + 3 := by
    have h2 : x^2 + 6 * x + 9 = (x + 3) ^ 2 := by ring
    rw [h2]
    rw [Real.sqrt_sq]
    all_goals nlinarith
  
  have h3 : (x + 2) / (x + 3) = 37 / 39 := by
    have h3 : Real.sqrt (x^2 + 4 * x + 4) / Real.sqrt (x^2 + 6 * x + 9) = (x + 2) / (x + 3) := by
      rw [h1, h2]
    rw [h3] at h 
    exact h
  
  have h4 : x + 3 ≠ 0 := by
    linarith
  
  field_simp [h4] at h3
  nlinarith