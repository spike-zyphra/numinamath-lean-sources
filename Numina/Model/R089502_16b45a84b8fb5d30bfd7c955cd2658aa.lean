import Mathlib

theorem algebra_304212 {x : ℝ} (hx : 15 - x^2 ≥ 0) (h : √(25 - x^2) - √(15 - x^2) = 2) :
    √(25 - x^2) + √(15 - x^2) = 5 := by
  have h1 : √(25 - x^2) ≥ 0 := by positivity
  have h2 : √(15 - x^2) ≥ 0 := by positivity
  have h4 : (√(25 - x^2)) ^ 2 = 25 - x^2 := by 
    rw [Real.sq_sqrt]
    have : 25 - x^2 ≥ 0 := by nlinarith
    linarith
  have h5 : (√(15 - x^2)) ^ 2 = 15 - x^2 := by 
    rw [Real.sq_sqrt]
    have : 15 - x^2 ≥ 0 := by linarith
    linarith
  have h6 : (√(25 - x^2) - √(15 - x^2)) * (√(25 - x^2) + √(15 - x^2)) = 10 := by
    calc 
      (√(25 - x^2) - √(15 - x^2)) * (√(25 - x^2) + √(15 - x^2)) = (√(25 - x^2))^2 - (√(15 - x^2))^2 := by ring
      _ = (25 - x^2) - (15 - x^2) := by rw [h4, h5]
      _ = 10 := by linarith
  have h7 : (√(25 - x^2) + √(15 - x^2)) = 5 := by
    have h9 : (√(25 - x^2) - √(15 - x^2)) = 2 := by linarith [h]
    have h10 : (√(25 - x^2) + √(15 - x^2)) = 5 := by
      have eq1 : (√(25 - x^2) - √(15 - x^2)) * (√(25 - x^2) + √(15 - x^2)) = 10 := by
        linarith [h6]
      rw [h9] at eq1
      nlinarith
    linarith [h10]
  linarith [h7]