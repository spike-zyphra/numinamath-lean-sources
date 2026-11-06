import Mathlib

theorem algebra_238658 (a b : ℝ) (ha : a ≠ 0) (h1 : 1 ≤ a * (-1)^2 + b * (-1) ∧ a * (-1)^2 + b * (-1) ≤ 2)
    (h2 : 2 ≤ a * 1^2 + b * 1 ∧ a * 1^2 + b * 1 ≤ 4) :
    5 ≤ a * (-2)^2 + b * (-2) ∧ a * (-2)^2 + b * (-2) ≤ 10 := by

  have h11 : 1 ≤ a * (-1)^2 + b * (-1) := h1.1
  have h12 : a * (-1)^2 + b * (-1) ≤ 2 := h1.2
  have h21 : 2 ≤ a * 1^2 + b * 1 := h2.1
  have h22 : a * 1^2 + b * 1 ≤ 4 := h2.2

  have h3 : 1 ≤ a - b := by linarith
  have h4 : a - b ≤ 2 := by linarith
  have h5 : 2 ≤ a + b := by linarith
  have h6 : a + b ≤ 4 := by linarith
  
  have h7 : a * (-2)^2 + b * (-2) = 3 * (a - b) + (a + b) := by 
    ring

  rw [h7]

  constructor
  · -- Prove the lower bound
    linarith
  
  · -- Prove the upper bound
    linarith