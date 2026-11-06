import Mathlib

theorem algebra_12656 {a b c : ℝ} (ha : a ≠ 0) (hvertex : ∀ x, a * x ^ 2 + b * x + c = a * (x - 3) ^ 2 + 7) (hx1 : a * (-2) ^ 2 + b * (-2) + c = 0) :
    ∃ x2, x2 ≠ -2 ∧ a * x2 ^ 2 + b * x2 + c = 0 := by
  have eq1 := hvertex 0
  have eq2 := hvertex 1
  have eq3 : c = 9 * a + 7 := by 
    linarith
  
  have eq4 : a + b + c = 4 * a + 7 := by 
    linarith
  
  have eq5 : b = -6 * a := by
    linarith [eq3, eq4]

  have h_a : a = -7 / 25 := by
    rw [show b = -6 * a by linarith [eq5], show c = 9 * a + 7 by linarith [eq3]] at hx1
    linarith
  
  have h8 : a * 8 ^ 2 + b * 8 + c = 0 := by
    rw [show b = -6 * a by linarith [eq5], show c = 9 * a + 7 by linarith [eq3]]
    rw [h_a]
    norm_num
  
  use 8
  constructor
  · 
    norm_num
  
  · 
    linarith [h8]