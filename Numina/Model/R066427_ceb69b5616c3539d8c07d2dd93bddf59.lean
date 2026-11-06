import Mathlib

theorem inequalities_1529 (a : ℝ) (ha : -1 < a ∧ a < 0) : -a > a^2 := by
  have h1 : -1 < a := ha.1
  have h2 : a < 0 := ha.2

  have h3 : a + 1 > 0 := by linarith
  
  have h4 : a * (a + 1) < 0 := by 
    apply mul_neg_of_neg_of_pos
    linarith
    linarith
  
  nlinarith