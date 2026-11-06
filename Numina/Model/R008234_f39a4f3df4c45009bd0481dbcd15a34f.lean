import Mathlib

theorem inequalities_127839 (a : ℝ) : a^6 - a^5 + a^4 + a^2 - a + 1 > 0 := by 
  have h1 : a^4 + 1 > 0 := by
    nlinarith [sq_nonneg (a ^ 2)]
  
  have h2 : a^2 - a + 1 > 0 := by
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (a + 1 / 2)]
  
  have h3 : a^6 - a^5 + a^4 + a^2 - a + 1 = (a^4 + 1) * (a^2 - a + 1) := by
    ring
  
  rw [h3]
  apply mul_pos 
  exact h1 
  exact h2