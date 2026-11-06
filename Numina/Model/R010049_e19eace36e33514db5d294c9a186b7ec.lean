import Mathlib

theorem algebra_18861 :
    IsGreatest {y | ∃ x : ℝ, x ^ 2 + y ^ 2 = 14 * x + 48 * y} 49 := by 
  constructor
  · -- Show that 49 can be obtained
    use 7
    norm_num
  · -- Show that any y in the set is at most 49
    intro y hy
    rcases hy with ⟨x, hx⟩
    
    have h : (x - 7) ^ 2 + (y - 24) ^ 2 = 25 ^ 2 := by 
      nlinarith
    nlinarith [sq_nonneg (x - 7), sq_nonneg (y - 24)]