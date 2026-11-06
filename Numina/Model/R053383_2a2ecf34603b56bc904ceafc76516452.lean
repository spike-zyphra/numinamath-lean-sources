import Mathlib

theorem algebra_2885 :
  IsLeast {t : ℝ | ∃ x y, t = 4 * x ^ 2 + 18 * x * y + 21 * y ^ 2 + 10 * x + 30 * y + 30} 5 := by 
  constructor 
  · -- Show that 5 is achievable
    use 10, -5 
    norm_num 
  · -- Show that 5 is a lower bound
    intro k hk 
    rcases hk with ⟨x, y, hk⟩
    nlinarith [sq_nonneg (x - 10), sq_nonneg (y + 5), sq_nonneg (x * 4 + y * 9 + 5), sq_nonneg (x * 9 + y * 21 + 15)]