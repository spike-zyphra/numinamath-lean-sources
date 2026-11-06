import Mathlib

open Real

theorem algebra_21956 {f g : ℝ → ℝ}
    (hf : ∀ x, f x = x ^ 2 - 2 * x + 1)
    (hg : ∀ x, g x = sqrt (2 * x + 1)) :
    f (g 4) - g (f 3) = 1 := by
  -- Calculate g(4) = sqrt(2*4 + 1) = sqrt(9) = 3
  have g4 : g 4 = 3 := by 
    rw [hg]
    have h1 : sqrt (2 * (4 : ℝ) + 1) = 3 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1]
  -- Calculate f(3) = 3^2 - 2*3 + 1 = 4
  have f3 : f 3 = 4 := by 
    rw [hf]
    norm_num
  -- Therefore f(g(4)) = f(3) = 4
  have fg4 : f (g 4) = 4 := by
    rw [g4]
    exact f3
  -- Calculate g(f(3)) = g(4) = 3
  have gf3 : g (f 3) = 3 := by 
    rw [f3]
    rw [hg]
    have h1 : sqrt (2 * (4 : ℝ) + 1) = 3 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1]
  -- Therefore f(g(4)) - g(f(3)) = 4 - 3 = 1
  rw [fg4, gf3]
  all_goals norm_num