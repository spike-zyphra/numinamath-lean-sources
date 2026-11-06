import Mathlib

theorem algebra_95281
  {f : ℝ → ℝ}
  (h : ∀ x y, 0 < x → 0 < y → f (x * y) = f x / y)
  (h' : f 500 = 3) :
  f 600 = 5 / 2 := by 
  have eq1 : f 600 = f (500 * (6 / 5 : ℝ)) := by
    norm_num
  rw [eq1]
  have eq2 : f (500 * (6 / 5 : ℝ)) = f 500 / (6 / 5 : ℝ) := by
    apply h
    all_goals norm_num
  rw [eq2, h']
  norm_num