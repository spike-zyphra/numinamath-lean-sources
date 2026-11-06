import Mathlib

def f (x y : ℝ) := |x - y|

theorem algebra_94745 : ¬ (∀ x, f x 0 = x) := by 
  intro h
  have h1 := h (-1 : ℝ)
  norm_num [f] at h1
  all_goals norm_num at h1 <;> linarith