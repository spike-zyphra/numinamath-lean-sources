import Mathlib

theorem calculus_228980 (f : ℝ → ℝ) (a : ℝ) (hf : f = fun x => x ^ a) (x : ℝ) (hx : x > 0) :
    deriv f x = a * x ^ (a - 1) := by 
  rw [hf]
  simp [deriv_pow', hx.ne']
  all_goals
    try positivity