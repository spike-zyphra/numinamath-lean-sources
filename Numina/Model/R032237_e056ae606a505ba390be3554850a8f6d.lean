import Mathlib


theorem algebra_9086 {f : ℝ → ℝ}  (hf : f = fun x => (x - 3) * Real.exp x) :
    (deriv f) 0 = -2 := by
  rw [hf]
  simp [deriv_mul, deriv_sub, deriv_id'', mul_comm]
  all_goals norm_num [Real.deriv_exp]