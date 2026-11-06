import Mathlib

open Real

theorem algebra_14207 {r : ℝ → ℝ} (hr : r = fun θ => 1 / (1 - θ)) :
    r (r (r (r (r (r 30))))) = 30 := by 
  rw [hr]
  norm_num