import Mathlib

theorem algebra_232922 {x : ℝ} (hx : x ≠ 0) 
    (h : (1 + 20 / 100) * x = 2 * (1 - 20 / 100) * (x - 20)) :
    x = 80 := by linarith