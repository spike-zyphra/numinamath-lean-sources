import Mathlib

def f (a b : ℝ) := 3 * a + 4 * b

theorem algebra_242541 {x : ℝ} (hx : f x 7 = 37) :
    f (1 / 3) (f x (1 / 4)) = 41 := by
  simp [f] at hx
  have hx_val : x = 3 := by
    linarith 
  simp [f, hx_val]
  all_goals linarith