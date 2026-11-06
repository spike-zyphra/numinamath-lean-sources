import Mathlib

theorem algebra_269082 {x y z : ℝ} (h : x + y + z = 0) :
    x^3 + y^3 + z^3 = 3 * x * y * z := by 
  have h1 : z = -x - y := by linarith 
  rw [h1]
  ring