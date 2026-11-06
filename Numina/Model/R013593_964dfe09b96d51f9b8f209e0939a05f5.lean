import Mathlib

theorem algebra_1105 (x : ℝ) (hx : x = -60 * Real.pi / 180) : Real.sin x = -Real.sqrt 3 / 2 := by
  have hx2 : x = - (Real.pi / 3) := by 
    rw [hx]
    ring_nf
  rw [hx2]
  have h1 : Real.sin (- (Real.pi / 3)) = - Real.sin (Real.pi / 3) := by 
    rw [Real.sin_neg]
  have h2 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  rw [h1, h2]
  ring