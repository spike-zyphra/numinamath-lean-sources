import Mathlib

theorem algebra_322485 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z * (x + y + z) = 1) :
    (x + y) * (y + z) ≥ 2 := by

  have h1 : (x + y) * (y + z) = y * (x + y + z) + x * z := by 
    ring
  have h2 : 0 < x * z := by
    apply mul_pos
    exact hx
    exact hz

  -- $y * (x + y + z) > 0$ because $y > 0$ and $x + y + z > 0$
  have h3 : 0 < y * (x + y + z) := by
    apply mul_pos
    all_goals linarith
  have h4 : y * (x + y + z) * (x * z) = 1 := by 
    nlinarith
  
  have h5 : y * (x + y + z) + x * z ≥ 2 := by
    nlinarith [sq_nonneg (y * (x + y + z) - 1), sq_nonneg (x * z - 1), 
      mul_pos h3 h2, h4]

  rw [h1]
  linarith [h5]