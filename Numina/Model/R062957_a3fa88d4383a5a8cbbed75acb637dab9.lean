import Mathlib

theorem inequalities_246965 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 1 / x + 1 / y + 1 / z = 1) :
    (x - 1) * (y - 1) * (z - 1) ≥ 8 := by
  have h1 : x * y * z ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    linarith
    linarith
    linarith

  -- Convert reciprocal equation to symmetric form without denominators
  have eq1 : x * y + x * z + y * z = x * y * z := by
    field_simp [h1] at h
    nlinarith
  
  -- Transform the left-hand side of the goal using algebra
  have h2 : (x - 1) * (y - 1) * (z - 1) = x + y + z - 1 := by
    nlinarith [eq1]

  -- Prove the required minimum value using squared expressions
  have h3 : x + y + z ≥ 9 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]
  
  -- Conclude the result by substituting into the transformed expression
  linarith [h2, h3]