import Mathlib

/- The lengths of two opposite sides of a square are decreased by $40\%$ while the lengths of the other two sides are increased by $50\%$ to form a rectangle. By what percent does the square's area decrease? -/
theorem algebra_20048 {x : ℝ} (hx : x ≠ 0) (h : (x * 0.6) * (x * 1.5) = (x ^ 2) * (1 - y)) :
  y = 0.1 := by
  -- Solve for the equation $(x * 0.6) * (x * 1.5) = (x ^ 2) * (1 - y)$
  rw [mul_assoc x, ← mul_assoc 0.6, mul_comm 0.6, ← mul_assoc, ← mul_assoc, pow_two] at h
  simp only [mul_assoc] at h
  apply mul_left_cancel₀ hx at h
  apply mul_left_cancel₀ hx at h
  ring_nf at h
  have yeq : y = 1 / 10 := by
    linarith
  rw [yeq]
  norm_num