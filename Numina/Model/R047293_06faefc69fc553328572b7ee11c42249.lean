import Mathlib

theorem inequalities_598902
    (x y z : ℝ)
    (hx : 0 ≤ x)
    (hy : 0 ≤ y)
    (hz : 0 ≤ z)
    (h : x * y + y * z + z * x = 1) :
    5 / 2 ≤ 1 / (x + y) + 1 / (y + z) + 1 / (z + x) := by

  have h1 : x + y > 0 := by 
    by_contra h1
    push_neg at h1
    have hx1 : x = 0 := by linarith
    have hy1 : y = 0 := by linarith
    rw [hx1, hy1] at h
    nlinarith

  have h2 : y + z > 0 := by 
    by_contra h2
    push_neg at h2
    have hy1 : y = 0 := by linarith
    have hz1 : z = 0 := by linarith
    rw [hy1, hz1] at h
    nlinarith

  have h3 : z + x > 0 := by
    by_contra h3
    push_neg at h3
    have hz1 : z = 0 := by linarith
    have hx1 : x = 0 := by linarith
    rw [hx1, hz1] at h
    nlinarith

  have h4 : 0 < (x + y) * (y + z) * (z + x) := by
    positivity

  have h5 : 1 / (x + y) + 1 / (y + z) + 1 / (z + x) - 5 / 2 ≥ 0 := by

    have pos1 : 0 < (x + y) * (y + z) * (z + x) := h4

    have h6 : 1 / (x + y) + 1 / (y + z) + 1 / (z + x) - 5 / 2 = (2 * (y + z) * (z + x) + 2 * (x + y) * (z + x) + 2 * (x + y) * (y + z) - 5 * (x + y) * (y + z) * (z + x)) / (2 * (x + y) * (y + z) * (z + x)) := by 
      field_simp
      <;> ring

    rw [h6] at *
    apply div_nonneg
    · -- Show the numerator is non-negative 
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x + y + z - 2), sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
          mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx 
        ]
    · -- Show the denominator is positive
      positivity

  linarith