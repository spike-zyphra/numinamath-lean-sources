import Mathlib

/- Let $x,$ $y,$ and $z$ be real numbers such that $x + y + z = 6$ and $\frac{1}{x} + \frac{1}{y} + \frac{1}{z} = 2.$  Find \[\frac{x + y}{z} + \frac{y + z}{x} + \frac{x + z}{y}.\] -/
theorem algebra_21132 {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (h₀ : x + y + z = 6) (h₁ : 1 / x + 1 / y + 1 / z = 2) : (x + y) / z + (y + z) / x + (x + z) / y = 9 := by
  -- Rewrite the left-hand side using the given solution
  calc
    (x + y) / z + (y + z) / x + (x + z) / y = (6 - z) / z + (6 - x) / x + (6 - y) / y := by
      rw [← h₀]
      ring_nf
    _ = 6 * (1 / x + 1 / y + 1 / z) - 3 := by
      have mid1 : (6 - x) / x = 6 / x - 1 := by
        field_simp
      have mid2 : (6 - y) / y = 6 / y - 1 := by
        field_simp
      have mid3 : (6 - z) / z = 6 / z - 1 := by
        field_simp
      rw [mid1, mid2, mid3]
      ring_nf
    _ = 6 * 2 - 3 := by
      rw [h₁]
    _ = 9 := by
      norm_num

