import Mathlib
set_option maxHeartbeats 800000
/- 15. (Switzerland) Given $x, y, z > 0$, and $xyz = 1$, prove:
$$\frac{(x+y-1)^{2}}{z}+\frac{(y+z-1)^{2}}{x}+\frac{(z+x-1)^{2}}{y} \geqslant x+y+z$$ -/
theorem inequalities_597268 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    (x + y - 1) ^ 2 / z + (y + z - 1) ^ 2 / x + (z + x - 1) ^ 2 / y ≥ x + y + z := by
  -- Apply AM-GM inequality to (x+y-1)²/z + z ≥ 2(x+y-1)
  have h1 : (x + y - 1) ^ 2 / z + z ≥ 2 * (x + y - 1) := by
    -- Prove that (x+y-1)² + z² ≥ 2z(x+y-1) using the square of difference
    have h : (x + y - 1) ^ 2 + z ^ 2 ≥ 2 * z * (x + y - 1) := by
      nlinarith [sq_nonneg (x + y - 1 - z)]
    -- Derive the AM-GM inequality in the form we need
    have h' : (x + y - 1) ^ 2 / z + z ≥ 2 * (x + y - 1) := by
      -- Show that the difference is non-negative
      have h1 : (x + y - 1) ^ 2 / z + z - 2 * (x + y - 1) ≥ 0 := by
        -- Restate the inequality in terms of squares
        have h2 : (x + y - 1) ^ 2 + z^2 - 2 * z * (x + y - 1) ≥ 0 := by linarith
        -- Algebraic manipulation to get the desired form
        have h3 : (x + y - 1) ^ 2 / z + z - 2 * (x + y - 1) = ((x + y - 1) ^ 2 + z^2 - 2 * z * (x + y - 1)) / z := by
          field_simp
          nlinarith
        rw [h3]
        exact div_nonneg h2 (by nlinarith)
      linarith
    linarith

  -- Apply AM-GM inequality to (y+z-1)²/x + x ≥ 2(y+z-1)
  have h2 : (y + z - 1) ^ 2 / x + x ≥ 2 * (y + z - 1) := by
    -- Prove that (y+z-1)² + x² ≥ 2x(y+z-1) using the square of difference
    have h : (y + z - 1) ^ 2 + x ^ 2 ≥ 2 * x * (y + z - 1) := by
      nlinarith [sq_nonneg (y + z - 1 - x)]
    -- Derive the AM-GM inequality in the form we need
    have h' : (y + z - 1) ^ 2 / x + x ≥ 2 * (y + z - 1) := by
      -- Show that the difference is non-negative
      have h1 : (y + z - 1) ^ 2 / x + x - 2 * (y + z - 1) ≥ 0 := by
        -- Restate the inequality in terms of squares
        have h2 : (y + z - 1) ^ 2 + x^2 - 2 * x * (y + z - 1) ≥ 0 := by linarith
        -- Algebraic manipulation to get the desired form
        have h3 : (y + z - 1) ^ 2 / x + x - 2 * (y + z - 1) = ((y + z - 1) ^ 2 + x^2 - 2 * x * (y + z - 1)) / x := by
          field_simp
          nlinarith
        rw [h3]
        exact div_nonneg h2 (by nlinarith)
      linarith
    linarith

  -- Apply AM-GM inequality to (z+x-1)²/y + y ≥ 2(z+x-1)
  have h3 : (z + x - 1) ^ 2 / y + y ≥ 2 * (z + x - 1) := by
    -- Prove that (z+x-1)² + y² ≥ 2y(z+x-1) using the square of difference
    have h : (z + x - 1) ^ 2 + y ^ 2 ≥ 2 * y * (z + x - 1) := by
      nlinarith [sq_nonneg (z + x - 1 - y)]
    -- Derive the AM-GM inequality in the form we need
    have h' : (z + x - 1) ^ 2 / y + y ≥ 2 * (z + x - 1) := by
      -- Show that the difference is non-negative
      have h1 : (z + x - 1) ^ 2 / y + y - 2 * (z + x - 1) ≥ 0 := by
        -- Restate the inequality in terms of squares
        have h2 : (z + x - 1) ^ 2 + y^2 - 2 * y * (z + x - 1) ≥ 0 := by linarith
        -- Algebraic manipulation to get the desired form
        have h3 : (z + x - 1) ^ 2 / y + y - 2 * (z + x - 1) = ((z + x - 1) ^ 2 + y^2 - 2 * y * (z + x - 1)) / y := by
          field_simp
          nlinarith
        rw [h3]
        exact div_nonneg h2 (by nlinarith)
      linarith
    linarith

  -- Combine the three AM-GM inequalities to get a lower bound
  have h4 : (x + y - 1) ^ 2 / z + (y + z - 1) ^ 2 / x + (z + x - 1) ^ 2 / y + (x + y + z) ≥ 4 * (x + y + z) - 6 := by
    linarith [h1, h2, h3]

  -- Simplify the inequality by subtracting (x+y+z) from both sides
  have h5 : (x + y - 1) ^ 2 / z + (y + z - 1) ^ 2 / x + (z + x - 1) ^ 2 / y ≥ 3 * (x + y + z) - 6 := by
    linarith [h4]

  -- Prove that 3(x+y+z)-6 ≥ x+y+z using the constraint xyz = 1
  have h6 : 3 * (x + y + z) - 6 ≥ x + y + z := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, hxyz]

  -- Combine the inequalities to reach the final conclusion
  linarith [h5, h6]
