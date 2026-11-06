import Mathlib

/- 6. Let positive numbers $x, y, z$ satisfy $x^{2}+y^{2}+z^{2}=1$, prove that $\frac{x y}{z}+\frac{y z}{x}+\frac{z x}{y} \geqslant \sqrt{3}$. -/
theorem inequalities_104909 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 = 1) :
    Real.sqrt 3 ≤ x * y / z + y * z / x + z * x / y := by

  -- Main proof: Show that our expression is greater than or equal to √3
  have h1 : x * y / z + y * z / x + z * x / y ≥ Real.sqrt 3 := by
    -- Strategy: Square both sides and prove the squared inequality
    have h2 : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ 3 := by
      -- Expand the square of the sum into individual terms
      have h3 : (x * y / z + y * z / x + z * x / y) ^ 2 = (x * y / z) ^ 2 + (y * z / x) ^ 2 + (z * x / y) ^ 2 + 2 * ((x * y / z) * (y * z / x) + (y * z / x) * (z * x / y) + (z * x / y) * (x * y / z)) := by
        ring
      rw [h3]
      -- Simplify the cross-product terms to x²+y²+z², which equals 1
      have h4 : (x * y / z) * (y * z / x) + (y * z / x) * (z * x / y) + (z * x / y) * (x * y / z) = x^2 + y^2 + z^2 := by
        field_simp
        nlinarith [mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]
      -- Apply AM-GM inequality to show the sum of squares is at least 3
      nlinarith [sq_nonneg (x * y / z - y * z / x), sq_nonneg (y * z / x - z * x / y), sq_nonneg (z * x / y - x * y / z)]
    -- Prove that our expression is non-negative (needed for taking square root)
    have h7 : x * y / z + y * z / x + z * x / y ≥ 0 := by
      apply add_nonneg
      apply add_nonneg
      -- Show xy/z ≥ 0
      · apply div_nonneg
        · apply mul_nonneg
          all_goals linarith
        · linarith
      -- Show yz/x ≥ 0
      · apply div_nonneg
        · apply mul_nonneg
          all_goals linarith
        · linarith
      -- Show zx/y ≥ 0
      · apply div_nonneg
        · apply mul_nonneg
          all_goals linarith
        · linarith
    -- Apply square root to both sides of the inequality
    have h8 : Real.sqrt 3 ≤ x * y / z + y * z / x + z * x / y := by
      -- Use the squared inequality and properties of square roots
      have h9 : Real.sqrt 3 ^ 2 ≤ (x * y / z + y * z / x + z * x / y) ^ 2 := by linarith [h2, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      nlinarith [h7, Real.sqrt_nonneg 3]
    linarith [h8]
  -- Conclude the proof using our main result
  linarith [h1]
