import Mathlib
set_option maxHeartbeats 800000
/- 4. 136 Positive numbers \( x, y, \approx \) satisfy the system of equations
\[
\left\{\begin{array}{l}
x^{2}+x y+\frac{y^{2}}{3}=25, \\
\frac{y^{2}}{3}+z^{2}=9, \\
z^{2}+z x+x^{2}=16 .
\end{array}\right.
\]

Find the value of \( x y + 2 y z + 3 z x \). -/
theorem algebra_121038 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + x * y + y^2 / 3 = 25) (h2 : y^2 / 3 + z^2 = 9) (h3 : z^2 + z * x + x^2 = 16) :
    x * y + 2 * y * z + 3 * z * x = 24 * Real.sqrt 3 := by
  -- First, we prove that the square of our target expression equals (24*√3)²
  -- using nonlinear arithmetic and several inequality facts
  have h5 : (x * y + 2 * y * z + 3 * z * x) ^ 2 = (24 * Real.sqrt 3) ^ 2 := by
    nlinarith [sq_nonneg (x - y / 2 - z * Real.sqrt 3), sq_nonneg (y - z * Real.sqrt 3), sq_nonneg (z - x / 2 - x * Real.sqrt 3),
              Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num),
              mul_self_nonneg (x - y / 2 - z * Real.sqrt 3), mul_self_nonneg (y - z * Real.sqrt 3),
              mul_self_nonneg (z - x / 2 - x * Real.sqrt 3)]

  -- Prove that our target expression is non-negative
  -- This is needed to determine the sign when taking the square root
  have h6 : x * y + 2 * y * z + 3 * z * x ≥ 0 := by
    nlinarith [mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith),
              mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ z by linarith),
              mul_nonneg (show 0 ≤ z by linarith) (show 0 ≤ x by linarith)]

  -- Main proof of the target equality
  have h7 : x * y + 2 * y * z + 3 * z * x = 24 * Real.sqrt 3 := by
    -- Duplicate the goal for clarity
    have h8 : x * y + 2 * y * z + 3 * z * x = 24 * Real.sqrt 3 := by
      -- Restate that our target expression is non-negative
      have h9 : x * y + 2 * y * z + 3 * z * x ≥ 0 := h6
      -- Prove that 24*√3 is also non-negative
      have h10 : 24 * Real.sqrt 3 ≥ 0 := by
        apply mul_nonneg
        norm_num
        apply Real.sqrt_nonneg
      -- Prove the equality by analyzing the squared equation
      have h11 : (x * y + 2 * y * z + 3 * z * x) = 24 * Real.sqrt 3 := by
        -- The difference of squares equals zero
        have h12 : (x * y + 2 * y * z + 3 * z * x) ^ 2 - (24 * Real.sqrt 3) ^ 2 = 0 := by linarith
        -- Factor the difference of squares
        have h13 : ((x * y + 2 * y * z + 3 * z * x) - 24 * Real.sqrt 3) * ((x * y + 2 * y * z + 3 * z * x) + 24 * Real.sqrt 3) = 0 := by
          ring_nf at h12 ⊢
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
        -- Since the product is zero, one of the factors must be zero
        cases' (mul_eq_zero.mp h13) with h14 h15
        · -- Case 1: (x*y + 2*y*z + 3*z*x) - 24*√3 = 0
          linarith
        · -- Case 2: (x*y + 2*y*z + 3*z*x) + 24*√3 = 0
          -- This would imply our expression equals -24*√3
          have h16 : x * y + 2 * y * z + 3 * z * x = -24 * Real.sqrt 3 := by linarith
          -- But this contradicts our non-negativity proof, so this case is impossible
          nlinarith [h9, Real.sqrt_nonneg 3, h16]
      linarith
    linarith
  -- Return the final result
  exact h7
