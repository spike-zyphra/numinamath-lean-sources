import Mathlib

theorem algebra_322401 {x y z : ℝ} (h : x ≠ -y) (h' : -2 * y + z ≠ 0) (h'' : (2 * x + z) ^ 2 / ((x + y) * (-2 * y + z)) = 8) :
    2 * x + 4 * y - z + 6 = 6 := by
  -- Prove the denominator is non-zero
  have h_denom_ne_zero : (x + y) * (-2 * y + z) ≠ 0 := by
    refine mul_ne_zero ?_ h' -- Use h' directly for the second part of the product
    -- Prove x + y ≠ 0 using h : x ≠ -y
    intro hxy_zero -- Assume x + y = 0 for contradiction
    apply h -- Use h to show this leads to a contradiction (x ≠ -y)
    linarith [hxy_zero] -- x + y = 0 implies x = -y, which contradicts h
  -- Rewrite the division equation h'' into a polynomial equation
  have h_eq_rw : (2 * x + z) ^ 2 = 8 * ((x + y) * (-2 * y + z)) := by
    -- We know A / B = C and B ≠ 0 => A = B * C. Use div_eq_iff
    rw [div_eq_iff h_denom_ne_zero] at h''
    exact h'' -- h'' is now exactly what we want
  -- From h_eq_rw, derive that (2 * (x + 2 * y) - z) ^ 2 = 0
  have h_sq_eq_zero : (2 * (x + 2 * y) - z) ^ 2 = 0 := by
    -- This requires algebraic manipulation which nlinarith can handle
    nlinarith [h_eq_rw]
  -- From (2 * (x + 2 * y) - z) ^ 2 = 0, derive 2 * (x + 2 * y) - z = 0
  have h_beaucoup_bolts : 2 * (x + 2 * y) - z = 0 := by
    -- If square is zero, the value must be zero. nlinarith can handle this.
    nlinarith [h_sq_eq_zero]
  -- Use the linear equation 2 * (x + 2 * y) - z = 0 to prove the final linear goal
  linarith [h_beaucoup_bolts] -- This should simplify 2x + 4y - z + 6 = 6 using h_beaucoup_bolts