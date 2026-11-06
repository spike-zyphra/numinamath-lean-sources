import Mathlib

theorem algebra_165896 (x : ℝ) (hx : x ≥ 0) :
    (Real.sqrt (x + 1) + Real.sqrt x)^3 + (Real.sqrt (x + 1) + Real.sqrt x)^2 = 2 ↔ x = 0 := by
  constructor
  · -- Assume the equation holds, prove x = 0
    intro h_eq
    -- We need to prove x = 0 from the equation
    have h1 : Real.sqrt (x + 1) + Real.sqrt x = 1 := by
      have eq1 : (Real.sqrt (x + 1) + Real.sqrt x) ^ 3 + (Real.sqrt (x + 1) + Real.sqrt x) ^ 2 - 2 = 0 := by
        linarith
      have h_eq1 : ((Real.sqrt (x + 1) + Real.sqrt x) - 1) * ((Real.sqrt (x + 1) + Real.sqrt x) ^ 2 + 2 * (Real.sqrt (x + 1) + Real.sqrt x) + 2) = 0 := by
        nlinarith [sq_nonneg ((Real.sqrt (x + 1) + Real.sqrt x) ^ 2 + 2 * (Real.sqrt (x + 1) + Real.sqrt x) + 2), sq_nonneg ((Real.sqrt (x + 1) + Real.sqrt x) - 1)]
      cases' (mul_eq_zero.mp h_eq1) with h_eq2 h_eq3
      · -- Case where ((Real.sqrt (x + 1) + Real.sqrt x) - 1) = 0
        linarith
      · -- Case where ((Real.sqrt (x + 1) + Real.sqrt x) ^ 2 + 2 * (Real.sqrt (x + 1) + Real.sqrt x) + 2) = 0
        nlinarith [sq_nonneg (Real.sqrt (x + 1) + Real.sqrt x + 1), sq_nonneg (Real.sqrt (x + 1) - Real.sqrt x), sq_nonneg (Real.sqrt (x + 1) + Real.sqrt x), mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (x + 1))]
    -- Now we have Real.sqrt (x + 1) + Real.sqrt x = 1, we need to solve for x
    have h2 : Real.sqrt (x + 1) = 1 - Real.sqrt x := by
      linarith [h1]
    -- Square both sides
    have h3 : Real.sqrt (x + 1) ^ 2 = (1 - Real.sqrt x) ^ 2 := by
      rw [h2]
    -- Simplify real.sqrt (x + 1) ^ 2 = x + 1
    have h4 : Real.sqrt (x + 1) ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
    rw [h4] at h3
    -- Expand (1 - Real.sqrt x)^2
    have h5 : (1 - Real.sqrt x) ^ 2 = 1 - 2 * Real.sqrt x + (Real.sqrt x) ^ 2 := by
      ring
    rw [h5] at h3
    -- Simplify (Real.sqrt x)^2 = x
    have h6 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
    rw [h6] at h3
    -- Simplify the equation to show contradiction
    have h7 : Real.sqrt x = 0 := by
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (x + 1)]
    -- Real.sqrt x = 0 implies x = 0
    have h8 : x = 0 := by
      rw [Real.sqrt_eq_zero (by linarith)] at h7
      linarith
    linarith
  · -- Assume x = 0, prove the equation
    intro h_eq
    rw [h_eq]
    have h1 : Real.sqrt (0 + 1 : ℝ) = 1 := by
      norm_num [Real.sqrt_eq_iff_sq_eq]
    have h2 : Real.sqrt (0 : ℝ) = 0 := by
      norm_num [Real.sqrt_eq_zero]
    rw [h1, h2]
    all_goals norm_num