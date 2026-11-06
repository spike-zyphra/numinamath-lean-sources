import Mathlib

theorem algebra_94630 (x y : ℝ) (hx : x^2 - 7 * x - 9 = 0) (hy : y^2 - 7 * y - 9 = 0)
    (hxy : x ≠ y) : |x - y| = Real.sqrt 85 := by

  -- Subtract the two equations: x^2 - 7x - 9 - (y^2 - 7 y - 9) = 0
  have h1 : x^2 - y^2 - 7 * (x - y) = 0 := by 
    nlinarith [hx, hy]

  -- This factors as (x - y)(x + y - 7) = 0
  have h2 : (x - y) * (x + y - 7) = 0 := by
    nlinarith [h1]

  cases (mul_eq_zero.mp h2) with
  | inl h3 =>
    -- This tells us that x - y = 0, which implies x = y, contradicting hxy
    exfalso
    apply hxy
    linarith

  | inr h4 =>
    -- This tells us that x + y - 7 = 0, so x + y = 7
    have h5 : x + y = 7 := by linarith

    -- Now, compute (x - y)^2 using algebra
    -- (x - y)^2 = (x + y)^2 - 4xy

    -- Compute xy using information from hx and hy
    have h6 : (x - y) ^ 2 = 85 := by
      nlinarith [hx, hy, h5]

    -- Now compute |x - y| = sqrt((x - y)^2) = sqrt(85)
    have h7 : |x - y| = Real.sqrt ((x - y) ^ 2) := by 
      rw [Real.sqrt_sq_eq_abs]
    
    rw [h7]
    rw [h6]
    all_goals norm_num