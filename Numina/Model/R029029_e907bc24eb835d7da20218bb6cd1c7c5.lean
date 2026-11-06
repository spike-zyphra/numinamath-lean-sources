import Mathlib

theorem algebra_21163 {x : ℤ} (hx : 0 ≤ x) (h : x * Real.sqrt x - 5 * x - 9 * Real.sqrt x = 35) :
    x = 49 := by
  have h1 : 0 ≤ (x : ℝ) := by exact_mod_cast hx
  have h3 : (x : ℝ) = (Real.sqrt (x : ℝ)) ^ 2 := by
    rw [Real.sq_sqrt]
    exact_mod_cast hx
  -- Now convert the equation into the polynomial in sqrt(x)
  -- Let's set y = sqrt(x). Then x = y^2. Then the equation becomes:
  -- y^2 * y - 5 * y^2 - 9 * y = 35, which simplifies to y^3 - 5y^2 - 9y - 35 = 0
  have h4 : (Real.sqrt (x : ℝ)) ^ 3 - 5 * (Real.sqrt (x : ℝ)) ^ 2 - 9 * (Real.sqrt (x : ℝ)) - 35 = 0 := by
    -- Set y = sqrt(x). The equation converted to polynomial in y.
    -- First, get the real version of h
    have h_eq : (x : ℝ) * Real.sqrt (x : ℝ) - 5 * (x : ℝ) - 9 * Real.sqrt (x : ℝ) = 35 := by
      exact_mod_cast h
    -- Now, use algebraic manipulation via nlinarith 
    -- to get the cubic polynomial in sqrt(x)
    have h_eq' : (x : ℝ) * Real.sqrt (x : ℝ) - 5 * (x : ℝ) - 9 * Real.sqrt (x : ℝ) = 35 := by
      exact_mod_cast h
    nlinarith [Real.sqrt_nonneg (x : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ x by exact_mod_cast hx), h_eq']
  -- Solve the cubic equation: y^3 - 5y^2 - 9y - 35 = 0 factors as (y - 7)(y^2 + 2y + 5) = 0.
  -- The quadratic y^2 + 2y + 5 has no real solutions because its discriminant is negative.
  -- Therefore, y = 7 is the only real solution. So sqrt(x) = 7, which means x = 49.
  have h6 : (Real.sqrt (x : ℝ) - 7) * ((Real.sqrt (x : ℝ)) ^ 2 + 2 * (Real.sqrt (x : ℝ)) + 5) = 0 := by
    nlinarith [Real.sqrt_nonneg (x : ℝ), h4]
  cases' (mul_eq_zero.1 h6) with h7 h8
  · -- Case 1: Real.sqrt (x : ℝ) - 7 = 0
    have h8' : Real.sqrt (x : ℝ) = 7 := by
      linarith [h7]
    have h9 : (x : ℝ) = 49 := by
      calc
        (x : ℝ) = (Real.sqrt (x : ℝ)) ^ 2 := by
          rw [Real.sq_sqrt]
          exact_mod_cast hx
        _ = (7 : ℝ) ^ 2 := by
          rw [h8']
        _ = (49 : ℝ) := by
          norm_num
    have h10 : x = 49 := by
      exact_mod_cast h9
    exact h10
  · -- Case 2: (Real.sqrt (x : ℝ)) ^ 2 + 2 * (Real.sqrt (x : ℝ)) + 5 = 0
    -- This quadratic has no real solutions because its discriminant is negative.
    -- We can show this using nlinarith.
    have h10 : (Real.sqrt (x : ℝ)) ^ 2 + 2 * (Real.sqrt (x : ℝ)) + 5 = 0 := by
      linarith [h8]
    -- Show that this leads to a contradiction
    nlinarith [Real.sqrt_nonneg (x : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ x by exact_mod_cast hx), sq_nonneg (Real.sqrt (x : ℝ) + 1), sq_nonneg (x : ℝ)]