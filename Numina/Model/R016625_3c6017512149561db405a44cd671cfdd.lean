import Mathlib

theorem algebra_322784 (x y : ℝ) (h : (Real.sqrt (x^2 + 1) - x + 1) * (Real.sqrt (y^2 + 1) - y + 1) = 2) :
    x * y = 1 := by
  have h1 : 0 ≤ Real.sqrt (x ^ 2 + 1) := Real.sqrt_nonneg (x ^ 2 + 1)
  have h2 : 0 ≤ Real.sqrt (y ^ 2 + 1) := Real.sqrt_nonneg (y ^ 2 + 1)
  have h3 : Real.sqrt (x^2 + 1) ^ 2 = x^2 + 1 := Real.sq_sqrt (by positivity)
  have h4 : Real.sqrt (y^2 + 1) ^ 2 = y^2 + 1 := Real.sq_sqrt (by positivity)
  have h5 : Real.sqrt (x^2 + 1) - x + 1 ≠ 0 := by
    by_contra h5
    have h6 : (Real.sqrt (x^2 + 1) - x + 1) * (Real.sqrt (y^2 + 1) - y + 1) = 0 := by 
      rw [h5]
      norm_num
    linarith
  have h6 : Real.sqrt (y^2 + 1) - y + 1 ≠ 0 := by
    by_contra h6
    have h7 : (Real.sqrt (x^2 + 1) - x + 1) * (Real.sqrt (y^2 + 1) - y + 1) = 0 := by 
      rw [h6]
      norm_num
    linarith
  have h7 : (Real.sqrt (x^2 + 1) - x) * (Real.sqrt (x^2 + 1) + x) = 1 := by
    nlinarith
  have h8 : (Real.sqrt (x^2 + 1) - x + 1) * (Real.sqrt (x^2 + 1) + x - 1) = 2 * x := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), sq_nonneg (x * y), h3]
  have h9 : (Real.sqrt (y^2 + 1) - y + 1) * (Real.sqrt (y^2 + 1) + y - 1) = 2 * y := by
    nlinarith [Real.sqrt_nonneg (y ^ 2 + 1), sq_nonneg (x * y), h4]
  -- Now proceeding to clear the square roots from the equation by multiplying conjugates 
  have h10 : (Real.sqrt (x^2 + 1) - x + 1) * (Real.sqrt (y^2 + 1) - y + 1) * ((Real.sqrt (x^2 + 1) + x - 1) * (Real.sqrt (y^2 + 1) + y - 1)) = 4 * (x * y) := by
    calc 
      (Real.sqrt (x^2 + 1) - x + 1) * (Real.sqrt (y^2 + 1) - y + 1) * ((Real.sqrt (x^2 + 1) + x - 1) * (Real.sqrt (y^2 + 1) + y - 1))
          = ((Real.sqrt (x^2 + 1) - x + 1) * (Real.sqrt (x^2 + 1) + x - 1)) * ((Real.sqrt (y^2 + 1) - y + 1) * (Real.sqrt (y^2 + 1) + y - 1)) := by 
            ring_nf
      _ = (2 * x) * (2 * y) := by 
          rw [h8, h9]
      _ = 4 * (x * y) := by 
          ring_nf
  -- Now using h and h10 to solve for x * y
  have eq3 : (Real.sqrt (x^2 + 1) + x - 1) * (Real.sqrt (y^2 + 1) + y - 1) = 2 * (x * y) := by
    have h11 : (Real.sqrt (x^2 + 1) - x + 1) * (Real.sqrt (y^2 + 1) - y + 1) * ((Real.sqrt (x^2 + 1) + x - 1) * (Real.sqrt (y^2 + 1) + y - 1)) = 4 * (x * y) := h10
    rw [show (Real.sqrt (x^2 + 1) - x + 1) * (Real.sqrt (y^2 + 1) - y + 1) = 2 by linarith [h]] at h11
    nlinarith
  have eq4 : x * y = 1 := by 
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), 
      Real.sqrt_nonneg (x^2 + 1), Real.sqrt_nonneg (y^2 + 1), 
      sq_nonneg (x + 1), sq_nonneg (y + 1), 
      mul_nonneg (Real.sqrt_nonneg (x^2 + 1)) (Real.sqrt_nonneg (y^2 + 1)), 
      sq_nonneg (Real.sqrt (x^2 + 1) - Real.sqrt (y^2 + 1)), 
      sq_nonneg (x - y),
      mul_nonneg (sq_nonneg (x - 1)) (sq_nonneg (y - 1))
    ]
  linarith