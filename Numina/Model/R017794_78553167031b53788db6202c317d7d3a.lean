import Mathlib

theorem algebra_299212 {x y : ℝ} (h : (x + Real.sqrt (x^2 + 1)) * (y + Real.sqrt (y^2 + 4)) = 9) :
    x * Real.sqrt (y^2 + 4) + y * Real.sqrt (x^2 + 1) = 77 / 18 := by

  have h3 : (x + Real.sqrt (x^2 + 1)) * (Real.sqrt (x^2 + 1) - x) = 1 := by 
    nlinarith [Real.sqrt_nonneg (x^2 + 1), Real.sq_sqrt (show 0 ≤ x ^ 2 + 1 by positivity)]
  have h4 : (y + Real.sqrt (y^2 + 4)) * (Real.sqrt (y^2 + 4) - y) = 4 := by
    nlinarith [Real.sqrt_nonneg (y^2 + 4), Real.sq_sqrt (show 0 ≤ y ^ 2 + 4 by positivity)]
  have h5 : (Real.sqrt (x^2 + 1) - x) * (Real.sqrt (y^2 + 4) - y) = 4 / 9 := by
    have h6 : (x + Real.sqrt (x^2 + 1)) * (y + Real.sqrt (y^2 + 4)) = 9 := h 
    have h7 : (x + Real.sqrt (x^2 + 1)) * (Real.sqrt (x^2 + 1) - x) = 1 := h3
    have h8 : (y + Real.sqrt (y^2 + 4)) * (Real.sqrt (y^2 + 4) - y) = 4 := h4
    have h9 : (x + Real.sqrt (x^2 + 1)) * (y + Real.sqrt (y^2 + 4)) * ((Real.sqrt (x^2 + 1) - x) * (Real.sqrt (y^2 + 4) - y)) = 4 := by 
      calc
        (x + Real.sqrt (x^2 + 1)) * (y + Real.sqrt (y^2 + 4)) * ((Real.sqrt (x^2 + 1) - x) * (Real.sqrt (y^2 + 4) - y))
          = ((x + Real.sqrt (x^2 + 1)) * (Real.sqrt (x^2 + 1) - x)) * ((y + Real.sqrt (y^2 + 4)) * (Real.sqrt (y^2 + 4) - y)) := by ring
        _ = 1 * 4 := by rw [h7, h8]
        _ = 4 := by norm_num
    rw [h6] at h9 
    nlinarith
  have eq3 : x * y + x * Real.sqrt (y^2 + 4) + y * Real.sqrt (x^2 + 1) + Real.sqrt (x^2 + 1) * Real.sqrt (y^2 + 4) = 9 := by
    nlinarith [Real.sqrt_nonneg (x^2 + 1), Real.sqrt_nonneg (y^2 + 4), 
      Real.sq_sqrt (show 0 ≤ x ^ 2 + 1 by positivity),
      Real.sq_sqrt (show 0 ≤ y ^ 2 + 4 by positivity),
      sq_nonneg (x - y), sq_nonneg (Real.sqrt (x^2 + 1) - Real.sqrt (y^2 + 4))
    ]
  have eq4 : Real.sqrt (x^2 + 1) * Real.sqrt (y^2 + 4) - (x * Real.sqrt (y^2 + 4) + y * Real.sqrt (x^2 + 1)) + (x * y) = 4 / 9 := by
    have h14 : (Real.sqrt (x^2 + 1) - x) * (Real.sqrt (y^2 + 4) - y) = 4 / 9 := h5 
    nlinarith [Real.sqrt_nonneg (x^2 + 1), Real.sqrt_nonneg (y^2 + 4),
      Real.sq_sqrt (show 0 ≤ x ^ 2 + 1 by positivity),
      Real.sq_sqrt (show 0 ≤ y ^ 2 + 4 by positivity),
      sq_nonneg (x - y), sq_nonneg (Real.sqrt (x^2 + 1) - Real.sqrt (y^2 + 4))
    ]
  have eq6 : x * Real.sqrt (y^2 + 4) + y * Real.sqrt (x^2 + 1) = 77 / 18 := by
    nlinarith [Real.sqrt_nonneg (x^2 + 1), Real.sqrt_nonneg (y^2 + 4),
      Real.sq_sqrt (show 0 ≤ x ^ 2 + 1 by positivity),
      Real.sq_sqrt (show 0 ≤ y ^ 2 + 4 by positivity),
      sq_nonneg (x - y), sq_nonneg (Real.sqrt (x^2 + 1) - Real.sqrt (y^2 + 4))
    ]
  exact eq6