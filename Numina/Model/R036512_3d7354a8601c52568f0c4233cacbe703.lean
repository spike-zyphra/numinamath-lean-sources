import Mathlib

theorem algebra_98387 {x : ℝ} (hx : x ≠ 0) (h : x + 1/x = Real.sqrt 5) :
    x^11 - 7*x^7 + x^3 = 0 := by
  have h1 : x^2 - x * Real.sqrt 5 + 1 = 0 := by
    field_simp at h 
    nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h2 : x^2 = x * Real.sqrt 5 - 1 := by 
    linarith
  have h3 : x^3 = 4 * x - Real.sqrt 5 := by 
    calc
      x^3 = x * x^2 := by ring
      _ = x * (x * Real.sqrt 5 - 1) := by rw [h2]
      _ = x^2 * Real.sqrt 5 - x := by ring
      _ = (x * Real.sqrt 5 - 1) * Real.sqrt 5 - x := by rw [h2]
      _ = x * (Real.sqrt 5 * Real.sqrt 5) - Real.sqrt 5 - x := by ring
      _ = x * (5) - Real.sqrt 5 - x := by 
        have hsqrt5sq : Real.sqrt 5 * Real.sqrt 5 = (5 : ℝ) := by
          rw [Real.mul_self_sqrt]
          all_goals norm_num
        rw [hsqrt5sq]
      _ = 5 * x - Real.sqrt 5 - x := by ring
      _ = 4 * x - Real.sqrt 5 := by ring
  have h4 : x^4 = 3 * x * Real.sqrt 5 - 4 := by 
    calc
      x^4 = x * x^3 := by ring
      _ = x * (4 * x - Real.sqrt 5) := by rw [h3]
      _ = 4 * x^2 - x * Real.sqrt 5 := by ring
      _ = 4 * (x * Real.sqrt 5 - 1) - x * Real.sqrt 5 := by 
        rw [h2]
      _ = 4 * x * Real.sqrt 5 - 4 - x * Real.sqrt 5 := by ring
      _ = 3 * x * Real.sqrt 5 - 4 := by ring
  have h7 : x^7 = 29 * x - 8 * Real.sqrt 5 := by
    calc
      x^7 = x^4 * x^3 := by ring
      _ = (3 * x * Real.sqrt 5 - 4) * (4 * x - Real.sqrt 5) := by 
        rw [h4, h3]
      _ = 29 * x - 8 * Real.sqrt 5 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), sq_nonneg (x^2 * Real.sqrt 5 * Real.sqrt 5), sq_nonneg (x * Real.sqrt 5)
        ]
  have h11 : x^11 = 199 * x - 55 * Real.sqrt 5 := by
    calc
      x^11 = x^7 * x^4 := by ring
      _ = (29 * x - 8 * Real.sqrt 5) * (3 * x * Real.sqrt 5 - 4) := by 
        rw [h7, h4]
      _ = 199 * x - 55 * Real.sqrt 5 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), sq_nonneg (x^2 * Real.sqrt 5 * Real.sqrt 5), sq_nonneg (x * Real.sqrt 5)
        ]
  -- Now substitute the derived expressions into the target expression
  rw [h11]
  have h7' : x^7 = 29 * x - 8 * Real.sqrt 5 := h7
  have eq3 : x^11 - 7*x^7 + x^3 = 0 := by
    nlinarith [h7', h3, Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  nlinarith [eq3, h3, h7', Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]