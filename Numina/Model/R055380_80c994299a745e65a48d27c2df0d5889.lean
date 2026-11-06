import Mathlib

theorem algebra_1520 {x y : ℝ}
  (h₁ : x + y = Real.sqrt (7 * Real.sqrt 3 - 5 * Real.sqrt 2))
  (h₂ : x - y = Real.sqrt (7 * Real.sqrt 2 - 5 * Real.sqrt 3)) :
  x * y = 3 * Real.sqrt 3 - 3 * Real.sqrt 2 := by
  have h₁_sq : (x + y) ^ 2 = 7 * Real.sqrt 3 - 5 * Real.sqrt 2 := by
    calc
      (x + y) ^ 2 = (Real.sqrt (7 * Real.sqrt 3 - 5 * Real.sqrt 2)) ^ 2 := by rw [h₁]
      _ = 7 * Real.sqrt 3 - 5 * Real.sqrt 2 := by
        apply Real.sq_sqrt
        all_goals
          have h3 : 7 * Real.sqrt 3 - 5 * Real.sqrt 2 ≥ 0 := by
            nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2,
              Real.sq_sqrt (show 0 ≤ 3 by norm_num), Real.sq_sqrt (show 0 ≤ 2 by norm_num),
              Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
            ]
          linarith
  -- Square equation h₂
  have h₂_sq : (x - y) ^ 2 = 7 * Real.sqrt 2 - 5 * Real.sqrt 3 := by
    calc
      (x - y) ^ 2 = (Real.sqrt (7 * Real.sqrt 2 - 5 * Real.sqrt 3)) ^ 2 := by rw [h₂]
      _ = 7 * Real.sqrt 2 - 5 * Real.sqrt 3 := by
        apply Real.sq_sqrt
        all_goals
          have h4 : 7 * Real.sqrt 2 - 5 * Real.sqrt 3 ≥ 0 := by
            nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2,
              Real.sq_sqrt (show 0 ≤ 3 by norm_num), Real.sq_sqrt (show 0 ≤ 2 by norm_num),
              Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
            ]
          linarith
  -- Subtract squared equations to solve for $xy$
  have h3 : x * y = 3 * Real.sqrt 3 - 3 * Real.sqrt 2 := by
    have h4 : (x + y) ^ 2 - (x - y) ^ 2 = 4 * (x * y) := by
      ring_nf
    have h5 : (x + y) ^ 2 - (x - y) ^ 2 = 12 * Real.sqrt 3 - 12 * Real.sqrt 2 := by
      linarith [h₁_sq, h₂_sq]
    linarith [h4, h5]
  linarith [h3]