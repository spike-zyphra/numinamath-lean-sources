import Mathlib

open Real

theorem inequalities_308591 (c : ℝ) :
    (∀ x y : ℝ, x > 0 → y > 0 → x ^ 2 + y ^ 2 = 1 → x ^ 6 + y ^ 6 ≥ c * x * y) ↔
    c ≤ 1 / 2 := by
  constructor
  · -- Assume the inequality holds, derive c ≤ 1/2
    intro h
    have h1 := h (Real.sqrt (1 / 2)) (Real.sqrt (1 / 2)) (by
      apply Real.sqrt_pos.mpr
      all_goals norm_num
    ) (by
      apply Real.sqrt_pos.mpr
      all_goals norm_num
    ) (by 
      have h1 : (Real.sqrt (1 / 2) : ℝ) ^ 2 = (1 / 2) := Real.sq_sqrt (by linarith)
      linarith 
    )
    have h21 : (Real.sqrt (1 / 2) : ℝ) ^ 2 = (1 / 2 : ℝ) := Real.sq_sqrt (by linarith)
    have h22 : (Real.sqrt (1 / 2) : ℝ) ^ 4 = (1 / 4 : ℝ) := by
      calc
        (Real.sqrt (1 / 2) : ℝ) ^ 4 = ((Real.sqrt (1 / 2) : ℝ) ^ 2) ^ 2 := by ring
        _ = ( (1 / 2) ) ^ 2 := by rw [h21]
        _ = (1 / 4) := by norm_num
    have h23 : (Real.sqrt (1 / 2) : ℝ) ^ 6 = (1 / 8 : ℝ) := by
      calc
        (Real.sqrt (1 / 2) : ℝ) ^ 6 = ((Real.sqrt (1 / 2) : ℝ) ^ 2) ^ 3 := by ring
        _ = ( (1 / 2) ) ^ 3 := by rw [h21]
        _ = (1 / 8) := by norm_num
    -- We have (Real.sqrt (1 / 2) : ℝ) ^ 6 + (Real.sqrt (1 / 2) : ℝ) ^ 6 ≥ c * (Real.sqrt (1 / 2) * Real.sqrt (1 / 2))
    -- Substitute our computations into this inequality
    have h6 : (1 / 4 : ℝ) ≥ c / 2 := by
      have h_left : (Real.sqrt (1 / 2) : ℝ) ^ 6 + (Real.sqrt (1 / 2) : ℝ) ^ 6 = (1 / 4 : ℝ) := by
        calc 
          (Real.sqrt (1 / 2) : ℝ) ^ 6 + (Real.sqrt (1 / 2) : ℝ) ^ 6 = 2 * ((Real.sqrt (1 / 2) : ℝ) ^ 6) := by ring 
          _ = 2 * (1 / 8 : ℝ) := by rw [h23]
          _ = (1 / 4 : ℝ) := by norm_num
      have h_right : c * (Real.sqrt (1 / 2) * Real.sqrt (1 / 2)) = c * (1 / 2 : ℝ) := by
        have h4 : Real.sqrt (1 / 2) * Real.sqrt (1 / 2) = (1 / 2 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (1 / 2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
        rw [h4]
      nlinarith [h1, h_left, h_right, sq_nonneg (c), Real.sqrt_nonneg (1 / 2 : ℝ)]
    linarith
  · -- Assume $c \leq 1/2$, need to show the inequality holds for all $x, y$
    intro hc x y hx hy hxy
    have h11 : x ^ 6 + y ^ 6 ≥ (1 / 2) * (x * y) := by
      nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x * y - 1 / 2), 
          sq_nonneg (x - y), sq_nonneg (x + y), 
          mul_pos hx hy, 
          pow_two_nonneg (x^2 - y^2), pow_two_nonneg (x * y - 1 / 2), 
          pow_two_nonneg (x - y), pow_two_nonneg (x + y), 
          sq_nonneg (x^3 - y^3), sq_nonneg (x * y * (x - y)), 
          hxy, 
          mul_pos hx hy
          ]
    have h15 : c * (x * y) ≤ (1 / 2) * (x * y) := by
      have hxy_pos : 0 ≤ x * y := by 
        nlinarith 
      have h14 : c ≤ (1 / 2 : ℝ) := by linarith 
      nlinarith [h14, mul_pos hx hy] 
    nlinarith [h11, h15, mul_pos hx hy]