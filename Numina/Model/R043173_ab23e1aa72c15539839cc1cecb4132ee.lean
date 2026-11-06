import Mathlib

theorem algebra_161140 {x : ℝ} (hx : x = Real.sqrt (8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) - Real.sqrt (8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5))) :
    x = Real.sqrt (20 - 4 * Real.sqrt 5) := by 
  rw [hx]
  have h1 : 0 ≤ Real.sqrt (8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) := Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt (8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) := Real.sqrt_nonneg _
  have h3 : 0 ≤ Real.sqrt (20 - 4 * Real.sqrt 5) := Real.sqrt_nonneg _
  have h4 : Real.sqrt (8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) ≥ Real.sqrt (8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) := by 
    apply Real.sqrt_le_sqrt 
    have h5 : Real.sqrt (10 + 2 * Real.sqrt 5) > 0 := by 
      positivity 
    nlinarith [Real.sqrt_nonneg (10 + 2 * Real.sqrt 5), Real.sq_sqrt (show (0 : ℝ) ≤ 10 + 2 * Real.sqrt 5 by positivity), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by positivity)]
  -- Subtract the squared square roots squared after factoring.
  have h5 : (Real.sqrt (8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) - Real.sqrt (8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) ) ^ 2 = 20 - 4 * Real.sqrt 5 := by 
    have h8 : Real.sqrt (8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) ^ 2 = 8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5) := by 
      rw [Real.sq_sqrt]
      have h13 : 8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5) ≥ 0 := by positivity 
      nlinarith 
    have h9 : Real.sqrt (8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5) ) ^2 = 8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5) := by
      rw [Real.sq_sqrt]
      have h14 : 8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5) ≥ 0 := by 
        have h5_ineq : Real.sqrt (10 + 2 * Real.sqrt 5) ≤ 4 := by
          nlinarith [Real.sqrt_nonneg (10 + 2 * Real.sqrt 5), Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (10 + 2 * Real.sqrt 5 : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by positivity), sq_nonneg (Real.sqrt (10 + 2 * Real.sqrt 5) - 4), sq_nonneg (Real.sqrt 5 - 3 / 2), Real.sqrt_nonneg (10 + 2 * Real.sqrt 5)]
        nlinarith [Real.sqrt_nonneg (10 + 2 * Real.sqrt 5), Real.sq_sqrt (show 0 ≤ (10 + 2 * Real.sqrt 5 : ℝ) by positivity), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by positivity)]
      nlinarith
    have h10 : Real.sqrt (8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) * Real.sqrt (8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) = Real.sqrt (24 - 8 * Real.sqrt 5) := by 
      calc 
        Real.sqrt (8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) * Real.sqrt (8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) = Real.sqrt ((8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) * (8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) ) := by 
          rw [← Real.sqrt_mul (by 
            nlinarith [Real.sqrt_nonneg (10 + 2 * Real.sqrt 5), Real.sq_sqrt (show 0 ≤ (10 + 2 * Real.sqrt 5 : ℝ) by positivity), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
          )
          ]
        _ = Real.sqrt (24 - 8 * Real.sqrt 5) := by 
          have h15 : (8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) * (8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) = 24 - 8 * Real.sqrt 5 := by 
            nlinarith [Real.sqrt_nonneg (10 + 2 * Real.sqrt 5), Real.sq_sqrt (show 0 ≤ (10 + 2 * Real.sqrt 5 : ℝ) by positivity), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
          rw [h15]
    have h11 : Real.sqrt (24 - 8 * Real.sqrt 5) = -2 + 2 * Real.sqrt 5 := by 
      have h5_nonneg : -2 + 2 * Real.sqrt 5 ≥ 0 := by 
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
      have h5_sq : (-2 + 2 * Real.sqrt 5) ^ 2 = 24 - 8 * Real.sqrt 5 := by 
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity), Real.sqrt_nonneg 5]
      rw [← h5_sq]
      field_simp [h5_nonneg, Real.sqrt_sq]
    calc 
      (Real.sqrt (8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) - Real.sqrt (8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) ) ^ 2 = (Real.sqrt (8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) )^2 + (Real.sqrt (8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) )^2 - 2 * (Real.sqrt (8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) * Real.sqrt (8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) ) := by 
        ring 
      _ = (8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) + (8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) - 2 * Real.sqrt (24 - 8 * Real.sqrt 5) := by 
        rw [h8, h9, h10]
      _ = 20 - 4 * Real.sqrt 5 := by 
        rw [h11]
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
  have h6 : (Real.sqrt (8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) - Real.sqrt (8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) )^2 = Real.sqrt (20 - 4 * Real.sqrt 5) ^ 2 := by 
    rw [h5]
    have h7_pos : 20 - 4 * Real.sqrt 5 ≥ 0 := by 
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
    rw [Real.sq_sqrt (show 20 - 4 * Real.sqrt 5 ≥ 0 by nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)])]
    all_goals linarith 
  have h7 : (Real.sqrt (8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) - Real.sqrt (8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) ) ^ 2 = Real.sqrt (20 - 4 * Real.sqrt 5) ^ 2 := h6 
  have h8_nonneg : Real.sqrt (20 - 4 * Real.sqrt 5) ≥ 0 := Real.sqrt_nonneg _ 
  have h9_val : Real.sqrt (8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) - Real.sqrt (8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) = Real.sqrt (20 - 4 * Real.sqrt 5) := by 
    nlinarith [Real.sqrt_nonneg (20 - 4 * Real.sqrt 5), Real.sqrt_nonneg (8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5)), Real.sqrt_nonneg (8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5)), h4, h8_nonneg, sq_nonneg (Real.sqrt (8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) - Real.sqrt (8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) - Real.sqrt (20 - 4 * Real.sqrt 5)), sq_nonneg (Real.sqrt (8 + 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) - Real.sqrt (20 - 4 * Real.sqrt 5)), sq_nonneg (Real.sqrt (8 - 2 * Real.sqrt (10 + 2 * Real.sqrt 5)) - Real.sqrt (20 - 4 * Real.sqrt 5)), Real.sqrt_nonneg (10 + 2 * Real.sqrt 5), Real.sqrt_nonneg 5]
  linarith [h9_val]