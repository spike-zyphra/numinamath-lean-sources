import Mathlib

theorem calculus_22281 (a b : ℝ × ℝ)
    (h₀ : Real.sqrt (a.1^2 + a.2^2) = 5)
    (h₁ : Real.sqrt (b.1^2 + b.2^2) = 4)
    (h₂ : Real.arccos ((a.1 * b.1 + a.2 * b.2) / (Real.sqrt (a.1^2 + a.2^2) * Real.sqrt (b.1^2 + b.2^2))) = Real.pi / 3) :
    Real.sqrt ((a.1 - b.1)^2 + (a.2 - b.2)^2) = Real.sqrt 21 := by
  have ha_sq : a.1^2 + a.2^2 = 25 := by
    calc
      a.1^2 + a.2^2 = (Real.sqrt (a.1^2 + a.2^2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 5^2 := by rw [h₀]
      _ = 25 := by norm_num
  have hb_sq : b.1^2 + b.2^2 = 16 := by
    calc
      b.1^2 + b.2^2 = (Real.sqrt (b.1^2 + b.2^2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 4^2 := by rw [h₁]
      _ = 16 := by norm_num
  have h₃ : (a.1 * b.1 + a.2 * b.2) / (Real.sqrt (a.1^2 + a.2^2) * Real.sqrt (b.1^2 + b.2^2)) = Real.cos (Real.pi / 3) := by
    have h₄ : Real.arccos ((a.1 * b.1 + a.2 * b.2) / (Real.sqrt (a.1^2 + a.2^2) * Real.sqrt (b.1^2 + b.2^2))) = Real.pi / 3 := h₂
    have h₅ : (a.1 * b.1 + a.2 * b.2) / (Real.sqrt (a.1^2 + a.2^2) * Real.sqrt (b.1^2 + b.2^2)) = Real.cos (Real.arccos ((a.1 * b.1 + a.2 * b.2) / (Real.sqrt (a.1^2 + a.2^2) * Real.sqrt (b.1^2 + b.2^2)) ) ) := by
      rw [Real.cos_arccos]
      all_goals
        have h6 : Real.sqrt (a.1^2 + a.2^2) * Real.sqrt (b.1^2 + b.2^2) ≥ 0 := by positivity
        have h7 : (a.1 * b.1 + a.2 * b.2) / (Real.sqrt (a.1^2 + a.2^2) * Real.sqrt (b.1^2 + b.2^2)) ≥ -1 := by
          have h8 : a.1 * b.1 + a.2 * b.2 ≥ - (Real.sqrt (a.1^2 + a.2^2) * Real.sqrt (b.1^2 + b.2^2)) := by
            nlinarith [sq_nonneg (a.1 * b.2 - a.2 * b.1), sq_nonneg (a.1 * b.1 + a.2 * b.2), Real.sq_sqrt (show 0 ≤ (a.1^2 + a.2^2 : ℝ) by positivity), Real.sq_sqrt (show 0 ≤ (b.1^2 + b.2^2 : ℝ) by positivity), Real.sqrt_nonneg (a.1^2 + a.2^2), Real.sqrt_nonneg (b.1^2 + b.2^2) ]
          have h9 : (a.1 * b.1 + a.2 * b.2) / (Real.sqrt (a.1^2 + a.2^2) * Real.sqrt (b.1^2 + b.2^2)) ≥ -1 := by
            apply (le_div_iff₀ (by positivity)).mpr
            nlinarith
          linarith
        have h10 : (a.1 * b.1 + a.2 * b.2) / (Real.sqrt (a.1^2 + a.2^2) * Real.sqrt (b.1^2 + b.2^2)) ≤ 1 := by
          have h8 : a.1 * b.1 + a.2 * b.2 ≤ Real.sqrt (a.1^2 + a.2^2) * Real.sqrt (b.1^2 + b.2^2) := by
            nlinarith [sq_nonneg (a.1 * b.2 - a.2 * b.1), sq_nonneg (a.1 * b.1 + a.2 * b.2), Real.sq_sqrt (show 0 ≤ (a.1^2 + a.2^2 : ℝ) by positivity), Real.sq_sqrt (show 0 ≤ (b.1^2 + b.2^2 : ℝ) by positivity), Real.sqrt_nonneg (a.1^2 + a.2^2), Real.sqrt_nonneg (b.1^2 + b.2^2) ]
          have h9 : (a.1 * b.1 + a.2 * b.2) / (Real.sqrt (a.1^2 + a.2^2) * Real.sqrt (b.1^2 + b.2^2)) ≤ 1 := by
            apply (div_le_iff₀ (by positivity)).mpr
            nlinarith
          linarith
        all_goals linarith
    rw [h₅]
    rw [h₄]
  have h_dot : a.1 * b.1 + a.2 * b.2 = 10 := by
    have h₄ : Real.sqrt (a.1^2 + a.2^2) * Real.sqrt (b.1^2 + b.2^2) = 20 := by
      calc
        Real.sqrt (a.1^2 + a.2^2) * Real.sqrt (b.1^2 + b.2^2) = 5 * 4 := by 
          rw [h₀, h₁]
        _ = 20 := by norm_num
    have h₅ : Real.cos (Real.pi / 3) = (1 : ℝ) / 2 := by
      have h6 : Real.cos (Real.pi / 3) = 1 / 2 := by 
        exact Real.cos_pi_div_three
      linarith
    rw [h₅] at h₃
    have h₆ : a.1 * b.1 + a.2 * b.2 = 10 := by
      field_simp [h₄] at h₃
      nlinarith
    linarith
  have h_diff_sq : (a.1 - b.1)^2 + (a.2 - b.2)^2 = 21 := by
    nlinarith [ha_sq, hb_sq, h_dot]
  rw [h_diff_sq]