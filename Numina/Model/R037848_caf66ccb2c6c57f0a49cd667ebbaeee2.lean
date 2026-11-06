import Mathlib

theorem algebra_142503 (n : ℕ) (hn : n = 230) :
    (n / 5000 : ℝ) * (1 - 0.9802) < 15 / √(10000 * (5000 - n)) := by 
  rw [hn]
  have h2 : √(10000 * (5000 - (230 : ℕ) : ℝ)) > 0 := by 
    positivity
  have h4 : √(10000 * (5000 - (230 : ℕ) : ℝ)) = Real.sqrt (47700000 : ℝ) := by
    norm_num
    <;> ring_nf
  have h7 : (230 / 5000 : ℝ) * (1 - (0.9802 : ℝ)) < (15 / Real.sqrt (47700000 : ℝ)) := by
    norm_num
    have h10 : Real.sqrt (47700000 : ℝ) > (0 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
    have h11 : (0.0009108 : ℝ) < 15 / Real.sqrt (47700000 : ℝ) := by
      have h14 : (0.0009108 : ℝ) * Real.sqrt (47700000 : ℝ) < (15 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (47700000 : ℝ), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (47700000 : ℝ) by norm_num)
             ]
      have h17 : Real.sqrt (47700000 : ℝ) > 0 := Real.sqrt_pos.mpr (by norm_num)
      have h18 : (0.0009108 : ℝ) < 15 / Real.sqrt (47700000 : ℝ) := by
        apply (lt_div_iff₀ (by positivity)).mpr
        nlinarith [Real.sqrt_nonneg (47700000 : ℝ), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (47700000 : ℝ) by norm_num)
             ]
      linarith
    linarith
  have h13 : (15 / √ (10000 * (5000 - (230 : ℕ) : ℝ)) : ℝ) = (15 / Real.sqrt (47700000 : ℝ)) := by 
    rw [h4]
  linarith [h7, h13]