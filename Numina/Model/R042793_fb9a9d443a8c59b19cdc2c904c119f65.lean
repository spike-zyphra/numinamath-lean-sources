import Mathlib

open Real

theorem inequalities_192965  :
    IsLeast {k : ℝ | ∀ x y : ℝ, x > 0 → y > 0 → √x + √y ≤ k * √(5 * x + y)} (√30 / 5) := by
  constructor
  · -- Show that √30 / 5 is in the set
    intro x y hx hy
    have h1 : (√x + √y) ^ 2 ≤ (√30 / 5 * √(5 * x + y)) ^ 2 := by 
      have h2 : (√x + √y) ^ 2 = (√x) ^ 2 + (√y) ^ 2 + 2 * (√x * √y) := by ring
      have h3 : (√x) ^ 2 = x := Real.sq_sqrt (by linarith)
      have h4 : (√y) ^ 2 = y := Real.sq_sqrt (by linarith)
      have h5 : √x * √y = Real.sqrt (x * y) := by 
        have h6 : Real.sqrt x * Real.sqrt y = Real.sqrt (x * y) := by 
          rw [← Real.sqrt_mul (by linarith)]
        linarith [h6]
      have h6 : (√30 / 5 * √(5 * x + y)) ^ 2 = (√30 / 5) ^ 2 * (√(5 * x + y) ) ^ 2 := by ring
      have h7 : (√30 / 5) ^ 2 = (30 : ℝ) / 25 := by 
        have h8 : Real.sqrt (30 : ℝ) ^ 2 = (30 : ℝ) := Real.sq_sqrt (by norm_num)
        nlinarith
      have h8 : (√(5 * x + y) ) ^ 2 = (5 * x + y : ℝ) := Real.sq_sqrt (by positivity)
      rw [h2, h3, h4, h5]
      rw [h6, h7, h8]
      have h9 : Real.sqrt (x * y) ^ 2 = x * y := Real.sq_sqrt (show x * y ≥ 0 by positivity)
      nlinarith [Real.sqrt_nonneg (x), Real.sqrt_nonneg (y), Real.sqrt_nonneg (x * y), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x : ℝ) by linarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ (y : ℝ) by linarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ (x * y : ℝ) by positivity),
          sq_nonneg (Real.sqrt x - Real.sqrt y), sq_nonneg (x - y),
          sq_nonneg (5 * x - y), sq_nonneg (25 * x - y), 
          mul_nonneg (Real.sqrt_nonneg (x)) (Real.sqrt_nonneg (y)), 
          mul_nonneg (show (0 : ℝ) ≤ 5 by norm_num) (show (0 : ℝ) ≤ x by linarith), 
          mul_pos hx hy, Real.sqrt_pos.mpr hx, Real.sqrt_pos.mpr hy
      ]
    have h2 : √x + √y ≥ 0 := by 
      positivity
    have h3 : √30 / 5 * √(5 * x + y) ≥ 0 := by 
      positivity
    nlinarith [h1, h2, h3, 
          Real.sqrt_nonneg (30 : ℝ), Real.sqrt_nonneg (5 * x + y : ℝ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (30 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (5 * x + y : ℝ) by positivity)
    ]
  · -- Show that √30 / 5 is the least
    intro k hk
    have h2 := hk 1 25 (by norm_num) (by norm_num)
    have h1 : Real.sqrt (1 : ℝ) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h5 : Real.sqrt (25 : ℝ) = 5 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h6 : Real.sqrt (5 * (1 : ℝ) + (25 : ℝ) ) = Real.sqrt (30 : ℝ) := by 
      norm_num
    rw [h1, h5, h6] at h2
    have h7 : (6 : ℝ) ≤ k * Real.sqrt (30 : ℝ) := by
      nlinarith 
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (30 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (30 : ℝ) by norm_num)
    ]