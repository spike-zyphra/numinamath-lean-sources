import Mathlib

theorem algebra_16469 (v : ℝ) :
    5 * ((-21 - Real.sqrt 301) / 10)^2 + 21 * (-21 - Real.sqrt 301) / 10 + v = 0 ↔ v = 7 := by
  constructor
  · -- Assume the equation holds, prove v = 7
    intro h
    have h1 : 5 * ((-21 - Real.sqrt 301) / 10) ^ 2 + 21 * ((-21 - Real.sqrt 301) / 10) + v = 0 := by 
      linarith [h]
    have h2 : Real.sqrt 301 ^ 2 = 301 := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    have eq1 : 5 * ((-21 - Real.sqrt 301) / 10) ^ 2 + 21 * ((-21 - Real.sqrt 301) / 10) = -7 := by 
      nlinarith [Real.sqrt_nonneg 301, Real.sq_sqrt (show (0 : ℝ) ≤ (301 : ℝ) by norm_num)]
    -- From equation, solving for v gives v = 7
    have h3 : v = 7 := by 
      linarith [h1, eq1]
    linarith
  · -- Assume v = 7, prove the equation
    intro h
    rw [h]
    have h1 : Real.sqrt 301 ^ 2 = 301 := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    -- Let's compute to confirm
    have eq1 : 5 * ((-21 - Real.sqrt 301) / 10) ^ 2 + 21 * ((-21 - Real.sqrt 301) / 10) + (7 : ℝ) = 0 := by 
      nlinarith [Real.sqrt_nonneg 301, Real.sq_sqrt (show (0 : ℝ) ≤ (301 : ℝ) by norm_num)]
    linarith