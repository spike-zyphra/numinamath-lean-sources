import Mathlib
theorem algebra_608565 : IsGreatest {a : ℝ | ∃ x y : ℝ, a = x + y ∧ x ^ 2 + y ^ 2 - 3 * y - 1 = 0} ((√26 + 3) / 2):= by
  constructor
  · -- Show existence of pair x, y that works
    use Real.sqrt 26 / 4, (6 + Real.sqrt 26) / 4
    constructor
    · -- Show a = x + y
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 26 by norm_num) , Real.sq_sqrt (show 0 ≤ (26 : ℝ) by norm_num)]
    · -- Show x^2+y^2-3y-1=0
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 26 by norm_num) , Real.sq_sqrt (show 0 ≤ (26 : ℝ) by norm_num)]
  · -- Show that this value is the greatest
    intro a ha
    rcases ha with ⟨x, y, ha, heq⟩
    nlinarith [sq_nonneg (x - (Real.sqrt 26 / 4)), sq_nonneg (y - (6 + Real.sqrt 26) / 4), 
          sq_nonneg ((x - y) + 3 / 2), 
          sq_nonneg ((x - 4 * y) + (Real.sqrt 26 + 6)), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < 26 by norm_num) , 
          Real.sq_sqrt (show 0 ≤ (26 : ℝ) by norm_num), 
          sq_nonneg (2 * (x - y + 3 / 2) - Real.sqrt 26)]