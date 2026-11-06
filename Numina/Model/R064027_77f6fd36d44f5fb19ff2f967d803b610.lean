import Mathlib

theorem algebra_184612 : (Real.sqrt (5 - 2 * Real.sqrt 6)) / ((3 ^ ((1 : ℝ) / 4) + 2 ^ ((1 : ℝ) / 4)) * (3 ^ ((1 : ℝ) / 4) - 2 ^ ((1 : ℝ) / 4))) = 1 := by
  have h1 : Real.sqrt (5 - 2 * Real.sqrt 6) = Real.sqrt 3 - Real.sqrt 2 := by
    have h2 : Real.sqrt 3 > Real.sqrt 2 := by
      have h3 : 3 > 2 := by norm_num
      have h4 : Real.sqrt 3 > Real.sqrt 2 := by
        apply Real.sqrt_lt_sqrt
        all_goals linarith [h3]
      linarith
    have h3 : Real.sqrt 3 - Real.sqrt 2 ≥ 0 := by linarith
    -- Show that $(\sqrt{3} - \sqrt{2})^2 = 5 - 2\sqrt{6}$
    have h4 : (Real.sqrt 3 - Real.sqrt 2) ^ 2 = 5 - 2 * Real.sqrt 6 := by 
      have h5 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      have h6 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have h7 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
        have h8 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt (3 * (2 : ℝ)) := by 
          rw [Real.sqrt_mul]
          all_goals norm_num
        rw [h8]
        have h9 : (3 : ℝ) * (2 : ℝ) = (6 : ℝ) := by norm_num
        rw [h9]
        all_goals norm_num
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, 
        Real.sqrt_nonneg (5 - 2 * Real.sqrt 6), h5, h6, h7]
    -- From h4 we have $(\sqrt{3} - \sqrt{2})^2 = 5 - 2\sqrt{6}$. Taking the square root yields $\sqrt{5 - 2\sqrt{6}} = |\sqrt{3} - \sqrt{2}| = \sqrt{3} - \sqrt{2}$ since $\sqrt{3} > \sqrt{2}$.
    have h8 : Real.sqrt ((5 - 2 * Real.sqrt 6)) = Real.sqrt ((Real.sqrt 3 - Real.sqrt 2) ^ 2) := by 
      rw [←h4]
    have h9 : Real.sqrt ((Real.sqrt 3 - Real.sqrt 2) ^ 2) = Real.sqrt 3 - Real.sqrt 2 := by 
      rw [Real.sqrt_sq]
      all_goals linarith
    rw [h8, h9]
  -- Show now that the denominator expands to $\sqrt{3} - \sqrt{2}$
  have h7 : (3 ^ ((1 : ℝ) / 4) + 2 ^ ((1 : ℝ) / 4)) * (3 ^ ((1 : ℝ) / 4) - 2 ^ ((1 : ℝ) / 4)) = Real.sqrt 3 - Real.sqrt 2 := by
    have h8 : ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt 3 := by
      have h9 : ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = (3 : ℝ) ^ ((1 / 2 : ℝ)) := by 
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals norm_num
      have h10 : (3 : ℝ) ^ ((1 / 2 : ℝ)) = Real.sqrt 3 := by 
        rw [Real.sqrt_eq_rpow]
      rw [h9, h10]
    have h9 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt 2 := by 
      have h10 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = (2 : ℝ) ^ ((1 / 2 : ℝ)) := by 
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals norm_num
      have h11 : (2 : ℝ) ^ ((1 / 2 : ℝ)) = Real.sqrt 2 := by 
        rw [Real.sqrt_eq_rpow]
      rw [h10, h11]
    -- Use the difference of squares: $(\sqrt[4]{3})^2 - (\sqrt[4]{2})^2 = \sqrt{3} - \sqrt{2}$
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, h8, h9, 
      Real.sqrt_nonneg 6, 
      show Real.sqrt 3 > Real.sqrt 2 by 
        have h14 : 3 > 2 := by norm_num
        have h15 : Real.sqrt 3 > Real.sqrt 2 := by 
          apply Real.sqrt_lt_sqrt
          all_goals linarith [h14]
        linarith
        ]
  rw [h1, h7]
  have h11 : Real.sqrt 3 - Real.sqrt 2 ≠ 0 := by 
    have h12 : Real.sqrt 3 > Real.sqrt 2 := by 
      have h3 : 3 > 2 := by norm_num
      have h13 : Real.sqrt 3 > Real.sqrt 2 := by 
        apply Real.sqrt_lt_sqrt
        all_goals linarith [h3]
      linarith
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2]
  field_simp [h11]
  <;> ring_nf <;> norm_num
  all_goals norm_num