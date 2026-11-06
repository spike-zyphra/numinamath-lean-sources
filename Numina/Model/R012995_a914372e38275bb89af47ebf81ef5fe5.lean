import Mathlib
open Real Set

theorem inequalities_1874 (x : ℝ) (hx : x ∈ Ioo 0 π) : sin x * (1 - cos x) ≤ 3 * √3 / 4 := by
  rcases hx with ⟨hx1, hx2⟩
  have h3 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  have h5 : sin x * (1 - cos x) ≤ 3 * Real.sqrt 3 / 4 := by
    nlinarith [sq_nonneg (sin x - Real.sqrt 3 / 2), sq_nonneg (cos x + 1 / 2), 
      sq_nonneg ((Real.sqrt 3 : ℝ) ^ 2 - 3), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
      sq_nonneg (sin x ^ 2 - 3 / 4), sq_nonneg (cos x + 1 / 2), 
      sq_nonneg (cos x - 1 / 2), Real.sqrt_nonneg 3, 
      Real.sin_sq_add_cos_sq x, mul_pos h3 (show 0 < 1 - cos x by
        have h4 : cos x < 1 := by
          have h5 : x < π := hx2
          have h6 : cos x < cos (0 : ℝ) := by
            apply Real.cos_lt_cos_of_nonneg_of_le_pi
            all_goals linarith
          have h7 : cos (0 : ℝ) = 1 := Real.cos_zero
          linarith
        nlinarith [Real.sin_sq_add_cos_sq x]
      )
    ]
  linarith