import Mathlib

theorem algebra_608906: IsLeast {54 * √3, 144, 108 * √6 - 108 * √2} (54 * √3) := by
  constructor
  · -- Show that $54 \sqrt{3}$ is in the set.
    simp
  · -- Show that $54 \sqrt{3}$ is the smallest
    intro x hx
    rcases hx with (rfl | rfl | rfl)
    · -- Show that $54 \sqrt{3} \leq 54 \sqrt{3}$
      all_goals
        linarith
    · -- Show that $54 \sqrt{3} \leq 144$
      have h1 : 54 * Real.sqrt 3 ≤ (144 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
      linarith [h1]
    · -- Show that $54 \sqrt{3} \leq 108 \sqrt{6} - 108 \sqrt{2}$
      have h2 : 54 * Real.sqrt 3 ≤ 108 * Real.sqrt 6 - 108 * Real.sqrt 2 := by
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (2 : ℝ),
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
          mul_nonneg (Real.sqrt_nonneg (6 : ℝ)) (Real.sqrt_nonneg (2 : ℝ)),
          Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (6 : ℝ) by norm_num),
          sq_nonneg (Real.sqrt 6 - Real.sqrt 2 - Real.sqrt 3 / 2),
          Real.sqrt_pos.mpr (show (0 : ℝ) < (6 : ℝ) by norm_num),
          Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num),
          Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)
        ]
      linarith [h2]