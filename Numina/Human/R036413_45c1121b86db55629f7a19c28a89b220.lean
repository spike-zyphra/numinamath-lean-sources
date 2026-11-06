import Mathlib

open Real

/-
$\left|\log _{\sqrt{3}} x-2\right|-\left|\log _{3} x-2\right|=2$.
-/
theorem algebra_167353 {x : ℝ} (hx : 0 < x) :
    abs (logb (sqrt 3) x - 2) - abs (logb 3 x - 2) = 2 ↔
    x = 1 / 9 ∨ x = 9 := by
        have h1 : logb (sqrt 3) x = 2 * logb 3 x := by
            have h2 : logb (sqrt 3) x = logb 3 x / logb 3 (sqrt 3) := by
                field_simp [logb]
            have h3 : logb 3 (sqrt 3) = 1 / 2 := by
                rw [show (sqrt 3 : ℝ) = 3 ^ (1 / 2 : ℝ) by simp [Real.sqrt_eq_rpow]]
                simp [logb_rpow]
            rw [h2, h3]
            ring
        rw [h1]
        constructor
        · -- Forward implication: |2 * log_3 x - 2| - |log_3 x - 2| = 2 → x = 1/9 ∨ x = 9
            intro h
            by_cases h2 : logb 3 x ≥ 2
            · -- Case 1: log_3 x ≥ 2
                rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
                have h3 : logb 3 x = 2 := by linarith
                have hx_eq_9 : x = 9 := by
                    have h4 : logb 3 x = 2 := h3
                    rw [logb_eq_iff_rpow_eq] at h4
                    · -- 3 ^ 2 = x
                        linarith
                    all_goals linarith
                right
                exact hx_eq_9
            · -- Case 2: log_3 x < 2
                by_cases h3 : logb 3 x ≥ 1
                · -- Subcase 2a: 1 ≤ log_3 x < 2
                    rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith)] at h
                    have h4 : logb 3 x = 2 := by linarith
                    linarith
                · -- Subcase 2b: log_3 x < 1
                    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at h
                    have h4 : logb 3 x = -2 := by linarith
                    have hx_eq_1_div_9 : x = 1 / 9 := by
                        have h5 : logb 3 x = -2 := h4
                        rw [logb_eq_iff_rpow_eq] at h5
                        · -- 3 ^ (-2) = x
                            have h6 : x = (3 : ℝ) ^ (-2 : ℝ) := by
                                linarith
                            rw [h6]
                            norm_num
                        all_goals linarith
                    left
                    exact hx_eq_1_div_9
        · -- Backward implication: x = 1/9 ∨ x = 9 → |2 * log_3 x - 2| - |log_3 x - 2| = 2
            rintro (h | h)
            · -- Case x = 1/9
                have hx : x = 1 / 9 := h
                have h1 : logb 3 x = -2 := by
                    rw [hx]
                    rw [logb_eq_iff_rpow_eq]
                    all_goals norm_num
                rw [h1]
                norm_num [abs_of_nonneg, abs_of_nonpos]
            · -- Case x = 9
                have hx : x = 9 := h
                have h1 : logb 3 x = 2 := by
                    rw [hx]
                    rw [logb_eq_iff_rpow_eq]
                    all_goals norm_num
                rw [h1]
                norm_num [abs_of_nonneg, abs_of_nonpos]
