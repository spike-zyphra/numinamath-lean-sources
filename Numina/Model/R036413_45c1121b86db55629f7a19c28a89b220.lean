import Mathlib

open Real


theorem algebra_167353 {x : ℝ} (hx : 0 < x) :
    abs (logb (sqrt 3) x - 2) - abs (logb 3 x - 2) = 2 ↔
    x = 1 / 9 ∨ x = 9 := by
        have h1 : logb (sqrt 3) x = 2 * logb 3 x := by
            have h2 : log (sqrt 3) = (1 / 2) * log 3 := by
                rw [Real.log_sqrt]
                all_goals linarith
            have h3 : logb (sqrt 3) x = log x / log (sqrt 3) := by
                field_simp [logb]
            have h4 : logb 3 x = log x / log 3 := by
                field_simp [logb]
            rw [h3, h4, h2]
            <;> field_simp <;> ring_nf

        rw [h1]
        constructor
        ·
            intro h
            by_cases h2 : logb 3 x ≥ 2
            ·
                rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by nlinarith)] at h
                have h3 : logb 3 x = 2 := by linarith
                have hx_eq_9 : x = 9 := by
                    have h4 : x = (3 : ℝ) ^ (logb 3 x : ℝ) := by
                        field_simp
                    rw [h4, h3]
                    all_goals norm_num
                right
                exact hx_eq_9
            ·
                by_cases h3 : logb 3 x ≥ 1
                ·
                    rw [abs_of_nonneg (by nlinarith), abs_of_neg (by nlinarith)] at h
                    linarith
                ·
                    rw [abs_of_neg (by nlinarith), abs_of_neg (by nlinarith)] at h
                    have h4 : logb 3 x = -2 := by
                        nlinarith
                    have hx_eq_1_div_9 : x = 1 / 9 := by
                        have h5 : x = (3 : ℝ) ^ (logb 3 x : ℝ) := by
                            field_simp
                        rw [h5, h4]
                        all_goals norm_num
                    left
                    exact hx_eq_1_div_9
        ·
            rintro (h | h)
            ·
                have hx : x = 1 / 9 := h
                have h1 : logb 3 x = -2 := by
                    rw [hx]
                    rw [logb_eq_iff_rpow_eq] <;> norm_num
                rw [h1]
                norm_num [abs_of_nonneg, abs_of_nonpos]
            ·
                have hx : x = 9 := h
                have h1 : logb 3 x = 2 := by
                    rw [hx]
                    rw [logb_eq_iff_rpow_eq] <;> norm_num
                rw [h1]
                norm_num [abs_of_nonneg, abs_of_nonpos]