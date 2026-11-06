import Mathlib

open Real

theorem inequalities_111973
    (a b c : ℝ)
    (ha : 1 < a)
    (hb : 1 < b)
    (hc : 1 < c) :
    3 / 5 ≤ logb (a * b^2 * c^2) a + logb (b * c^2 * a^2) b + logb (c * a^2 * b^2) c := by
        have h1 : logb (a * b^2 * c^2) a = (log a) / (log (a * b^2 * c^2)) := by 
            field_simp [logb]
        have h2 : logb (b * c^2 * a^2) b = (log b) / (log (b * c^2 * a^2)) := by 
            field_simp [logb]
        have h3 : logb (c * a^2 * b^2) c = (log c) / (log (c * a^2 * b^2)) := by 
            field_simp [logb]

        have h4 : log (a * b^2 * c^2) = log a + 2 * log b + 2 * log c := by
            have h11 : log (a * b^2 * c^2) = log (a * (b^2 * c^2)) := by ring
            rw [h11]
            have h14 : log (a * (b^2 * c^2)) = log a + log (b^2 * c^2) := by 
                rw [log_mul (by positivity) (by positivity)]
            rw [h14]
            have h15 : log (b^2 * c^2) = log (b^2) + log (c^2) := by 
                rw [log_mul (by positivity) (by positivity)]
            rw [h15]
            have h16 : log (b^2) = 2 * log b := by 
                simp [log_pow]
            have h17 : log (c^2) = 2 * log c := by 
                simp [log_pow]
            rw [h16, h17]
            all_goals ring

        have h5 : log (b * c^2 * a^2) = log b + 2 * log c + 2 * log a := by
            have h18 : log (b * c^2 * a^2) = log (b * (c^2 * a^2)) := by ring
            rw [h18]
            have h19 : log (b * (c^2 * a^2)) = log b + log (c^2 * a^2) := by 
                rw [log_mul (by positivity) (by positivity)]
            rw [h19]
            have h20 : log (c^2 * a^2) = log (c^2) + log (a^2) := by 
                rw [log_mul (by positivity) (by positivity)]
            rw [h20]
            have h21 : log (c^2) = 2 * log c := by 
                simp [log_pow]
            have h22 : log (a^2) = 2 * log a := by 
                simp [log_pow]
            rw [h21, h22]
            all_goals ring

        have h6 : log (c * a^2 * b^2) = log c + 2 * log a + 2 * log b := by
            have h23 : log (c * a^2 * b^2) = log (c * (a^2 * b^2)) := by ring
            rw [h23]
            have h24 : log (c * (a^2 * b^2)) = log c + log (a^2 * b^2) := by 
                rw [log_mul (by positivity) (by positivity)]
            rw [h24]
            have h25 : log (a^2 * b^2) = log (a^2) + log (b^2) := by 
                rw [log_mul (by positivity) (by positivity)]
            rw [h25]
            have h26 : log (a^2) = 2 * log a := by 
                simp [log_pow]
            have h27 : log (b^2) = 2 * log b := by 
                simp [log_pow]
            rw [h26, h27]
            all_goals ring

        have ha1 : 0 < log a := by 
            apply log_pos
            linarith
        have hb1 : 0 < log b := by 
            apply log_pos
            linarith
        have hc1 : 0 < log c := by 
            apply log_pos
            linarith

        rw [h1, h2, h3, h4, h5, h6]

        have h7 : 0 < log a + 2 * log b + 2 * log c := by
            linarith
        have h8 : 0 < log b + 2 * log c + 2 * log a := by 
            linarith
        have h9 : 0 < log c + 2 * log a + 2 * log b := by 
            linarith

        have h10 : (log a) / (log a + 2 * log b + 2 * log c) + (log b) / (log b + 2 * log c + 2 * log a) + (log c) / (log c + 2 * log a + 2 * log b) ≥ 3 / 5 := by
            have h11 : 0 < (log a + 2 * log b + 2 * log c) * (log b + 2 * log c + 2 * log a) * (log c + 2 * log a + 2 * log b) := by 
                positivity
            have h12 : (log a) / (log a + 2 * log b + 2 * log c) + (log b) / (log b + 2 * log c + 2 * log a) + (log c) / (log c + 2 * log a + 2 * log b) - 3 / 5 ≥ 0 := by 
                have h13 : (log a) / (log a + 2 * log b + 2 * log c) + (log b) / (log b + 2 * log c + 2 * log a) + (log c) / (log c + 2 * log a + 2 * log b) - 3 / 5 =
                    ((log a) * (log b + 2 * log c + 2 * log a) * (log c + 2 * log a + 2 * log b) +
                    (log b) * (log a + 2 * log b + 2 * log c) * (log c + 2 * log a + 2 * log b) +
                    (log c) * (log a + 2 * log b + 2 * log c) * (log b + 2 * log c + 2 * log a)
                    - 3 / 5 * (log a + 2 * log b + 2 * log c) * (log b + 2 * log c + 2 * log a) * (log c + 2 * log a + 2 * log b)) / ((log a + 2 * log b + 2 * log c) * (log b + 2 * log c + 2 * log a) * (log c + 2 * log a + 2 * log b)) := by 
                    field_simp
                    ring
                rw [h13]
                apply div_nonneg 
                nlinarith [sq_nonneg (log a - log b), sq_nonneg (log b - log c), sq_nonneg (log c - log a),
                    sq_nonneg (log a * (log a - log b)), sq_nonneg (log a * (log b - log c)), sq_nonneg (log a * (log c - log a)),
                    sq_nonneg (log b * (log b - log c)), sq_nonneg (log b * (log c - log a)), sq_nonneg (log b * (log a - log b)),
                    sq_nonneg (log c * (log c - log a)), sq_nonneg (log c * (log a - log b)), sq_nonneg (log c * (log b - log c)),
                    mul_pos ha1 hb1, mul_pos hb1 hc1, mul_pos ha1 hc1
                    ]
                all_goals positivity 
            linarith
        linarith