import Mathlib

theorem inequalities_180249 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 9 := by
        have h1 : 0 < a * b * c := by
            apply mul_pos
            apply mul_pos
            exact ha
            exact hb
            exact hc

        have h2 : 1 / a + 1 / b + 1 / c = (a * b + a * c + b * c) / (a * b * c) := by 
            field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc]
            ring

        have h3 : (a + b + c) * (1 / a + 1 / b + 1 / c) - 9 ≥ 0 := by
            rw [h2]
            have h4 : (a + b + c) * ( (a * b + a * c + b * c) / (a * b * c) ) - 9 =
                ( (a + b + c) * (a * b + a * c + b * c) - 9 * (a * b * c) ) / (a * b * c) := by 
                field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc]
                ring
            rw [h4]
            have h5 : (a + b + c) * (a * b + a * c + b * c) - 9 * (a * b * c) =
                a * (b - c)^2 + b * (a - c)^2 + c * (a - b)^2 := by
                ring
            rw [h5]
            have h6 : a * (b - c)^2 + b * (a - c)^2 + c * (a - b)^2 ≥ 0 := by
                nlinarith [sq_nonneg (b - c), sq_nonneg (a - c), sq_nonneg (a - b), 
                          ha, hb, hc 
                          ]
            have h7 : 0 < a * b * c := h1
            have h8 : (a * b * c) > 0 := h7
            exact div_nonneg h6 (by positivity)

        linarith