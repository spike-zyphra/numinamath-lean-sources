import Mathlib

open Real
/-Example 12. For a >0, b> 0, and 1/b - 1/a = 1, compare the sizes of the following four numbers
: √(1+a),1/(1-b/2),1+a/2,1/√(1-b).
-/
theorem algebra_315143 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : 1 / b - 1 / a = 1) :
    1 / (1 - b / 2) < 1 / sqrt (1 - b) ∧
    1 / sqrt (1 - b) = sqrt (1 + a) ∧
    sqrt (1 + a) < 1 + a / 2 := by

    -- fist we will show that a * b ≠ 0 --
        have h1 : a * b ≠ 0 := by
            apply mul_ne_zero
            · linarith
            · linarith
-- simplify the equation 1/b - 1/a = 1 --
        have h2 : a - b = a * b := by
            field_simp [show a ≠ 0 by linarith, show b ≠ 0 by linarith] at h
            nlinarith
-- prove some fundamental inequalities --
        have h3 : 0 < 1 + a := by nlinarith

        have h4 : 0 < 1 - b := by
            nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1 / 2), h2]

        have h5 : 0 < sqrt (1 + a) := by
            apply Real.sqrt_pos.2
            linarith

        have h6 : 0 < sqrt (1 - b) := by
            apply Real.sqrt_pos.2
            linarith
-- prove the first equality --
        have h_eq : 1 / sqrt (1 - b) = sqrt (1 + a) := by
            have h7 : (1 + a) = 1 / (1 - b) := by
                have h7 : a * (1 - b) = b := by linarith [h2]
                have h8 : 1 - b > 0 := by nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1 / 2), h2]
                have h9 : 1 + a > 0 := by nlinarith
                have h10 : (1 - b) * (1 + a) = 1 := by
                    nlinarith [h7]
                field_simp
                nlinarith
            have h10 : sqrt (1 + a) = sqrt (1 / (1 - b)) := by
                rw [h7]
            have h11 : sqrt (1 / (1 - b)) = 1 / sqrt (1 - b) := by
                field_simp [Real.sqrt_div]
            rw [h10, h11]
-- prove the first inequality --
        have h_ineq1 : 1 / (1 - b / 2) < 1 / sqrt (1 - b) := by
            have h1 : 0 < 1 - b / 2 := by
                nlinarith [sq_nonneg (b - 1 / 2), h4]
            have h2 : 0 < sqrt (1 - b) := by
                exact h6
            have h3 : sqrt (1 - b) < 1 - b / 2 := by
                have h4 : sqrt (1 - b) ^ 2 < (1 - b / 2) ^ 2 := by
                    have h4 : (sqrt (1 - b)) ^ 2 = 1 - b := by
                        rw [Real.sq_sqrt]
                        linarith
                    have h5 : (1 - b / 2) ^ 2 = 1 - b + (b ^ 2) / 4 := by
                        ring
                    have h6 : 0 < (b ^ 2) / 4 := by
                        nlinarith [sq_pos_of_pos hb]
                    nlinarith [h4, h5, h6]
                nlinarith [h4, Real.sqrt_nonneg (1 - b), show 0 ≤ (1 - b / 2) by nlinarith]
            have h4 : 1 / (1 - b / 2) < 1 / sqrt (1 - b) := by
                apply (one_div_lt_one_div (by linarith) (by linarith)).2
                linarith [h3]
            linarith
-- prove the second inequality --
        have h_ineq2 : sqrt (1 + a) < 1 + a / 2 := by
            have h4 : 0 < Real.sqrt (1 + a) := by
                exact h5
            have h5 : Real.sqrt (1 + a) < 1 + a / 2 := by
                have h6 : Real.sqrt (1 + a) ^ 2 < (1 + a / 2) ^ 2 := by
                    have h6 : Real.sqrt (1 + a) ^ 2 = 1 + a := by
                        rw [Real.sq_sqrt]
                        linarith
                    have h7 : (1 + a / 2) ^ 2 = 1 + a + (a ^ 2) / 4 := by
                        ring
                    have h8 : 0 < (a ^ 2) / 4 := by
                        nlinarith [sq_pos_of_pos ha]
                    nlinarith [h6, h7, h8]
                have h7 : 0 ≤ Real.sqrt (1 + a) := Real.sqrt_nonneg (1 + a)
                have h8 : 0 < 1 + a / 2 := by nlinarith
                nlinarith [h6, h7, h8]
            linarith [h5]

        exact ⟨h_ineq1, h_eq, h_ineq2⟩
        