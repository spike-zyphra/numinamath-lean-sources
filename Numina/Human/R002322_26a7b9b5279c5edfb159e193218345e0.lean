import Mathlib
open Real
/- Given that $a,b$, and $c$ are positive real numbers such that $ab + bc + ca \geq 1$, prove that
\[ \frac{1}{a^2} + \frac{1}{b^2} + \frac{1}{c^2} \geq \frac{\sqrt{3}}{abc} .\] -/
theorem inequalities_84743 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a ≥ 1) :
    1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 ≥ sqrt 3 / (a * b * c) := by
        -- Prove that a*b*c is positive (needed for later steps)
        have h2 : 0 < a * b * c := by
            apply mul_pos
            apply mul_pos
            all_goals linarith

        -- Key inequality: a²b² + b²c² + c²a² ≥ √3 * (a*b*c)
        -- This will be used to prove our target inequality
        have h3 : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ≥ sqrt 3 * (a * b * c) := by
            -- First prove that a + b + c ≥ √3
            have h4 : a + b + c ≥ sqrt 3 := by
                -- Use the inequality (a+b+c)² ≥ 3(ab+bc+ca)
                -- This follows from expanding and using the AM-QM inequality
                have h5 : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a) := by
                    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

                -- Establish that √3 is non-negative
                have h8 : 0 ≤ sqrt 3 := Real.sqrt_nonneg 3

                -- Prove that a + b + c ≥ √3
                have h9 : a + b + c ≥ sqrt 3 := by
                    -- Show that a+b+c is non-negative
                    have h11 : 0 ≤ (a + b + c) := by nlinarith

                    -- Use the fact that √3² = 3
                    have h12 : sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)

                    -- Show that √3 ≤ a+b+c by comparing squares
                    have h13 : sqrt 3 ≤ (a + b + c) := by
                        have h14 : sqrt 3 ^ 2 ≤ (a + b + c) ^ 2 := by nlinarith
                        have h15 : 0 ≤ sqrt 3 := Real.sqrt_nonneg 3
                        nlinarith [h14, h15, h11]
                    linarith
                exact h9

            -- Use the AM-QM inequality and previous results to prove h3
            nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
              Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
              Real.sq_sqrt (show (0 : ℝ) ≤ (a * b * c) ^ 2 by nlinarith),
              sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
              h4, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
              Real.sq_sqrt (show (0 : ℝ) ≤ (a * b * c) ^ 2 by nlinarith),
              mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

        -- Final step: Prove the target inequality using h3
        have h4 : 1 / a^2 + 1 / b^2 + 1 / c^2 ≥ sqrt 3 / (a * b * c) := by
            -- Rewrite the left side in terms of a common denominator
            have h5 : (1 / a^2 + 1 / b^2 + 1 / c^2) = (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) / (a * b * c)^2 := by
                field_simp
                ring

            -- Rewrite the right side with the same denominator
            have h6 : sqrt 3 / (a * b * c) = (sqrt 3 * (a * b * c)) / (a * b * c)^2 := by
                field_simp
                ring

            -- Apply the rewrites
            rw [h5, h6]

            -- Show that (a*b*c)² > 0 to use division inequality
            have h7 : (a * b * c) ^ 2 > 0 := by
                apply pow_pos
                apply mul_pos
                apply mul_pos
                all_goals linarith

            -- Compare the numerators since denominators are equal and positive
            apply (div_le_div_right h7).mpr
            nlinarith [h3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

        -- Conclude the proof
        linarith [h4]
