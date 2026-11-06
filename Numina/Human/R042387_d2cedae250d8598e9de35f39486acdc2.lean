import Mathlib

open Real
set_option maxHeartbeats 800000
/- Prove the inequality

$\frac{b^2+c^2-a^2}{a\left(b+c\right)}+\frac{c^2+a^2-b^2}{b\left(c+a\right)}+\frac{a^2+b^2-c^2}{c\left(a+b\right)}\geq\frac32$

for any three positive reals $a$, $b$, $c$.

[i]Comment.[/i] This was an attempt of creating a contrast to the (rather hard) inequality at the QEDMO before. However, it turned out to be more difficult than I expected (a wrong solution was presented during the competition).

  Darij -/
theorem inequalities_35861     (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    3 / 2 ≤ (b ^ 2 + c ^ 2 - a ^ 2) / (a * (b + c)) +
    (c ^ 2 + a ^ 2 - b ^ 2) / (b * (c + a)) +
    (a ^ 2 + b ^ 2 - c ^ 2) / (c * (a + b)) := by
        -- Proving that denominators are non-zero
        have h4 : a * (b + c) ≠ 0 := by
            apply mul_ne_zero
            linarith
            nlinarith
        have h5 : b * (c + a) ≠ 0 := by
            apply mul_ne_zero
            linarith
            nlinarith
        have h6 : c * (a + b) ≠ 0 := by
            apply mul_ne_zero
            linarith
            nlinarith
        -- Reformulating the problem as showing that the difference with 3/2 is non-negative
        have h : (b ^ 2 + c ^ 2 - a ^ 2) / (a * (b + c)) + (c ^ 2 + a ^ 2 - b ^ 2) / (b * (c + a)) + (a ^ 2 + b ^ 2 - c ^ 2) / (c * (a + b)) - 3 / 2 ≥ 0 := by
            -- Proving that all denominators are positive
            have h1 : a * (b + c) > 0 := mul_pos (by linarith) (add_pos (by linarith) (by linarith))
            have h2 : b * (c + a) > 0 := mul_pos (by linarith) (add_pos (by linarith) (by linarith))
            have h3 : c * (a + b) > 0 := mul_pos (by linarith) (add_pos (by linarith) (by linarith))
            -- Finding a common denominator and simplifying the expression
            have h : (b ^ 2 + c ^ 2 - a ^ 2) / (a * (b + c)) + (c ^ 2 + a ^ 2 - b ^ 2) / (b * (c + a)) + (a ^ 2 + b ^ 2 - c ^ 2) / (c * (a + b)) - 3 / 2 =
                (2 * (b ^ 2 + c ^ 2 - a ^ 2) * b * c * (c + a) * (a + b) + 2 * (c ^ 2 + a ^ 2 - b^2) * a * c * (a + b) * (b + c) + 2 * (a^2 + b^2 - c^2) * a * b * (b + c) * (c + a) - 3 * a * b * c * (b + c) * (c + a) * (a + b))
                / (2 * a * b * c * (b + c) * (c + a) * (a + b)) := by
                field_simp [h4, h5, h6]
                ring
            rw [h]
            -- Proving that the numerator is non-negative using various square non-negativity facts
            have h4 : 2 * (b ^ 2 + c ^ 2 - a ^ 2) * b * c * (c + a) * (a + b) + 2 * (c ^ 2 + a ^ 2 - b^2) * a * c * (a + b) * (b + c) + 2 * (a^2 + b^2 - c^2) * a * b * (b + c) * (c + a) - 3 * a * b * c * (b + c) * (c + a) * (a + b) ≥ 0 := by
                nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                    mul_pos h1 h2, mul_pos h2 h3, mul_pos h1 h3]
            -- Proving that the denominator is positive
            have h5 : 2 * a * b * c * (b + c) * (c + a) * (a + b) > 0 := by
                apply mul_pos
                apply mul_pos
                apply mul_pos
                apply mul_pos
                apply mul_pos
                all_goals nlinarith
            -- Applying the division rule for non-negative numerator and positive denominator
            apply div_nonneg
            · linarith
            · nlinarith
        -- Concluding the proof using the reformulated inequality
        linarith
