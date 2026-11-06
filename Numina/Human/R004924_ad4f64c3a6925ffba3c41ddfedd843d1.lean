import Mathlib
/- Prove that for all positive real numbers $a, b, c$ we have

$$
\sqrt{a^{2}-a b+b^{2}}+\sqrt{b^{2}-b c+c^{2}} \geqslant \sqrt{a^{2}+a c+c^{2}} .
$$ -/
theorem algebra_604655 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    √(a ^ 2 - a * b + b ^ 2) + √(b ^ 2 - b * c + c ^ 2) ≥
    √(a ^ 2 + a * c + c ^ 2) := by
        -- First, prove that the expressions under square roots are non-negative
        have g1 : a ^ 2 - a * b + b ^ 2 ≥ 0:= by
            have g1 : (a - b) ^ 2 ≥ 0:= by positivity
            have g2 : a * b ≥ 0:= by positivity
            linarith
        have g2 : b ^ 2 - b * c + c ^ 2 ≥ 0:= by
            have g2 : (b - c) ^ 2 ≥ 0:= by positivity
            have g3 : b * c ≥ 0:= by positivity
            linarith

        -- Convert expressions to use absolute values since we know they're non-negative
        rw [show √(a ^ 2 + a * c + c ^ 2) = |√(a ^ 2 + a * c + c ^ 2)| by exact Eq.symm (abs_of_nonneg (by positivity))]
        rw [show √(a ^ 2 - a * b + b ^ 2) + √(b ^ 2 - b * c + c ^ 2) = |√(a ^ 2 - a * b + b ^ 2) + √(b ^ 2 - b * c + c ^ 2)| by exact Eq.symm (abs_of_nonneg (by positivity))]

        -- Reduce to comparing squares (if x² ≥ y² and x,y ≥ 0, then x ≥ y)
        suffices (√(a ^ 2 - a * b + b ^ 2) + √(b ^ 2 - b * c + c ^ 2)) ^ 2 ≥ (√(a ^ 2 + a * c + c ^ 2)) ^ 2 by exact sq_le_sq.mp this

        -- Simplify squares of square roots since we know arguments are non-negative
        rw [Real.sq_sqrt (by positivity)]
        rw [show (√(a ^ 2 - a * b + b ^ 2) + √(b ^ 2 - b * c + c ^ 2)) ^ 2 = (√(a ^ 2 - a * b + b ^ 2)) ^ 2 + (√(b ^ 2 - b * c + c ^ 2)) ^ 2 + 2 * √(a ^ 2 - a * b + b ^ 2) * √(b ^ 2 - b * c + c ^ 2) by ring_nf]
        rw [Real.sq_sqrt (by positivity)]
        rw [Real.sq_sqrt (by positivity)]

        -- Focus on proving the inequality for the cross term
        suffices 2 * √(a ^ 2 - a * b + b ^ 2) * √(b ^ 2 - b * c + c ^ 2) ≥ a * b + b * c + a * c - 2 * b ^ 2 by linarith
        have g3 : |a * b + b * c + a * c - 2 * b ^ 2| ≥ a * b + b * c + a * c - 2 * b ^ 2:= by exact le_abs_self (a * b + b * c + a * c - 2 * b ^ 2)

        -- Continue reducing using absolute values and squares
        suffices 2 * √(a ^ 2 - a * b + b ^ 2) * √(b ^ 2 - b * c + c ^ 2) ≥ |a * b + b * c + a * c - 2 * b ^ 2| by linarith
        rw [show 2 * √(a ^ 2 - a * b + b ^ 2) * √(b ^ 2 - b * c + c ^ 2) = |2 * √(a ^ 2 - a * b + b ^ 2) * √(b ^ 2 - b * c + c ^ 2)| by exact Eq.symm (abs_of_nonneg (by positivity))]
        suffices (2 * √(a ^ 2 - a * b + b ^ 2) * √(b ^ 2 - b * c + c ^ 2)) ^ 2 ≥ (a * b + b * c + a * c - 2 * b ^ 2) ^ 2 by exact sq_le_sq.mp this

        -- Simplify the squared expressions
        rw [show (2 * √(a ^ 2 - a * b + b ^ 2) * √(b ^ 2 - b * c + c ^ 2)) ^ 2 = 4 * (√(a ^ 2 - a * b + b ^ 2)) ^ 2 * (√(b ^ 2 - b * c + c ^ 2)) ^ 2 by ring_nf]
        rw [Real.sq_sqrt (by positivity)]
        rw [Real.sq_sqrt (by positivity)]

        -- Final algebraic manipulations
        suffices 4 * (a ^ 2 - a * b + b ^ 2) * (b ^ 2 - b * c + c ^ 2) - (a * b + b * c + a * c - 2 * b ^ 2) ^ 2 ≥ 0 by linarith
        ring_nf
        suffices 2 * a * b ^ 2 * c + a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 ≥ 2 * a ^ 2 * b * c + 2 * a * b * c ^ 2 by linarith

        -- Complete the proof using the fact that (ab + bc - ac)² ≥ 0
        have g4 : (a * b + b * c - a * c) ^ 2 ≥ 0:= by positivity
        linarith
