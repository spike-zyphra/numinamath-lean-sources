import Mathlib
/- Soient $x, y$ des réels strictement positifs. Montrer que:

$$
x+\frac{y^{2}}{x} \geqslant 2 y
$$

et trouver les cas d'égalité. -/
theorem algebra_607248 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x + y ^ 2 / x ≥ 2 * y ∧ (x + y ^ 2 / x = 2 * y ↔ x = y) := by
        constructor
        . -- First part: proving the inequality x + y²/x ≥ 2y
            -- Multiply both sides by x (which is positive, so inequality direction preserves)
            suffices x * (x + y ^ 2 / x) ≥ x * (2 * y) by exact le_of_mul_le_mul_left this hx
            -- Simplify left side: x * (x + y²/x) = x² + y²
            rw [show x * (x + y ^ 2 / x) = x ^ 2 + y ^ 2 by field_simp ; linarith]
            -- Use the fact that (x-y)² ≥ 0 for all real numbers
            have h1 : (x - y) ^ 2 ≥ 0:= by positivity
            linarith -- Complete the proof using linear arithmetic
        . -- Second part: proving that equality holds if and only if x = y
            constructor
            . -- (→) direction: if x + y²/x = 2y, then x = y
                intro h
                -- Multiply both sides by x
                replace h : x * (x + y ^ 2 / x) = x * (2 * y):= by rw [h]
                -- Simplify to x² + y² = 2xy
                rw [show x * (x + y ^ 2 / x) = x ^ 2 + y ^ 2 by field_simp ; linarith] at h
                -- This means (x-y)² = 0
                replace h : (x - y) ^ 2 = 0:= by linarith
                -- Therefore x - y = 0
                replace h : x - y = 0:= by exact pow_eq_zero h
                linarith -- Conclude x = y
            . -- (←) direction: if x = y, then x + y²/x = 2y
                intro h
                -- Substitute x with y
                rw [h]
                -- Simplify the expression 
                field_simp
                -- Complete the proof using linear arithmetic
                linarith
