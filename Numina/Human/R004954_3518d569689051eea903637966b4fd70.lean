import Mathlib
/- Prove that for all positive real numbers $a, b$, and $c$,

$$
\frac{a^{3}}{b c}+\frac{b^{3}}{c a}+\frac{c^{3}}{a b} \geq a+b+c
$$

and determine when equality occurs.

Each of the inequalities used in the solutions below has the property that equality holds if and only if $a=b=c$. Thus equality holds for the given inequality if and only if $a=b=c$. -/

theorem algebra_604778 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) ≥ a + b + c) ∧
    (a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) = a + b + c ↔ a = b ∧ b = c) := by

    -- Key algebraic manipulation: express the difference as a sum of squares
    have h1 : a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) - (a + b + c) =
    1 / (2 * a * b * c) * ((a ^ 2 - b ^ 2) ^ 2 + (b ^ 2 - c ^ 2) ^ 2 + (c ^ 2 - a ^ 2) ^ 2 + (a * b - b * c) ^ 2 + (b * c - c * a) ^ 2 + (c * a - a * b) ^ 2):= by
        field_simp
        ring_nf
    constructor
    -- First part: prove the inequality
    .
        -- Since the RHS is a sum of squares divided by positive numbers, it's ≥ 0
        suffices a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) - (a + b + c) ≥ 0 by linarith
        rw [h1]
        positivity
    -- Second part: prove the equality condition
    .
        constructor
        -- Forward direction: if equality holds, then a = b = c
        .
            intro h
            -- If equality holds, then the sum of squares must be zero
            replace h : 1 / (2 * a * b * c) * ((a ^ 2 - b ^ 2) ^ 2 + (b ^ 2 - c ^ 2) ^ 2 + (c ^ 2 - a ^ 2) ^ 2 + (a * b - b * c) ^ 2 + (b * c - c * a) ^ 2 + (c * a - a * b) ^ 2) = 0:= by linarith
            -- The denominator is positive
            have h2 : 1 / (2 * a * b * c) ≠ 0:= by positivity
            -- Therefore the sum of squares must be zero
            replace h : (a ^ 2 - b ^ 2) ^ 2 + (b ^ 2 - c ^ 2) ^ 2 + (c ^ 2 - a ^ 2) ^ 2 + (a * b - b * c) ^ 2 + (b * c - c * a) ^ 2 + (c * a - a * b) ^ 2 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero h2 h
            -- Each square term is non-negative
            have g1 : (a ^ 2 - b ^ 2) ^ 2 ≥ 0:= by positivity
            have g2 : (b ^ 2 - c ^ 2) ^ 2 ≥ 0:= by positivity
            have g3 : (c ^ 2 - a ^ 2) ^ 2 ≥ 0:= by positivity
            have g4 : (a * b - b * c) ^ 2 ≥ 0:= by positivity
            have g5 : (b * c - c * a) ^ 2 ≥ 0:= by positivity
            have g6 : (c * a - a * b) ^ 2 ≥ 0:= by positivity
            -- If sum of non-negative terms is zero, each term must be zero
            replace g4 : (a * b - b * c) ^ 2 = 0:= by linarith
            replace g5 : (b * c - c * a) ^ 2 = 0:= by linarith
            -- Square root of zero is zero
            replace g4 : a * b - b * c = 0:= by exact pow_eq_zero g4
            replace g5 : b * c - c * a = 0:= by exact pow_eq_zero g5
            -- Algebraic manipulation to show a = b = c
            replace g4 : b * (a - c) = 0:= by linarith only [g4]
            replace g5 : c * (b - a) = 0:= by linarith only [g5]
            have g7 : b ≠ 0:= by positivity
            have g8 : c ≠ 0:= by positivity
            replace g4 : a - c = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero g7 g4
            replace g5 : b - a = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero g8 g5
            constructor
            all_goals
            linarith
        -- Backward direction: if a = b = c, then equality holds
        .
            intro h
            rcases h with ⟨h2, h3⟩
            rw [h2, h3]
            field_simp
            linarith
