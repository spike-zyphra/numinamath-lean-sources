import Mathlib
/- Let $a, b$, and $c$ be positive real numbers. Prove that

$$
\frac{2 a^{2}}{b+c}+\frac{2 b^{2}}{c+a}+\frac{2 c^{2}}{a+b} \geq a+b+c
$$ -/
theorem inequalities_607989 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 * a ^ 2 / (b + c) + 2 * b ^ 2 / (c + a) + 2 * c ^ 2 / (a + b) ≥ a + b + c := by
        -- Prove that the product of denominators is positive
        have h1 : (a + b) * (b + c) * (c + a) > 0:= by positivity
        -- Multiply both sides by the product of denominators to clear fractions
        suffices (a + b) * (b + c) * (c + a) * (2 * a ^ 2 / (b + c) + 2 * b ^ 2 / (c + a) + 2 * c ^ 2 / (a + b)) ≥ (a + b) * (b + c) * (c + a) * (a + b + c) by exact le_of_mul_le_mul_left this h1
        -- Simplify the left side using field operations and linear arithmetic
        rw [show (a + b) * (b + c) * (c + a) * (2 * a ^ 2 / (b + c) + 2 * b ^ 2 / (c + a) + 2 * c ^ 2 / (a + b)) =
        2 * a ^ 2 * (a + b) * (c + a) + 2 * b ^ 2 * (b + c) * (a + b) + 2 * c ^ 2 * (c + a) * (b + c) by field_simp ; linarith]
        -- The following three inequalities are key to the proof:
        -- 1. Sum of squared differences multiplied by squares
        have h2 : a ^ 2 * (b - c) ^ 2 + b ^ 2 * (c - a) ^ 2 + c ^ 2 * (a - b) ^ 2 ≥ 0:= by positivity
        -- 2. Sum of squared differences of squares
        have h3 : (a ^ 2 - b ^ 2) ^ 2 + (b ^ 2 - c ^ 2) ^ 2 + (c ^ 2 - a ^ 2) ^ 2 ≥ 0:= by positivity
        -- 3. Cyclic sum of products of differences
        have h4 : a * b * (a - b) ^ 2 + b * c * (b - c) ^ 2 + c * a * (c - a) ^ 2 ≥ 0:= by positivity
        -- Complete the proof using linear arithmetic
        linarith
