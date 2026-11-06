import Mathlib
/- Soient a, b, c des réels strictement positifs. Montrer que
$$
\frac{a}{b c}+\frac{b}{a c}+\frac{c}{a b} \geqslant \frac{2}{a}+\frac{2}{b}-\frac{2}{c} .
$$
Attention, il y a bien un "moins" dans le membre de droite! -/
theorem algebra_607707 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b * c) + b / (a * c) + c / (a * b) ≥ 2 / a + 2 / b - 2 / c := by
        -- First, prove that the product abc is positive
        have h1 : a * b * c > 0:= by positivity
        -- Multiply both sides by abc (which preserves inequality since abc > 0)
        suffices (a / (b * c) + b / (a * c) + c / (a * b)) * (a * b * c) ≥ (2 / a + 2 / b - 2 / c) * (a * b * c) by exact le_of_mul_le_mul_right this h1
        -- Simplify left side to a² + b² + c²
        rw [show (a / (b * c) + b / (a * c) + c / (a * b)) * (a * b * c) = a ^ 2 + b ^ 2 + c ^ 2 by field_simp ; linarith]
        -- Simplify right side to 2ac + 2bc - 2ab
        rw [show (2 / a + 2 / b - 2 / c) * (a * b * c) = 2 * a * c + 2 * b * c - 2 * a * b by field_simp ; linarith]
        -- Use the fact that (a + b - c)² ≥ 0
        have h2 : (a + b - c) ^ 2 ≥ 0:= by positivity
        -- Complete the proof using linear arithmetic
        linarith
