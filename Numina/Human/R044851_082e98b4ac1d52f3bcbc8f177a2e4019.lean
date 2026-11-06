import Mathlib
/- Prove that for positive $a, b, c, d$

$$
\frac{a+c}{a+b}+\frac{b+d}{b+c}+\frac{c+a}{c+d}+\frac{d+b}{d+a} \geq 4 .
$$ -/
theorem algebra_241525 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
(a + c) / (a + b) + (b + d) / (b + c) + (c + a) / (c + d) + (d + b) / (d + a) ≥ 4:= by
    -- Helper lemma: For positive x, y, proves x + y ≥ 4 * (1 / (1/x + 1/y))
    have h1 : ∀ x y : ℝ, x > 0 → y > 0 → x + y ≥ 4 * (1 / (1 / x + 1 / y)):= by
        intro x y hx hy
        field_simp
        -- Transform the inequality into an equivalent form
        suffices x + y - 4 * (x * y) / (y + x) ≥ 0 by linarith
        -- Show that the expression equals (x-y)²/(x+y)
        rw [show x + y - 4 * (x * y) / (y + x) = (x - y) ^ 2 / (x + y) by field_simp ; linarith]
        positivity

    -- Apply helper lemma to first pair of terms
    have h2:= h1 ((a + c) / (a + b)) ((c + a) / (c + d)) (by positivity) (by positivity)
    -- Apply helper lemma to second pair of terms
    have h3:= h1 ((b + d) / (b + c)) ((d + b) / (d + a)) (by positivity) (by positivity)
    -- Final step: Show that the sum equals 4
    suffices 4 * (1 / (1 / ((a + c) / (a + b)) + 1 / ((c + a) / (c + d)))) + 4 * (1 / (1 / ((b + d) / (b + c)) + 1 / ((d + b) / (d + a)))) = 4 by linarith
    field_simp
    linarith
