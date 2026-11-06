import Mathlib
/- Prove that

$$
\left(a^{2}+2\right)\left(b^{2}+2\right)\left(c^{2}+2\right) \geq 9(a b+b c+c a)
$$

for all real numbers $a, b, c>0$. -/
theorem algebra_604886 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a ^ 2 + 2) * (b ^ 2 + 2) * (c ^ 2 + 2) ≥ 9 * (a * b + b * c + c * a):= by
    -- Define auxiliary variables for sum, sum of products, and product
    set p:= a + b + c with hp
    set q:= a * b + b * c + c * a with hq
    set r:= a * b * c with hr
    clear_value p q r

    -- The main inequality can be reduced to a sum of non-negative terms
    suffices (r - p / 3) ^ 2 + 10 / 9 * (q ^ 2 - 3 * p * r) + 35 / 9 * (p ^ 2 - 3 * q) + 8 / 9 * (q - 3) ^ 2 ≥ 0 by rw [hp, hq, hr] at this ; linarith

    -- First term is non-negative as it's a square
    have h1 : (r - p / 3) ^ 2 ≥ 0:= by positivity

    -- Second term is non-negative (related to sum of squares of differences of products)
    have h2 : q ^ 2 - 3 * p * r ≥ 0:= by
        rw [hp, hq, hr]
        have g1 : (a * b - b * c) ^ 2 + (b * c - c * a) ^ 2 + (c * a - a * b) ^ 2 ≥ 0:= by positivity
        linarith

    -- Third term is non-negative (related to sum of squares of differences)
    have h3 : p ^ 2 - 3 * q ≥ 0:= by
        rw [hp, hq]
        have g1 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 0:= by positivity
        linarith

    -- Fourth term is non-negative as it's a square
    have h4 : (q - 3) ^ 2 ≥ 0:= by positivity
    linarith
