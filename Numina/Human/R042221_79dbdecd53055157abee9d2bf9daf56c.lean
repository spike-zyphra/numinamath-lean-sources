import Mathlib
/- Let the real numbers $a, b, c, d$ satisfy the relations $a+b+c+d=6$ and $a^{2}+b^{2}+c^{2}+d^{2}=12$. Prove that  $$ 36 \leq 4\left(a^{3}+b^{3}+c^{3}+d^{3}\right)-\left(a^{4}+b^{4}+c^{4}+d^{4}\right) \leq 48 $$  (Ukraine) -/
theorem algebra_23908 (a b c d : ℝ) (h1 : a + b + c + d = 6) (h2 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 12) :
36 ≤ 4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) ∧ 4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) ≤ 48:= by
    -- Transform the expression using algebraic manipulation
    have h3 : 4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) = 52 - (a - 1) ^ 4 - (b - 1) ^ 4 - (c - 1) ^ 4 - (d - 1) ^ 4:= by linarith
    rw [h3]
    -- Introduce new variables shifted by 1
    set x:= a - 1 with hx
    set y:= b - 1 with hy
    set z:= c - 1 with hz
    set t:= d - 1 with ht
    clear_value x y z t
    -- Transform the original conditions for the new variables
    replace h1 : x + y + z + t = 2:= by linarith
    replace h2 : x ^ 2 + y ^ 2 + z ^ 2 + t ^ 2 = 4:= by
        rw [hx, hy, hz, ht]
        linarith
    clear hx hy hz ht h3 a b c d
    -- Upper bound: sum of fourth powers is less than square of sum of squares
    have h3 : x ^ 4 + y ^ 4 + z ^ 4 + t ^ 4 ≤ (x ^ 2 + y ^ 2 + z ^ 2 + t ^ 2) ^ 2:= by
        suffices (x ^ 2 + y ^ 2 + z ^ 2 + t ^ 2) ^ 2 - (x ^ 4 + y ^ 4 + z ^ 4 + t ^ 4) ≥ 0 by linarith
        ring_nf
        positivity
    -- Lower bound: sum of fourth powers is greater than square of sum of squares divided by 4
    have h4 : x ^ 4 + y ^ 4 + z ^ 4 + t ^ 4 ≥ (x ^ 2 + y ^ 2 + z ^ 2 + t ^ 2) ^ 2 / 4:= by
        have g1 : (x ^ 2 - y ^ 2) ^ 2 ≥ 0:= by positivity
        have g2 : (z ^ 2 - t ^ 2) ^ 2 ≥ 0:= by positivity
        have g3 : (x ^ 2 + y ^ 2 - z ^ 2 - t ^ 2) ^ 2 ≥ 0:= by positivity
        linarith
    rw [h2] at h3 h4
    constructor
    all_goals
    linarith
