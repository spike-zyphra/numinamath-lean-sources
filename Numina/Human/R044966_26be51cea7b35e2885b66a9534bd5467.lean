import Mathlib
open Real
/- Show that \[\log_{a}bc+\log_bca+\log_cab \ge 4(\log_{ab}c+\log_{bc}a+\log_{ca}b)\] for all $a,b,c$ greater than 1. -/
theorem inequalities_72088 (a b c : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) : logb a (b * c) + logb b (c * a) + logb c (a * b) ≥ 4 * logb (a * b) c + 4 * logb (b * c) a + 4 * logb (c * a) b:= by
    -- Convert logarithms with different bases to expressions using natural logarithm
    simp [←Real.log_div_log]
    -- Expand the logarithm of products using the property log(x*y) = log(x) + log(y)
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    -- Introduce substitutions for simplicity: x = log(a), y = log(b), z = log(c)
    set x:= log a with hx
    set y:= log b with hy
    set z:= log c with hz
    -- Clear the value associations to work with x, y, z directly
    clear_value x y z
    -- Replace the original conditions with equivalent conditions on x, y, z
    replace hx : x > 0:= by subst x ; exact log_pos ha
    replace hy : y > 0:= by subst y ; exact log_pos hb
    replace hz : z > 0:= by subst z ; exact log_pos hc
    -- Clear the original variables and conditions as they're no longer needed
    clear ha hb hc a b c
    -- Rewrite the left side of the inequality using algebraic manipulation
    rw [show (y + z) / x + (z + x) / y + (x + y) / z = x * (1 / y + 1 / z) + y * (1 / z + 1 / x) + z * (1 / x + 1 / y) by field_simp ; linarith]
    -- Prove a helper lemma: for positive a, b, c, the expression a*(1/b + 1/c) - 4*(a/(b+c)) ≥ 0
    have h1 : ∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → a * (1 / b + 1 / c) - 4 * (a / (b + c)) ≥ 0:= by
        intro a b c ha hb hc
        -- Rewrite the expression as a perfect square divided by positive terms
        rw [show a * (1 / b + 1 / c) - 4 * (a / (b + c)) = a / (b * c * (b + c)) * (b - c) ^ 2 by field_simp ; linarith]
        -- The expression is non-negative because it's a perfect square divided by positive terms
        positivity
    -- Apply the helper lemma to our variables in different permutations
    have g1:= h1 x y z hx hy hz
    have g2:= h1 y z x hy hz hx
    have g3:= h1 z x y hz hx hy
    -- Combine the results to prove the original inequality
    linarith
