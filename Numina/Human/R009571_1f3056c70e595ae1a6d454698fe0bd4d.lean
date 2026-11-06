import Mathlib
/- Démontrer, pour tous réels $\mathrm{a}, \mathrm{b}, \mathrm{c}$ strictement positifs, l'inégalité suivante :

$$
\frac{a}{9 b c+1}+\frac{b}{9 c a+1}+\frac{c}{9 a b+1} \geqslant \frac{a+b+c}{1+(a+b+c)^{2}} .
$$ -/
theorem algebra_607145 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (9 * b * c + 1) + b / (9 * c * a + 1) + c / (9 * a * b + 1) ≥
    (a + b + c) / (1 + (a + b + c)^2) := by
    -- First, prove Cauchy-Schwarz inequality for 3D vectors
    have h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
        (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2:= by
        intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
        have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
        linarith
    -- Transform Cauchy-Schwarz into a weighted form
    replace h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
        (x1 ^ 2 / x2 + y1 ^ 2 / y2 + z1 ^ 2 / z2) * (x2 + y2 + z2) ≥ (x1 + y1 + z1) ^ 2:= by
        intro x1 y1 z1 x2 y2 z2 hx1 hy1 hz1 hx2 hy2 hz2
        have g1 : √(x1 ^ 2 / x2) ^ 2 = x1 ^ 2 / x2:= by refine Real.sq_sqrt (by positivity)
        have g2 : √(y1 ^ 2 / y2) ^ 2 = y1 ^ 2 / y2:= by refine Real.sq_sqrt (by positivity)
        have g3 : √(z1 ^ 2 / z2) ^ 2 = z1 ^ 2 / z2:= by refine Real.sq_sqrt (by positivity)
        have g4 : √x2 ^ 2 = x2:= by refine Real.sq_sqrt (by positivity)
        have g5 : √y2 ^ 2 = y2:= by refine Real.sq_sqrt (by positivity)
        have g6 : √z2 ^ 2 = z2:= by refine Real.sq_sqrt (by positivity)
        have h1:= h1 (√(x1 ^ 2 / x2)) (√(y1 ^ 2 / y2)) (√(z1 ^ 2 / z2)) (√x2) (√y2) (√z2) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
        rw [g1, g2, g3, g4, g5, g6] at h1
        rw [(Eq.symm (Real.sqrt_mul (by positivity) x2)), (show x1 ^ 2 / x2 * x2 = x1 ^ 2 by field_simp), (show √(x1 ^ 2) = x1 by refine Real.sqrt_sq (by positivity))] at h1
        rw [(Eq.symm (Real.sqrt_mul (by positivity) y2)), (show y1 ^ 2 / y2 * y2 = y1 ^ 2 by field_simp), (show √(y1 ^ 2) = y1 by refine Real.sqrt_sq (by positivity))] at h1
        rw [(Eq.symm (Real.sqrt_mul (by positivity) z2)), (show z1 ^ 2 / z2 * z2 = z1 ^ 2 by field_simp), (show √(z1 ^ 2) = z1 by refine Real.sqrt_sq (by positivity))] at h1
        exact h1
    -- Rewrite fractions to match the form needed for applying the inequality
    rw [show a / (9 * b * c + 1) = a ^ 2 / ((9 * b * c + 1) * a)  by field_simp ; linarith]
    rw [show b / (9 * c * a + 1) = b ^ 2 / ((9 * c * a + 1) * b)  by field_simp ; linarith]
    rw [show c / (9 * a * b + 1) = c ^ 2 / ((9 * a * b + 1) * c)  by field_simp ; linarith]
    -- Apply the weighted Cauchy-Schwarz inequality with specific values
    specialize h1 a b c ((9 * b * c + 1) * a) ((9 * c * a + 1) * b) ((9 * a * b + 1) * c) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)

    -- Simplify the denominator sum using ring normalization
    rw [show (9 * b * c + 1) * a + (9 * c * a + 1) * b + (9 * a * b + 1) * c = 27 * a * b * c + a + b + c by ring_nf] at h1

    -- Prove positivity of the denominator
    have g1 : 27 * a * b * c + a + b + c > 0:= by positivity

    -- Rewrite inequality using division
    replace h1 : a ^ 2 / ((9 * b * c + 1) * a) + b ^ 2 / ((9 * c * a + 1) * b) + c ^ 2 / ((9 * a * b + 1) * c) ≥ (a + b + c) ^ 2 / (27 * a * b * c + a + b + c):= by exact (div_le_iff₀ g1).mpr h1

    -- Set up final step of the proof
    suffices (a + b + c) ^ 2 / (27 * a * b * c + a + b + c) ≥ (a + b + c) / (1 + (a + b + c) ^ 2) by linarith
    clear h1

    -- Prove key inequality about the denominator
    have h1 : 27 * a * b * c + a + b + c ≤ (a + b + c) ^ 3 + a + b + c:= by
        -- Use sum of squares inequalities
        have g1 : (a + b) * (a - b) ^ 2 + (b + c) * (b - c) ^ 2 + (c + a) * (c - a) ^ 2 ≥ 0:= by positivity
        have g2 : a * (b - c) ^ 2 + b * (c - a) ^ 2 + c * (a - b) ^ 2 ≥ 0:= by positivity
        linarith

    -- Square is nonnegative
    have g2 : (a + b + c) ^ 2 ≥ 0:= by positivity

    -- Apply division inequality
    replace h1 : (a + b + c) ^ 2 / (27 * a * b * c + a + b + c) ≥ (a + b + c) ^ 2 / ((a + b + c) ^ 3 + a + b + c):= by refine div_le_div_of_nonneg_left g2 g1 h1

    -- Final algebraic simplification
    rw [show (a + b + c) ^ 2 / ((a + b + c) ^ 3 + a + b + c) = (a + b + c) / (1 + (a + b + c) ^ 2) by field_simp ; linarith] at h1
    linarith
