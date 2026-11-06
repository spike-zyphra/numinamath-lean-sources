import Mathlib
/- MKCD

Let $x, y, z$ be positive real numbers that satisfy the equality $x^{2}+y^{2}+z^{2}=3$. Prove that

$$
\frac{x^{2}+y z}{x^{2}+y z+1}+\frac{y^{2}+z x}{y^{2}+z x+1}+\frac{z^{2}+x y}{z^{2}+x y+1} \leq 2
$$ -/

theorem algebra_604728 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x ^ 2 + y ^ 2 + z ^ 2 = 3) :
(x ^ 2 + y * z) / (x ^ 2 + y * z + 1) + (y ^ 2 + z * x) / (y ^ 2 + z * x + 1) + (z ^ 2 + x * y) / (z ^ 2 + x * y + 1) ≤ 2 := by

    -- Helper lemma 1: Simplify each fraction to 1 - 1/(a^2 + bc + 1)
    have h1 : ∀ a b c: ℝ, a > 0 → b > 0 → c > 0 → (a ^ 2 + b * c) / (a ^ 2 + b * c + 1) = 1 - 1 / (a ^ 2 + b * c + 1) := by
        intro a b c ha hb hc
        field_simp

    -- Apply the simplification to all three fractions
    rw [h1 x y z hx hy hz]
    rw [h1 y z x hy hz hx]
    rw [h1 z x y hz hx hy]
    clear h1

    -- Helper lemma 2: Cauchy-Schwarz inequality in vector form
    have h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
        (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2:= by
        intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
        have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
        linarith

    -- Transform Cauchy-Schwarz into weighted form
    replace h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
        (x1 ^ 2 / x2 + y1 ^ 2 / y2 + z1 ^ 2 / z2) * (x2 + y2 + z2) ≥ (x1 + y1 + z1) ^ 2:= by
        intro x1 y1 z1 x2 y2 z2 hx1 hy1 hz1 hx2 hy2 hz2

        -- Handle square roots for positive numbers
        have g1 : √(x1 ^ 2 / x2) ^ 2 = x1 ^ 2 / x2:= by refine Real.sq_sqrt (by positivity)
        have g2 : √(y1 ^ 2 / y2) ^ 2 = y1 ^ 2 / y2:= by refine Real.sq_sqrt (by positivity)
        have g3 : √(z1 ^ 2 / z2) ^ 2 = z1 ^ 2 / z2:= by refine Real.sq_sqrt (by positivity)
        have g4 : √x2 ^ 2 = x2:= by refine Real.sq_sqrt (by positivity)
        have g5 : √y2 ^ 2 = y2:= by refine Real.sq_sqrt (by positivity)
        have g6 : √z2 ^ 2 = z2:= by refine Real.sq_sqrt (by positivity)

        -- Apply previous Cauchy-Schwarz and simplify
        have h1:= h1 (√(x1 ^ 2 / x2)) (√(y1 ^ 2 / y2)) (√(z1 ^ 2 / z2)) (√x2) (√y2) (√z2) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
        rw [g1, g2, g3, g4, g5, g6] at h1
        rw [(Eq.symm (Real.sqrt_mul (by positivity) x2)), (show x1 ^ 2 / x2 * x2 = x1 ^ 2 by field_simp), (show √(x1 ^ 2) = x1 by refine Real.sqrt_sq (by positivity))] at h1
        rw [(Eq.symm (Real.sqrt_mul (by positivity) y2)), (show y1 ^ 2 / y2 * y2 = y1 ^ 2 by field_simp), (show √(y1 ^ 2) = y1 by refine Real.sqrt_sq (by positivity))] at h1
        rw [(Eq.symm (Real.sqrt_mul (by positivity) z2)), (show z1 ^ 2 / z2 * z2 = z1 ^ 2 by field_simp), (show √(z1 ^ 2) = z1 by refine Real.sqrt_sq (by positivity))] at h1
        exact h1

    -- Apply the inequality with specific values
    specialize h1 1 1 1 (x ^ 2 + y * z + 1) (y ^ 2 + z * x + 1) (z ^ 2 + x * y + 1) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)

    -- Simplify expressions using ring normalization
    rw [show x ^ 2 + y * z + 1 + (y ^ 2 + z * x + 1) + (z ^ 2 + x * y + 1) = x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x + 3 by ring_nf] at h1
    rw [show ((1 : ℝ) + 1 + 1) ^ 2 = 9 by ring_nf] at h1

    -- Prove positivity of denominator
    have h2 : x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x + 3 > 0:= by positivity

    -- Transform inequality using division
    replace h1 : 1 ^ 2 / (x ^ 2 + y * z + 1) + 1 ^ 2 / (y ^ 2 + z * x + 1) + 1 ^ 2 / (z ^ 2 + x * y + 1) ≥ 9 / (x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x + 3):= by exact (div_le_iff₀ h2).mpr h1

    -- Prove upper bound using the condition x^2 + y^2 + z^2 = 3
    have h3 : x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x + 3 ≤ 9:= by
        rw [h]
        have : x * y + y * z + z * x ≤ 3:= by
            rw [←h]
            have h3 : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 ≥ 0:= by positivity
            linarith
        linarith

    -- Final steps using division properties
    replace h3 : 9 / (x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x + 3) ≥ 1:= by exact (one_le_div₀ h2).mpr h3
    rw [show (1 : ℝ) ^ 2 = 1 by ring_nf] at h1
    linarith
