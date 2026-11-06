import Mathlib
/- Montrer que pour tous les réels $x, y, z$, on a

$$
\frac{x^{2}-y^{2}}{2 x^{2}+1}+\frac{y^{2}-z^{2}}{2 y^{2}+1}+\frac{z^{2}-x^{2}}{2 z^{2}+1} \leqslant 0 .
$$ -/
theorem algebra_607161 (x y z : ℝ) : (x ^ 2 - y ^ 2) / (2 * x ^ 2 + 1) + (y ^ 2 - z ^ 2) / (2 * y ^ 2 + 1) +
(z ^ 2 - x ^ 2) / (2 * z ^ 2 + 1) ≤ 0 := by
    -- Multiply both sides by 2 to simplify the inequality
    suffices 2 * ((x ^ 2 - y ^ 2) / (2 * x ^ 2 + 1) + (y ^ 2 - z ^ 2) / (2 * y ^ 2 + 1) + (z ^ 2 - x ^ 2) / (2 * z ^ 2 + 1)) ≤ 0 by linarith
    -- Distribute the multiplication by 2
    rw [show 2 * ((x ^ 2 - y ^ 2) / (2 * x ^ 2 + 1) + (y ^ 2 - z ^ 2) / (2 * y ^ 2 + 1) + (z ^ 2 - x ^ 2) / (2 * z ^ 2 + 1)) = 2 * (x ^ 2 - y ^ 2) / (2 * x ^ 2 + 1) + 2 * (y ^ 2 - z ^ 2) / (2 * y ^ 2 + 1) + 2 * (z ^ 2 - x ^ 2) / (2 * z ^ 2 + 1) by ring]

    -- Prove the inequality x^3 + y^3 + z^3 - 3xyz ≥ 0 for positive x, y, z
    have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0:= by
        intro x y z hx hy hz
        -- Express in terms of squares of differences
        have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
        rw [h1]
        positivity

    -- Transform the inequality using cube roots
    replace h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x + y + z - (x * y * z) ^ ((1 : ℝ) / 3) * 3 ≥ 0 := by
        intro x y z hx hy hz
        specialize h1 (x ^ ((1 : ℝ) / 3)) (y ^ ((1 : ℝ) / 3)) (z ^ ((1 : ℝ) / 3)) (by positivity) (by positivity) (by positivity)
        rw [show (x ^ ((1 : ℝ) / 3)) ^ 3 = (x ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
        rw [show (y ^ ((1 : ℝ) / 3)) ^ 3 = (y ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
        rw [show (z ^ ((1 : ℝ) / 3)) ^ 3 = (z ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
        rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
        rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
        rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
        rw [show (1 : ℝ) / 3 * 3 = 1 by ring_nf] at h1
        rw [Eq.symm (Real.mul_rpow (by linarith) (by linarith))] at h1
        rw [Eq.symm (Real.mul_rpow (by positivity) (by linarith))] at h1
        simp at h1
        simp
        linarith

    -- Key algebraic identity for the transformation
    have h2 : ∀ a b : ℝ, 2 * (a ^ 2 - b ^ 2) / (2 * a ^ 2 + 1) = 1 - (2 * b ^ 2 + 1) / (2 * a ^ 2 + 1):= by
        intro a b
        have _ : 2 * a ^ 2 + 1 > 0:= by positivity
        field_simp
        linarith

    -- Apply the inequality to the transformed expressions
    specialize h1 ((2 * y ^ 2 + 1) / (2 * x ^ 2 + 1)) ((2 * z ^ 2 + 1) / (2 * y ^ 2 + 1)) ((2 * x ^ 2 + 1) / (2 * z ^ 2 + 1)) (by positivity) (by positivity) (by positivity)

    -- Establish positivity of denominators
    have g1 : 2 * x ^ 2 + 1 > 0:= by positivity
    have g2 : 2 * y ^ 2 + 1 > 0:= by positivity
    have g3 : 2 * z ^ 2 + 1 > 0:= by positivity

    -- Simplify the product of fractions
    rw [show (2 * y ^ 2 + 1) / (2 * x ^ 2 + 1) * ((2 * z ^ 2 + 1) / (2 * y ^ 2 + 1)) * ((2 * x ^ 2 + 1) / (2 * z ^ 2 + 1)) = 1 by field_simp ; linarith] at h1
    simp at h1

    -- Apply the algebraic identity to each term
    have h3:= h2 x y
    have h4:= h2 y z
    have h5:= h2 z x
    rw [h3, h4, h5]
    clear h2 h3 h4 h5
    linarith
