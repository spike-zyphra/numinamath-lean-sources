import Mathlib
/- Let $a, b$, and $c$ be positive real numbers. Prove:

$$
\frac{a}{b}+\frac{b}{c}+\frac{c}{a} \leq \frac{a^{2}}{b^{2}}+\frac{b^{2}}{c^{2}}+\frac{c^{2}}{a^{2}}
$$ -/

theorem algebra_607923 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + b / c + c / a ≤ a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 := by
    -- Step 1: Prove a key lemma about cubic terms
    -- For positive x, y, z: x³ + y³ + z³ - 3xyz ≥ 0
    have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0:= by
        intro x y z hx hy hz
        -- Express the cubic inequality in terms of squares of differences
        have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
        rw [h1]
        positivity

    -- Step 2: Transform the cubic inequality to work with cube roots
    -- This gives us: x + y + z - 3(xyz)^(1/3) ≥ 0
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
    -- Step 3: Apply the inequality to our specific terms a/b, b/c, c/a
    specialize h1 (a / b) (b / c) (c / a) (by positivity) (by positivity) (by positivity)
    -- Note that (a/b)(b/c)(c/a) = 1
    rw [show (a / b) * (b / c) * (c / a) = 1 by field_simp] at h1
    simp at h1

    -- Step 4: Prove auxiliary inequalities using squared differences
    -- For each term, prove: x² + 1 ≥ 2x using (x-1)² ≥ 0
    have h2 : a ^ 2 / b ^ 2 + 1 ≥ 2 * (a / b):= by
        have h2 : (a / b - 1) ^ 2 ≥ 0:= by positivity
        ring_nf at h2
        ring_nf
        linarith

    have h3 : b ^ 2 / c ^ 2 + 1 ≥ 2 * (b / c):= by
        have h3 : (b / c - 1) ^ 2 ≥ 0:= by positivity
        ring_nf at h3
        ring_nf
        linarith

    have h4 : c ^ 2 / a ^ 2 + 1 ≥ 2 * (c / a):= by
        have h4 : (c / a - 1) ^ 2 ≥ 0:= by positivity
        ring_nf at h4
        ring_nf
        linarith

    -- Finally, combine all inequalities to prove the main result
    linarith
