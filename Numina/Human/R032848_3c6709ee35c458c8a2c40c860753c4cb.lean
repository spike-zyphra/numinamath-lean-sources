import Mathlib
/- Given strictly positive real numbers x, y, z such that xy + yz + zx = 1, prove that:

$$
2\left(x^{2}+y^{2}+z^{2}\right)+\frac{4}{3}\left(\frac{1}{x^{2}+1}+\frac{1}{y^{2}+1}+\frac{1}{z^{2}+1}\right) \geqslant 5
$$ -/
theorem algebra_607360 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = 1) :
    2 * (x ^ 2 + y ^ 2 + z ^ 2) + (4 / 3) * (1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1) + 1 / (z ^ 2 + 1)) ≥ 5 := by
        -- Step 1: Prove that sum of squares is greater than sum of products
        -- Using the fact that sum of squared differences is non-negative
        have h1 : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x := by
            have h1 : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 ≥ 0 := by positivity
            linarith

        -- Step 2: Prove a key inequality: for any positive x, x + 1/x ≥ 2
        -- This is equivalent to (x - 1)² ≥ 0
        have h2 : ∀ x : ℝ, x > 0 → x + 1 / x ≥ 2:= by
            intro x hx
            field_simp
            suffices 2 * x ≤ (x * x + 1) / x * x by exact le_of_mul_le_mul_right this hx
            rw [show (x * x + 1) / x * x = x ^ 2 + 1 by field_simp ; linarith]
            suffices (x - 1) ^ 2 ≥ 0 by linarith
            positivity

        -- Step 3: Scale the previous inequality to get: 3/4 * x + 4/3 * (1/x) ≥ 2
        replace h2 : ∀ x : ℝ, x > 0 → 3 / 4 * x + 4 / 3 * (1 / x) ≥ 2:= by
            intro x hx
            specialize h2 (3 / 4 * x) (by linarith)
            ring_nf at h2
            ring_nf
            exact h2

        -- Step 4: Apply the scaled inequality to x² + 1, y² + 1, and z² + 1
        have h3:= h2 (x ^ 2 + 1) (by positivity)
        have h4:= h2 (y ^ 2 + 1) (by positivity)
        have h5:= h2 (z ^ 2 + 1) (by positivity)

        -- Step 5: Combine all inequalities to prove the final result
        linarith
