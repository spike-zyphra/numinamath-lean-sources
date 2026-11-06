import Mathlib
/- Soit $x, y, z>0$ tels que $x y z=8$. Montrer que

$$
\frac{x-2}{x+1}+\frac{y-2}{y+1}+\frac{z-2}{z+1} \leqslant 0
$$ -/
theorem algebra_607470 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxyz : x * y * z = 8) :
(x - 2) / (x + 1) + (y - 2) / (y + 1) + (z - 2) / (z + 1) ≤ 0:= by

    -- Helper lemma: Simplifies (a-2)/(a+1) to 1 - 3/(a+1) for any positive real number a
    have h1 : ∀ a : ℝ, a > 0 → (a - 2) / (a + 1) = 1 - 3 * (1 / (a + 1)):= by
        intro a ha
        field_simp
        linarith

    -- Apply the helper lemma to each term
    rw [h1 x hx]
    rw [h1 y hy]
    rw [h1 z hz]
    clear h1

    -- Key step: Prove that 1/(x+1) + 1/(y+1) + 1/(z+1) ≥ 1
    have h1 : 1 / (x + 1) + 1 / (y + 1) + 1 / (z + 1) ≥ 1:= by
        -- Inner lemma: For positive reals, x³ + y³ + z³ - 3xyz ≥ 0
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
            -- Series of algebraic manipulations to simplify the expression
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

        -- Apply the transformed inequality to our specific case where xyz = 8
        specialize h1 x y z hx hy hz
        rw [hxyz] at h1
        rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by ring_nf] at h1
        rw [(Eq.symm (Real.rpow_mul (by linarith) 3 (1 / 3)))] at h1
        rw [show (3 : ℝ) * (1 / 3) = 1 by ring_nf] at h1
        simp at h1

        -- Final steps to prove the inequality using multiplication by positive numbers
        have g1 : (x + 1) * (y + 1) * (z + 1) > 0:= by positivity
        suffices (1 / (x + 1) + 1 / (y + 1) + 1 / (z + 1)) * ((x + 1) * (y + 1) * (z + 1)) ≥ 1 * ((x + 1) * (y + 1) * (z + 1)) by exact le_of_mul_le_mul_right this g1
        rw [show (1 / (x + 1) + 1 / (y + 1) + 1 / (z + 1)) * ((x + 1) * (y + 1) * (z + 1)) = (x + 1) * (y + 1) + (y + 1) * (z + 1) + (z + 1) * (x + 1) by field_simp ; linarith]
        linarith

    -- Complete the proof using the inequality we just proved
    linarith
