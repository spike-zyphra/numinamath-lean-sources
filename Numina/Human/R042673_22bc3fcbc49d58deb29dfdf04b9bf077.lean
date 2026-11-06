import Mathlib
/- Let $a, b, c$ be positive real numbers. Prove the inequality

$$
\left(a^{2}+a c+c^{2}\right)\left(\frac{1}{a+b+c}+\frac{1}{a+c}\right)+b^{2}\left(\frac{1}{b+c}+\frac{1}{a+b}\right)>a+b+c
$$ -/
theorem algebra_605989 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 + a * c + c ^ 2) * (1 / (a + b + c) + 1 / (a + c)) +
    b ^ 2 * (1 / (b + c) + 1 / (a + b)) > a + b + c := by
        -- First, prove a helper lemma: For positive x, y, we have 1/x + 1/y ≥ 4/(x+y)
        have h1 : ∀ x y : ℝ, x > 0 → y > 0 → 1 / x + 1 / y ≥ 4 / (x + y):= by
            intro x y hx hy
            have h1 : x * y * (x + y) > 0:= by positivity
            suffices (x * y * (x + y)) * (1 / x + 1 / y) ≥ (x * y * (x + y)) * (4 / (x + y)) by exact le_of_mul_le_mul_left this h1
            rw [show (x * y * (x + y)) * (1 / x + 1 / y) = (x + y) ^ 2 by field_simp ; linarith]
            rw [show (x * y * (x + y)) * (4 / (x + y)) = 4 * x * y by field_simp ; linarith]
            replace h1 : (x - y) ^ 2 ≥ 0:= by positivity
            linarith
        -- Apply the helper lemma to our specific terms
        have h2:= h1 (a + b + c) (a + c) (by positivity) (by positivity)
        replace h1:= h1 (b + c) (a + b) (by positivity) (by positivity)

        -- Prove that a² + ac + c² ≥ 3/4(a+c)²
        have h3 : a ^ 2 + a * c + c ^ 2 ≥ 3 / 4 * (a + c) ^ 2:= by
            have h3 : (a - c) ^ 2 ≥ 0:= by positivity
            linarith

        -- Combine the inequalities using multiplication
        replace h3 : (a ^ 2 + a * c + c ^ 2) * (1 / (a + b + c) + 1 / (a + c)) ≥ 3 / 4 * (a + c) ^ 2 * (4 / (a + b + c + (a + c))):= by refine mul_le_mul_of_nonneg h3 h2 (by positivity) (by positivity)
        clear h2
        replace h1 : b ^ 2 * (1 / (b + c) + 1 / (a + b)) ≥ b ^ 2 * (4 / (b + c + (a + b))):= by refine(mul_le_mul_iff_of_pos_left (by positivity)).mpr h1

        -- Field simplification and algebraic manipulation
        rw [show 3 / 4 * (a + c) ^ 2 * (4 / (a + b + c + (a + c))) = (3 * (a + c) ^ 2) / (2 * a + b + 2 * c) by field_simp ; linarith] at h3
        rw [show b ^ 2 * (4 / (b + c + (a + b))) = 3 * b ^ 2 / (b + c + (a + b)) + b ^ 2 / (b + c + (a + b))by field_simp ; linarith] at h1

        -- Prove positivity of intermediate term
        have h2 : b ^ 2 / (b + c + (a + b)) > 0:= by positivity

        -- Reduce to proving a simpler inequality
        suffices (3 * (a + c) ^ 2) / (2 * a + b + 2 * c) + 3 * b ^ 2 / (b + c + (a + b)) ≥ a + b + c by linarith
        clear h1 h2 h3

        -- Final helper lemma: For positive x,y,z,w, we have x²/z + y²/w ≥ (x+y)²/(z+w)
        have h1 : ∀ x y z w : ℝ, x > 0 → y > 0 → z > 0 → w > 0 → x ^ 2 / z + y ^ 2 / w ≥ (x + y) ^ 2 / (z + w):= by
            intro x y z w _ _ hz hw
            have h1 : z + w > 0:= by positivity
            suffices (x ^ 2 / z + y ^ 2 / w) * (z + w) ≥ (x + y) ^ 2 / (z + w) * (z + w) by exact le_of_mul_le_mul_right this h1
            rw [show (x + y) ^ 2 / (z + w) * (z + w) = (x + y) ^ 2 by field_simp]
            rw [show (x ^ 2 / z + y ^ 2 / w) * (z + w) = x ^ 2 + y ^ 2 + x ^ 2 * (w / z) + y ^ 2 * (z / w) by field_simp ; linarith]
            have h2 : x ^ 2 * (w / z) + y ^ 2 * (z / w) ≥ 2 * x * y:= by
                have h2 : w * z > 0:= by positivity
                suffices (x ^ 2 * (w / z) + y ^ 2 * (z / w)) * (w * z) ≥ (2 * x * y) * (w * z) by exact le_of_mul_le_mul_right this h2
                rw [show (x ^ 2 * (w / z) + y ^ 2 * (z / w)) * (w * z) = x ^ 2 * w ^ 2 + y ^ 2 * z ^ 2 by field_simp ; linarith]
                have h3 : (x * w - y * z) ^ 2 ≥ 0:= by positivity
                linarith
            linarith
        -- Apply the final lemma and complete the proof
        specialize h1 (a + c) b (2 * a + b + 2 * c) (b + c + (a + b)) (by positivity) (by positivity) (by positivity) (by positivity)
        rw [show 3 * (a + c) ^ 2 / (2 * a + b + 2 * c) + 3 * b ^ 2 / (b + c + (a + b)) = 3 * ((a + c) ^ 2 / (2 * a + b + 2 * c) + b ^ 2 / (b + c + (a + b))) by ring]
        rw [show (a + c + b) ^ 2 / (2 * a + b + 2 * c + (b + c + (a + b))) = (a + b + c) / 3 by field_simp ; linarith] at h1
        linarith
