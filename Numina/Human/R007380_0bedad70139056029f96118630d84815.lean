import Mathlib
/- Let $a, b$ and $c$ be positive real numbers. Prove that

$$
a^{3} b^{6}+b^{3} c^{6}+c^{3} a^{6}+3 a^{3} b^{3} c^{3} \geq a b c\left(a^{3} b^{3}+b^{3} c^{3}+c^{3} a^{3}\right)+a^{2} b^{2} c^{2}\left(a^{3}+b^{3}+c^{3}\right)
$$ -/

theorem algebra_604388 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 * b ^ 6 + b ^ 3 * c ^ 6 + c ^ 3 * a ^ 6 + 3 * a ^ 3 * b ^ 3 * c ^ 3 ≥
    a * b * c * (a ^ 3 * b ^ 3 + b ^ 3 * c ^ 3 + c ^ 3 * a ^ 3) +
    a ^ 2 * b ^ 2 * c ^ 2 * (a ^ 3 + b ^ 3 + c ^ 3) := by

        -- Helper lemma: For positive x, y, z where x ≥ y ≥ z, prove a polynomial inequality
        have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ≥ y → y ≥ z → x * (x - y) * (x - z) + y * (y - z) * (y - x) + z * (z - x) * (z - y) ≥ 0 := by
            intro x y z hx _ hz h1 h2

            -- Prove that z * (z - x) * (z - y) ≥ 0
            have h3 : z * (z - x) * (z - y) ≥ 0:= by
                have g1 : x - z ≥ 0:= by linarith
                have g2 : y - z ≥ 0:= by linarith
                have g3 : z * (x - z) * (y - z) ≥ 0:= by positivity
                linarith

            -- Prove that (x - y) * (x * (x - z) - y * (y - z)) ≥ 0
            have h4 : (x - y) * (x * (x - z) - y * (y - z)) ≥ 0:= by
                have g1 : x - y ≥ 0:= by linarith
                suffices x * (x - z) - y * (y - z) ≥ 0 by positivity
                have _ : x ≥ y:= by linarith
                have g3 : x - z ≥ y - z:= by linarith
                suffices x * (x - z) ≥ y * (y - z) by linarith
                refine mul_le_mul h1 g3 (by linarith) (by linarith)
            linarith

        -- Substitute variables to simplify the expression
        set x:= a * b ^ 2 with hx
        set y:= b * c ^ 2 with hy
        set z:= c * a ^ 2 with hz

        -- Rewrite expressions using the substituted variables
        rw [show a ^ 3 * b ^ 6 = x ^ 3 by ring]
        rw [show b ^ 3 * c ^ 6 = y ^ 3 by ring]
        rw [show c ^ 3 * a ^ 6 = z ^ 3 by ring]
        rw [show 3 * a ^ 3 * b ^ 3 * c ^ 3 = 3 * x * y * z by ring]
        rw [show a * b * c * (a ^ 3 * b ^ 3 + b ^ 3 * c ^ 3 + c ^ 3 * a ^ 3) + a ^ 2 * b ^ 2 * c ^ 2 * (a ^ 3 + b ^ 3 + c ^ 3) = x * y ^ 2 + x ^ 2 * y + x * z ^ 2 + x ^ 2 * z + y * z ^ 2 + y ^ 2 * z by ring]

        -- Prove positivity of substituted variables
        have hxpos : x > 0:= by positivity
        have hypos : y > 0:= by positivity
        have hzpos : z > 0:= by positivity

        -- Clear unnecessary hypotheses and variables
        clear_value x y z
        clear hx hy hz ha hb hc a b c

        -- Case analysis based on the ordering of x, y, z
        by_cases gx : x ≥ y
        .
            by_cases gy : y ≥ z
            .
                specialize h1 x y z hxpos hypos hzpos gx gy
                linarith
            .
                by_cases gz : z ≥ x
                .
                    specialize h1 z x y hzpos hxpos hypos (by linarith) (by linarith)
                    linarith
                .
                    simp at gz gy
                    specialize h1 x z y hxpos hzpos hypos (by linarith) (by linarith)
                    linarith
        .
            simp at gx
            by_cases gy : y ≥ z
            .
                by_cases gz : z ≥ x
                .
                    specialize h1 y z x hypos hzpos hxpos (by linarith) (by linarith)
                    linarith
                .
                    simp at gz gy
                    specialize h1 y x z hypos hxpos hzpos (by linarith) (by linarith)
                    linarith
            .
                simp at gy
                specialize h1 z y x hzpos hypos hxpos (by linarith) (by linarith)
                linarith
