import Mathlib

/- Let $a, b, c$ be positive real numbers such that $a b c=\frac{2}{3}$. Prove that

$$
\frac{a b}{a+b}+\frac{b c}{b+c}+\frac{c a}{c+a} \geqslant \frac{a+b+c}{a^{3}+b^{3}+c^{3}}
$$

(FYR Macedonia) -/
theorem algebra_605563 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 2 / 3) :
    a * b / (a + b) + b * c / (b + c) + c * a / (c + a) ≥
    (a + b + c) / (a ^ 3 + b ^ 3 + c ^ 3) := by
        -- Step 1: Transform each fraction using abc = 2/3
        -- Express a*b/(a+b) in terms of c
        have h1 : a * b / (a + b) = 2 / 3 * (1 / (a * c + b * c)):= by
            replace habc : c = 2 / 3 / (a * b):= by
                field_simp
                linarith
            rw [habc]
            field_simp
            linarith
        -- Express b*c/(b+c) in terms of a
        have h2 : b * c / (b + c) = 2 / 3 * (1 / (b * a + c * a)):= by
            replace habc : a = 2 / 3 / (b * c):= by
                field_simp
                linarith
            rw [habc]
            field_simp
            linarith
        -- Express c*a/(c+a) in terms of b
        have h3 : c * a / (c + a) = 2 / 3 * (1 / (c * b + a * b)):= by
            replace habc : b = 2 / 3 / (c * a):= by
                field_simp
                linarith
            rw [habc]
            field_simp
            linarith
        -- Step 2: Prove Cauchy-Schwarz inequality in a general form
        -- For positive real numbers, (x1²+y1²+z1²)(x2²+y2²+z2²) ≥ (x1x2+y1y2+z1z2)²
        have h4 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
            (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2:= by
            intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
            have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
            linarith
        -- Step 3: Transform Cauchy-Schwarz into a more useful form
        -- This gives us a weighted version of the inequality
        replace h4 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
            (x1 ^ 2 / x2 + y1 ^ 2 / y2 + z1 ^ 2 / z2) * (x2 + y2 + z2) ≥ (x1 + y1 + z1) ^ 2:= by
            intro x1 y1 z1 x2 y2 z2 hx1 hy1 hz1 hx2 hy2 hz2
            have g1 : √(x1 ^ 2 / x2) ^ 2 = x1 ^ 2 / x2:= by refine Real.sq_sqrt (by positivity)
            have g2 : √(y1 ^ 2 / y2) ^ 2 = y1 ^ 2 / y2:= by refine Real.sq_sqrt (by positivity)
            have g3 : √(z1 ^ 2 / z2) ^ 2 = z1 ^ 2 / z2:= by refine Real.sq_sqrt (by positivity)
            have g4 : √x2 ^ 2 = x2:= by refine Real.sq_sqrt (by positivity)
            have g5 : √y2 ^ 2 = y2:= by refine Real.sq_sqrt (by positivity)
            have g6 : √z2 ^ 2 = z2:= by refine Real.sq_sqrt (by positivity)
            have h4:= h4 (√(x1 ^ 2 / x2)) (√(y1 ^ 2 / y2)) (√(z1 ^ 2 / z2)) (√x2) (√y2) (√z2) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
            rw [g1, g2, g3, g4, g5, g6] at h4
            rw [(Eq.symm (Real.sqrt_mul (by positivity) x2)), (show x1 ^ 2 / x2 * x2 = x1 ^ 2 by field_simp), (show √(x1 ^ 2) = x1 by refine Real.sqrt_sq (by positivity))] at h4
            rw [(Eq.symm (Real.sqrt_mul (by positivity) y2)), (show y1 ^ 2 / y2 * y2 = y1 ^ 2 by field_simp), (show √(y1 ^ 2) = y1 by refine Real.sqrt_sq (by positivity))] at h4
            rw [(Eq.symm (Real.sqrt_mul (by positivity) z2)), (show z1 ^ 2 / z2 * z2 = z1 ^ 2 by field_simp), (show √(z1 ^ 2) = z1 by refine Real.sqrt_sq (by positivity))] at h4
            exact h4
        -- Step 4: Apply Cauchy-Schwarz inequality with specific values
        -- Let x1=y1=z1=1 and x2=(ac+bc), y2=(ba+ca), z2=(cb+ab)
        specialize h4 1 1 1 (a * c + b * c) (b * a + c * a) (c * b + a * b) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
        -- Simplify (1:ℝ)^2 = 1
        rw [show (1 : ℝ) ^ 2 = 1 by ring_nf] at h4
        -- Combine similar terms in denominator
        rw [show a * c + b * c + (b * a + c * a) + (c * b + a * b) = 2 * (a * b + b * c + c * a) by ring_nf] at h4
        -- Simplify (1+1+1)^2 = 9
        rw [show ((1 : ℝ) + 1 + 1) ^ 2 = 9 by ring_nf] at h4
        -- Transform inequality into sum of reciprocals form
        replace h4 : 1 / (a * c + b * c) + 1 / (b * a + c * a) + 1 / (c * b + a * b) ≥ 9 / (2 * (a * b + b * c + c * a)):= by exact (div_le_iff₀ (by positivity)).mpr h4
        -- Apply earlier transformations h1, h2, h3
        rw [h1, h2, h3]
        -- Combine similar terms with factor 2/3
        rw [show 2 / 3 * (1 / (a * c + b * c)) + 2 / 3 * (1 / (b * a + c * a)) + 2 / 3 * (1 / (c * b + a * b)) = 2 / 3 * (1 / (a * c + b * c) + 1 / (b * a + c * a) + 1 / (c * b + a * b)) by ring]
        -- State intermediate goal for the final inequality
        suffices 9 / (2 * (a * b + b * c + c * a)) ≥ 3 / 2 * ((a + b + c) / (a ^ 3 + b ^ 3 + c ^ 3)) by linarith
        -- Prove denominator is positive
        have g1 : 2 * (a * b + b * c + c * a) > 0:= by positivity
        -- Rearrange inequality by multiplying both sides
        suffices 9 ≥ 3 / 2 * ((a + b + c) / (a ^ 3 + b ^ 3 + c ^ 3)) * (2 * (a * b + b * c + c * a)) by exact (le_div_iff₀ g1).mpr this
        -- Simplify the right side of inequality
        rw [show 3 / 2 * ((a + b + c) / (a ^ 3 + b ^ 3 + c ^ 3)) * (2 * (a * b + b * c + c * a)) = 3 * (a + b + c) * (a * b + b * c + c * a) / (a ^ 3 + b ^ 3 + c ^ 3) by field_simp ; linarith]
        -- Prove denominator is positive
        have g2 : a ^ 3 + b ^ 3 + c ^ 3 > 0:= by positivity
        -- State final goal after clearing denominators
        suffices 9 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ 3 * (a + b + c) * (a * b + b * c + c * a) by exact (div_le_iff₀ g2).mpr this
        -- Helper lemma: (x-y)²(x+y) ≥ 0 for positive x,y
        have g3 : ∀ x y : ℝ, x > 0 → y > 0 → (x - y) ^ 2 * (x + y) ≥ 0:= by
            intro x y hx hy
            positivity
        -- Apply helper lemma to pairs (a,b), (b,c), (c,a)
        have h5:= g3 a b ha hb
        have h6:= g3 b c hb hc
        have h7:= g3 c a hc ha
        -- Clear unnecessary hypotheses
        clear h1 h2 h3 h4 g1 g2 g3 habc
        -- Transform inequalities into useful form
        replace h5 : a ^ 3 + b ^ 3 ≥ a * b * (a + b):= by linarith only [h5]
        replace h6 : b ^ 3 + c ^ 3 ≥ b * c * (b + c):= by linarith only [h6]
        replace h7 : c ^ 3 + a ^ 3 ≥ c * a * (c + a):= by linarith only [h7]
        -- Final key inequality: x³ + y³ + z³ - 3xyz ≥ 0
        have h8 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0:= by
            intro x y z hx hy hz
            -- Express in terms of squares of differences
            have h8 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
            rw [h8]
            positivity
        -- Apply final inequality to a, b, c
        specialize h8 a b c ha hb hc
        -- Complete proof using linear arithmetic
        linarith
