import Mathlib
/- BLR   Let $a, b, c$ be positive real numbers such that $a b+b c+c a \leq 3 a b c$. Prove that  $$ \sqrt{\frac{a^{2}+b^{2}}{a+b}}+\sqrt{\frac{b^{2}+c^{2}}{b+c}}+\sqrt{\frac{c^{2}+a^{2}}{c+a}}+3 \leq \sqrt{2}(\sqrt{a+b}+\sqrt{b+c}+\sqrt{c+a}) . $$ -/
theorem inequalities_23802 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
(h : a * b + b * c + c * a ≤ 3 * a * b * c) : √((a ^ 2 + b ^ 2) / (a + b)) + √((b ^ 2 + c ^ 2) / (b + c)) +
√((c ^ 2 + a ^ 2) / (c + a)) + 3 ≤ √2 * (√(a + b) + √(b + c) + √(c + a)):= by

    -- Key lemma 1: For positive x, y, proves √2*√(x+y) ≥ √(2xy/(x+y)) + √((x²+y²)/(x+y))
    have h1 : ∀ x y : ℝ, x > 0 → y > 0 → √2 * √(x + y) ≥ √(2 * x * y / (x + y)) + √((x ^ 2 + y ^ 2) / (x + y)):= by
        intro x y hx hy
        have h1 : √2 * √(x + y) = 2 * √(x * y / (x + y)) * √(1 / 2 * (2 + (x ^ 2 + y ^ 2) / (x * y))):= by
            rw [show 2 + (x ^ 2 + y ^ 2) / (x * y) = (x + y) ^ 2 / (x * y) by field_simp ; linarith]
            rw [show √(1 / 2 * ((x + y) ^ 2 / (x * y))) = √(1 / 2) * √((x + y) ^ 2 / (x * y)) by field_simp]
            suffices √2 * √(x + y) = 2 * √(1 / 2) * (√(x * y / (x + y)) * √((x + y) ^ 2 / (x * y))) by linarith
            rw [show 2 * √(1 / 2) = √2 by field_simp]
            rw [show √(x * y / (x + y)) * √((x + y) ^ 2 / (x * y)) = √((x * y / (x + y)) * ((x + y) ^ 2 / (x * y))) by field_simp]
            rw [show (x * y / (x + y)) * ((x + y) ^ 2 / (x * y)) = x + y by field_simp ; linarith]
        have h2 : √(1 / 2 * (2 + (x ^ 2 + y ^ 2) / (x * y))) ≥ 1 / 2 * (√2 + √((x ^ 2 + y ^ 2) / (x * y))):= by
            have h2 : ∀ a b : ℝ, a > 0 → b > 0 → √((a ^ 2 + b ^ 2) / 2) ≥ (a + b) / 2:= by
                intro a b ha hb
                have h2 : (a ^ 2 + b ^ 2) / 2 ≥ ((a + b) / 2) ^ 2:= by
                    have h2 : (a - b) ^ 2 ≥ 0:= by positivity
                    linarith
                replace h2 : √((a ^ 2 + b ^ 2) / 2) ≥ √(((a + b) / 2) ^ 2):= by exact Real.sqrt_le_sqrt h2
                rw [show √(((a + b) / 2) ^ 2) = (a + b) / 2 by refine Real.sqrt_sq (by linarith)] at h2
                exact h2
            specialize h2 √2 (√((x ^ 2 + y ^ 2) / (x * y))) (by positivity) (by positivity)
            rw [show √2 ^ 2 = 2 by field_simp] at h2
            rw [show √((x ^ 2 + y ^ 2) / (x * y)) ^ 2 = (x ^ 2 + y ^ 2) / (x * y) by refine Real.sq_sqrt (by positivity)] at h2
            field_simp
            field_simp at h2
            rw [show √x * √y * 2 = 2 * (√x * √y) by ring] at h2
            rw [show √x * √y * √2 = √2 * (√x * √y) by ring] at h2
            exact h2
        have g1 : 2 * √(x * y / (x + y)) ≥ 0:= by positivity
        replace h2 : 2 * √(x * y / (x + y)) * √(1 / 2 * (2 + (x ^ 2 + y ^ 2) / (x * y))) ≥ 2 * √(x * y / (x + y)) * (1 / 2 * (√2 + √((x ^ 2 + y ^ 2) / (x * y)))):= by exact mul_le_mul_of_nonneg_left h2 g1
        rw [show 2 * √(x * y / (x + y)) * (1 / 2 * (√2 + √((x ^ 2 + y ^ 2) / (x * y)))) = √(x * y / (x + y)) * √2 + √(x * y / (x + y)) * √((x ^ 2 + y ^ 2) / (x * y)) by linarith] at h2
        rw [show √(x * y / (x + y)) * √2 = √(2 * x * y / (x + y)) by field_simp ; linarith] at h2
        rw [show √(x * y / (x + y)) * √((x ^ 2 + y ^ 2) / (x * y)) = √((x ^ 2 + y ^ 2) / (x + y)) by field_simp ; linarith] at h2
        linarith

    -- Apply lemma h1 to pairs (b,c), (c,a), and (a,b)
    have h2:= h1 b c hb hc
    have h3:= h1 c a hc ha
    replace h1:= h1 a b ha hb

    -- Reduce to proving √(2bc/(b+c)) + √(2ca/(c+a)) + √(2ab/(a+b)) ≥ 3
    suffices √(2 * b * c / (b + c)) + √(2 * c * a / (c + a)) + √(2 * a * b / (a + b)) ≥ 3 by linarith
    clear h1 h2 h3

    -- Key lemma 2: For positive x, y, z, proves x + y + z ≥ 3*√(3/(1/x² + 1/y² + 1/z²))
    have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x + y + z ≥ 3 * √(3 / (1 / x ^ 2 + 1 / y ^ 2 + 1 / z ^ 2)):= by
        intro x y z hx hy hz
        have h1 : 3 / (1 / x ^ 2 + 1 / y ^ 2 + 1 / z ^ 2) ≤ ((x + y + z) / 3) ^ 2:= by
            have h1 : 1 / x ^ 2 + 1 / y ^ 2 + 1 / z ^ 2 ≥ (1 / x + 1 / y + 1 / z) ^ 2 / 3:= by
                have h1 : (1 / x - 1 / y) ^ 2 + (1 / y - 1 / z) ^ 2 + (1 / z - 1 / x) ^ 2 ≥ 0:= by positivity
                rw [show 1 / x ^ 2 = (1 / x) ^ 2 by ring]
                rw [show 1 / y ^ 2 = (1 / y) ^ 2 by ring]
                rw [show 1 / z ^ 2 = (1 / z) ^ 2 by ring]
                linarith
            have g1 : (1 / x + 1 / y + 1 / z) ^ 2 / 3 > 0:= by positivity
            replace g1 : 3 / (1 / x ^ 2 + 1 / y ^ 2 + 1 / z ^ 2) ≤ 3 / ((1 / x + 1 / y + 1 / z) ^ 2 / 3):= by refine div_le_div_of_nonneg_left (by linarith) g1 h1
            suffices 3 / ((1 / x + 1 / y + 1 / z) ^ 2 / 3) ≤ ((x + y + z) / 3) ^ 2 by linarith
            clear g1 h1
            rw [show 3 / ((1 / x + 1 / y + 1 / z) ^ 2 / 3) = (3 / (1 / x + 1 / y + 1 / z)) ^ 2 by field_simp ; linarith]
            suffices |3 / (1 / x + 1 / y + 1 / z)| ≤ |(x + y + z) / 3| by exact sq_le_sq.mpr this
            rw [show |3 / (1 / x + 1 / y + 1 / z)| = 3 / (1 / x + 1 / y + 1 / z) by exact abs_of_nonneg (by positivity)]
            rw [show |(x + y + z) / 3| = (x + y + z) / 3 by exact abs_of_nonneg (by positivity)]
            have g1 : 1 / x + 1 / y + 1 / z > 0:= by positivity
            suffices 3 ≤ (x + y + z) / 3 * (1 / x + 1 / y + 1 / z) by exact (div_le_iff₀ g1).mpr this
            rw [show (x + y + z) / 3 * (1 / x + 1 / y + 1 / z) = 1 / 3 * (3 + x / y + y / x + x / z + z / x + y / z + z / y) by field_simp ; linarith]
            have h2 : ∀ x y : ℝ, x > 0 → y > 0 → x / y + y / x - 2 ≥ 0:= by
                intro x y hx hy
                rw [show x / y + y / x - 2 = (x - y) ^ 2 / (x * y) by field_simp ; linarith]
                positivity
            have h3:= h2 x y hx hy
            have h4:= h2 y z hy hz
            have h5:= h2 z x hz hx
            linarith
        replace h1 : √(3 / (1 / x ^ 2 + 1 / y ^ 2 + 1 / z ^ 2)) ≤ √(((x + y + z) / 3) ^ 2):= by exact Real.sqrt_le_sqrt h1
        rw [Real.sqrt_sq (by positivity)] at h1
        linarith

    -- Apply lemma h1 to the three square roots
    specialize h1 √(2 * b * c / (b + c)) √(2 * c * a / (c + a)) √(2 * a * b / (a + b)) (by positivity) (by positivity) (by positivity)

    -- Simplify expressions using square root properties
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1

    -- Final algebraic manipulation to complete the proof
    rw [show 3 / (1 / (2 * b * c / (b + c)) + 1 / (2 * c * a / (c + a)) + 1 / (2 * a * b / (a + b))) = 3 * a * b * c / (a * b + b * c + c * a) by field_simp ; linarith] at h1

    -- Prove that 3abc/(ab+bc+ca) ≥ 1 using the hypothesis
    have h2 : 3 * a * b * c / (a * b + b * c + c * a) ≥ 1:= by
        have g1 : a * b + b * c + c * a > 0:= by positivity
        exact (one_le_div₀ g1).mpr h

    -- Take square root of the inequality
    replace h2 : √(3 * a * b * c / (a * b + b * c + c * a)) ≥ 1:= by exact Real.one_le_sqrt.mpr h2
    linarith
