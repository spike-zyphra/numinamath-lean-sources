import Mathlib
/- Let $a$ and $b$ be positive real numbers such that $3 a^{2}+2 b^{2}=3 a+2 b$. Find the minimum value of

$$
A=\sqrt{\frac{a}{b(3 a+2)}}+\sqrt{\frac{b}{a(2 b+3)}}
$$ -/
theorem algebra_605790 : IsLeast {A : ℝ | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ 3 * a ^ 2 + 2 * b ^ 2 = 3 * a + 2 * b ∧ A = √(a / (b * (3 * a + 2))) + √(b / (a * (2 * b + 3)))} (2 / √5):= by
    constructor
    -- Part 1: Prove that 2/√5 is achievable by showing it occurs at a=b=1
    .
        simp
        use 1
        simp
        use 1
        simp
        norm_num
        field_simp
        ring_nf
    -- Part 2: Prove that 2/√5 is the minimum value
    .
        simp [lowerBounds]
        intro A a ha b hb h hA
        subst A
        -- Prove that 5(3a² + 2b²) ≥ (3a + 2b)² using (a-b)² ≥ 0
        have h1 : 5 * (3 * a ^ 2 + 2 * b ^ 2) ≥ (3 * a + 2 * b) * (3 * a + 2 * b):= by
            have h1 : (a - b) ^ 2 ≥ 0:= by positivity
            linarith
        rw [h] at h1
        -- Show 3a + 2b > 0
        have h2 : 3 * a + 2 * b > 0:= by linarith
        -- Derive that 5 ≥ 3a + 2b
        replace h1 : 5 ≥ 3 * a + 2 * b:= by exact le_of_mul_le_mul_right h1 h2
        -- Apply AM-GM inequality: For positive x,y: x + y ≥ 2√(xy)
        have h3 : ∀ x y : ℝ, x > 0 → y > 0 → x + y ≥ 2 * √(x * y):= by
            intro x y hx hy
            have h3 : (√x - √y) ^ 2 ≥ 0:= by positivity
            ring_nf at h3
            rw [show √x ^ 2 = x by refine Real.sq_sqrt (by linarith)] at h3
            rw [show √y ^ 2 = y by refine Real.sq_sqrt (by linarith)] at h3
            rw [show √x * √y = √(x * y) by refine Eq.symm (Real.sqrt_mul' x (by linarith))] at h3
            linarith
        -- Apply AM-GM to our specific terms
        specialize h3 (√(a / (b * (3 * a + 2)))) (√(b / (a * (2 * b + 3)))) (by positivity) (by positivity)
        -- Simplify the product under the square root
        rw [Eq.symm (Real.sqrt_mul' (a / (b * (3 * a + 2))) (by positivity))] at h3
        rw [show a / (b * (3 * a + 2)) * (b / (a * (2 * b + 3))) = 1 / ((3 * a + 2) * (2 * b + 3)) by field_simp ; linarith] at h3
        -- Prove that (3a + 2)(2b + 3) ≤ 25 using (3a - 2b - 1)² ≥ 0
        have h4 : (3 * a + 2) * (2 * b + 3) ≤ 25:= by
            have h4 : (3 * a + 2) * (2 * b + 3) ≤ (3 * a + 2 * b + 5) ^ 2 / 4:= by
                have h4 : (3 * a - 2 * b - 1) ^ 2 ≥ 0:= by positivity
                linarith
            replace h1 : 3 * a + 2 * b + 5 ≤ 10:= by linarith
            have h5 : 3 * a + 2 * b + 5 ≥ 0:= by linarith
            replace h1 : (3 * a + 2 * b + 5) ^ 2 ≤ 100:= by nlinarith only [h1, h5]
            linarith
        -- Complete the proof using properties of square roots and inequalities
        replace h4 : 1 / ((3 * a + 2) * (2 * b + 3)) ≥ 1 / 25:= by refine one_div_le_one_div_of_le (by positivity) h4
        replace h4 : √(1 / ((3 * a + 2) * (2 * b + 3))) ≥ √(1 / 25):= by exact Real.sqrt_le_sqrt h4
        rw [show (1 : ℝ) / 25 = (1 / 5) ^ 2 by ring_nf] at h4
        rw [show √((1 / 5) ^ 2) = 1 / 5 by refine Real.sqrt_sq (by linarith)] at h4
        replace h4 : √√(1 / ((3 * a + 2) * (2 * b + 3))) ≥ √(1 / 5):= by exact Real.sqrt_le_sqrt h4
        have h6 : 2 / √5 = 2 * √(1 / 5):= by field_simp
        rw [h6]
        linarith
