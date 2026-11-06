import Mathlib
/- Let $a, b$ be positive real numbers. Prove that $\sqrt{\frac{a^{2}+a b+b^{2}}{3}}+\sqrt{a b} \leq a+b$. -/
theorem algebra_605787 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    √((a ^ 2 + a * b + b ^ 2) / 3) + √(a * b) ≤ a + b := by
    -- First, we prove a helper lemma:
    -- For any positive x, y: x + y ≤ √(2(x² + y²))
    have h1 : ∀ x y : ℝ, x > 0 → y > 0 → x + y ≤ √(2 * (x ^ 2 + y ^ 2)):= by
        intro x y hx hy
        -- This inequality follows from (x - y)² ≥ 0
        have h1 : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2):= by
            have h1 : (x - y) ^ 2 ≥ 0:= by positivity
            linarith
        -- Take square root of both sides
        replace h1 : √((x + y) ^ 2) ≤ √(2 * (x ^ 2 + y ^ 2)):= by exact Real.sqrt_le_sqrt h1
        rw [show √((x + y) ^ 2) = x + y by refine Real.sqrt_sq (by linarith)] at h1
        exact h1
    -- Apply the helper lemma to our specific terms
    specialize h1 √((a ^ 2 + a * b + b ^ 2) / 3) √(a * b) (by positivity) (by positivity)
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1
    -- Now prove that 2((a² + ab + b²)/3 + ab) ≤ (a + b)²
    -- This follows from (a - b)² ≥ 0
    have h2 : 2 * ((a ^ 2 + a * b + b ^ 2) / 3 + a * b) ≤ (a + b) ^ 2:= by
        have h2 : (a - b) ^ 2 ≥ 0:= by positivity
        linarith
    -- Take square root of both sides
    replace h2 : √(2 * ((a ^ 2 + a * b + b ^ 2) / 3 + a * b)) ≤ √((a + b) ^ 2):= by exact Real.sqrt_le_sqrt h2
    rw [show √((a + b) ^ 2) = a + b by refine Real.sqrt_sq (by linarith)] at h2
    -- Combine the inequalities to complete the proof
    linarith
