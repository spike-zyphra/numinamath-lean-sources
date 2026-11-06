import Mathlib

/- Let $a, b, c$ be positive real numbers with $a b c=1$. Prove that

$$
\frac{a}{a^{2}+2}+\frac{b}{b^{2}+2}+\frac{c}{c^{2}+2} \leq 1
$$ -/
theorem inequalities_606159 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a / (a ^ 2 + 2) + b / (b ^ 2 + 2) + c / (c ^ 2 + 2) ≤ 1 := by
        -- First, prove that for any positive x, x/(x^2 + 2) ≤ 1/(2 + 1/x)
        have h1 : ∀ x : ℝ, x > 0 → x / (x ^ 2 + 2) ≤ 1 / (2 + 1 / x):= by
            intro x hx
            -- Use the fact that (x-1)^2 ≥ 0 to prove x^2 + 2 ≥ 2x + 1
            have h1 : (x - 1) ^ 2 ≥ 0:= by positivity
            replace h1 : x ^ 2 + 2 ≥ 2 * x + 1:= by linarith
            -- Apply this inequality to show x/(x^2 + 2) ≤ x/(2x + 1)
            replace h1 : x / (x ^ 2 + 2) ≤ x / (2 * x + 1):= by refine div_le_div_of_nonneg_left (by linarith) (by linarith) h1
            -- Show that x/(2x + 1) = 1/(2 + 1/x) by field manipulation
            rw [show x / (2 * x + 1) = 1 / (2 + 1 / x) by field_simp] at h1
            exact h1
        -- Apply the inequality to a, b, and c
        have h2:= h1 a ha
        have h3:= h1 b hb
        have h4:= h1 c hc
        clear h1

        -- Reduce to proving 1/(2 + 1/a) + 1/(2 + 1/b) + 1/(2 + 1/c) ≤ 1
        suffices 1 / (2 + 1 / a) + 1 / (2 + 1 / b) + 1 / (2 + 1 / c) ≤ 1 by linarith

        -- Substitute x = 1/a, y = 1/b, z = 1/c for simplification
        set x:= 1 / a with hx
        set y:= 1 / b with hy
        set z:= 1 / c with hz

        -- Establish positivity of x, y, z and their product relation
        have hxpos : x > 0:= by positivity
        have hypos : y > 0:= by positivity
        have hzpos : z > 0:= by positivity
        have hxyz : x * y * z = 1:= by
            rw [hx, hy, hz]
            field_simp
            rw [habc]

        -- Clear unnecessary hypotheses and variables
        clear_value x y z
        clear hx hy hz h2 h3 h4 habc ha hb hc a b c

        -- Use multiplication by positive number to transform inequality
        have h1 : (2 + x) * (2 + y) * (2 + z) > 0:= by positivity
        suffices (1 / (2 + x) + 1 / (2 + y) + 1 / (2 + z)) * ((2 + x) * (2 + y) * (2 + z)) ≤ 1 * ((2 + x) * (2 + y) * (2 + z)) by exact le_of_mul_le_mul_right this h1

        -- Expand and simplify the inequality
        rw [show (1 / (2 + x) + 1 / (2 + y) + 1 / (2 + z)) * ((2 + x) * (2 + y) * (2 + z)) = (2 + x) * (2 + y) + (2 + x) * (2 + z) + (2 + y) * (2 + z) by field_simp ; linarith]

        -- Reduce to proving x*y*z + x*y + x*z + y*z ≥ 4
        suffices x * y * z + x * y + x * z + y * z ≥ 4 by linarith
        clear h1

        -- Use cubic inequality: x^3 + y^3 + z^3 ≥ 3xyz for positive reals
        have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0:= by
            intro x y z hx hy hz
            -- Express in terms of squares of differences
            have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
            rw [h1]
            positivity

        -- Transform the cubic inequality using cube roots
        replace h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x + y + z - (x * y * z) ^ ((1 : ℝ) / 3) * 3 ≥ 0 := by
            intro x y z hx hy hz
            -- Apply previous inequality to cube roots
            specialize h1 (x ^ ((1 : ℝ) / 3)) (y ^ ((1 : ℝ) / 3)) (z ^ ((1 : ℝ) / 3)) (by positivity) (by positivity) (by positivity)
            -- Simplify powers using real number properties
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

        -- Apply the inequality to the products xy, xz, yz
        specialize h1 (x * y) (x * z) (y * z) (by positivity) (by positivity) (by positivity)
        -- Simplify using xyz = 1
        rw [show (x * y) * (x * z) * (y * z) = (x * y * z) ^ 2 by ring_nf] at h1
        rw [hxyz]
        rw [hxyz] at h1
        simp at h1
        linarith
