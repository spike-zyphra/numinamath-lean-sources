import Mathlib
/- Let $a, b, c$ be positive numbers such that $a b+b c+c a=3$. Prove that
$$
\frac{a}{\sqrt{a^{3}+5}}+\frac{b}{\sqrt{b^{3}+5}}+\frac{c}{\sqrt{c^{3}+5}} \leq \frac{\sqrt{6}}{2}
$$ -/
theorem algebra_604971 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 3) :
    a / √(a ^ 3 + 5) + b / √(b ^ 3 + 5) + c / √(c ^ 3 + 5) ≤ √6 / 2 := by
        -- Step 1: Rewrite each term using the square root of a fraction
        have h1 : ∀ x : ℝ, x > 0 → x / √(x ^ 3 + 5) = √(2 * x ^ 2 / (2 * (x ^ 3 + 5))):= by
            intro x hx
            field_simp
            ring
        rw [h1 a ha, h1 b hb, h1 c hc]
        clear h1

        -- Step 2: Prove an inequality between denominators using (2x+1)(x-1)^2 ≥ 0
        have h1 : ∀ x : ℝ, x > 0 → 2 * x ^ 2 / (2 * (x ^ 3 + 5)) ≤ 2 * x ^ 2 / (3 * (x ^ 2 + 3)):= by
            intro x hx
            have h1 : 2 * (x ^ 3 + 5) ≥ 3 * (x ^ 2 + 3):= by
                have h1 : (2 * x + 1) * (x - 1) ^ 2 ≥ 0:= by positivity
                linarith
            refine div_le_div_of_nonneg_left (by positivity) (by positivity) h1
        -- Step 3: Apply square root to both sides of the inequality
        replace h1 : ∀ x : ℝ, x > 0 → √(2 * x ^ 2 / (2 * (x ^ 3 + 5))) ≤ √(2 * x ^ 2 / (3 * (x ^ 2 + 3))):= by
            intro x hx
            specialize h1 x hx
            exact Real.sqrt_le_sqrt h1
        have h2:= h1 a ha
        have h3:= h1 b hb
        have h4:= h1 c hc

        -- Step 4: Rewrite denominators using the condition ab + bc + ca = 3
        suffices √(2 * a ^ 2 / (3 * (a ^ 2 + 3))) + √(2 * b ^ 2 / (3 * (b ^ 2 + 3))) + √(2 * c ^ 2 / (3 * (c ^ 2 + 3))) ≤ √6 / 2 by linarith
        clear h1 h2 h3 h4
        rw [show a ^ 2 + 3 = (a + b) * (a + c) by rw [←h] ; linarith]
        rw [show b ^ 2 + 3 = (b + c) * (b + a) by rw [←h] ; linarith]
        rw [show c ^ 2 + 3 = (c + a) * (c + b) by rw [←h] ; linarith]

        -- Step 5: Prove key inequality using AM-GM inequality
        have h1 : ∀ x y z: ℝ, x > 0 → y > 0 → z > 0 → √(2 * x ^ 2 / (3 * ((x + y) * (x + z)))) ≤ √6 / 6 * (x / (x + y) + x / (x + z)):= by
            -- Use AM-GM inequality: √(xy) ≤ (x+y)/2
            have h1 : ∀ x y : ℝ, x > 0 → y > 0 → √(x * y) ≤ (x + y) / 2:= by
                intro x y hx hy
                have h1 : (√x - √y) ^ 2 ≥ 0:= by positivity
                ring_nf at h1
                rw [show √x ^ 2 = x by refine Real.sq_sqrt (by linarith)] at h1
                rw [show √y ^ 2 = y by refine Real.sq_sqrt (by linarith)] at h1
                rw [show √x * √y = √(x * y) by refine Eq.symm (Real.sqrt_mul' x (by linarith))] at h1
                linarith

        -- Step 6: Apply the inequality to each term
            intro x y z hx hy hz
            rw [show 2 * x ^ 2 / (3 * ((x + y) * (x + z))) = 2 / 3 * ((x / (x + y)) * (x / (x + z))) by field_simp ; linarith]
            rw [show √(2 / 3 * ((x / (x + y)) * (x / (x + z)))) = √(2 / 3) * √((x / (x + y)) * (x / (x + z))) by refine Real.sqrt_mul (by linarith) (x / (x + y) * (x / (x + z)))]
            specialize h1 (x / (x + y)) (x / (x + z)) (by positivity) (by positivity)
            rw [show √(2 / 3) = √6 / 3 by field_simp ; rw [show (6 : ℝ) = 2 * 3 by ring] ; rw [show √(2 * 3) = √2 * √3 by refine Real.sqrt_mul' 2 (by linarith)] ; rw [show √2 * √3 * √3 = √2 * (√3 * √3) by ring] ; rw [show √3 * √3 = 3 by norm_num]]
            have g1 : √6 / 3 > 0:= by positivity
            replace h1 : (√6 / 3) * (√(x / (x + y) * (x / (x + z)))) ≤ (√6 / 3) * ((x / (x + y) + x / (x + z)) / 2):= by exact (mul_le_mul_iff_of_pos_left g1).mpr h1
            linarith

        -- Step 7: Apply the inequality to each cyclic permutation
        have h2:= h1 a b c ha hb hc
        have h3:= h1 b c a hb hc ha
        have h4:= h1 c a b hc ha hb

        -- Step 8: Final step - prove that the sum equals √6/2
        suffices √6 / 6 * (a / (a + b) + a / (a + c)) + √6 / 6 * (b / (b + c) + b / (b + a)) + √6 / 6 * (c / (c + a) + c / (c + b)) = √6 / 2 by linarith
        rw [show √6 / 6 * (a / (a + b) + a / (a + c)) + √6 / 6 * (b / (b + c) + b / (b + a)) + √6 / 6 * (c / (c + a) + c / (c + b)) = √6 / 6 * (a / (a + b) + a / (a + c) + b / (b + c) + b / (b + a) + c / (c + a) + c / (c + b)) by ring]
        rw [show a / (a + b) + a / (a + c) + b / (b + c) + b / (b + a) + c / (c + a) + c / (c + b) = 3 by field_simp ; linarith]
        linarith
