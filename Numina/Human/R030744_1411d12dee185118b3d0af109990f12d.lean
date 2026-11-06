import Mathlib

/- If $a, b, c>0$ prove that  $$ \frac{1}{a^{3}+b^{3}+a b c}+\frac{1}{b^{3}+c^{3}+a b c}+\frac{1}{c^{3}+a^{3}+a b c} \leq \frac{1}{a b c} . $$ -/
theorem algebra_606079 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) +
    1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
    -- First, prove that for any positive x,y: (x-y)²(x+y) ≥ 0
    have h1 : ∀ x y : ℝ, x > 0 → y > 0 → (x - y) ^ 2 * (x + y) ≥ 0:= by
        intro x y hx hy
        positivity
    -- Apply the inequality to pairs (b,c), (c,a), and (a,b)
    have h2:= h1 b c hb hc
    have h3:= h1 c a hc ha
    replace h1:= h1 a b ha hb
    -- Show that denominators are greater than or equal to products
    replace h1 : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c):= by linarith
    replace h2 : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (b + c + a):= by linarith
    replace h3 : c ^ 3 + a ^ 3 + a * b * c ≥ c * a * (c + a + b):= by linarith
    -- Apply one_div_le_one_div_of_le to get reciprocal inequalities
    replace h1 : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)):= by refine one_div_le_one_div_of_le (by positivity) h1
    replace h2 : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (b + c + a)):= by refine one_div_le_one_div_of_le (by positivity) h2
    replace h3 : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (c * a * (c + a + b)):= by refine one_div_le_one_div_of_le (by positivity) h3
    -- Rewrite fractions to have common factor 1/(abc)
    rw [show 1 / (a * b * (a + b + c)) = 1 / (a * b * c) * (c / (a + b + c)) by field_simp ; linarith] at h1
    rw [show 1 / (b * c * (b + c + a)) = 1 / (a * b * c) * (a / (b + c + a)) by field_simp ; linarith] at h2
    rw [show 1 / (c * a * (c + a + b)) = 1 / (a * b * c) * (b / (c + a + b)) by field_simp ; linarith] at h3
    -- Final step: prove that the sum of coefficients equals 1
    suffices 1 / (a * b * c) * (c / (a + b + c) + a / (b + c + a) + b / (c + a + b)) ≤ 1 / (a * b * c) by linarith
    rw [show 1 / (a * b * c) * (c / (a + b + c) + a / (b + c + a) + b / (c + a + b)) = 1 / (a * b * c) * (c / (a + b + c) + a / (b + c + a) + b / (c + a + b)) by field_simp]
    -- Key insight: the sum of these three fractions equals 1
    have h4 : c / (a + b + c) + a / (b + c + a) + b / (c + a + b) = 1:= by field_simp ; linarith
    rw [h4]
    simp
