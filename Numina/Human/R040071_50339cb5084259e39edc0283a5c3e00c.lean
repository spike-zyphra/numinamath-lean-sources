import Mathlib

/- Let $a, b, c$ be positive real numbers such that $a b c=1$. Prove that

$$
\frac{1}{a^{5}+b^{5}+c^{2}}+\frac{1}{b^{5}+c^{5}+a^{2}}+\frac{1}{c^{5}+a^{5}+b^{2}} \leq 1 .
$$ -/
theorem inequalities_605291 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) :
    1 / (a ^ 5 + b ^ 5 + c ^ 2) + 1 / (b ^ 5 + c ^ 5 + a ^ 2) + 1 / (c ^ 5 + a ^ 5 + b ^ 2) ≤ 1 := by
  -- Note that x⁵ + y⁵ ≥ xy(x³ + y³) for x, y > 0.
  have lemma₀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x ^ 5 + y ^ 5 ≥ x * y * (x ^ 3 + y ^ 3) := by
    -- The inequality is equivalent to 0 ≤ (x - y)²(x² + y²)(x + y).
    nlinarith [sq_nonneg (x - y), show 0 ≤ (x ^ 2 + y ^ 2) * (x + y) by positivity]
  calc
    1 / (a ^ 5 + b ^ 5 + c ^ 2) + 1 / (b ^ 5 + c ^ 5 + a ^ 2) + 1 / (c ^ 5 + a ^ 5 + b ^ 2)
    _ ≤ 1 / (a * b * (a ^ 3 + b ^ 3 + c ^ 3)) + 1 / (b * c * (b ^ 3 + c ^ 3 + a ^ 3)) + 1 / (c * a * (c ^ 3 + a ^ 3 + b ^ 3)) := by
      -- Use lemma₀ and habc to prove that 1 / (a ^ 5 + b ^ 5 + c ^ 2) + 1 / (b ^ 5 + c ^ 5 + a ^ 2) + 1 / (c ^ 5 + a ^ 5 + b ^ 2) ≤ 1 / (a * b * (a ^ 3 + b ^ 3 + c ^ 3)) + 1 / (b * c * (b ^ 3 + c ^ 3 + a ^ 3)) + 1 / (c * a * (c ^ 3 + a ^ 3 + b ^ 3)).
      apply add_le_add
      apply add_le_add
      apply div_le_div₀ (by norm_num) (by rfl) (by positivity)
      rw [mul_add, show c ^ 3 = c * c ^ 2 by ring, <-mul_assoc, habc, one_mul]
      apply add_le_add
      exact lemma₀ a b ha hb
      rfl
      apply div_le_div₀ (by norm_num) (by rfl) (by positivity)
      rw [mul_add, show a ^ 3 = a * a ^ 2 by ring, <-mul_assoc, show b * c * a = a * b * c by ring, habc, one_mul]
      apply add_le_add
      exact lemma₀ b c hb hc
      rfl
      apply div_le_div₀ (by norm_num) (by rfl) (by positivity)
      rw [mul_add, show b ^ 3 = b * b ^ 2 by ring, <-mul_assoc, show c * a * b = a * b * c by ring, habc, one_mul]
      apply add_le_add
      exact lemma₀ c a hc ha
      rfl
    _ = 1 / (a ^ 3 + b ^ 3 + c ^ 3) * (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) := by
      -- Rewrite the R.H.S. to 1 / (a ^ 3 + b ^ 3 + c ^ 3) * (1 / (a * b) + 1 / (b * c) + 1 / (c * a)).
      field_simp
      ring
    _ = 1 / (a ^ 3 + b ^ 3 + c ^ 3) * ((a + b + c) / (a * b * c)) := by
      -- Rewrite the R.H.S. to 1 / (a ^ 3 + b ^ 3 + c ^ 3) * ((a + b + c) / (a * b * c)).
      field_simp
      ring
    _ = (a + b + c) / 3 / ((a ^ 3 + b ^ 3 + c ^ 3) / 3) := by
      field_simp [habc]
    _ ≤ (a + b + c) / 3 / (((a + b + c) / 3) ^ 3) := by
      -- Use the fact that ((x + y + z) / 3)³ ≤ (x³ + y³ + z³) / 3 for x, y, z > 0.
      have lemma₁ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : ((x + y + z) / 3) ^ 3 ≤ (x ^ 3 + y ^ 3 + z ^ 3) / 3 := by
        -- The inequality is equivalent to 0 ≤ (x - y)²(y - z)²(z - x)².
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
      apply div_le_div₀ (by positivity) (by norm_num) (by positivity)
      exact lemma₁ a b c ha hb hc
    _ = 9 / (a + b + c) ^ 2 := by
      -- Rewrite the R.H.S. to 9 / (a + b + c) ^ 2.
      field_simp
      ring
    _ ≤ 9 / (3 * (a * b * c) ^ (1 / 3 : ℝ)) ^ 2 := by
      -- Use the AM-GM inequality for 3 variables.
      have lemma₂ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / 3 : ℝ) * x + (1 / 3 : ℝ) * y + (1 / 3 : ℝ) * z ≥ x ^ (1 / 3 : ℝ) * y ^ (1 / 3 : ℝ) * z ^ (1 / 3 : ℝ) := by
        apply Real.geom_mean_le_arith_mean3_weighted (by norm_num) (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity) (by norm_num)
      apply div_le_div₀ (by norm_num) (by rfl) (by positivity)
      rw [Real.mul_rpow, Real.mul_rpow, sq_le_sq₀, mul_comm, <-le_div_iff₀, add_div, add_div, <-one_div_mul_eq_div 3 a, <-one_div_mul_eq_div 3 b, <-one_div_mul_eq_div 3 c]
      apply lemma₂ a b c ha hb hc
      all_goals
        positivity
    _ = 1 := by
      rw [habc]
      norm_num
