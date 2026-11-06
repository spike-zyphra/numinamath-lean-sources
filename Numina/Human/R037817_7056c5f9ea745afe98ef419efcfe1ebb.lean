import Mathlib
/- . Let $a, b, c>0$, show that

$$
\frac{3}{a^{3}+b^{3}+c^{3}} \leqslant \frac{1}{a^{3}+b^{3}+a b c}+\frac{1}{b^{3}+c^{3}+a b c}+\frac{1}{c^{3}+a^{3}+a b c} \leqslant \frac{1}{a b c}
$$ -/
theorem inequalities_125535 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
3 / (a ^ 3 + b ^ 3 + c ^ 3) ≤ 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ∧ 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c):= by
  -- Split the proof into two parts for the double inequality
  constructor
  -- First part: proving the left inequality
  .
    -- Cauchy-Schwarz inequality in vector form
    have h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
      (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2:= by
      intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
      -- The sum of squares of differences is non-negative
      have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
      linarith
    -- Transforming the Cauchy-Schwarz inequality into a weighted form
    replace h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
      (x1 ^ 2 / x2 + y1 ^ 2 / y2 + z1 ^ 2 / z2) * (x2 + y2 + z2) ≥ (x1 + y1 + z1) ^ 2:= by
      intro x1 y1 z1 x2 y2 z2 hx1 hy1 hz1 hx2 hy2 hz2
      -- Simplifying square roots of squares for positive values
      have g1 : √(x1 ^ 2 / x2) ^ 2 = x1 ^ 2 / x2:= by refine Real.sq_sqrt (by positivity)
      have g2 : √(y1 ^ 2 / y2) ^ 2 = y1 ^ 2 / y2:= by refine Real.sq_sqrt (by positivity)
      have g3 : √(z1 ^ 2 / z2) ^ 2 = z1 ^ 2 / z2:= by refine Real.sq_sqrt (by positivity)
      have g4 : √x2 ^ 2 = x2:= by refine Real.sq_sqrt (by positivity)
      have g5 : √y2 ^ 2 = y2:= by refine Real.sq_sqrt (by positivity)
      have g6 : √z2 ^ 2 = z2:= by refine Real.sq_sqrt (by positivity)
      -- Apply the original Cauchy-Schwarz inequality with transformed variables
      have h1:= h1 (√(x1 ^ 2 / x2)) (√(y1 ^ 2 / y2)) (√(z1 ^ 2 / z2)) (√x2) (√y2) (√z2) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
      rw [g1, g2, g3, g4, g5, g6] at h1
      -- Simplify expressions involving square roots
      rw [(Eq.symm (Real.sqrt_mul (by positivity) x2)), (show x1 ^ 2 / x2 * x2 = x1 ^ 2 by field_simp), (show √(x1 ^ 2) = x1 by refine Real.sqrt_sq (by positivity))] at h1
      rw [(Eq.symm (Real.sqrt_mul (by positivity) y2)), (show y1 ^ 2 / y2 * y2 = y1 ^ 2 by field_simp), (show √(y1 ^ 2) = y1 by refine Real.sqrt_sq (by positivity))] at h1
      rw [(Eq.symm (Real.sqrt_mul (by positivity) z2)), (show z1 ^ 2 / z2 * z2 = z1 ^ 2 by field_simp), (show √(z1 ^ 2) = z1 by refine Real.sqrt_sq (by positivity))] at h1
      exact h1
    -- Apply the inequality with specific values for our problem
    specialize h1 1 1 1 (a ^ 3 + b ^ 3 + a * b * c) (b ^ 3 + c ^ 3 + a * b * c) (c ^ 3 + a ^ 3 + a * b * c) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    rw [show (1 : ℝ) ^ 2 = 1 by simp] at h1
    rw [show ((1 : ℝ) + 1 + 1) ^ 2 = 9 by ring_nf] at h1
    -- Rewrite the inequality in terms of fractions
    replace h1 : (1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c)) ≥ 9 / (a ^ 3 + b ^ 3 + a * b * c + (b ^ 3 + c ^ 3 + a * b * c) + (c ^ 3 + a ^ 3 + a * b * c)):= by exact (div_le_iff₀ (by positivity)).mpr h1
    -- Simplify the denominator in the right-hand side
    rw [show (a ^ 3 + b ^ 3 + a * b * c + (b ^ 3 + c ^ 3 + a * b * c) + (c ^ 3 + a ^ 3 + a * b * c)) = 2 * (a ^ 3 + b ^ 3 + c ^ 3) + 3 * a * b * c by ring_nf] at h1
    -- Use AM-QM inequality to establish an upper bound
    have h2 : 2 * (a ^ 3 + b ^ 3 + c ^ 3) + 3 * a * b * c ≤ 3 * (a ^ 3 + b ^ 3 + c ^ 3):= by
      suffices (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) ≥ 0 by linarith
      positivity
    have g1 : (9 : ℝ) ≥ 0:= by positivity
    -- Apply division inequality
    replace h2:= div_le_div_of_nonneg_left g1 (by positivity) h2
    rw [show 9 / (3 * (a ^ 3 + b ^ 3 + c ^ 3)) = 3 / (a ^ 3 + b ^ 3 + c ^ 3) by field_simp ; linarith] at h2
    linarith
  -- Second part: proving the right inequality
  .
    -- Use AM-QM inequality for each pair of terms
    have h1 : a ^ 3 + b ^ 3 + a * b * c ≥ a ^ 2 * b + b ^ 2 * a + a * b * c:= by
      suffices (a + b) * (a - b) ^ 2 ≥ 0 by linarith
      positivity
    have h2 : b ^ 3 + c ^ 3 + a * b * c ≥ b ^ 2 * c + c ^ 2 * b + a * b * c:= by
      suffices (b + c) * (b - c) ^ 2 ≥ 0 by linarith
      positivity
    have h3 : c ^ 3 + a ^ 3 + a * b * c ≥ c ^ 2 * a + a ^ 2 * c + a * b * c:= by
      suffices (a + c) * (a - c) ^ 2 ≥ 0 by linarith
      positivity
    -- Apply the fact that if x ≥ y > 0, then 1/x ≤ 1/y
    replace h1:= one_div_le_one_div_of_le (by positivity) h1
    replace h2:= one_div_le_one_div_of_le (by positivity) h2
    replace h3:= one_div_le_one_div_of_le (by positivity) h3
    -- Algebraic identity for the sum of fractions
    have h4 :  1 / (a ^ 2 * b + b ^ 2 * a + a * b * c) + 1 / (b ^ 2 * c + c ^ 2 * b + a * b * c) + 1 / (c ^ 2 * a + a ^ 2 * c + a * b * c) = 1 / (a * b * c):= by
      field_simp
      linarith
    linarith
