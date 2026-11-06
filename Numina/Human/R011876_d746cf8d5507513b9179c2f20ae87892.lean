import Mathlib
/- Let $a$, $b$ and $c$ be real numbers such that $abc=1$. Prove that the most two of numbers
$$2a-\frac{1}{b},\ 2b-\frac{1}{c},\ 2c-\frac{1}{a}$$
are greater than $1$. -/
theorem algebra_70646 (a b c : ℝ) (h : a * b * c = 1) : 2 * a - 1 / b ≤ 1 ∨ 2 * b - 1 / c ≤ 1 ∨ 2 * c - 1 / a ≤ 1:= by
  -- Proof by contradiction: assume all three expressions are greater than 1
  by_contra H
  simp at H
  field_simp at H
  rcases H with ⟨H1, H2, H3⟩
  -- Since a*b*c = 1, none of a, b, c can be zero
  have g1 : a * b * c ≠ 0:= by linarith
  simp at g1
  rcases g1 with ⟨⟨g1, g2⟩, g3⟩
  -- Each of a, b, c must be either positive or negative
  replace g1 : a < 0 ∨ a > 0:= by exact lt_or_gt_of_ne g1
  replace g2 : b < 0 ∨ b > 0:= by exact lt_or_gt_of_ne g2
  replace g3 : c < 0 ∨ c > 0:= by exact lt_or_gt_of_ne g3
  -- Case analysis: first consider when a < 0
  rcases g1 with g1 | g1
  .
    -- Case: a < 0
    rcases g2 with g2 | g2
    .
      -- Case: a < 0, b < 0
      rcases g3 with g3 | g3
      .
        -- Case: a < 0, b < 0, c < 0
        -- This leads to a contradiction with a*b*c = 1
        replace g1 : a * b > 0:= by exact mul_pos_of_neg_of_neg g1 g2
        replace g1 : a * b * c < 0:= by exact mul_neg_of_pos_of_neg g1 g3
        linarith
      .
        -- Case: a < 0, b < 0, c > 0
        -- This leads to a contradiction with our assumption
        replace g3 : 1 / c > 0:= by positivity
        linarith
    .
      -- Case: a < 0, b > 0
      rcases g3 with _ | g3
      .
        -- Case: a < 0, b > 0, c < 0
        -- This leads to a contradiction with our assumption
        replace g2 : 1 / b > 0:= by positivity
        linarith
      .
        -- Case: a < 0, b > 0, c > 0
        -- This leads to a contradiction with a*b*c = 1
        replace g1 : a * b < 0:= by exact mul_neg_of_neg_of_pos g1 g2
        replace g1 : a * b * c < 0:= by exact mul_neg_of_neg_of_pos g1 g3
        linarith
  .
    -- Case: a > 0
    rcases g2 with g2 | g2
    .
      -- Case: a > 0, b < 0
      rcases g3 with g3 | g3
      .
        -- Case: a > 0, b < 0, c < 0
        -- This leads to a contradiction with our assumption
        replace g1 : 1 / a > 0:= by positivity
        linarith
      .
        -- Case: a > 0, b < 0, c > 0
        -- This leads to a contradiction with a*b*c = 1
        replace g1 : a * b < 0:= by exact mul_neg_of_pos_of_neg g1 g2
        replace g1 : a * b * c < 0:= by exact mul_neg_of_neg_of_pos g1 g3
        linarith
    .
      -- Case: a > 0, b > 0
      rcases g3 with g3 | g3
      .
        -- Case: a > 0, b > 0, c < 0
        -- This leads to a contradiction with a*b*c = 1
        replace g1 : a * b > 0:= by positivity
        replace g1 : a * b * c < 0:= by exact mul_neg_of_pos_of_neg g1 g3
        linarith
      .
        -- Case: a > 0, b > 0, c > 0 (main case)
        -- Rewrite the expressions using the fact that a*b*c = 1
        rw [show 1 / b = a * c by field_simp ; linarith] at H1
        rw [show 1 / c = a * b by field_simp ; linarith] at H2
        rw [show 1 / a = b * c by field_simp ; linarith] at H3
        -- Simplify the inequalities
        replace H1 : a * (2 - c) > 1:= by linarith
        replace H2 : b * (2 - a) > 1:= by linarith
        replace H3 : c * (2 - b) > 1:= by linarith
        -- Prove that 2-a > 0
        have g4 : 2 - a > 0:= by
          by_contra H
          simp at H
          replace H : a - 2 ≥ 0:= by linarith
          replace H : b * (a - 2) ≥ 0:= by positivity
          linarith
        -- Prove that 2-b > 0
        have g5 : 2 - b > 0:= by
          by_contra H
          simp at H
          replace H : b - 2 ≥ 0:= by linarith
          replace H : c * (b - 2) ≥ 0:= by positivity
          linarith
        -- Prove that 2-c > 0
        have g6 : 2 - c > 0:= by
          by_contra H
          simp at H
          replace H : c - 2 ≥ 0:= by linarith
          replace H : a * (c - 2) ≥ 0:= by positivity
          linarith
        -- Multiply the inequalities together
        replace H1 : a * (2 - c) * (b * (2 - a)) > 1 * 1:= by refine Right.mul_lt_mul_of_nonneg H1 H2 (by positivity) (by positivity)
        replace H1:= Right.mul_lt_mul_of_nonneg H1 H3 (by positivity) (by positivity)
        simp at H1
        clear H2 H3
        -- Simplify the product using a*b*c = 1
        rw [show a * (2 - c) * (b * (2 - a)) * (c * (2 - b)) = 1 * (2 - a) * (2 - b) * (2 - c) by rw [←h] ; ring] at H1
        simp at H1
        -- Apply AM-GM inequality: for positive reals, x^3 + y^3 + z^3 - 3xyz ≥ 0
        have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0:= by
          intro x y z hx hy hz
          have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
          rw [h1]
          positivity
        -- Reformulate the inequality in terms of cube roots
        replace h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x + y + z - (x * y * z) ^ ((1 : ℝ) / 3) * 3 ≥ 0 := by
          intro x y z hx hy hz
          specialize h1 (x ^ ((1 : ℝ) / 3)) (y ^ ((1 : ℝ) / 3)) (z ^ ((1 : ℝ) / 3)) (by positivity) (by positivity) (by positivity)
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
        -- Apply the inequality to a, b, c
        specialize h1 a b c g1 g2 g3
        rw [h] at h1
        simp at h1
        -- Apply AM-GM inequality: for positive reals, xyz ≤ ((x+y+z)/3)^3
        have h2 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x * y * z ≤ ((x + y + z) / 3) ^ 3:= by
          intro x y z hx hy hz
          have g1 : x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2 ≥ 0:= by positivity
          have g2 : (y + z) * (y - z) ^ 2 + (z + x) * (z - x) ^ 2 + (x + y) * (x - y) ^ 2 ≥ 0:= by positivity
          linarith
        -- Apply the inequality to (2-a), (2-b), (2-c)
        specialize h2 (2 - a) (2 - b) (2 - c) g4 g5 g6
        rw [show (2 - a + (2 - b) + (2 - c)) / 3 = 2 - (a + b + c) / 3 by linarith] at h2
        have h3 : 2 - (a + b + c) / 3 ≥ 0:= by linarith
        replace h1 : 2 - (a + b + c) / 3 ≤ 1:= by linarith
        replace h1 : (2 - (a + b + c) / 3) ^ 3 ≤ 1:= by exact pow_le_one₀ h3 h1
        -- Final contradiction
        linarith
