import Mathlib

/- Let $a, b, c$ be positive real numbers. Prove that

$$
\frac{1}{a b(b+1)(c+1)}+\frac{1}{b c(c+1)(a+1)}+\frac{1}{c a(a+1)(b+1)} \geq \frac{3}{(1+a b c)^{2}}
$$ -/
theorem inequalities_604938
  (a b c : ℝ)
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c) :
  1 / (a * b * (b + 1) * (c + 1)) +
    1 / (b * c * (c + 1) * (a + 1)) +
    1 / (c * a * (a + 1) * (b + 1))
    ≥ 3 / (1 + a * b * c) ^ 2 := by
  -- By cancelling the denominators, the original problem is equivalent to
  --
  -- (1 + a * b * c) ^ 2 * (a * b + b * c + c * a + a + b + c) ≥ 3 * a * b * c * (a * b + b * c + c * a + a + b + c + a * b * c + 1)
  --
  -- We can rewrite the left-hand side as
  --
  -- (1 + a * b * c) ^ 2 * (a * b + b * c + c * a + a + b + c)
  suffices H : (1 + a * b * c) ^ 2 * (a * b + b * c + c * a + a + b + c) ≥ 3 * a * b * c * (a * b + b * c + c * a + a + b + c + a * b * c + 1) by
    -- Multiply both sides by the lcm of the denominators to clear them
    refine le_of_mul_le_mul_of_pos_left ?_ (show 0 < a * b * c * (a + 1) * (b + 1) * (c + 1) * (1 + a * b * c) ^ 2 by positivity)
    calc
      _ = 3 * a * b * c * (a * b + b * c + c * a + a + b + c + a * b * c + 1) * ((1 + a * b * c) ^ 2 / (1 + a * b * c) ^ 2) := by ring
      _ = 3 * a * b * c * (a * b + b * c + c * a + a + b + c + a * b * c + 1) := by simp [show (1 + a * b * c) ^ 2 ≠ 0 by positivity]
      _ ≤ (1 + a * b * c) ^ 2 * (a * b + b * c + c * a + a + b + c) := H
      _ = _ := Eq.symm ?_
    calc
      _ = (1 + a * b * c) ^ 2 * (c * (a + 1) * ((a * b * (b + 1) * (c + 1)) / (a * b * (b + 1) * (c + 1))) + a * (b + 1) * ((b * c * (c + 1) * (a + 1)) / (b * c * (c + 1) * (a + 1))) + b * (c + 1) * ((c * a * (a + 1) * (b + 1)) / (c * a * (a + 1) * (b + 1)))) := by ring
      _ = (1 + a * b * c) ^ 2 * (c * (a + 1) + a * (b + 1) + b * (c + 1)) := by
        simp [show a * b * (b + 1) * (c + 1) ≠ 0 by positivity, show b * c * (c + 1) * (a + 1) ≠ 0 by positivity, show c * a * (a + 1) * (b + 1) ≠ 0 by positivity]
      _ = (1 + a * b * c) ^ 2 * (a * b + b * c + c * a + a + b + c) := by ring

  -- Set m := a + b + c, n := a * b + b * c + c * a, and x ^ 3 = a * b * c
  let m := a + b + c
  let n := a * b + b * c + c * a
  obtain ⟨x, xpos, hx⟩ : ∃ x : ℝ, 0 < x ∧ a * b * c = x ^ 3 := by
    use (a * b * c) ^ (1 / 3 : ℝ), by positivity
    rw [← Real.rpow_mul_natCast (by positivity)]
    simp
  -- We can rewrite the left-hand side as
  -- (m + n) * (x ^ 3 + 1) ^ 2
  -- and the right-hand side as
  -- 3 * x ^ 3 * (x ^ 3 + m + n + 1)
  -- Subtracting 3 * x ^ 3 * (m + n) from both sides, it suffices to prove that
  -- (m + n) * (x ^ 6 - x ^ 3 + 1) ≥ 3 * x ^ 3 * (x ^ 3 + 1)
  suffices H : (m + n) * (x ^ 6 - x ^ 3 + 1) ≥ 3 * x ^ 3 * (x ^ 3 + 1) by
    simp only [m, n, show x ^ 6 = (x ^ 3) ^ 2 by ring, ← hx] at H
    linarith only [H]
  -- We have m ≥ 3 * x and n ≥ 3 * x ^ 2 by the AM-GM inequality
  have hm : m ≥ 3 * x := by
    have H := Real.geom_mean_le_arith_mean3_weighted (show 0 ≤ (1 / 3 : ℝ) by norm_num) (show 0 ≤ (1 / 3 : ℝ) by norm_num) (show 0 ≤ (1 / 3 : ℝ) by norm_num) (show 0 ≤ a from le_of_lt ha) (show 0 ≤ b from le_of_lt hb) (show 0 ≤ c from le_of_lt hc) (by norm_num)
    rw [← Real.mul_rpow (by positivity) (by positivity), ← Real.mul_rpow (by positivity) (by positivity), hx, ← Real.rpow_natCast_mul (by positivity)] at H
    simp at H
    simp only [m]
    linarith only [H]
  have hn : n ≥ 3 * x ^ 2 := by
    have H := Real.geom_mean_le_arith_mean3_weighted (show 0 ≤ (1 / 3 : ℝ) by norm_num) (show 0 ≤ (1 / 3 : ℝ) by norm_num) (show 0 ≤ (1 / 3 : ℝ) by norm_num) (show 0 ≤ a * b by positivity) (show 0 ≤ b * c by positivity) (show 0 ≤ c * a by positivity) (by norm_num)
    rw [← Real.mul_rpow (by positivity) (by positivity), ← Real.mul_rpow (by positivity) (by positivity)] at H
    rw [show a * b * (b * c) * (c * a) = (a * b * c) ^ 2 by ring, hx, show (x ^ 3) ^ 2 = (x ^ 2) ^ 3 by ring, ← Real.rpow_natCast_mul (by positivity)] at H
    simp at H
    simp only [n]
    linarith only [H]
  -- So m + n ≥ 3 * x * (x + 1)
  have hmn : m + n ≥ 3 * x * (x + 1) := by linarith only [hm, hn]
  calc
    -- It suffices to prove that
    -- 3 * x * (x + 1) * (x ^ 6 - x ^ 3 + 1) ≥ 3 * x ^ 3 * (x ^ 3 + 1)
    _ ≥ 3 * x * (x + 1) * (x ^ 6 - x ^ 3 + 1) := mul_le_mul_of_nonneg_right hmn (by linarith only [show x ^ 3 > 0 by positivity, show (x ^ 3 - 1) ^ 2 ≥ 0 from sq_nonneg _])
    -- Move the term to one side
    _ ≥ _ := sub_nonneg.1 ?_
  rw [← ge_iff_le]
  calc
    -- Factorize, and we find that each factor is nonnegative
    _ = 3 * x * (x + 1) * (x ^ 2 + 1) * (x ^ 2 - 1) ^ 2 := by ring
    _ ≥ 0 := by positivity
