import Mathlib

theorem algebra_301632 {a : ℕ → ℝ} (ha1 : a 1 = 1)
    (hsum : ∀ t > 0, ∀ n ≥ 2, 3 * t * ∑ i in Finset.Icc 1 n, a i - (2 * t + 3) * ∑ i in Finset.Icc 1 (n - 1), a i = 3 * t) :
    (∃ r, ∀ n, a n = a 1 * r ^ (n - 1)) ∧
    (∃ b : ℕ → ℝ, b 1 = 1 ∧ ∀ n ≥ 2, b n = r * (1 / b (n - 1)) ∧
      ∑ i in Finset.Icc 1 (2 * n), (-1 : ℝ) ^ (i - 1) * b i * b (i + 1) = -8 / 9 * n ^ 2 - 4 / 3 * n) := by
  have eq1 := hsum 1 (by norm_num) 2 (by norm_num)
  have eq2 := hsum 2 (by norm_num) 2 (by norm_num)
  norm_num [Finset.sum_Icc_succ_top, ha1] at eq1 eq2
  all_goals linarith