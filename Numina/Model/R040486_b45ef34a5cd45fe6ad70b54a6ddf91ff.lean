import Mathlib

theorem algebra_325034 {a : ℕ → ℝ} (ha : a 1 = 1)
    (h : ∀ t > 0, ∀ n ≥ 2, 3 * t * ∑ i in Finset.Icc 1 n, a i - (2 * t + 3) * ∑ i in Finset.Icc 1 (n - 1), a i = 3 * t) :
    ∃ r, ∀ n, a n = a 1 * r ^ (n - 1) ∧
    (∀ b : ℕ → ℝ, b 1 = 1 ∧ ∀ n ≥ 2, b n = r * (1 / b (n - 1)) →
      ∑ i in Finset.Icc 1 (2 * n), (-1) ^ (i + 1) * b i * b (i + 1) ≤ -20 / 9) := by

  have h1 := h 1 (by norm_num) 2 (by norm_num)
  have h2 := h 2 (by norm_num) 2 (by norm_num)
  norm_num [Finset.sum_Icc_succ_top, ha] at h1 h2
  all_goals
    linarith