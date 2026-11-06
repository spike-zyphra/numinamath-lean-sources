import Mathlib

theorem algebra_279432 {a : ℕ → ℝ} (ha : ∀ n, a (2 * n - 1) + a (2 * n) = 2 ^ n + 3 * n ∧ a (2 * n - 1) * a (2 * n) = 3 * n * 2 ^ n)
    (h : ∀ n, a (2 * n - 1) ≤ a (2 * n)) (f : ℕ → ℝ) (hf : ∀ n, f n = (|Real.sin n| / Real.sin n + 3) / 2)
    (T : ℕ → ℝ) (hT : ∀ n, T n = ∑ i ∈ Finset.Icc 2 (n + 1), (-1) ^ f i / (a (2 * i - 1) * a (2 * i))) :
    ∀ n, 1 / 6 ≤ T n ∧ T n ≤ 5 / 24 := by
  intro n
  have h1 := ha 0
  norm_num at h1
  all_goals linarith