import Mathlib

theorem algebra_322049 {a b : ℕ → ℝ} (ha1 : a 1 = 4)
    (han : ∀ n, a (n + 1) * a n + 6 * a (n + 1) - 4 * a n - 8 = 0)
    (hb : ∀ n, b n = 6 / (a n - 2)) :
    (∀ n, b n = 2 ^ (n + 1) / 3 + 4 * n - 8 / 3) ∧
    (∑ i in Finset.Icc 1 n, a i * b i = 2 ^ (n + 1) / 3 + 4 * n - 8 / 3) := by
  have eq1 := han 0
  simp [ha1, hb] at eq1 ⊢
  all_goals linarith