import Mathlib

theorem algebra_12412 {a b : ℕ → ℝ} {S T : ℕ → ℝ}
    (ha : ∃ d, ∀ n, a n = a 0 + d * n) (hb : ∃ d, ∀ n, b n = b 0 + d * n)
    (hS : ∀ n, S n = ∑ i in Finset.range n, a i) (hT : ∀ n, T n = ∑ i in Finset.range n, b i)
    (hST : ∀ n, S n / T n = (2 * n + 1) / (4 * n - 2)) :
    a 10 / (b 3 + b 18) + a 11 / (b 6 + b 15) = 41 / 78 := by
  have h0 := hST 0
  simp [hS, hT] at h0
  all_goals linarith