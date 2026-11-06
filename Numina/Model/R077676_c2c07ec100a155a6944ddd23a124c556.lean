import Mathlib

theorem algebra_254396 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (x : ℕ → ℕ) (hx0 : x 0 = 0) (hx1 : x 1 = 1)
    (hxn : ∀ n, x (n + 2) = a * x (n + 1) + b * x n) :
    ∀ m n, 0 < m → 0 < n → ∃ k, ∏ i ∈ Finset.range n, x (m + i + 1) / x (i + 1) = k := by
  intro m n hm hn
  refine' ⟨∏ i ∈ Finset.range n, x (m + i + 1) / x (i + 1), by simp⟩