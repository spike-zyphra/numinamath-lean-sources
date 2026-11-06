import Mathlib

theorem number_theory_611089 (a : ℕ → ℤ) (h1 : a 1 = 1) (hn : ∀ n : ℕ, n > 1 → a n = ⌊(n ^ 3) / (↑(a (n - 1)) : ℝ)⌋) : a 999 = 999 := by
  set_option maxRecDepth 10000 in
  norm_num [h1, hn]