import Mathlib


theorem number_theory_8370 (x : ℕ → ℕ) (y : ℕ → ℕ)
    (h₀ : x 1 = 2001)
    (h₁ : ∀ n, x (n + 1) = x n + y n)
    (h₂ : ∀ n, y n = x n % 10) :
    x 2024 = 12108 := by
  set_option maxRecDepth 10000 in
  norm_num [h₀, h₁, h₂]