import Mathlib

theorem number_theory_188181 (a : ℕ → ℕ)
    (h₀ : a 1 = 1)
    (h₁ : ∀ n > 1, a n = ⌊(n ^ 3 / a (n - 1 : ℕ))⌋₊) :
    a 999 = 999 := by
  set_option maxRecDepth 10000 in
  norm_num [h₀, h₁]