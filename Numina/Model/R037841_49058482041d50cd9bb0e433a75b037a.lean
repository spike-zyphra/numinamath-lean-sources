import Mathlib

theorem number_theory_154760 (m n : ℤ) (h₀ : n ∣ m * (n + 1)) : n ∣ m := by
  rcases h₀ with ⟨t, ht⟩
  use t - m
  linarith