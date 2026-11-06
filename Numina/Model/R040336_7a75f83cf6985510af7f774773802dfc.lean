import Mathlib

theorem number_theory_13883 (n m : ℕ) (h₀ : n ∈ Set.Icc 100 999) (h₁ : m ∈ Set.Icc 100 999)
    (h₂ : (100 * n + m) = 3 * (n * m)) : 100 * n + m = 167334 := by
  rcases h₀ with ⟨hn0, hn1⟩
  rcases h₁ with ⟨hm0, hm1⟩
  nlinarith