import Mathlib

theorem number_theory_314386 (n : ℕ) (hn : n ≥ 17) :
    ∃ k, k * 7 + (n - k) * 11 = 77 * n := by 
  have h1 : n ≥ 17 := hn
  use 55 * n / 2 - 66 * n / 4
  omega