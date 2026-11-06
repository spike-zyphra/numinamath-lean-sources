import Mathlib

theorem number_theory_235710 (m n : ℕ) (h₀ : m = n / 2) (h₁ : 4 * n + 2 * m = 115) :
    n ≤ 27 := by
  rw [h₀] at h₁
  omega