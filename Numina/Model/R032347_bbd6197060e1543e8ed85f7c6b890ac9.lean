import Mathlib

theorem number_theory_287714 (n : ℕ) (h₀ : n < 200) (h₁ : (3 * n) / 100 = n / 100 + 36) :
    n = 188 := by
  have h2 : n / 100 = 0 ∨ n / 100 = 1 := by
    omega
  rcases h2 with (h2 | h2)
  · -- Suppose n / 100 = 0, then n < 100
    rw [h2] at h₁
    omega
  · -- Suppose n / 100 = 1, then 100 ≤ n < 200
    rw [h2] at h₁
    omega