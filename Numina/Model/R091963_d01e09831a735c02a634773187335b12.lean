import Mathlib

theorem number_theory_182453 (n : ℕ) (h₀ : n > 0) (h₁ : (10 * n + 1) % 1000000 = 3 * n) :
    n = 142857 ∨ n = 428571 := by
  have h2 : n < 1000000 := by
    by_contra h
    push_neg at h
    have h3 : n ≥ 1000000 := by omega
    have h4 : (10 * n + 1) % 1000000 = 3 * n % 1000000 := by
      omega
    omega
  have h6 : n % 1000000 = 142857 := by
    omega
  have h7 : n = 142857 := by
    omega
  left
  exact h7