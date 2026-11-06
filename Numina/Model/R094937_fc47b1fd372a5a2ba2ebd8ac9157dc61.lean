import Mathlib

theorem algebra_241095 (n : ℕ) (h₀ : n > 0) (h₁ : (n ^ 2 + (n + 1) ^ 2 + (n + 2) ^ 2 + (n + 3) ^ 2) = (n + 4) ^ 2 + (n + 5) ^ 2 + (n + 6) ^ 2) :
    n ^ 2 = 441 := by
  ring_nf at h₁ 
  have h3 : n ≤ 21 := by
    nlinarith
  interval_cases n <;> omega