import Mathlib

theorem number_theory_52309 (a : ℕ → ℕ) (ha1 : a 1 = 2)
    (han : ∀ n, a (n + 1) = a n ^ 3 - a n + 1) :
    ∀ n p, 0 < n → Odd p → Nat.Prime p → p ∣ a n → p > n := by
  have h1 := han 0
  have h2 : a 1 = a 0 ^ 3 - a 0 + 1 := by
    simpa using h1
  have h3 : a 1 = 2 := ha1
  rw [h3] at h2
  have h4 : a 0 ^ 3 - a 0 + 1 = 2 := by 
    omega
  have h5 : a 0 ^ 3 - a 0 = 1 := by 
    omega
  have h6 : a 0 < 2 := by
    by_contra h
    push_neg at h
    have h10 : a 0 ≥ 2 := by linarith
    have h13 : a 0 ^ 3 - a 0 ≥ 6 := by
      have h17 : a 0 ≥ 2 := h10
      have h18 : a 0 ^ 3 ≥ a 0 + 6 := by
        have h19 : a 0 ≥ 2 := h17
        nlinarith [sq_nonneg (a 0 - 1 : ℤ), sq_nonneg (a 0 : ℤ)]
      omega
    omega
  have h7 : a 0 = 0 ∨ a 0 = 1 := by
    omega
  rcases h7 with (h8 | h8)
  all_goals
  rw [h8] at h5
  all_goals omega