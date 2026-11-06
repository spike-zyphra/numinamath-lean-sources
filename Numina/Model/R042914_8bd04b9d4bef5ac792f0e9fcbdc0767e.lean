import Mathlib

theorem number_theory_608102 (n : ℕ) (hn : 1 < n) :
    ∃ m : ℕ, n ^ m > n ^ n ∧ ∃ k : ℕ, (n ^ m - m ^ n) / (n + m) = k := by
  use n ^ (n + 1)
  constructor
  · -- Show that n ^ (n ^ (n + 1)) > n ^ n
    have h1 : n ^ (n + 1) > n := by
      have h3 : n > 1 := hn
      have h4 : n + 1 > 1 := by
        nlinarith
      have h5 : n ^ (n + 1) > n ^ 1 := by
        apply Nat.pow_lt_pow_right
        all_goals linarith
      rw [show n ^ 1 = n by ring] at h5
      linarith
    have h2 : n ^ (n ^ (n + 1)) > n ^ n := by
      have h1' : n ^ (n + 1) > n := h1
      have h3 : n > 1 := hn
      have h4 : n ^ (n ^ (n + 1)) > n ^ n := by
        apply Nat.pow_lt_pow_right
        all_goals
          try linarith
      linarith
    exact h2
  · -- Show quotient exists
    refine' ⟨(n ^ (n ^ (n + 1)) - (n ^ (n + 1)) ^ n) / (n + n ^ (n + 1)), by omega⟩