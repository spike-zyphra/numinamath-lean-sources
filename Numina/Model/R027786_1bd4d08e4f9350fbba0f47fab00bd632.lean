import Mathlib

theorem number_theory_57738 (n : ℕ) : 3 ∣ 2^(2*n) - 1 := by
  have h1 : ∀ (n : ℕ), 3 ∣ 2 ^ (2 * n) - 1 := by 
    intro n 
    induction n with 
    | zero =>
      simp
    | succ n ih =>
      have h2 : 2 ^ (2 * (n + 1)) - 1 = 4 * (2 ^ (2 * n)) - 1 := by
        ring_nf
      rw [h2]
      omega
  specialize h1 n
  simpa using h1