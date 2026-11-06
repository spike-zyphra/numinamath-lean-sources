import Mathlib

theorem no_solution : ¬∃ n : ℕ, 0 < n ∧ Nat.totient n = 2002 ^ 2 - 1 := by
  rintro ⟨n, hn, h⟩
  have h1 : n ≥ 1 := by
    omega
  have heq : Nat.totient n = 4008003 := by
    omega
  by_cases h3 : n ≤ 2
  · -- Case n ≤ 2
    interval_cases n <;> simp [Nat.totient_one, Nat.totient_two] at heq 
    all_goals omega
  · -- Case n > 2
    have h4 : n > 2 := by 
      omega
    have h5 : Nat.totient n % 2 = 0 := by
      have h6 : n > 2 := h4
      have h7 : n ≥ 3 := by omega
      have h8 : n ≠ 1 := by omega
      have h9 : n ≠ 2 := by omega
      have h8 : n ≠ 1 := by omega
      have h9 : n ≠ 2 := by omega
      have h10 : Even (Nat.totient n) := by
        have h11 : n ≥ 3 := by omega
        have h12 : n ≠ 1 := by omega
        have h13 : n ≠ 2 := by omega
        apply Nat.totient_even 
        all_goals 
          omega
      exact Nat.even_iff.mp h10
    have h6 : (4008003 : ℕ) % 2 = 1 := by 
      omega
    rw [show Nat.totient n = 4008003 by linarith [heq]] at h5
    omega