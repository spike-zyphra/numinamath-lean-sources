import Mathlib

theorem number_theory_8873 (n : ℕ) :
    0 < n ∧ Nat.Prime (n ^ 5 + n + 1) ↔ n = 1 := by
  constructor
  · -- Forward: if 0 < n and n^5 + n + 1 is prime, then n = 1
    intro h
    rcases h with ⟨hn_pos, h_prime⟩
    by_cases h1 : n > 1
    · -- n > 1
      have h2 : n ^ 5 + n + 1 = (n ^ 2 + n + 1) * (n ^ 3 - n ^ 2 + 1) := by
        cases n with
        | zero =>
          all_goals linarith
        | succ n =>
          simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
          <;> ring_nf <;> omega
      have h3 : n ^ 2 + n + 1 > 1 := by
        nlinarith [h1]
      have h4 : n ^ 3 - n ^ 2 + 1 > 1 := by
        have h6 : n ≥ 2 := by linarith 
        have h7 : n ^ 3 - n^2 ≥ 2 := by
          have h8 : n ≥ 2 := h6
          have h9 : n ^ 2 ≥ 4 := by nlinarith
          have h10 : n - 1 ≥ 1 := by omega 
          have h11 : n ^ 2 * (n - 1) ≥ 4 := by
            nlinarith 
          have h12 : n ^ 3 - n ^ 2 = n ^ 2 * (n - 1) := by
            cases n with
            | zero => omega
            | succ n => 
              simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
              <;> ring_nf <;> omega 
          have h13 : n ^ 2 * (n - 1) ≥ 4 := by 
            nlinarith 
          omega 
        omega 
      rw [h2] at h_prime
      have h6 : ¬ Nat.Prime ((n ^ 2 + n + 1) * (n ^ 3 - n ^ 2 + 1)) := by
        apply Nat.not_prime_mul (by nlinarith)
        all_goals nlinarith
      contradiction
    · -- n ≤ 1
      have h1' : n = 1 := by
        linarith
      exact h1'
  · -- Backward: n = 1 implies 0 < n ∧ Nat.Prime (n ^ 5 + n + 1)
    intro h_eq
    rw [h_eq]
    constructor
    · norm_num
    · norm_num