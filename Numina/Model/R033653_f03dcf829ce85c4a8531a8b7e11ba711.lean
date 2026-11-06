import Mathlib

theorem algebra_179734 (n : ℕ) : ∃ k, (n^3 - 2 * n^2 - 4 * n + 8) / (n + 2) = k := by
  use (n ^ 3 - 2 * n ^ 2 - 4 * n + 8) / (n + 2)
  all_goals
  try { 
    all_goals
    have h1 : (n ^ 3 - 2 * n ^ 2 - 4 * n + 8 : ℕ) = (n + 2) * (n ^ 2 - 4 * n + 4) := by
      cases n with
      | zero => 
        omega
      | succ n => 
        simp [pow_two, pow_three, Nat.pow_succ, Nat.mul_add, Nat.add_mul, mul_add, add_mul]
        all_goals 
          ring_nf at *
          all_goals
            try { 
              cases n with
              | zero => 
                omega
              | succ n => 
                simp [pow_two, pow_succ, Nat.mul_add, Nat.add_mul, mul_add, add_mul]
                all_goals 
                  ring_nf at *
                  all_goals
                  omega
            }
            all_goals 
              try { 
                omega
              }
    have h5 : (n ^ 3 - 2 * n ^ 2 - 4 * n + 8 : ℕ) = (n + 2) * (n ^ 2 - 4 * n + 4) := h1
    have h2 : (n ^ 3 - 2 * n ^ 2 - 4 * n + 8) / (n + 2) = (n ^ 2 - 4 * n + 4) := by
      rw [h5]
      field_simp
      all_goals 
        nlinarith 
    omega
  }
  all_goals 
    omega