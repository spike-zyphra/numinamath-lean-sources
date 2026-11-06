import Mathlib

theorem number_theory_4531_v0001 (n : ℕ) (hn : n > 1) :
    ¬ Nat.Prime (n ^ 5 + n ^ 4 + 1) := by
  have h1 : n ^ 5 + n ^ 4 + 1 = (n ^ 2 + n + 1) * (n ^ 3 - n + 1) := by
    have h3 : n ≥ 2 := by omega
    have h12 : (n ^ 2 + n + 1) * (n ^ 3 - n + 1) = n ^ 5 + n ^ 4 + 1 := by
      have h10 : n ^ 3 ≥ n := by
        nlinarith [sq_nonneg (n : ℕ), sq_nonneg ((n : ℕ) - 1 : ℕ), sq_nonneg ((n + 1 : ℕ) : ℕ), sq_pos_of_pos (show 0 < (n : ℕ) by linarith)]
      have h11 : (n ^ 3 - n : ℕ) = n ^ 3 - n := rfl
      cases n with
      | zero => linarith
      | succ n =>
        cases n with
        | zero => linarith
        | succ n =>
          simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, mul_add, mul_assoc, Nat.add_sub_assoc, Nat.mul_sub_left_distrib]
          all_goals
            ring_nf <;> omega
    linarith
  rw [h1]
  have h9 : n ^ 2 + n + 1 > 1 := by
    nlinarith [sq_pos_of_pos (show 0 < (n : ℕ) by linarith)]
  have h10 : (n ^ 3 - n + 1) > 1 := by
    have h9 : n ≥ 2 := by omega
    have h11 : n ^ 3 - n + 1 > 1 := by
      have h10 : n ^ 3 ≥ n + 1 := by
        nlinarith [sq_nonneg (n : ℕ), sq_nonneg ((n : ℕ) - 1 : ℕ), sq_nonneg ((n + 1 : ℕ) : ℕ), sq_pos_of_pos (show 0 < (n : ℕ) by linarith)]
      have h13 : (n ^ 3 - n : ℕ) ≥ 1 := by
        omega
      omega
    linarith
  apply Nat.not_prime_mul (by linarith) (by linarith)