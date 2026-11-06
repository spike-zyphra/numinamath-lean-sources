import Mathlib

theorem number_theory_261685 (n : ℕ) :
    9 ∣ 2^(2*n) + 15 * n - 1 := by

  have h1 : ∀ (n : ℕ), 9 ∣ 2 ^ (2 * n) + 15 * n - 1 := by 
    intro n 
    induction n with 
    | zero =>
      norm_num
    | succ k ih =>
      have eq1 : (2 ^ (2 * (k + 1)) + 15 * (k + 1) - 1 : ℕ) = 4 * (2 ^ (2 * k)) + 15 * k + 14 := by 
        cases k with
        | zero =>
          all_goals 
            norm_num
        | succ m =>
          simp [pow_succ, pow_mul, Nat.mul_add, Nat.add_mul]
          <;> ring_nf
          <;> omega 
      rw [eq1] 
      have h3 : 9 ∣ 4 * (2 ^ (2 * k)) + 15 * k + 14 := by 
        have h4 : 9 ∣ (2 ^ (2 * k) + 15 * k - 1) := ih 
        -- Show that $P(k+1) = P(k) + \text{multiple of }9$
        have h5 : (4 * (2 ^ (2 * k)) + 15 * k + 14 : ℕ) =
          (2 ^ (2 * k) + 15 * k - 1) + (3 * (2 ^ (2 * k)) + 15) := by 
            cases k with
            | zero =>
              omega 
            | succ m =>
              simp [pow_succ, pow_mul, Nat.add_sub_assoc, Nat.mul_add, Nat.add_mul, Nat.sub_sub]
              <;> ring_nf
              <;> omega
        rw [h5] 
        have h6 : ∀ k : ℕ, (3 * (2 ^ (2 * k)) + 15 : ℕ) % 9 = 0 := by 
          intro k' 
          induction k' with 
          | zero => 
            norm_num 
          | succ k' ih2 =>
            simp [pow_succ, pow_mul, Nat.add_mod, Nat.mul_mod] at ih2 ⊢
            <;> omega
        have h7 : (3 * (2 ^ (2 * k)) + 15 : ℕ) % 9 = 0 := h6 k 
        omega 
      exact h3 
  specialize h1 n 
  simpa using h1