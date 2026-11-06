import Mathlib


theorem number_theory_607425 :
    Set.Infinite {(m, n) : ℕ × ℕ | m > 0 ∧ n > 0 ∧ m ≠ n ∧ ∃ k, (Nat.factorial m) * (Nat.factorial n) = k ^ 2} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => ( (n + 2)^2 - 1, (n + 2)^2 ) )
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    omega
  · -- Show that all pairs are in the set
    intro n
    simp [Prod.ext_iff]
    all_goals 
      have h_exists_k : ∃ k, Nat.factorial ((n + 2 : ℕ) ^ 2 - 1) * Nat.factorial ((n + 2 : ℕ) ^ 2) = k ^ 2 := by 
        use ( (n + 2 : ℕ) * (Nat.factorial ((n + 2 : ℕ) ^ 2 - 1 : ℕ)) )
        have h2 : Nat.factorial ((n + 2 : ℕ) ^ 2) = ((n + 2 : ℕ) ^ 2) * (Nat.factorial ((n + 2 : ℕ) ^ 2 - 1)) := by
          have h12 : ((n + 2 : ℕ) ^ 2 : ℕ) = ((n + 2 : ℕ) ^ 2 - 1 : ℕ) + 1 := by
            cases n with
            | zero =>
              all_goals simp
            | succ n =>
              all_goals 
                have h22 : ((n + 1 + 2 : ℕ) ^ 2) = ((n + 1 + 2 : ℕ) ^ 2 - 1) + 1 := by
                  simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul]
                  <;> ring_nf <;> omega
                exact h22
          rw [h12] 
          rw [Nat.factorial_succ]
          all_goals 
            simp [Nat.add_sub_cancel_left] 
            <;> ring_nf <;> omega
        rw [h2]
        ring_nf
        <;> omega
        all_goals tauto
      have hm1 : ((n + 2 : ℕ) ^ 2 - 1 : ℕ) > 0 := by
        have h11 : (n + 2 : ℕ) ^ 2 ≥ 4 := by
          have h22 : n + 2 ≥ 2 := by omega
          have h33 : (n + 2 : ℕ) ^ 2 ≥ 4 := by nlinarith 
          linarith
        omega
      have hn1 : ((n + 2 : ℕ) ^ 2 : ℕ) > 0 := by
        have h1 : (n + 2 : ℕ) ^ 2 ≥ 4 := by
          have h2 : n + 2 ≥ 2 := by omega
          nlinarith
        linarith 
      have h1 : ((n + 2 : ℕ) ^ 2 - 1 : ℕ) ≠ ((n + 2 : ℕ) ^ 2 : ℕ) := by 
        omega
      tauto