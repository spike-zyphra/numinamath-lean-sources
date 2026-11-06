import Mathlib

theorem number_theory_45148 : Set.Infinite {k : ℕ | ∃ n, 3^n ≡ k [MOD n]} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => 3 ^ n)
  · -- Show f is injective
    intro n m h
    have h_eq : 3 ^ n = 3 ^ m := by
      simpa using h
    have : n = m := by
      exact Nat.pow_right_injective (by norm_num) h_eq
    assumption
  · -- Show that all f(n) are in the set
    intro n
    use 3 ^ n
    have h1 : (3 ^ (3 ^ n) : ℕ) % (3 ^ n) = (3 ^ n : ℕ) % (3 ^ n) := by
      have h_eq1 : (3 ^ (3 ^ n) : ℕ) % (3 ^ n) = 0 := by
        have h1 : (3 ^ n : ℕ) ∣ (3 ^ (3 ^ n) : ℕ) := by
          have h3 : n ≤ 3 ^ n := by
            have h4 : ∀ (m : ℕ), m ≤ 3 ^ m := by
              intro m
              induction m with 
              | zero => 
                norm_num
              | succ m ih => 
                have h12 : m ≤ 3 ^ m := ih
                have h13 : (3 : ℕ) ^ (m + 1) = 3 ^ m * 3 := by
                  ring_nf
                nlinarith [show (3 ^ m : ℕ) ≥ 1 by 
                  have : (3 : ℕ) ^ m ≥ 1 := by
                    apply Nat.one_le_pow
                    all_goals omega
                  linarith
                ]
            exact h4 n
          apply pow_dvd_pow _ (by linarith)
        exact Nat.mod_eq_zero_of_dvd h1
      have h_eq2 : (3 ^ n : ℕ) % (3 ^ n) = 0 := by
        have h1 : (3 ^ n : ℕ) ∣ (3 ^ n : ℕ) := by 
          exact dvd_refl (3 ^ n)
        exact Nat.mod_eq_zero_of_dvd h1
      linarith
    simp [Nat.ModEq] at *
    all_goals 
      omega