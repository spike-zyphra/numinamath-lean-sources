import Mathlib

def is_prime (n : ℕ) : Prop := n.Prime

theorem number_theory_3674 :
  IsGreatest {q | ∃ p : ℕ, is_prime p ∧ is_prime (q : ℕ) ∧ q = 4^p + p^4 + 4} 149 := by
  constructor
  · -- Show 149 is in the set
    use 3
    all_goals
      norm_num [is_prime]
  · -- Show there is no larger element in the set
    intro q h
    rcases h with ⟨p, hp, hq, hq_eq⟩
    by_contra h'
    push_neg at h'
    have h1 : p ≥ 4 := by
      by_contra h
      push_neg at h
      interval_cases p <;> norm_num [is_prime, hq_eq] at hp hq
      <;> omega
    have h3 : p % 3 = 1 ∨ p % 3 = 2 := by
      by_contra h
      push_neg at h
      have h4 : p % 3 = 0 := by
        omega
      have h6 : p > 3 := by
        by_contra h7
        push_neg at h7
        interval_cases p <;> norm_num at hp h4
      have h5 : ¬is_prime p := by
        rw [is_prime]
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals
          omega
      contradiction
    rcases h3 with (h3 | h3)
    · -- p % 3 = 1
      have h4 : p ^ 4 % 3 = 1 := by
        have hp1 : p % 3 = 1 := h3
        have h1 : p ^ 4 % 3 = 1 := by
          simp [Nat.pow_mod, hp1]
        exact h1
      have h5 : (4 ^ p) % 3 = 1 := by
        have h1 : ∀ (k : ℕ), (4 ^ (k + 1) : ℕ) % 3 = 1 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [pow_add, pow_one, Nat.mul_mod, Nat.add_mod] at ih ⊢
            all_goals omega
        specialize h1 (p - 1)
        have h2 : p - 1 + 1 = p := by omega
        rw [h2] at h1
        omega
      have h7 : q % 3 = 0 := by
        omega
      have h8 : q > 3 := by
        by_contra h
        push_neg at h
        have h9 : q ≤ 3 := by linarith
        omega
      have h9 : ¬is_prime (q : ℕ) := by
        rw [is_prime]
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (q : ℕ) by omega)
        all_goals
          omega
      contradiction
    · -- p % 3 = 2
      have h4 : p ^ 4 % 3 = 1 := by
        have hp1 : p % 3 = 2 := h3
        have h1 : p ^ 4 % 3 = 1 := by
          simp [Nat.pow_mod, hp1]
        exact h1
      have h5 : (4 ^ p) % 3 = 1 := by
        have h1 : ∀ (k : ℕ), (4 ^ (k + 1) : ℕ) % 3 = 1 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [pow_add, pow_one, Nat.mul_mod, Nat.add_mod] at ih ⊢
            all_goals omega
        specialize h1 (p - 1)
        have h2 : p - 1 + 1 = p := by omega
        rw [h2] at h1
        omega
      have h7 : q % 3 = 0 := by
        omega
      have h8 : q > 3 := by
        by_contra h
        push_neg at h
        have h9 : q ≤ 3 := by linarith
        omega
      have h9 : ¬is_prime (q : ℕ) := by
        rw [is_prime]
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (q : ℕ) by omega)
        all_goals
          omega
      contradiction