import Mathlib

def is_composite (n : ℕ) := n ≠ 1 ∧ ¬n.Prime

theorem number_theory_195051 :
    IsGreatest {n | ¬∃ c1 c2, c1 ≠ 0 ∧ c2 ≠ 0 ∧ is_composite c1 ∧ is_composite c2 ∧ c1 + c2 = n} 11 := by
  constructor
  · -- Show 11 is in the set
    show ¬∃ c1 c2, c1 ≠ 0 ∧ c2 ≠ 0 ∧ is_composite c1 ∧ is_composite c2 ∧ c1 + c2 = 11
    intro h
    rcases h with ⟨c1, c2, hc1, hc2, hc1', hc2', hsum⟩
    rcases hc1' with ⟨hc11, hc1p⟩
    rcases hc2' with ⟨hc21, hc2p⟩
    have h1 : c1 ≤ 11 := by omega
    have h2 : c2 ≤ 11 := by omega
    interval_cases c1 <;> interval_cases c2 <;> norm_num [is_composite, Nat.Prime] at hc11 hc1p hc21 hc2p hsum ⊢
    <;> tauto
  · -- Show 11 is greatest in the set
    intro n hn
    have h : ¬∃ c1 c2, c1 ≠ 0 ∧ c2 ≠ 0 ∧ is_composite c1 ∧ is_composite c2 ∧ c1 + c2 = n := hn
    by_contra h1
    push_neg at h1
    have h2 : n > 11 := by linarith
    by_cases h3 : n % 2 = 0
    · -- Assume n is even
      have h4 : ∃ c1 c2, c1 ≠ 0 ∧ c2 ≠ 0 ∧ is_composite c1 ∧ is_composite c2 ∧ c1 + c2 = n := by
        use 4, n - 4
        constructor
        · norm_num
        constructor
        · omega
        constructor
        · constructor
          · norm_num
          · norm_num
        constructor
        · constructor
          · omega
          · have : ¬(n - 4).Prime := by
              by_contra h_prime
              have h5 : (n - 4) % 2 = 0 := by
                omega
              have h6 : (n - 4) > 2 := by
                omega
              have h7 : ¬(n - 4).Prime := by
                apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (n - 4) by omega)
                all_goals omega
              contradiction
            tauto
        · omega
      exfalso
      exact h (h4)
    · -- Assume n is odd
      have h4 : ∃ c1 c2, c1 ≠ 0 ∧ c2 ≠ 0 ∧ is_composite c1 ∧ is_composite c2 ∧ c1 + c2 = n := by
        use 9, n - 9
        constructor
        · norm_num
        constructor
        · omega
        constructor
        · constructor
          · norm_num
          · norm_num
        constructor
        · constructor
          · omega
          · have : ¬(n - 9).Prime := by
              by_contra h_prime
              have h5 : (n - 9) % 2 = 0 := by
                omega
              have h6 : (n - 9) > 2 := by
                omega
              have h7 : ¬(n - 9).Prime := by
                apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (n - 9) by omega)
                all_goals omega
              contradiction
            tauto
        · omega
      exfalso
      exact h (h4)