import Mathlib

theorem number_theory_5938
    {a : ℕ} (ha : ∃ m, 1 < m ∧ m < a ∧ m ∣ a) :
    ∃ p, Nat.Prime p ∧ p ∣ a := by
  rcases ha with ⟨m, hm1, hm2, hm3⟩
  have h3 : ∃ p, Nat.Prime p ∧ p ∣ m := by 
    by_cases hm : Nat.Prime m 
    · refine ⟨m, hm, by tauto⟩
    · 
      have h4 : m > 1 := by linarith
      have h5 : ∃ p, Nat.Prime p ∧ p ∣ m := by
        apply Nat.exists_prime_and_dvd
        omega
      exact h5
  rcases h3 with ⟨p, hp, hpdiv⟩
  have h4 : p ∣ a := by 
    exact Nat.dvd_trans hpdiv hm3
  exact ⟨p, hp, h4⟩