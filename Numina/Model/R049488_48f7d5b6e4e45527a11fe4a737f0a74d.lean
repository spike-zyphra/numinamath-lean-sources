import Mathlib

theorem number_theory_169430 (p : ℕ) (hp : p.Prime ∧ (p + 2).Prime ∧ (p + 4).Prime) :
    p = 3 := by 
  rcases hp with ⟨h1, h2, h3⟩
  by_cases h : p ≤ 3
  · -- check all cases where p is less than 4
    interval_cases p <;> norm_num at h1 h2 h3 <;> trivial
  · -- case where p > 3 so we can apply divisibility
    push_neg at h
    have h4 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by 
      omega
    rcases h4 with (h4 | h4 | h4)
    · 
      have h5 : 3 ∣ p := by 
        omega
      have h6 : ¬ p.Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by exact h5) (by omega) (by omega)
      contradiction
    · 
      have h5 : (p + 2) % 3 = 0 := by
        simp [Nat.add_mod, h4]
      have h6 : 3 ∣ (p + 2) := by 
        omega
      have h7 : ¬ (p + 2).Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 2) by exact h6) (by omega) (by omega)
      contradiction
    · 
      have h5 : (p + 4) % 3 = 0 := by
        simp [Nat.add_mod, h4]
      have h6 : 3 ∣ (p + 4) := by 
        omega
      have h7 : ¬ (p + 4).Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 4) by exact h6) (by omega) (by omega)
      contradiction