import Mathlib

theorem number_theory_277239 :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p^2 + 2)} = {3} := by 
  ext p 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume p is prime and p^2+2 is prime, prove p = 3
    intro hp
    rcases hp with ⟨h_prime, h_prime2⟩
    by_cases h : p > 3
    · -- Assume p > 3
      have h1 : p % 3 = 1 ∨ p % 3 = 2 := by 
        have h2 : p % 3 = 1 ∨ p % 3 = 2 := by 
          by_contra h 
          push_neg at h 
          have h3 : p % 3 = 0 := by 
            omega 
          have h4 : p > 1 := by 
            linarith 
          have h5 : ¬Nat.Prime p := by 
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) 
            all_goals omega 
          contradiction
        assumption 
      rcases h1 with (h1 | h1)
      · -- p % 3 = 1 
        have h3 : (p ^ 2 + 2) % 3 = 0 := by 
          have h4 : p % 3 = 1 := h1 
          have h5 : p ^ 2 % 3 = 1 := by 
            simp [Nat.pow_mod, h4]
          omega 
        have h4 : ¬Nat.Prime (p^2 + 2) := by 
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p^2 + 2 by omega) 
          all_goals nlinarith 
        contradiction 
      · -- p % 3 = 2 
        have h3 : (p ^ 2 + 2) % 3 = 0 := by 
          have h4 : p % 3 = 2 := h1 
          have h5 : p ^ 2 % 3 = 1 := by 
            simp [Nat.pow_mod, h4]
          omega 
        have h4 : ¬Nat.Prime (p^2 + 2) := by 
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p^2 + 2 by omega) 
          all_goals nlinarith 
        contradiction 
    · -- p ≤ 3 
      have hp2 : p ≤ 3 := by 
        omega 
      interval_cases p <;> norm_num at h_prime h_prime2 ⊢ 
      <;> try tauto 
  · -- Assume p = 3, prove both primes
    intro h 
    rw [h] 
    constructor 
    · norm_num 
    · norm_num