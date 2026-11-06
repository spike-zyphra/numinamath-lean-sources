import Mathlib

theorem number_theory_6638 {p : ℕ} (hp : p.Prime ∧ (Nat.digits 10 p).length = 2010) :
    IsLeast {k | 0 < k ∧ 12 ∣ (p ^ 2 - k)} 1 := by
  rcases hp with ⟨h_prime, hp_length⟩
  constructor
  · -- Show that 1 is in the set
    constructor
    · -- Show 1 > 0
      norm_num
    · -- Show 12 divides p ^ 2 - 1
      have h1 : p ≥ 10 := by
        by_contra h
        push_neg at h
        have : p < 10 := by omega
        interval_cases p <;> norm_num at hp_length h_prime
      have h2 : p % 4 = 1 ∨ p % 4 = 3 := by
        by_contra h
        push_neg at h
        have h4 : p % 4 = 0 ∨ p % 4 = 2 := by omega
        have h4' : p % 2 = 0 := by
          omega
        have : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
          all_goals
            omega
        contradiction
      have h3 : p % 3 = 1 ∨ p % 3 = 2 := by
        by_contra h
        push_neg at h
        have h3 : p % 3 = 0 := by omega
        have : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
          all_goals
            omega
        contradiction
      have h4 : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by 
        omega
      have h5 : p ^ 2 % 12 = 1 := by 
        rcases h4 with (h | h | h | h) <;> 
          simp [Nat.pow_mod, h, Nat.mul_mod] 
      have : 12 ∣ p ^ 2 - 1 := by
        omega
      exact this
  · -- Show that 1 is minimal
    intro k ⟨hk, hkdiv⟩ 
    by_contra h 
    push_neg at h 
    have h0 : k = 0 := by
      omega 
    omega