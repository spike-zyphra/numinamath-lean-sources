import Mathlib

theorem number_theory_16009 {p : ℕ} (hp₁ : Nat.Prime p) (hp₂ : (Nat.digits 10 p).length = 2010) :
    IsLeast {k : ℕ | 0 < k ∧ 12 ∣ p^2 - k } 1 := by
  have h1 : p ≥ 4 := by
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num at hp₁ hp₂
  
  constructor
  · -- Show 1 is in the set.
    constructor
    · -- Show 1 > 0.
      norm_num
    · -- Show 12 divides p ^ 2 - 1.
      have h12 : p % 3 = 1 ∨ p % 3 = 2 := by 
        by_contra h
        push_neg at h
        have h2 : p % 3 = 0 := by omega
        have h3 : 3 ∣ p := by omega
        have h4 : p ≤ 3 := by
          by_contra h'
          push_neg at h'
          have h5 : ¬Nat.Prime p := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
          tauto
        interval_cases p <;> norm_num at hp₁ hp₂ h3
      have h2 : p % 2 = 1 := by 
        by_contra h
        push_neg at h
        have h2 : p % 2 = 0 := by omega
        have h3 : 2 ∣ p := by omega
        have h4 : p ≤ 2 := by 
          by_contra h'
          push_neg at h'
          have h5 : ¬Nat.Prime p := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
          tauto
        interval_cases p <;> norm_num at hp₁ hp₂
      have h9 : p ^ 2 % 3 = 1 := by
        rcases h12 with (h | h)
        · simp [Nat.pow_mod, h]
        · simp [Nat.pow_mod, h]
      have h11 : p ^ 2 % 4 = 1 := by
        have h10 : p % 4 = 1 ∨ p % 4 = 3 := by
          omega
        rcases h10 with (h | h)
        · simp [Nat.pow_mod, h]
        · simp [Nat.pow_mod, h]
      omega
  · -- Show no smaller element is in the set.
    intro k hk
    rcases hk with ⟨hk_pos, hk_div⟩
    have h1 : k ≥ 1 := by 
      omega
    linarith