import Mathlib

theorem number_theory_226944 :
    {(p, q) : ℕ × ℕ | p.Prime ∧ q.Prime ∧ p > 0 ∧ q > 0 ∧ p + p^2 + p^4 - q - q^2 - q^4 = 83805} = {(17, 2)} := by 
  ext ⟨p, q⟩
  simp [-one_div]
  constructor 
  · -- First direction: show any element in the set must be (17, 2)
    rintro ⟨h_p, h_q, hp1, hq1, heq⟩ 
    by_cases h5 : p % 2 = 1 
    · -- Assume p is odd 
      by_cases h6 : q % 2 = 1 
      · -- Assume both p and q are odd 
        exfalso 
        have h11 : (p + p^2 + p^4 : ℕ) % 2 = 1 := by 
          have hp11 : p % 2 = 1 := by 
            omega 
          simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hp11]
        have h22 : (q + q^2 + q^4 : ℕ) % 2 = 1 := by 
          have hq11 : q % 2 = 1 := by 
            omega 
          simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hq11]
        omega 
      · -- Assume q is even 
        have h7 : q % 2 = 0 := by 
          omega 
        have h8 : q = 2 := by 
          by_cases h10 : q > 2 
          · -- Assume q > 2 
            have h9 : ¬q.Prime := by 
              apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega) (by omega) (by omega)
            tauto 
          · -- Assume q ≤ 2 
            interval_cases q <;> norm_num at h_q ⊢ 
        rw [h8] at heq 
        have eq1 : p + p^2 + p^4 = 83827 := by
          omega
        have hx1 : p ≤ 100 := by 
          by_contra h 
          push_neg at h 
          have h100 : p ^ 4 ≥ 101 ^ 4 := by 
            have h11 : p ≥ 101 := by 
                omega 
            have h22 : p^4 ≥ 101^4 := by 
                apply Nat.pow_le_pow_of_le_left 
                omega 
            linarith 
          omega 
        interval_cases p <;> norm_num at eq1 h_p ⊢ 
        <;> try { 
          omega 
        }
    · -- Assume p is even 
      have h4 : p % 2 = 0 := by 
        omega 
      have h8 : p = 2 := by 
        by_cases h10 : p > 2 
        · -- Assume p > 2 
          have h9 : ¬p.Prime := by 
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
          tauto 
        · -- Assume p ≤ 2 
          interval_cases p <;> norm_num at h_p ⊢ 
      rw [h8] at heq 
      exfalso 
      omega 
  · -- Second direction: show that (17, 2) is a valid pair 
    rintro ⟨rfl, rfl⟩ 
    constructor 
    · norm_num 
    constructor 
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Now verify the equation 
      norm_num