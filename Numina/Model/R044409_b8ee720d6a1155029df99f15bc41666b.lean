import Mathlib

theorem number_theory_91821 (p : ℕ) (hp : Odd p ∧ Nat.Prime p) :
    (6 : ℤ) ∣ p^2 * (p^2 - 1999) ∧ ¬(12 : ℤ) ∣ p^2 * (p^2 - 1999) := by
  rcases hp with ⟨hp_odd, hp_prime⟩
  have h1 : (p : ℤ) % 2 = 1 := by
    have h1 : p % 2 = 1 := by
      obtain ⟨k, hk⟩ := hp_odd
      omega
    omega
  have h4 : p ≥ 3 := by
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num at hp_prime hp_odd <;> all_goals tauto
  constructor
  · -- Show that 6 divides the expression
    have h5 : (p : ℤ) % 3 = 0 ∨ (p : ℤ) % 3 = 1 ∨ (p : ℤ) % 3 = 2 := by omega
    rcases h5 with (h | h | h)
    · -- case p % 3 = 0
      have h6 : (p : ℤ) % 3 = 0 := h
      have h7 : p = 3 := by
        have h8 : p % 3 = 0 := by
          omega
        have h9 : p ≤ 3 := by
          by_contra h
          push_neg at h
          have h10 : p > 3 := by linarith
          have h11 : ¬Nat.Prime p := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
            all_goals linarith
          tauto
        interval_cases p <;> norm_num at hp_prime hp_odd h8 <;> all_goals omega
      rw [show (p : ℤ) = 3 by omega]
      all_goals omega
    · -- case p % 3 = 1
      have h6 : (p : ℤ) % 3 = 1 := h
      have h7 : (p : ℤ) ^ 2 % 3 = 1 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h6]
      have h8 : (p^2 * (p^2 - 1999) : ℤ) % 3 = 0 := by
        simp [Int.mul_emod, Int.sub_emod, h7, h6]
      have h9 : (p^2 * (p^2 - 1999) : ℤ) % 2 = 0 := by
        have h10 : (p : ℤ) ^ 2 % 2 = 1 := by
          simp [pow_two, Int.add_emod, Int.mul_emod, h1]
        have h11 : (p^2 - 1999 : ℤ) % 2 = 0 := by
          omega
        simp [Int.mul_emod, Int.add_emod, h10, h11]
      omega
    · -- case p % 3 = 2
      have h6 : (p : ℤ) % 3 = 2 := h
      have h7 : (p : ℤ) ^ 2 % 3 = 1 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h6]
      have h8 : (p^2 * (p^2 - 1999) : ℤ) % 3 = 0 := by
        simp [Int.mul_emod, Int.sub_emod, h7, h6]
      have h9 : (p^2 * (p^2 - 1999) : ℤ) % 2 = 0 := by
        have h10 : (p : ℤ) ^ 2 % 2 = 1 := by
          simp [pow_two, Int.add_emod, Int.mul_emod, h1]
        have h11 : (p^2 - 1999 : ℤ) % 2 = 0 := by
          omega
        simp [Int.mul_emod, Int.add_emod, h10, h11]
      omega
  · -- Show the expression is not divisible by 12
    intro h
    have h10 : (p^2 * (p^2 - 1999) : ℤ) % 4 = 0 := by
      omega
    have h11 : (p^2 * (p^2 - 1999) : ℤ) % 4 = 2 := by
      have h12 : (p : ℤ) % 4 = 1 ∨ (p : ℤ) % 4 = 3 := by
        have h13 : p % 2 = 1 := by
          obtain ⟨k, hk⟩ := hp_odd
          omega
        omega
      rcases h12 with (h | h)
      · -- case p % 4 = 1
        have h5 : (p : ℤ) % 4 = 1 := h
        have h6 : (p ^ 2 : ℤ) % 4 = 1 := by
          simp [pow_two, Int.add_emod, Int.mul_emod, h5]
        have h7 : (p^2 - 1999 : ℤ) % 4 = 2 := by
          omega
        simp [Int.mul_emod, h6, h7, Int.mul_emod]
      · -- case p % 4 = 3
        have h5 : (p : ℤ) % 4 = 3 := h
        have h6 : (p ^ 2 : ℤ) % 4 = 1 := by
          simp [pow_two, Int.add_emod, Int.mul_emod, h5]
        have h7 : (p^2 - 1999 : ℤ) % 4 = 2 := by
          omega
        simp [Int.mul_emod, h6, h7, Int.mul_emod]
    omega