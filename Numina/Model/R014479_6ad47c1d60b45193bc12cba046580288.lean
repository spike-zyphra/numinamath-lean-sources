import Mathlib


lemma lemma_1 (n : ℤ) : 6 ∣ n^17 - n := by
  have h3 : n ^ 17 % 3 = n % 3 := by
    have h4 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h4 with (h4 | h4 | h4)
    ·
      simp [h4, pow_succ, Int.mul_emod, Int.sub_emod, Int.emod]
    ·
      simp [h4, pow_succ, Int.mul_emod, Int.sub_emod, Int.emod]
    ·
      have h6 : n % 3 = 2 := h4
      have h7 : n ^ 17 % 3 = 2 := by
        have h8 : n % 3 = 2 := h6
        have h9 : n ^ 17 % 3 = 2 := by
          have h10 : n % 3 = 2 := h8
          have h11 : n ^ 17 % 3 = 2 := by
            simp [h10, pow_succ, Int.add_emod, Int.mul_emod, Int.emod]
          exact h11
        exact h9
      have h8 : n % 3 = 2 := h6
      have h9 : n % 3 = 2 := h8
      have h10 : n % 3 = 2 := h9
      have h11 : n ^ 17 % 3 = n % 3 := by
        omega
      exact h11
  have h4 : n ^ 17 % 2 = n % 2 := by
    have h5 : n % 2 = 0 ∨ n % 2 = 1 := by
      omega
    rcases h5 with (h5 | h5)
    ·
      have h6 : n % 2 = 0 := h5
      have h7 : n ^ 17 % 2 = 0 := by
        simp [h6, pow_succ, Int.mul_emod, Int.emod]
      have h8 : n % 2 = 0 := h6
      have h9 : n ^ 17 % 2 = n % 2 := by
        omega
      exact h9
    ·
      have h6 : n % 2 = 1 := h5
      have h7 : n ^ 17 % 2 = 1 := by
        simp [h6, pow_succ, Int.mul_emod, Int.emod]
      have h8 : n % 2 = 1 := h6
      have h9 : n ^ 17 % 2 = n % 2 := by
        omega
      exact h9
  have h2 : n ^ 17 % 6 = n % 6 := by
    omega
  have h5 : (n ^ 17 - n) % 6 = 0 := by
    simp [Int.sub_emod, h2]
  have h6 : 6 ∣ n ^ 17 - n := by
    omega
  exact h6


theorem number_theory_161138 (n : ℤ) : IsGreatest {x | ∀ m : ℤ, x ∣ m^17 - m} 510 := by
  constructor
  · -- Show 510 is in the set
    show ∀ m : ℤ, 510 ∣ m ^ 17 - m
    intro m
    have h1 : m ^ 17 % 2 = m % 2 := by
      have h2 : m % 2 = 0 ∨ m % 2 = 1 := by omega
      rcases h2 with (h2 | h2)
      · simp [h2, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h2, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
    have h7 : m ^ 17 % 3 = m % 3 := by
      have h3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases h3 with (h3 | h3 | h3)
      · simp [h3, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h3, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h3, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
    have h5 : m ^ 17 % 5 = m % 5 := by
      have h7 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by omega
      rcases h7 with (h7 | h7 | h7 | h7 | h7)
      · simp [h7, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h7, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h7, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h7, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h7, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
    have h17 : m ^ 17 % 17 = m % 17 := by
      have h6 : m % 17 = 0 ∨ m % 17 = 1 ∨ m % 17 = 2 ∨ m % 17 = 3 ∨ m % 17 = 4 ∨ m % 17 = 5 ∨ m % 17 = 6 ∨ m % 17 = 7 ∨ m % 17 = 8 ∨ m % 17 = 9 ∨ m % 17 = 10 ∨ m % 17 = 11 ∨ m % 17 = 12 ∨ m % 17 = 13 ∨ m % 17 = 14 ∨ m % 17 = 15 ∨ m % 17 = 16 := by omega
      rcases h6 with (h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6)
      · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
      · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod]
    have h2 : (m ^ 17 - m) % 2 = 0 := by
      omega
    have h3 : (m ^ 17 - m) % 3 = 0 := by
      omega
    have h5' : (m ^ 17 - m) % 5 = 0 := by
      omega
    have h17' : (m ^ 17 - m) % 17 = 0 := by
      omega
    omega
  · -- Show there is no greater element in the set
    intro k hk
    have h1 := hk 2
    have h2 := hk 3
    have h3 := hk 5
    have h4 := hk 7
    have h5 := hk 11
    have h6 := hk 13
    norm_num at h1 h2 h3 h4 h5 h6
    have h8 : k ∣ 510 := by
      exact Int.dvd_gcd (Int.dvd_gcd (Int.dvd_gcd (Int.dvd_gcd (Int.dvd_gcd h1 h2) h3) h4) h5) h6
    have h9 : k ≤ 510 := by
      exact Int.le_of_dvd (by norm_num) h8
    linarith