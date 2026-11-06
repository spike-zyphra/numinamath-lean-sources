import Mathlib

theorem number_theory_140311 :
    {(p1, p2, p3) : ℕ × ℕ × ℕ | p2 = p1 + 80 ∧ p3 = p2 + 80 ∧ Nat.Prime p1 ∧ Nat.Prime p2 ∧ Nat.Prime p3}.ncard = 1 := by 
  have h1 : {(p1, p2, p3) : ℕ × ℕ × ℕ | p2 = p1 + 80 ∧ p3 = p2 + 80 ∧ Nat.Prime p1 ∧ Nat.Prime p2 ∧ Nat.Prime p3} = {(3, 83, 163)} := by 
    ext ⟨p1, p2, p3⟩
    simp
    constructor
    · -- Assume h
      rintro ⟨h1, h2, hp1, hp2, hp3⟩
      have h3 : p2 = p1 + 80 := by linarith
      have h4 : p3 = p1 + 160 := by 
        linarith [h1, h3]
      by_cases h5 : p1 % 3 = 0
      · -- p1 % 3 = 0
        have h6 : p1 = 3 := by
          by_cases h7 : p1 > 3
          · -- p1 > 3
            have h8 : p1 % 3 = 0 := h5
            have h9 : p1 ≠ 3 := by
              omega
            have h10 : ¬Nat.Prime p1 := by
              apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p1 by omega) (by omega) (by omega)
            contradiction
          · -- p1 ≤ 3
            interval_cases p1 <;> tauto
        have hp2' : p2 = 83 := by
          linarith [h6, h3]
        have hp3' : p3 = 163 := by
          linarith [h6, h4]
        simp [h6, hp2', hp3']
      · -- p1 % 3 ≠ 0
        have h7 : p1 % 3 = 1 ∨ p1 % 3 = 2 := by 
          omega
        rcases h7 with (h7 | h7)
        · -- p1 % 3 = 1
          have h8 : p2 % 3 = 0 := by
            omega
          have h9 : p2 > 3 := by
            omega
          have h10 : ¬Nat.Prime p2 := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p2 by omega) (by omega) (by omega)
          contradiction
        · -- p1 % 3 = 2
          have h10 : p3 % 3 = 0 := by 
            omega
          have h11 : p3 > 3 := by
            omega
          have h12 : ¬Nat.Prime p3 := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p3 by omega) (by omega) (by omega)
          contradiction
    · -- Show that (3, 83, 163) is in the set
      rintro ⟨rfl, rfl, rfl⟩
      constructor
      · -- Show p2 = p1 + 80
        norm_num
      constructor
      · -- Show p3 = p2 + 80
        norm_num
      constructor
      · -- Show Nat.Prime 3
        norm_num
      constructor
      · -- Show Nat.Prime 83
        norm_num
      · -- Show Nat.Prime 163
        norm_num
  rw [h1]
  simp