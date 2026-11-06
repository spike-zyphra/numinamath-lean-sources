import Mathlib

theorem number_theory_283008 (p : ℕ) (hp : Nat.Prime p) (h5 : 5 < p) :
    p^2 ≡ 1 [ZMOD 30] ∨ p^2 ≡ 19 [ZMOD 30] := by

  have h1 : p ≥ 6 := by linarith

  have h2 : p % 2 = 1 := by
    by_contra h
    push_neg at h
    have : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals omega
    contradiction

  have h3 : p % 3 = 1 ∨ p % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h4 : p % 3 = 0 := by omega
    have : 3 ∣ p := by omega
    have h55 : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
      all_goals omega
    contradiction

  have h4 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
    by_contra h
    push_neg at h
    have h8 : p % 5 = 0 := by omega
    have : 5 ∣ p := by omega
    have h55 : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega)
      all_goals omega
    contradiction

  have h6 : (p : ℤ) % 2 = 1 := by omega
  have h7 : (p : ℤ) % 3 = 1 ∨ (p : ℤ) % 3 = 2 := by omega
  have h8 : (p : ℤ) % 5 = 1 ∨ (p : ℤ) % 5 = 2 ∨ (p : ℤ) % 5 = 3 ∨ (p : ℤ) % 5 = 4 := by omega

  have h66 : (p : ℤ) ^ 2 % 2 = 1 := by
    have : (p : ℤ) % 2 = 1 := h6
    simp [pow_two, Int.add_emod, Int.mul_emod, this]

  have h67 : (p : ℤ) ^ 2 % 3 = 1 := by
    rcases h7 with (h7 | h7)
    · simp [pow_two, Int.add_emod, Int.mul_emod, h7]
    · simp [pow_two, Int.add_emod, Int.mul_emod, h7]

  have h68 : (p : ℤ) ^ 2 % 5 = 1 ∨ (p : ℤ) ^ 2 % 5 = 4 := by
    rcases h8 with (h8 | h8 | h8 | h8)
    · simp [pow_two, Int.add_emod, Int.mul_emod, h8]
    · simp [pow_two, Int.add_emod, Int.mul_emod, h8]
    · simp [pow_two, Int.add_emod, Int.mul_emod, h8]
    · simp [pow_two, Int.add_emod, Int.mul_emod, h8]

  rcases h68 with (h68 | h68)
  · -- Case where squared ≡ 1 mod 5
    have h30 : (p : ℤ) ^ 2 % 30 = 1 := by
      omega
    left
    simp [Int.ModEq, h30]

  · -- Case where squared ≡ 4 (mod 5)
    have h30 : (p : ℤ) ^ 2 % 30 = 19 := by
      omega
    right
    simp [Int.ModEq, h30]