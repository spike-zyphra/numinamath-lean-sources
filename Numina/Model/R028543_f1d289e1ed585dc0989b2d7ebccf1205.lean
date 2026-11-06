import Mathlib

theorem number_theory_111980 (p : ℕ) (hp : Nat.Prime p) (h : 5 < p) :
    p^2 ≡ 1 [ZMOD 30] ∨ p^2 ≡ 19 [ZMOD 30] := by 
  have h1 : p % 2 = 1 := by 
    by_contra h2 
    push_neg at h2
    have h2 : ¬(Nat.Prime p) := by 
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals linarith 
    contradiction
  have h2 : p % 3 = 1 ∨ p % 3 = 2 := by 
    have h3 : p % 3 = 1 ∨ p % 3 = 2 ∨ p % 3 = 0 := by 
      omega 
    have h3n : p % 3 ≠ 0 := by 
      by_contra h4 
      have h4 : 3 ∣ p := by 
        omega 
      have h4n : ¬(Nat.Prime p) := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals linarith 
      contradiction
    tauto 
  have h3 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
    have h4 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 ∨ p % 5 = 0 := by 
      omega 
    have h3n : p % 5 ≠ 0 := by 
      by_contra h4 
      have h4 : 5 ∣ p := by 
        omega 
      have h4n : ¬(Nat.Prime p) := by 
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega)
        all_goals linarith 
      contradiction 
    tauto 
  have h4 : (p : ℤ) % 2 = 1 := by 
    omega 
  have h55 : (p : ℤ) % 3 = 1 ∨ (p : ℤ) % 3 = 2 := by 
    omega 
  have h56 : (p : ℤ) % 5 = 1 ∨ (p : ℤ) % 5 = 2 ∨ (p : ℤ) % 5 = 3 ∨ (p : ℤ) % 5 = 4 := by 
    omega 
  have h530 : (p ^ 2 : ℤ) % 2 = 1 := by 
    have h5301 : (p : ℤ) % 2 = 1 := h4 
    simp [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h5301]
  have h531 : (p ^ 2 : ℤ) % 3 = 1 := by 
    rcases h55 with (h55 | h55) 
    all_goals 
      simp [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h55]
  have h532 : ((p : ℤ) ^ 2) % 5 = 1 ∨ ((p : ℤ) ^ 2) % 5 = 4 := by 
    rcases h56 with (h56 | h56 | h56 | h56)
    all_goals 
      simp [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h56]
  by_cases h9 : (p ^ 2 : ℤ) % 5 = 1 
  · 
    -- Assume (p ^ 2) ≡ 1 (mod 5)
    left
    simp [Int.ModEq] at *
    omega 
  · 
    -- Assume p ^ 2 ≡ 4 (mod 5)
    right
    simp [Int.ModEq] at *
    have h11 : (p ^ 2 : ℤ) % 5 = 4 := by 
      omega 
    omega