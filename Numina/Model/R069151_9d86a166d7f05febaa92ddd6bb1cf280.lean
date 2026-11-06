import Mathlib

theorem number_theory_262130 : ∀ (n : ℤ), Odd n → 8 ∣ (n ^ 2 - 1) := by 
  intro n hn
  have h1 : n % 2 = 1 := by 
    rcases hn with ⟨k, hk⟩
    omega
  have h2 : n ^ 2 % 8 = 1 := by
    have h1' : n % 2 = 1 := h1
    have h3 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by 
      omega
    rcases h3 with (h | h | h | h)
    · -- n ≡ 1 (mod 8)
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
    · -- n ≡ 3 (mod 8)
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
    · -- n ≡ 5 (mod 8)
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
    · -- n ≡ 7 (mod 8)
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
  omega