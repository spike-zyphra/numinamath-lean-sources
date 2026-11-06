import Mathlib

theorem number_theory_316054 (n : ℤ) (h₀ : Odd n) : n^2 ≡ 1 [ZMOD 8] := by 
  have h2 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    rcases h₀ with ⟨k, hk⟩
    have : n % 2 = 1 := by 
      omega
    omega

  rcases h2 with (h | h | h | h)
  · -- Case n ≡ 1 [mod 8]
    have h11 : (n : ℤ) % 8 = 1 := h
    norm_num [Int.ModEq] at *
    have : n ^ 2 % 8 = 1 := by 
      have h1 : n % 8 = 1 := h11
      norm_num [pow_two, Int.mul_emod, h1] at *
      <;> omega
    exact_mod_cast this

  · -- Case n ≡ 3 [mod 8]
    have h11 : (n : ℤ) % 8 = 3 := h
    norm_num [Int.ModEq] at *
    have : n ^ 2 % 8 = 1 := by 
      have h1 : n % 8 = 3 := h11
      norm_num [pow_two, Int.mul_emod, h1] at *
      <;> omega
    exact_mod_cast this

  · -- Case n ≡ 5 [mod 8]
    have h11 : (n : ℤ) % 8 = 5 := h
    norm_num [Int.ModEq] at *
    have : n ^ 2 % 8 = 1 := by 
      have h1 : n % 8 = 5 := h11
      norm_num [pow_two, Int.mul_emod, h1] at *
      <;> omega
    exact_mod_cast this

  · -- Case n ≡ 7 [mod 8]
    have h11 : (n : ℤ) % 8 = 7 := h
    norm_num [Int.ModEq] at *
    have : n ^ 2 % 8 = 1 := by 
      have h1 : n % 8 = 7 := h11
      norm_num [pow_two, Int.mul_emod, h1] at *
      <;> omega
    exact_mod_cast this