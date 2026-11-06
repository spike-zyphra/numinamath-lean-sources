import Mathlib

theorem number_theory_67031 (a : ℤ) (h : IsCoprime a 35) :
    35 ∣ (a^4 - 1)*(a^4 + 15*a^2 + 1) := by
  -- Need to show a % 5 ≠ 0 and a % 7 ≠ 0 from IsCoprime a 35
  have h1 : a % 5 ≠ 0 := by 
    by_contra h1
    have h1' : 5 ∣ a := by 
      omega 
    have h2 : IsCoprime a 35 := h 
    have h9 : Int.gcd a (35 : ℤ) = 1 := by 
      rw [Int.isCoprime_iff_gcd_eq_one] at h2 
      omega 
    have h5div : (5 : ℤ) ∣ a := h1'
    have h5div_gcd : (5 : ℤ) ∣ Int.gcd a (35 : ℤ) := by 
      apply dvd_gcd 
      · -- Show 5 ∣ a 
        exact h5div 
      · -- Show 5 ∣ 35 
        norm_num 
    -- We have Int.gcd a 35 = 1 
    -- So 5 ∣ 1, which is a contradiction. 
    have h5d1 : (5 : ℤ) ∣ (1 : ℤ) := by 
      rw [show Int.gcd a (35 : ℤ) = 1 by omega] at h5div_gcd 
      exact h5div_gcd 
    omega 
  -- Therefore, a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 
  have h1' : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by
    omega
  -- Therefore, a cannot be 0 mod 7
  -- Need to show a % 7 ≠ 0 from IsCoprime a 35.
  have h3 : a % 7 ≠ 0 := by 
    by_contra h3
    have h1' : 7 ∣ a := by 
      omega 
    have h8 : IsCoprime a 35 := h 
    have h9 : Int.gcd a (35 : ℤ) = 1 := by 
      rw [Int.isCoprime_iff_gcd_eq_one] at h8 
      omega 
    -- We have 7 divides a
    have h7k : (7 : ℤ) ∣ a := h1'
    -- We have 7 divides 35
    have h5div_gcd : (7 : ℤ) ∣ Int.gcd a (35 : ℤ) := by 
      apply dvd_gcd 
      · -- Show 7 ∣ a 
        exact h7k 
      · -- Show 7 ∣ 35 
        norm_num 
    -- We have Int.gcd a 35 = 1. 
    -- So 7 ∣ 1, which is a contradiction. 
    have h5d1 : (7 : ℤ) ∣ (1 : ℤ) := by 
      rw [show Int.gcd a (35 : ℤ) = 1 by omega] at h5div_gcd 
      exact h5div_gcd 
    omega 
  have h4 : a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by
    omega
  -- Prove that ... ≡ 0 (mod 5)
  have h5 : (a ^ 4 - 1) * (a ^ 4 + 15 * a ^ 2 + 1) % 5 = 0 := by
    rcases h1' with (h6 | h6 | h6 | h6) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, h6, Int.mul_emod]
  -- Prove that ... ≡ 0 (mod 7)
  have h7 : (a ^ 4 - 1) * (a ^ 4 + 15 * a ^ 2 + 1) % 7 = 0 := by
    rcases h4 with (h8 | h8 | h8 | h8 | h8 | h8) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, h8, Int.mul_emod]
  omega