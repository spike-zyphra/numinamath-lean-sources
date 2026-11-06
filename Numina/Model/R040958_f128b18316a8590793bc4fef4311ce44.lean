import Mathlib

theorem number_theory_206847 (a b c d : ℤ) (h : 5 ∣ a^4 + b^4 + c^4 + d^4) : 625 ∣ a * b * c * d := by

  have h1 : a^4 % 5 = 0 ∨ a^4 % 5 = 1 := by 
    have h1 : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by 
      omega 
    rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> 
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod] 
  have h2 : b^4 % 5 = 0 ∨ b^4 % 5 = 1 := by
    have h1 : b % 5 = 0 ∨ b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by 
      omega 
    rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> 
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod] 
  have h3 : c^4 % 5 = 0 ∨ c^4 % 5 = 1 := by
    have h1 : c % 5 = 0 ∨ c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 := by
      omega 
    rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> 
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod] 
  have h4 : d^4 % 5 = 0 ∨ d^4 % 5 = 1 := by 
    have h1 : d % 5 = 0 ∨ d % 5 = 1 ∨ d % 5 = 2 ∨ d % 5 = 3 ∨ d % 5 = 4 := by 
      omega 
    rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> 
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod] 
  -- From the divisibility condition, we can conclude each fourth power must be 0 mod 5
  have h5 : a^4 % 5 = 0 := by
    omega 
  have h6 : b^4 % 5 = 0 := by 
    omega 
  have h7 : c^4 % 5 = 0 := by 
    omega 
  have h8 : d^4 % 5 = 0 := by
    omega 
  -- From x^4 ≡ 0 (mod 5) implies x ≡ 0 (mod 5)
  have h9 : a % 5 = 0 := by 
    have h1 : a^4 % 5 = 0 := h5 
    have : a % 5 = 0 := by 
      have h2 : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by 
        omega 
      rcases h2 with (h2 | h2 | h2 | h2 | h2) <;> 
        norm_num [pow_succ, Int.add_emod, Int.mul_emod, h2] at h1 <;> omega 
    assumption 
  -- Similarly for b, c, d 
  have h10 : b % 5 = 0 := by 
    have h1 : b^4 % 5 = 0 := h6
    have : b % 5 = 0 := by 
      have h2 : b % 5 = 0 ∨ b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by 
        omega 
      rcases h2 with (h2 | h2 | h2 | h2 | h2) <;> 
        norm_num [pow_succ, Int.add_emod, Int.mul_emod, h2] at h1 <;> omega 
    assumption 
  -- Similarly for c and d 
  have h11 : c % 5 = 0 := by 
    have h1 : c^4 % 5 = 0 := h7 
    have : c % 5 = 0 := by 
      have h2 : c % 5 = 0 ∨ c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 := by 
        omega 
      rcases h2 with (h2 | h2 | h2 | h2 | h2) <;> 
        norm_num [pow_succ, Int.add_emod, Int.mul_emod, h2] at h1 <;> omega 
    assumption 
  -- Similarly for d 
  have h12 : d % 5 = 0 := by 
    have h1 : d^4 % 5 = 0 := h8
    have : d % 5 = 0 := by 
      have h2 : d % 5 = 0 ∨ d % 5 = 1 ∨ d % 5 = 2 ∨ d % 5 = 3 ∨ d % 5 = 4 := by 
        omega 
      rcases h2 with (h2 | h2 | h2 | h2 | h2) <;> 
        norm_num [pow_succ, Int.add_emod, Int.mul_emod, h2] at h1 <;> omega 
    assumption 
  -- From a % 5 = 0, we can conclude 5 divides a 
  have h13 : 5 ∣ a := by 
    omega 
  have h14 : 5 ∣ b := by 
    omega 
  have h15 : 5 ∣ c := by 
    omega 
  have h16 : 5 ∣ d := by 
    omega 
  -- Let a = 5k, b = 5m, c = 5n, d = 5p 
  rcases h13 with ⟨k1, h17⟩ 
  rcases h14 with ⟨k2, h18⟩ 
  rcases h15 with ⟨k3, h19⟩ 
  rcases h16 with ⟨k4, h20⟩ 
  -- Then a * b * c * d = (5k)(5m)(5n)(5p) = 625 * (k*m*n*p) 
  use k1 * k2 * k3 * k4 
  rw [h17, h18, h19, h20] 
  ring