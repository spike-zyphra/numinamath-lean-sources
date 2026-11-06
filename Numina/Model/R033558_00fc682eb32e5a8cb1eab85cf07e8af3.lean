import Mathlib

theorem number_theory_288525 (n : ℤ) (h : ¬ 5 ∣ n) :
    ∃ m, m = n^2 ∧ (5 ∣ m - 1 ∨ 5 ∣ m + 1) := by
  use n ^ 2
  constructor
  · -- m = n ^ 2
    rfl
  -- Show either 5 divides n^2 - 1 or 5 divides n^2 + 1
  have h1 : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
    omega
  rcases h1 with (h2 | h3 | h4 | h5)
  · -- If n ≡ 1 (mod 5), then n^2 ≡ 1 (mod 5)
    have h2' : n ^ 2 % 5 = 1 := by
      norm_num [pow_two, Int.mul_emod, h2, Int.add_emod]
    have h3 : 5 ∣ n^2 - 1 := by 
      omega
    left
    omega
  · -- If n ≡ 2 (mod 5), then n^2 ≡ 4 (mod 5)
    have h3' : n ^ 2 % 5 = 4 := by
      norm_num [pow_two, Int.mul_emod, h3, Int.add_emod]
    have h4 : 5 ∣ n^2 + 1 := by 
      omega
    right
    omega
  · -- If n ≡ 3 (mod 5), then n^2 ≡ 4 (mod 5)
    have h4' : n ^ 2 % 5 = 4 := by
      norm_num [pow_two, Int.mul_emod, h4, Int.add_emod]
    have h5 : 5 ∣ n^2 + 1 := by 
      omega
    right
    omega
  · -- If n ≡ 4 (mod 5), then n^2 ≡ 1 (mod 5)
    have h5' : n ^ 2 % 5 = 1 := by
      norm_num [pow_two, Int.mul_emod, h5, Int.add_emod]
    have h6 : 5 ∣ n^2 - 1 := by 
      omega
    left
    omega