import Mathlib

theorem number_theory_321042 (x y : ℤ) :
    x^3 + 3 * x * y^2 ≠ ∑ i ∈ Finset.range 2018, 10^i := by 
  intro h 
  have h1 : (x ^ 3 + 3 * x * y ^ 2 : ℤ) % 9 = (∑ i in Finset.range 2018, (10 : ℤ) ^ i) % 9 := by 
    omega 
  have h2 : (∑ i in Finset.range 2018, (10 : ℤ) ^ i) % 9 = 2 := by 
    native_decide 
  -- From h1 and h2, it follow that left side equal to right side 
  have h3 : (x ^ 3 + 3 * x * y ^ 2 : ℤ) % 9 = 2 := by 
    omega 
  have h4 : x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨ x % 9 = 6 ∨ x % 9 = 7 ∨ x % 9 = 8 := by 
    omega 
  have h5 : y % 9 = 0 ∨ y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 3 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 6 ∨ y % 9 = 7 ∨ y % 9 = 8 := by 
    omega 
  rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5) <;> 
    simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h4, h5] at h3