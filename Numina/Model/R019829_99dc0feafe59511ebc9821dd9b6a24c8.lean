import Mathlib

theorem number_theory_306909 (x y : ℤ) : ¬(x^2 + y^2 - 2017 * x * y - 2017 = 0) := by 
  by_contra h
  have eq1 : x^2 + y^2 - 2017 * x * y - 2017 = 0 := by 
    nlinarith
  have h_mod5 : (x ^ 2 + y ^ 2 - 2017 * x * y - 2017) % 5 = 0 := by
    omega 
  have h1 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by 
    omega
  have h2 : y % 5 = 0 ∨ y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by
    omega
  rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2 | h2) <;> 
    simp [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, h1, h2, Int.ofNat, Int.sub_emod] at h_mod5 <;> omega