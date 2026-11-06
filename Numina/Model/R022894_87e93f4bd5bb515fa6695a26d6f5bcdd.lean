import Mathlib

theorem number_theory_136470 (x y : ℤ) : ¬(2*x^2-5*y^2=7) := by
  rintro h
  have h1 : (2 * x ^ 2 - 5 * y ^ 2) % 8 = 7 % 8 := by
    omega
  have h2 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by
    omega
  have h3 : y % 8 = 0 ∨ y % 8 = 1 ∨ y % 8 = 2 ∨ y % 8 = 3 ∨ y % 8 = 4 ∨ y % 8 = 5 ∨ y % 8 = 6 ∨ y % 8 = 7 := by
    omega
  have h4 : (2 * x ^ 2) % 8 = 0 ∨ (2 * x ^ 2) % 8 = 2 := by
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h2] <;> omega
  have h5 : (5 * y ^ 2) % 8 = 0 ∨ (5 * y ^ 2) % 8 = 5 ∨ (5 * y ^ 2) % 8 = 4 := by
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> simp [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h3] <;> omega
  omega