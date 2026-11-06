import Mathlib

theorem number_theory_8215 (x y z : ℤ) : x^2 + y^2 - 8 * z^3 = 6 → False := by
  intro h
  have h1 : x^2 % 8 = 0 ∨ x^2 % 8 = 1 ∨ x^2 % 8 = 4 := by
    have h2 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by 
      omega
    rcases h2 with (h | h | h | h | h | h | h | h) <;> 
      simp [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h]
  have h2 : y^2 % 8 = 0 ∨ y^2 % 8 = 1 ∨ y^2 % 8 = 4 := by
    have h3 : y % 8 = 0 ∨ y % 8 = 1 ∨ y % 8 = 2 ∨ y % 8 = 3 ∨ y % 8 = 4 ∨ y % 8 = 5 ∨ y % 8 = 6 ∨ y % 8 = 7 := by
      omega
    rcases h3 with (h | h | h | h | h | h | h | h) <;> 
      simp [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h]
  have h4 : (x ^ 2 + y ^ 2 : ℤ) = 8 * z^3 + 6 := by
    linarith
  have h5 : (x^2 + y^2) % 8 = 6 := by
    omega
  have h3 : (x^2 + y^2) % 8 = 0 ∨ (x^2 + y^2) % 8 = 1 ∨ (x^2 + y^2) % 8 = 2 ∨ (x^2 + y^2) % 8 = 4 ∨ (x^2 + y^2) % 8 = 5 := by
    omega
  omega