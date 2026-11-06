import Mathlib


theorem number_theory_43414 (x y z : ℤ) :
    x^4 + y^4 + z^4 - 2 * x^2 * y^2 - 2 * y^2 * z^2 - 2 * z^2 * x^2 ≠ 2000 := by 
  intro h
  have eq1 : (x ^ 4 + y ^ 4 + z ^ 4 - 2 * x ^ 2 * y ^ 2 - 2 * y ^ 2 * z ^ 2 - 2 * z ^ 2 * x ^ 2 : ℤ) % 3 = 0 ∨
      (x ^ 4 + y ^ 4 + z ^ 4 - 2 * x ^ 2 * y ^ 2 - 2 * y ^ 2 * z ^ 2 - 2 * z ^ 2 * x ^ 2 : ℤ) % 3 = 1 := by
    have h1 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
    have h2 : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by omega
    have h3 : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
    rcases h1 with (h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2) <;> rcases h3 with (h3 | h3 | h3) <;>
      simp [Int.add_emod, Int.mul_emod, Int.sub_emod, pow_two, pow_succ, h1, h2, h3, Int.ofNat] <;> omega

  have eq2 : (x ^ 4 + y ^ 4 + z ^ 4 - 2 * x^2 * y^2 - 2 * y^2 * z^2 - 2 * z^2 * x^2 : ℤ) % 3 = 2 := by
    omega

  omega