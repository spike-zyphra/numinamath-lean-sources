import Mathlib

theorem algebra_312353 : ¬∃ x y : ℤ, x^3 + 6 * x^2 + 5 * x = y^3 - y + 2 := by
  rintro ⟨x, y, h⟩
  have h1 : (x ^ 3 + 6 * x ^ 2 + 5 * x) % 3 = (y ^ 3 - y + 2) % 3 := by
    omega
  have eq1 : (x ^ 3 + 6 * x ^ 2 + 5 * x) % 3 = 0 := by
    have h2 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by 
      omega 
    rcases h2 with (h2 | h2 | h2)
    ·
      simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h2]
    ·
      simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h2]
    ·
      simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h2]
  have eq2 : (y ^ 3 - y + 2) % 3 = 2 := by
    have h2 : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by
      omega
    rcases h2 with (h2 | h2 | h2)
    · 
      simp [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, pow_succ, h2]
    · 
      simp [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, pow_succ, h2]
    · 
      simp [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, pow_succ, h2]
  omega