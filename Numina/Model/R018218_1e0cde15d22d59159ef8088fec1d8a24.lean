import Mathlib

theorem number_theory_6329 (x y : ℤ) : 3 * x ^ 10 - y ^ 10 ≠ 1990 := by
  intro h
  have eq1 : (3 * x ^ 10 - y ^ 10) % 3 = 1990 % 3 := by 
    omega
  norm_num at eq1 
  have eq2 : y ^ 10 % 3 = 0 ∨ y ^ 10 % 3 = 1 := by
    have h1 : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by
      omega 
    rcases h1 with (h1 | h1 | h1)
    · 
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · 
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · 
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
  have eq3 : y ^ 10 % 3 = 0 ∨ y ^ 10 % 3 = 1 := eq2
  have eq4 : (3 * x ^ 10 - y ^ 10) % 3 = ( - (y ^ 10) ) % 3 := by
    have eq5 : (3 * x ^ 10 : ℤ) % 3 = 0 := by
      simp [Int.mul_emod]
    omega
  have eq5 : (3 * x ^ 10 - y ^ 10) % 3 = 1 := by 
    omega
  have eq6 : (y ^ 10) % 3 = 2 := by
    omega
  omega