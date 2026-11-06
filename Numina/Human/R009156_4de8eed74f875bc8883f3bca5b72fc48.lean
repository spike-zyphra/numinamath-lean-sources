import Mathlib

theorem number_theory_3441 (x y : ℤ) : ¬(6*x-1=y^2) := by 
  intro h
  have h1 : y^2 % 3 = 0 ∨ y^2 % 3 = 1 := by
    have h1 : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by 
      omega
    rcases h1 with (h1 | h1 | h1)
    · left
      simp [pow_two, Int.mul_emod, h1]
    · right
      simp [pow_two, Int.mul_emod, h1]
    · right
      simp [pow_two, Int.mul_emod, h1]
  have h2 : y^2 % 3 = 2 := by 
    omega
  omega