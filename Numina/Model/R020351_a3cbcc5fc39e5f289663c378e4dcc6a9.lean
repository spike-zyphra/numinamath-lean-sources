import Mathlib

theorem number_theory_141157 (a b : ℤ) (_ : a % 7 = 3) (h₀ : b % 7 = 4) :
    (a + b)^2 % 7 = 0 := by
  have h1 : (a + b) % 7 = 0 := by 
    omega 
  simp [pow_two, Int.add_emod, Int.mul_emod, h1]
  all_goals omega