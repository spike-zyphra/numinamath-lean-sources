import Mathlib

theorem number_theory_248390 (a b : ℤ) (ha : a > 0) (hb : b > 0)
    (h : a^2 + a * b + b^2 = 2018) :
    False := by 
  have h1 : (a^2 + a * b + b^2) % 3 = 2 := by 
    omega 
  have h4 : (a^2 + a * b + b^2) % 3 = 0 ∨ (a^2 + a * b + b^2) % 3 = 1 := by 
    have h2 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by 
      omega 
    have h3 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by 
      omega 
    rcases h2 with (h2 | h2 | h2) <;> rcases h3 with (h3 | h3 | h3) <;> 
      simp [pow_two, Int.add_emod, Int.mul_emod, h2, h3] at *
      <;> omega 
  omega