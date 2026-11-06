import Mathlib

theorem number_theory_113671 : ¬∃ x y : ℤ, 2*x^2 - 215*y^2 = 1 := by 
  rintro ⟨x, y, h_eq⟩
  have h1 : x^2 % 5 = 0 ∨ x^2 % 5 = 1 ∨ x^2 % 5 = 4 := by 
    have h2 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by 
      omega 
    rcases h2 with (h2 | h2 | h2 | h2 | h2) <;> 
      ( 
        simp [pow_two, Int.add_emod, Int.mul_emod, h2] 
      )
  have h2 : (2 * x^2) % 5 = 0 ∨ (2 * x^2) % 5 = 2 ∨ (2 * x^2) % 5 = 3 := by 
    rcases h1 with (h1 | h1 | h1) <;> 
      ( 
        have : (2 * x^2) % 5 = 0 ∨ (2 * x^2) % 5 = 2 ∨ (2 * x^2) % 5 = 3 := by 
          simp [Int.mul_emod, h1, Int.add_emod] 
          all_goals omega 
        assumption 
      )
  have h3 : (2 * x ^ 2 - 215 * y ^ 2) % 5 = 1 := by 
    omega 
  have h4 : (2 * x ^ 2) % 5 = 1 := by 
    omega 
  omega