import Mathlib

theorem number_theory_12684 : (9 ∈ {x | ∃ a b : ℤ, x = a^2 - b^2}) ∧ (10 ∉ {x | ∃ a b : ℤ, x = a^2 - b^2}) := by 
  constructor
  · -- Show that 9 ∈ M
    use 3, 0
    all_goals norm_num 
  · -- Show that 10 ∉ M
    intro h 
    rcases h with ⟨a, b, h_eq⟩ 
    have h1 : a^2 % 4 = 0 ∨ a^2 % 4 = 1 := by 
      have h1 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by 
        omega 
      rcases h1 with (h1 | h1 | h1 | h1) <;> norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h1] at *
    
    have h2 : b^2 % 4 = 0 ∨ b^2 % 4 = 1 := by 
      have h2 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by 
        omega 
      rcases h2 with (h2 | h2 | h2 | h2) <;> norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h2] at *
    
    have h3 : (a^2 - b^2) % 4 = 2 := by 
      omega 

    omega