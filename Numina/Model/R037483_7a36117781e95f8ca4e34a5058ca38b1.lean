import Mathlib

theorem number_theory_150689 :
    Set.Infinite {n : ℤ | ¬∃ x y z, n = x^3 + y^3 + z^3} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (4 + n * 9 : ℤ))
  · -- Show the function f is injective
    intro a b h
    simp at h 
    all_goals omega
  · -- Show all elements in the image of f are in the set.
    intro n 
    simp at *
    all_goals 
      have h1 : ¬∃ x y z : ℤ, (4 + (n : ℕ) * 9 : ℤ) = x^3 + y^3 + z^3 := by 
        rintro ⟨x, y, z, heq⟩
        have eq1 : (x^3 + y^3 + z^3) % 9 = 4 := by 
          have eq2 : (4 + (n : ℕ) * 9 : ℤ) % 9 = 4 := by 
            simp [Int.add_emod, Int.mul_emod]
          omega
        have h21 : x^3 % 9 = 0 ∨ x^3 % 9 = 1 ∨ x^3 % 9 = 8 := by 
          have h : x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨ x % 9 = 6 ∨ x % 9 = 7 ∨ x % 9 = 8 := by 
            omega 
          rcases h with (h | h | h | h | h | h | h | h | h) <;> 
            simp [Int.add_emod, Int.mul_emod, pow_succ, h, Int.sub_emod]
        have h22 : y^3 % 9 = 0 ∨ y^3 % 9 = 1 ∨ y^3 % 9 = 8 := by 
          have h : y % 9 = 0 ∨ y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 3 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 6 ∨ y % 9 = 7 ∨ y % 9 = 8 := by 
            omega 
          rcases h with (h | h | h | h | h | h | h | h | h) <;> 
            simp [Int.add_emod, Int.mul_emod, pow_succ, h, Int.sub_emod]
        have h23 : z^3 % 9 = 0 ∨ z^3 % 9 = 1 ∨ z^3 % 9 = 8 := by 
          have h : z % 9 = 0 ∨ z % 9 = 1 ∨ z % 9 = 2 ∨ z % 9 = 3 ∨ z % 9 = 4 ∨ z % 9 = 5 ∨ z % 9 = 6 ∨ z % 9 = 7 ∨ z % 9 = 8 := by 
            omega 
          rcases h with (h | h | h | h | h | h | h | h | h) <;> 
            simp [Int.add_emod, Int.mul_emod, pow_succ, h, Int.sub_emod]
        omega
      simpa using h1