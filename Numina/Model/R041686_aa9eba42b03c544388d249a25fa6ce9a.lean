import Mathlib

theorem number_theory_8718 :
    (∃ A B C D E : ℤ, 2018 = A^5 + B^5 + C^5 + D^5 + E^5) ∧
    ¬∃ A B C D : ℤ, 2018 = A^5 + B^5 + C^5 + D^5 := by
  constructor
  · -- Show that there exist five integers A, B, C, D, and E such that 2018 = A^5 + B^5 + C^5 + D^5 + E^5.
    use 4, 4, 1, 1, -2
    norm_num
  · -- Show that there do not exist four integers A, B, C, and D such that 2018 = A^5 + B^5 + C^5 + D^5.
    intro h
    rcases h with ⟨A, B, C, D, h_eq⟩
    have h1 : A^5 % 11 = 0 ∨ A^5 % 11 = 1 ∨ A^5 % 11 = 10 := by
      have h1 : A % 11 = 0 ∨ A % 11 = 1 ∨ A % 11 = 2 ∨ A % 11 = 3 ∨ A % 11 = 4 ∨ A % 11 = 5 ∨ A % 11 = 6 ∨ A % 11 = 7 ∨ A % 11 = 8 ∨ A % 11 = 9 ∨ A % 11 = 10 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
      ( 
        simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        <;> try tauto
      )
    have h2 : B^5 % 11 = 0 ∨ B^5 % 11 = 1 ∨ B^5 % 11 = 10 := by
      have h2 : B % 11 = 0 ∨ B % 11 = 1 ∨ B % 11 = 2 ∨ B % 11 = 3 ∨ B % 11 = 4 ∨ B % 11 = 5 ∨ B % 11 = 6 ∨ B % 11 = 7 ∨ B % 11 = 8 ∨ B % 11 = 9 ∨ B % 11 = 10 := by
        omega
      rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> 
      ( 
        simp [h2, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        <;> try tauto
      )
    have h3 : C^5 % 11 = 0 ∨ C^5 % 11 = 1 ∨ C^5 % 11 = 10 := by
      have h3 : C % 11 = 0 ∨ C % 11 = 1 ∨ C % 11 = 2 ∨ C % 11 = 3 ∨ C % 11 = 4 ∨ C % 11 = 5 ∨ C % 11 = 6 ∨ C % 11 = 7 ∨ C % 11 = 8 ∨ C % 11 = 9 ∨ C % 11 = 10 := by
        omega
      rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> 
      ( 
        simp [h3, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        <;> try tauto
      )
    have h4 : D^5 % 11 = 0 ∨ D^5 % 11 = 1 ∨ D^5 % 11 = 10 := by
      have h4 : D % 11 = 0 ∨ D % 11 = 1 ∨ D % 11 = 2 ∨ D % 11 = 3 ∨ D % 11 = 4 ∨ D % 11 = 5 ∨ D % 11 = 6 ∨ D % 11 = 7 ∨ D % 11 = 8 ∨ D % 11 = 9 ∨ D % 11 = 10 := by
        omega
      rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> 
      ( 
        simp [h4, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        <;> try tauto
      )
    omega