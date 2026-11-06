import Mathlib

theorem number_theory_184086 : ¬ ∃ (m n : ℤ), m^2 + 1954 = n^2 := by
  rintro ⟨m, n, h⟩
  have h1 : n^2 - m^2 = 1954 := by linarith
  have h2 : n^2 % 4 = 0 ∨ n^2 % 4 = 1 := by
    have h1 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by 
      omega
    rcases h1 with (h1 | h1 | h1 | h1) <;> 
      simp [pow_two, Int.add_emod, Int.mul_emod, h1, Int.sub_emod]
    all_goals omega
  have h3 : m^2 % 4 = 0 ∨ m^2 % 4 = 1 := by
    have h1 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by 
      omega
    rcases h1 with (h1 | h1 | h1 | h1) <;> 
      simp [pow_two, Int.add_emod, Int.mul_emod, h1, Int.sub_emod]
    all_goals omega
  omega