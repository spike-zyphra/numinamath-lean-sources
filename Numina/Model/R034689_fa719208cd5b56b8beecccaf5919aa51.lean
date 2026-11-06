import Mathlib

theorem number_theory_78517 (n : ℤ) :
    ¬ ∃ m, m^2 = n^2 + (n+1)^2 + (n+2)^2 + (n+3)^2 + (n+4)^2 := by 
  rintro ⟨m, hm⟩ 
  have eq1 : m^2 = 5 * n^2 + 20 * n + 30 := by 
    nlinarith 
  have eq2 : m^2 % 4 = 0 ∨ m^2 % 4 = 1 := by 
    have h1 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by 
      omega 
    rcases h1 with (h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1] at *
  have eq3 : (5 * n^2 + 20 * n + 30) % 4 = (n^2 + 2) % 4 := by 
    ring_nf 
    <;> omega 
  have eq4 : m^2 % 4 = (n^2 + 2) % 4 := by 
    omega 
  have eq5 : (n^2 + 2) % 4 = 2 ∨ (n^2 + 2) % 4 = 3 := by 
    have h1 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by 
      omega 
    rcases h1 with (h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1, Int.sub_emod] 
  omega