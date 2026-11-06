import Mathlib

theorem number_theory_92103 (n : ℤ) (hn : n > 0) :
    ¬ (∃ k l m, k^2 = 2 * n^2 - 1 ∧ l^2 = 3 * n^2 - 1 ∧ m^2 = 6 * n^2 - 1) := by

  rintro ⟨k, l, m, hk, hl, hm⟩
  
  have h1 : m^2 % 6 = 0 ∨ m^2 % 6 = 1 ∨ m^2 % 6 = 3 ∨ m^2 % 6 = 4 := by
    have h1 : m % 6 = 0 ∨ m % 6 = 1 ∨ m % 6 = 2 ∨ m % 6 = 3 ∨ m % 6 = 4 ∨ m % 6 = 5 := by 
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1) <;> simp [h1, pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod]

  have h2 : m^2 % 6 = 5 := by
    have : m^2 = 6 * n^2 - 1 := hm
    omega
  
  omega