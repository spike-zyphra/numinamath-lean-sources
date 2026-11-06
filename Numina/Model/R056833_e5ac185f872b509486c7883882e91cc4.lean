import Mathlib

theorem number_theory_173045 : ¬∃ n : ℤ, n^3 = 10^100 + 5 * 10^50 + 1 := by 
  rintro ⟨n, hn⟩
  have h1 : n^3 % 9 = 0 ∨ n^3 % 9 = 1 ∨ n^3 % 9 = 8 := by
    have h1 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by
      omega
    rcases h1 with (h | h | h | h | h | h | h | h | h) <;> 
      simp [h, pow_succ, Int.mul_emod, Int.add_emod, Int.sub_emod]
  have h2 : (n^3 : ℤ) % 9 = 7 := by 
    omega
  omega