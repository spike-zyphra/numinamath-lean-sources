import Mathlib

theorem number_theory_112084 (a : ℤ) : 5 ∣ a^5 - a := by
  have h1 : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by 
    omega
  rcases h1 with (h | h | h | h | h) <;> ( 
    simp [Int.dvd_iff_emod_eq_zero, pow_succ, Int.sub_emod, Int.mul_emod, h, Int.emod_self]
)
  <;> omega