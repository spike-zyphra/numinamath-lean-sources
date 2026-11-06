import Mathlib

theorem number_theory_47061 (n : ℤ) : 6 ∣ n * (n ^ 2 + 5) := by
  have h1 : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
    omega
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1) <;> ( 
    simp [Int.dvd_iff_emod_eq_zero, Int.mul_emod, pow_two, Int.add_emod, Int.sub_emod, h1, Int.mul_emod]
    <;> omega
)