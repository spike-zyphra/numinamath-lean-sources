import Mathlib

theorem number_theory_36509 (n : ℤ) : 6 ∣ 2 * n ^ 3 + 3 * n ^ 2 + 7 * n := by 
  have h1 : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by 
    omega
  rcases h1 with (h | h | h | h | h | h) <;> ( 
    rw [Int.dvd_iff_emod_eq_zero] <;> simp [h, pow_two, pow_three, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod_emod]
  )