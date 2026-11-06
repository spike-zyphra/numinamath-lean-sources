import Mathlib

theorem number_theory_101691 (n : ℤ) : 9 ∣ n^3 + (n+1)^3 + (n+2)^3 := by
  have h1 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by
    omega
  rcases h1 with (h | h | h | h | h | h | h | h | h) <;> -- apply to all cases
    ( 
      simp [Int.dvd_iff_emod_eq_zero, Int.add_emod, Int.mul_emod, pow_two, pow_succ, h, Int.sub_emod]
    ) <;> omega