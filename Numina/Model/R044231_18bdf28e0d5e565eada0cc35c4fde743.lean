import Mathlib

theorem number_theory_253676 (n : ℤ) : ¬ 4 ∣ (1 + n + n^2 + n^3 + n^4) := by
  have h1 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
    omega

  rcases h1 with (h | h | h | h) <;> ( 
    simp [Int.dvd_iff_emod_eq_zero, h, pow_two, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod] <;> omega
  )