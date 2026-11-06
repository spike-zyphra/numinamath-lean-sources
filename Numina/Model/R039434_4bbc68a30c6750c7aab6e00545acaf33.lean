import Mathlib

theorem number_theory_270478 (n : ℤ) :
    9 ∣ n^6 - 3*n^5 + 4*n^4 - 3*n^3 + 4*n^2 - 3*n := by 
  have h1 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by 
    omega 
  rcases h1 with (h | h | h | h | h | h | h | h | h) <;> ( 
    simp [Int.dvd_iff_emod_eq_zero, pow_two, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, h, 
      Int.emod]
  )