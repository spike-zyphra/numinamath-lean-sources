import Mathlib
theorem number_theory_607424 (a b : ℤ) : 2 ∣ a * b * (a - b):= by 
  have h1 : a % 2 = 0 ∨ a % 2 = 1 := by 
    omega 
  have h2 : b % 2 = 0 ∨ b % 2 = 1 := by 
    omega 
  rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2) <;> ( 
    simp [Int.dvd_iff_emod_eq_zero, Int.mul_emod, Int.sub_emod, h1, h2] <;> omega 
  )
  all_goals omega