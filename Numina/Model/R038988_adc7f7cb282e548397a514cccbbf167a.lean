import Mathlib

theorem number_theory_303799 (u v : ℤ) : (9 ∣ u^2 + u * v + v^2) → (3 ∣ u) ∧ (3 ∣ v) := by 
  intro h
  have h1 : u % 9 = 0 ∨ u % 9 = 1 ∨ u % 9 = 2 ∨ u % 9 = 3 ∨ u % 9 = 4 ∨ u % 9 = 5 ∨ u % 9 = 6 ∨ u % 9 = 7 ∨ u % 9 = 8 := by
    omega
  have h2 : v % 9 = 0 ∨ v % 9 = 1 ∨ v % 9 = 2 ∨ v % 9 = 3 ∨ v % 9 = 4 ∨ v % 9 = 5 ∨ v % 9 = 6 ∨ v % 9 = 7 ∨ v % 9 = 8 := by
    omega
  have h3 : u % 3 = 0 := by
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> ( 
      simp [Int.dvd_iff_emod_eq_zero, pow_two, Int.add_emod, Int.mul_emod, h1, h2] at h 
      <;> omega 
    )
  have h4 : v % 3 = 0 := by
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> ( 
      simp [Int.dvd_iff_emod_eq_zero, pow_two, Int.add_emod, Int.mul_emod, h1, h2] at h 
      <;> omega 
    )
  constructor
  · -- Prove 3 ∣ u
    exact Int.dvd_of_emod_eq_zero h3
  · -- Prove 3 ∣ v
    exact Int.dvd_of_emod_eq_zero h4