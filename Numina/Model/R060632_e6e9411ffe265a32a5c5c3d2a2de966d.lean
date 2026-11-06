import Mathlib

theorem number_theory_291675 (x y : ℤ) : 3 ∣ x^2 + y^2 → 3 ∣ x ∧ 3 ∣ y := by 
  intro h
  have h1 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by
    omega

  have h2 : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by
    omega

  have h5 : (x^2 + y^2) % 3 = 0 := by
    omega

  rcases h1 with (h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2) <;> simp [Int.add_emod, pow_two, Int.mul_emod, h1, h2] at h5 <;> omega