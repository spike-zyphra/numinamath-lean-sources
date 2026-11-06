import Mathlib

theorem number_theory_287929 (x y : ℤ) (h₀ : 3 ∣ x^2 + y^2) : 3 ∣ x ∧ 3 ∣ y := by
  have h1 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  have h2 : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by omega
  have h3 : (x^2 + y^2) % 3 = 0 := by 
    omega
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> simp [pow_two, 
          Int.add_emod, Int.mul_emod, h1, h2] at h3 <;> omega