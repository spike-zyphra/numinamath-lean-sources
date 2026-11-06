import Mathlib

theorem number_theory_7455 : ¬∃ m : ℤ, ∃ k : ℕ, m^2 = 5 * k + 2 := by 
  rintro ⟨m, ⟨k, hk⟩⟩
  have h1 : m^2 % 5 = 2 := by 
    omega
  have h2 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by 
    omega
  rcases h2 with (h | h | h | h | h)
  · -- Case m % 5 = 0
    have h3 : m^2 % 5 = 0 := by 
      simp [pow_two, Int.mul_emod, h]
    omega 
  · -- Case m % 5 = 1
    have h3 : m^2 % 5 = 1 := by 
      simp [pow_two, Int.mul_emod, h]
    omega 
  · -- Case m % 5 = 2
    have h3 : m^2 % 5 = 4 := by 
      simp [pow_two, Int.mul_emod, h]
    omega 
  · -- Case m % 5 = 3
    have h3 : m^2 % 5 = 4 := by 
      simp [pow_two, Int.mul_emod, h]
    omega 
  · -- Case m % 5 = 4
    have h3 : m^2 % 5 = 1 := by 
      simp [pow_two, Int.mul_emod, h]
    omega