import Mathlib

theorem number_theory_232758 : ¬ ∃ x y : ℤ, 5 * x ^ 2 - 4 * y ^ 2 = 2015 := by
  rintro ⟨x, y, h⟩
  have h1 : (5 * x ^ 2 - 4 * y ^ 2 : ℤ) % 4 = 2015 % 4 := by
    omega
  have h2 : (5 * x ^ 2 - 4 * y ^ 2 : ℤ) % 4 = (x ^ 2 : ℤ) % 4 := by
    ring_nf
    <;> omega
  have h3 : (x ^ 2 : ℤ) % 4 = 3 := by
    omega
  have h4 : (x ^ 2 : ℤ) % 4 = 0 ∨ (x ^ 2 : ℤ) % 4 = 1 := by
    have h5 : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by
      omega
    rcases h5 with (h5 | h5 | h5 | h5)
    · -- x % 4 = 0 
      have h6 : (x ^ 2 : ℤ) % 4 = 0 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h5, Int.mul_emod]
        all_goals omega
      omega
    · -- x % 4 = 1 
      have h6 : (x ^ 2 : ℤ) % 4 = 1 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h5, Int.mul_emod]
        all_goals omega
      omega
    · -- x % 4 = 2 
      have h6 : (x ^ 2 : ℤ) % 4 = 0 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h5, Int.mul_emod]
        all_goals omega
      omega
    · -- x % 4 = 3 
      have h6 : (x ^ 2 : ℤ) % 4 = 1 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h5, Int.mul_emod]
        all_goals omega
      omega
  omega