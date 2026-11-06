import Mathlib

theorem number_theory_69802 (n : ℤ) : 12 ∣ n^2 * (n^2 - 1) := by 
  have h1 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  have h2 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  have h3 : n^2 * (n^2 - 1) % 3 = 0 := by
    rcases h1 with (h1 | h1 | h1)
    · -- n % 3 = 0
      simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- n % 3 = 1
      simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- n % 3 = 2
      simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
  have h4 : n^2 * (n^2 - 1) % 4 = 0 := by
    rcases h2 with (h2 | h2 | h2 | h2)
    · -- n % 4 = 0
      simp [h2, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- n % 4 = 1
      simp [h2, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- n % 4 = 2
      simp [h2, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- n % 4 = 3
      simp [h2, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
  omega