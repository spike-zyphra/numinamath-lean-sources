import Mathlib

theorem number_theory_154696 (n : ℤ) : ¬(3 ∣ n^2 + 1) ∧ ¬(4 ∣ n^2 + 1) := by
  constructor
  · -- Assume 3 divides n^2 + 1
    intro h
    have h1 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h1 with (h1 | h1 | h1)
    · -- Case n % 3 = 0
      have h2 : n ^ 2 % 3 = 0 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      have h3 : (n ^ 2 + 1) % 3 = 1 := by
        omega
      omega
    · -- Case n % 3 = 1
      have h2 : n ^ 2 % 3 = 1 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      have h3 : (n ^ 2 + 1) % 3 = 2 := by
        omega
      omega
    · -- Case n % 3 = 2
      have h2 : n ^ 2 % 3 = 1 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      have h3 : (n ^ 2 + 1) % 3 = 2 := by
        omega
      omega
  · -- Assume 4 divides n^2 + 1
    intro h
    have h1 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases h1 with (h1 | h1 | h1 | h1)
    · -- Case n % 4 = 0
      have h2 : n ^ 2 % 4 = 0 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      have h3 : (n ^ 2 + 1) % 4 = 1 := by
        omega
      omega
    · -- Case n % 4 = 1
      have h2 : n ^ 2 % 4 = 1 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      have h3 : (n ^ 2 + 1) % 4 = 2 := by
        omega
      omega
    · -- Case n % 4 = 2
      have h2 : n ^ 2 % 4 = 0 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      have h3 : (n ^ 2 + 1) % 4 = 1 := by
        omega
      omega
    · -- Case n % 4 = 3
      have h2 : n ^ 2 % 4 = 1 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      have h3 : (n ^ 2 + 1) % 4 = 2 := by
        omega
      omega