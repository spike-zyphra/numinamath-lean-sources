import Mathlib

theorem algebra_93391 (m n : ℤ) :
    m^3 + 6 * m^2 + 5 * m = 27 * n^3 + 27 * n^2 + 9 * n + 1 ↔ False := by
  constructor
  · -- Assume the equation is true, then derive False
    intro h
    have h1 : m^3 + 6 * m^2 + 5 * m = 27 * n^3 + 27 * n^2 + 9 * n + 1 := h
    have h2 : (m^3 + 6 * m^2 + 5 * m) % 9 = 1 % 9 := by
      omega
    have h3 : m % 9 = 0 ∨ m % 9 = 1 ∨ m % 9 = 2 ∨ m % 9 = 3 ∨ m % 9 = 4 ∨ m % 9 = 5 ∨ m % 9 = 6 ∨ m % 9 = 7 ∨ m % 9 = 8 := by
      omega
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3)
    · -- m % 9 = 0
      have h4 : (m ^ 3 + 6 * m ^ 2 + 5 * m) % 9 = 0 := by
        simp [pow_succ, pow_zero, Int.mul_emod, add_assoc, Int.add_emod, Int.sub_emod, h3]
        <;> omega
      omega
    · -- m % 9 = 1
      have h4 : (m ^ 3 + 6 * m ^ 2 + 5 * m) % 9 = 3 := by
        simp [pow_succ, pow_zero, Int.mul_emod, add_assoc, Int.add_emod, Int.sub_emod, h3]
        <;> omega
      omega
    · -- m % 9 = 2
      have h4 : (m ^ 3 + 6 * m ^ 2 + 5 * m) % 9 = 6 := by
        simp [pow_succ, pow_zero, Int.mul_emod, add_assoc, Int.add_emod, Int.sub_emod, h3]
        <;> omega
      omega
    · -- m % 9 = 3
      have h4 : (m ^ 3 + 6 * m ^ 2 + 5 * m) % 9 = 6 := by
        simp [pow_succ, pow_zero, Int.mul_emod, add_assoc, Int.add_emod, Int.sub_emod, h3]
        <;> omega
      omega
    · -- m % 9 = 4
      have h4 : (m ^ 3 + 6 * m ^ 2 + 5 * m) % 9 = 0 := by
        simp [pow_succ, pow_zero, Int.mul_emod, add_assoc, Int.add_emod, Int.sub_emod, h3]
        <;> omega
      omega
    · -- m % 9 = 5
      have h4 : (m ^ 3 + 6 * m ^ 2 + 5 * m) % 9 = 3 := by
        simp [pow_succ, pow_zero, Int.mul_emod, add_assoc, Int.add_emod, Int.sub_emod, h3]
        <;> omega
      omega
    · -- m % 9 = 6
      have h4 : (m ^ 3 + 6 * m ^ 2 + 5 * m) % 9 = 3 := by
        simp [pow_succ, pow_zero, Int.mul_emod, add_assoc, Int.add_emod, Int.sub_emod, h3]
        <;> omega
      omega
    · -- m % 9 = 7
      have h4 : (m ^ 3 + 6 * m ^ 2 + 5 * m) % 9 = 6 := by
        simp [pow_succ, pow_zero, Int.mul_emod, add_assoc, Int.add_emod, Int.sub_emod, h3]
        <;> omega
      omega
    · -- m % 9 = 8
      have h4 : (m ^ 3 + 6 * m ^ 2 + 5 * m) % 9 = 0 := by
        simp [pow_succ, pow_zero, Int.mul_emod, add_assoc, Int.add_emod, Int.sub_emod, h3]
        <;> omega
      omega
  · -- Assume False, prove anything
    intro h
    cases h