import Mathlib

theorem algebra_300321 (p : ℤ) (x : ℤ) :
    x^2 - 2 * x - (10 * p^2 + 10 * p + 2) ≠ 0 := by
  rintro h
  have h1 : (x - 1 : ℤ) ^ 2 = 10 * p^2 + 10 * p + 3 := by
    nlinarith
  have h2 : (x - 1 : ℤ) ^ 2 % 5 = 0 ∨ (x - 1 : ℤ) ^ 2 % 5 = 1 ∨ (x - 1 : ℤ) ^ 2 % 5 = 4 := by
    have h3 : (x - 1) % 5 = 0 ∨ (x - 1) % 5 = 1 ∨ (x - 1) % 5 = 2 ∨ (x - 1) % 5 = 3 ∨ (x - 1) % 5 = 4 := by
      omega
    rcases h3 with (h3 | h3 | h3 | h3 | h3)
    · -- case (x - 1) % 5 = 0
      simp [pow_two, Int.add_emod, Int.mul_emod, h3, Int.sub_emod]
    · -- case (x - 1) % 5 = 1
      simp [pow_two, Int.add_emod, Int.mul_emod, h3, Int.sub_emod]
    · -- case (x - 1) % 5 = 2
      simp [pow_two, Int.add_emod, Int.mul_emod, h3, Int.sub_emod]
    · -- case (x - 1) % 5 = 3
      simp [pow_two, Int.add_emod, Int.mul_emod, h3, Int.sub_emod]
    · -- case (x - 1) % 5 = 4
      simp [pow_two, Int.add_emod, Int.mul_emod, h3, Int.sub_emod]
  have h3 : (10 * p^2 + 10 * p + 3 : ℤ) % 5 = 3 := by
    ring_nf
    <;> omega
  have h4 : (x - 1 : ℤ) ^ 2 % 5 = 3 := by
    omega
  omega