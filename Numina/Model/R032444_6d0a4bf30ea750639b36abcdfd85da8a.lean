import Mathlib

theorem number_theory_6902 (a : ℤ) (ha : Odd a) : 24 ∣ a * (a^2 - 1) := by

  have h2 : (a * (a ^ 2 - 1)) % 8 = 0 := by
    have h1' : a % 2 = 1 := by
      obtain ⟨k, hk⟩ := ha
      omega
    have h3 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
      omega
    rcases h3 with (h3 | h3 | h3 | h3)
    · -- a % 8 = 1
      simp [Int.add_emod, Int.mul_emod, Int.sub_emod, pow_two, pow_succ, h3]
    · -- a % 8 = 3
      simp [Int.add_emod, Int.mul_emod, Int.sub_emod, pow_two, pow_succ, h3]
    · -- a % 8 = 5
      simp [Int.add_emod, Int.mul_emod, Int.sub_emod, pow_two, pow_succ, h3]
    · -- a % 8 = 7
      simp [Int.add_emod, Int.mul_emod, Int.sub_emod, pow_two, pow_succ, h3]

  have h3 : (a * (a ^ 2 - 1)) % 3 = 0 := by
    have h4 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by
      omega
    rcases h4 with (h4 | h4 | h4)
    · -- a % 3 = 0
      simp [Int.add_emod, Int.mul_emod, Int.sub_emod, pow_two, pow_succ, h4]
    · -- a % 3 = 1
      simp [Int.add_emod, Int.mul_emod, Int.sub_emod, pow_two, pow_succ, h4]
    · -- a % 3 = 2
      simp [Int.add_emod, Int.mul_emod, Int.sub_emod, pow_two, pow_succ, h4]

  omega