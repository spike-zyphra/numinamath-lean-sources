import Mathlib

theorem number_theory_225477 (a : ℤ) (h : Odd a) : 48 ∣ a^3 + 3 * a^2 - a - 3 := by
  have h1 : a % 2 = 1 := by
    obtain ⟨k, hk⟩ := h
    omega
  have h3 : (a ^ 3 + 3 * a ^ 2 - a - 3) % 3 = 0 := by
    have h2 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by
      omega
    rcases h2 with (h2 | h2 | h2)
    · -- a % 3 = 0
      simp [h2, pow_two, pow_three, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- a % 3 = 1
      simp [h2, pow_two, pow_three, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- a % 3 = 2
      simp [h2, pow_two, pow_three, Int.add_emod, Int.mul_emod, Int.sub_emod]
  have h4 : (a ^ 3 + 3 * a ^ 2 - a - 3) % 16 = 0 := by
    have ha8 : a % 16 = 1 ∨ a % 16 = 3 ∨ a % 16 = 5 ∨ a % 16 = 7 ∨ a % 16 = 9 ∨ a % 16 = 11 ∨ a % 16 = 13 ∨ a % 16 = 15 := by
      have : a % 2 = 1 := h1
      omega
    rcases ha8 with (h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8)
    · -- a % 16 = 1
      simp [h8, pow_two, pow_three, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- a % 16 = 3
      simp [h8, pow_two, pow_three, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- a % 16 = 5
      simp [h8, pow_two, pow_three, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- a % 16 = 7
      simp [h8, pow_two, pow_three, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- a % 16 = 9
      simp [h8, pow_two, pow_three, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- a % 16 = 11
      simp [h8, pow_two, pow_three, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- a % 16 = 13
      simp [h8, pow_two, pow_three, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- a % 16 = 15
      simp [h8, pow_two, pow_three, Int.add_emod, Int.mul_emod, Int.sub_emod]
  omega