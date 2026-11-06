import Mathlib

theorem algebra_88865 :
    {a : ℤ | 15 ∣ (5 * a + 1) * (3 * a + 2)} = {a | a ≡ 1 [ZMOD 15]} := by
  ext a
  simp [Int.ModEq]
  constructor
  · -- Assume that 15 divides (5a + 1)(3a + 2), prove that a ≡ 1 [ZMOD 15]
    intro h
    have h1 : (5 * a + 1) * (3 * a + 2) % 15 = 0 := by
      omega
    have h2 : a % 15 = 1 := by
      have h2 : a % 15 = 0 ∨ a % 15 = 1 ∨ a % 15 = 2 ∨ a % 15 = 3 ∨ a % 15 = 4 ∨ a % 15 = 5 ∨ a % 15 = 6 ∨ a % 15 = 7 ∨ a % 15 = 8 ∨ a % 15 = 9 ∨ a % 15 = 10 ∨ a % 15 = 11 ∨ a % 15 = 12 ∨ a % 15 = 13 ∨ a % 15 = 14 := by
        omega
      rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [h2, Int.add_emod, Int.mul_emod, Int.sub_emod] at h1 <;> omega
    omega
  · -- Assume that a ≡ 1 [ZMOD 15], prove that 15 divides (5a + 1)(3a + 2)
    intro h
    have h1 : a % 15 = 1 := by
      omega
    have h2 : (5 * a + 1) * (3 * a + 2) % 15 = 0 := by
      have h2 : a % 15 = 1 := h1
      simp [h2, Int.add_emod, Int.mul_emod, Int.sub_emod]
      all_goals omega
    omega