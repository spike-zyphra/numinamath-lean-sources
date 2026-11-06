import Mathlib

open Int

theorem number_theory_4652 (a : ℤ) (h₀ : Odd a) : a^2 ≡ 1 [ZMOD 8] := by
  have h1 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
    have h2 : a % 2 = 1 := by
      obtain ⟨k, hk⟩ := h₀
      omega
    omega
  rcases h1 with (h | h | h | h)
  · -- a % 8 = 1
    simp [Int.ModEq, pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
  · -- a % 8 = 3
    simp [Int.ModEq, pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
  · -- a % 8 = 5
    simp [Int.ModEq, pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
  · -- a % 8 = 7
    simp [Int.ModEq, pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]