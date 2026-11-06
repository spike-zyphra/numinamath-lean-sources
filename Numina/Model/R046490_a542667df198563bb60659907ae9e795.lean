import Mathlib

theorem number_theory_6269 (x : ℤ) :
    x^5 - 3 * x^2 + 2 ≡ 0 [ZMOD 7] ↔ x ≡ 1 [ZMOD 7] ∨ x ≡ 5 [ZMOD 7] := by
  constructor
  · -- Assume x^5 - 3 * x^2 + 2 ≡ 0 [ZMOD 7], prove x ≡ 1 [ZMOD 7] ∨ x ≡ 5 [ZMOD 7]
    intro h
    have h1 : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [Int.ModEq, pow_two, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod, h1] at h ⊢ <;> try { tauto }
  · -- Assume x ≡ 1 [ZMOD 7] ∨ x ≡ 5 [ZMOD 7], prove x^5 - 3 * x^2 + 2 ≡ 0 [ZMOD 7]
    rintro (h | h)
    · -- Assume x ≡ 1 [ZMOD 7]
      have h1 : x % 7 = 1 := h
      simp [Int.ModEq, pow_two, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod, h1]
    · -- Assume x ≡ 5 [ZMOD 7]
      have h1 : x % 7 = 5 := h
      simp [Int.ModEq, pow_two, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod, h1]