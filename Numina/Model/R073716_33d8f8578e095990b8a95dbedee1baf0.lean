import Mathlib

theorem number_theory_151106 (a : ℤ) : 5 ∣ a^3 + 3 * a + 1 ↔ a ≡ 1 [ZMOD 5] ∨ a ≡ 2 [ZMOD 5] := by
  constructor
  · -- Assume 5 divides a^3 + 3a + 1, prove a ≡ 1 [ZMOD 5] ∨ a ≡ 2 [ZMOD 5]
    intro h
    have h1 : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1)
    · -- a % 5 = 0
      have h2 : (a ^ 3 + 3 * a + 1) % 5 = 1 := by
        simp [pow_succ, Int.add_emod, Int.mul_emod, Int.emod_self, h1]
        all_goals omega
      omega
    · -- a % 5 = 1
      have h2 : (a ^ 3 + 3 * a + 1) % 5 = 0 := by
        simp [pow_succ, Int.add_emod, Int.mul_emod, Int.emod_self, h1]
        all_goals omega
      left
      show a ≡ 1 [ZMOD 5]
      exact h1
    · -- a % 5 = 2
      have h2 : (a ^ 3 + 3 * a + 1) % 5 = 0 := by
        simp [pow_succ, Int.add_emod, Int.mul_emod, Int.emod_self, h1]
        all_goals omega
      right
      show a ≡ 2 [ZMOD 5]
      exact h1
    · -- a % 5 = 3
      have h2 : (a ^ 3 + 3 * a + 1) % 5 = 2 := by
        simp [pow_succ, Int.add_emod, Int.mul_emod, Int.emod_self, h1]
        all_goals omega
      omega
    · -- a % 5 = 4
      have h2 : (a ^ 3 + 3 * a + 1) % 5 = 2 := by
        simp [pow_succ, Int.add_emod, Int.mul_emod, Int.emod_self, h1]
        all_goals omega
      omega
  · -- Assume a ≡ 1 [ZMOD 5] ∨ a ≡ 2 [ZMOD 5], prove 5 divides a^3 + 3a + 1
    rintro (h | h)
    · -- a ≡ 1 [ZMOD 5]
      have h1 : a % 5 = 1 := h
      have : (a ^ 3 + 3 * a + 1) % 5 = 0 := by
        simp [pow_succ, Int.add_emod, Int.mul_emod, Int.emod_self, h1]
        all_goals omega
      exact Int.dvd_of_emod_eq_zero this
    · -- a ≡ 2 [ZMOD 5]
      have h1 : a % 5 = 2 := h
      have : (a ^ 3 + 3 * a + 1) % 5 = 0 := by
        simp [pow_succ, Int.add_emod, Int.mul_emod, Int.emod_self, h1]
        all_goals omega
      exact Int.dvd_of_emod_eq_zero this