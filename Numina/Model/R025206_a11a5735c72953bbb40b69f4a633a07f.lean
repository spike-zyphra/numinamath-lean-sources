import Mathlib

theorem number_theory_172690 (a : ℕ) (ha : a > 0) :
    ¬(2 ∣ a^2 - a + 1 ∧ 2 ∣ a^2 + a - 1) ∧ ¬(3 ∣ a^2 - a + 1 ∧ 3 ∣ a^2 + a - 1) := by
  constructor
  · -- Assume both 2 divides a^2 - a + 1 and 2 divides a^2 + a - 1
    intro h
    have h1 : 2 ∣ a^2 - a + 1 := h.1
    have h2 : 2 ∣ a^2 + a - 1 := h.2
    have h3 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rcases h3 with (h3 | h3)
    · -- If a is even
      have h4 : a % 2 = 0 := h3
      have eq1 : (a ^ 2 - a + 1) % 2 = 1 := by
        have h6 : a % 2 = 0 := h3
        have h7 : a ^ 2 % 2 = 0 := by
          simp [Nat.pow_mod, h6]
        omega
      omega
    · -- If a is odd
      have h4 : a % 2 = 1 := h3
      have eq1 : (a ^ 2 - a + 1) % 2 = 1 := by
        have h6 : a % 2 = 1 := h4
        have h7 : a ^ 2 % 2 = 1 := by
          simp [Nat.pow_mod, h6]
        omega
      omega
  · -- Assume both 3 divides a^2 - a + 1 and 3 divides a^2 + a - 1
    intro h
    have h1 : 3 ∣ a^2 - a + 1 := h.left
    have h2 : 3 ∣ a^2 + a - 1 := h.right
    have h3 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases h3 with (h3 | h3 | h3)
    · -- If a % 3 = 0
      have h5 : a % 3 = 0 := h3
      have eq1 : (a ^ 2 - a + 1) % 3 = 1 := by
        have h6 : a % 3 = 0 := h5
        have h7 : a ^ 2 % 3 = 0 := by
          simp [Nat.pow_mod, h6]
        omega
      omega
    · -- If a % 3 = 1
      have h5 : a % 3 = 1 := h3
      have eq1 : (a ^ 2 - a + 1) % 3 = 1 := by
        have h6 : a % 3 = 1 := h5
        have h7 : a ^ 2 % 3 = 1 := by
          simp [Nat.pow_mod, h6]
        omega
      omega
    · -- If a % 3 = 2
      have h5 : a % 3 = 2 := h3
      have eq1 : (a ^ 2 + a - 1) % 3 = 2 := by
        have h6 : a % 3 = 2 := h5
        have h7 : a ^ 2 % 3 = 1 := by
          simp [Nat.pow_mod, h6]
        omega
      omega