import Mathlib

theorem number_theory_44683 (a n : ℕ) (ha : 0 < a) (hn : 0 < n)
    (h : a ≥ n ∧ n ≥ 2) :
    ∃ k, (a + 1)^n + a - 1 = 2^k ↔ (a, n) = (3, 4) := by

  use 1

  have h1 : a ≥ n := h.1
  have h2 : n ≥ 2 := h.2

  simp [Prod.ext_iff] at *
  constructor
  · -- Forward direction
    intro h_eq

    have h_eq1 : (a + 1) ^ n + a = 3 := by
      omega

    have h3 : (a + 1) ^ n ≥ (a + 1) ^ 2 := by
      have h4 : n ≥ 2 := h2
      have : (a + 1) ^ n ≥ (a + 1) ^ 2 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals
          omega
      linarith

    have h6 : (a + 1) ^ n ≥ 9 := by
      have h7 : a ≥ 2 := by
        omega
      have h8 : (a + 1) ^ 2 ≥ 9 := by
        have h9 : a + 1 ≥ 3 := by
          omega
        have h10 : (a + 1) ^ 2 ≥ 3 ^ 2 := by
          apply Nat.pow_le_pow_left
          all_goals
            omega
        have h11 : 3 ^ 2 = 9 := by norm_num
        omega
      have h9 : (a + 1) ^ n ≥ (a + 1) ^ 2 := h3
      linarith

    have h7 : a ≥ 2 := by
      omega

    have h8 : (a + 1) ^ n + a ≥ 11 := by
      have h9 : (a + 1) ^ n ≥ 9 := h6
      have h10 : a ≥ 2 := by omega
      omega

    omega

  · -- Backward direction
    rintro ⟨rfl, rfl⟩
    exfalso
    omega