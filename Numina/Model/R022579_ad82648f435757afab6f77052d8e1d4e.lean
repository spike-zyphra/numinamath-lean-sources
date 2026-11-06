import Mathlib

theorem algebra_311442 (a : ℤ) :
    ∃ x : ℤ, (a + 1) * x ^ 2 - (a ^ 2 + 1) * x + 2 * a ^ 3 - 6 = 0 ↔
    a = -1 ∨ a = 0 ∨ a = 1 := by
  by_cases h : a = -1 ∨ a = 0 ∨ a = 1
  · -- Assume a = -1 ∨ a = 0 ∨ a = 1.
    rcases h with (h | h | h)
    · -- Case a = -1
      rw [show a = -1 by exact h]
      use -4
      norm_num
    · -- Case a = 0
      rw [show a = 0 by exact h]
      use 3
      norm_num
    · -- Case a = 1
      rw [show a = 1 by exact h]
      use 2
      norm_num
  · -- Assume ¬(a = -1 ∨ a = 0 ∨ a = 1).
    push_neg at h
    use 0
    constructor
    · -- Prove the forward implication
      intro h_eq
      have h_eq' : 2 * a ^ 3 = 6 := by
        nlinarith
      have h_eq1 : a ^ 3 = 3 := by
        linarith
      have h2 : a ≤ 1 := by
        nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a - 1), sq_nonneg (a + 1)]
      have h3 : a ≥ 1 := by
        nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a - 1), sq_nonneg (a + 1)]
      have h_eq4 : a = 1 := by
        nlinarith
      have h1' : a = 1 := by linarith
      exfalso
      tauto
    · -- Prove the backward implication
      intro h_eq
      rcases h_eq with (h_eq1 | h_eq2 | h_eq3)
      all_goals
        exfalso
        tauto