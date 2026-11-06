import Mathlib

theorem algebra_163566 (a b : ℕ) : a * b + 2 = a ^ 3 + 2 * b ↔
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 1) ∨ (a = 3 ∧ b = 25) ∨
    (a = 4 ∧ b = 31) ∨ (a = 5 ∧ b = 41) ∨ (a = 8 ∧ b = 85) := by
  constructor
  · -- Forward implication: equation to solutions
    intro h
    have h1 : a * b + 2 = a ^ 3 + 2 * b := by linarith
    have h2 : a ≤ 8 := by
      by_contra h3
      push_neg at h3
      have h4 : b ≤ a ^ 2 + 2 * a + 4 := by
        by_cases hne : a > 2
        · -- Assume a > 2.
          nlinarith [sq_nonneg (a - 2 : ℕ), sq_nonneg (a + 2 : ℕ), sq_nonneg (b : ℕ)]
        · -- a ≤ 2
          have ha2 : a ≤ 2 := by omega
          interval_cases a <;> omega
          all_goals nlinarith
      have h5 : a ≥ 9 := by omega
      nlinarith [h1, h4, sq_pos_of_pos (show 0 < a by nlinarith), sq_nonneg (a - 2 : ℕ), sq_nonneg (a + 2 : ℕ), sq_nonneg (b : ℕ), sq_nonneg ((a : ℕ) * (a - 2 : ℕ)), sq_nonneg ((a - 2 : ℕ) * (b : ℕ))]
    interval_cases a <;> omega
    <;> norm_num at h1 <;> omega
  · -- Backward implication: solutions to the equation
    rintro (h | h | h | h | h | h)
    · -- First pair (0,1)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Second pair (1,1)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Third pair (3,25)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Fourth pair (4,31)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Fifth pair (5,41)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Sixth pair (8,85)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num