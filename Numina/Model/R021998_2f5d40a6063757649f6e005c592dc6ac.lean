import Mathlib

theorem algebra_71661 (a b : ℝ) :
    ∃ d, a = 10 + d ∧ b = a + d ∧ a * b = b + d ↔ (a = 4 ∧ b = -2) ∨ (a = 2.5 ∧ b = -5) := by
  use a - 10
  constructor
  · -- Forward direction
    intro h
    rcases h with ⟨h1, h2, h3⟩
    have h4 : b = 2 * a - 10 := by
      nlinarith 
    rw [show b = 2 * a - 10 by linarith [h4]] at h3
    have h41 : 2 * a ^ 2 - 13 * a + 20 = 0 := by
      linarith
    have h42 : (a - 4) * (2 * a - 5) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.1 h42) with ha1 ha2
    · -- Case 1: a - 4 = 0
      have ha4 : a = 4 := by linarith
      have hb4 : b = -2 := by
        linarith [h4, ha4]
      left
      exact ⟨by linarith, by linarith⟩
    · -- Case 2: 2 * a - 5 = 0
      have ha5 : a = 2.5 := by
        have h51 : 2 * a = 5 := by linarith
        linarith
      have hb5 : b = -5 := by
        linarith [h4, ha5]
      right
      exact ⟨by linarith, by linarith⟩
  · -- Backward direction
    rintro (h | h)
    · -- Case 1
      rcases h with ⟨ha4, hb4⟩
      constructor
      · -- a = 10 + (a - 10)
        linarith
      constructor
      · -- b = a + (a - 10)
        rw [show a = 4 by linarith [ha4], show b = -2 by linarith [hb4]]
        norm_num
      · -- a * b = b + (a - 10)
        rw [show a = 4 by linarith [ha4], show b = -2 by linarith [hb4]]
        norm_num
    · -- Case 2
      rcases h with ⟨ha5, hb5⟩
      constructor
      · -- a = 10 + (a - 10)
        linarith
      constructor
      · -- b = a + (a - 10)
        rw [show a = 2.5 by linarith [ha5], show b = -5 by linarith [hb5]]
        norm_num
      · -- a * b = b + (a - 10)
        rw [show a = 2.5 by linarith [ha5], show b = -5 by linarith [hb5]]
        norm_num