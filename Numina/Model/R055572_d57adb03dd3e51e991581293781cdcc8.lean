import Mathlib

open Real Set

theorem inequalities_36499 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x + y + x * y = 3) :
    x + y ≥ 2 ∧ (x + y = 2 ↔ x = 1 ∧ y = 1) := by 
  constructor
  · -- Prove the inequality
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x * y - 1), mul_pos hx hy]
  · -- Now prove the equivalence
    constructor
    · -- Show that if x + y = 2, then x = 1 ∧ y = 1
      intro h2
      have h2' : x * y = 1 := by
        nlinarith
      have h3' : x = 1 := by 
        have h4 : x ^ 2 - 2 * x + 1 = 0 := by
          have h5 : y = 2 - x := by linarith
          rw [h5] at h2'
          nlinarith
        have h6 : (x - 1) ^ 2 = 0 := by linarith
        have h7 : x - 1 = 0 := by
          apply pow_eq_zero 
          exact h6
        linarith
      have h4' : y = 1 := by 
        nlinarith [h3']
      exact ⟨h3', h4'⟩
    · -- Show the reverse implication
      rintro ⟨rfl, rfl⟩
      norm_num