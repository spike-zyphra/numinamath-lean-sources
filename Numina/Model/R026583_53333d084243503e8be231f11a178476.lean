import Mathlib

theorem algebra_18697 {x : ℕ} (hx : x > 0) :
    x * (x + 1) * (x + 2) * (x + 3) + 1 = 379 ^ 2 ↔ x = 18 := by 
  constructor
  · -- Forward implication: if the equation holds, then x = 18
    intro h
    have h1 : x * (x + 1) * (x + 2) * (x + 3) + 1 = 379 ^ 2 := h
    have h2 : x * (x + 1) * (x + 2) * (x + 3) = 143640 := by
      nlinarith 
    have h3 : x ≤ 20 := by
      by_contra h4
      push_neg at h4
      have h4' : x * (x + 1) * (x + 2) * (x + 3) ≥ 21 * 22 * 23 * 24 := by
        have h5 : x ≥ 21 := by
          omega
        have h6 : x + 1 ≥ 22 := by
          omega
        have h7 : x + 2 ≥ 23 := by
          omega
        have h8 : x + 3 ≥ 24 := by
          omega
        have h9 : x * (x + 1) * (x + 2) * (x + 3) ≥ 21 * 22 * 23 * 24 := by
          apply Nat.mul_le_mul
          apply Nat.mul_le_mul
          apply Nat.mul_le_mul
          all_goals omega
        linarith
      nlinarith
    interval_cases x <;> omega
  · -- Backward implication: if x = 18, then the equation holds
    intro h
    rw [h]
    all_goals
      norm_num