import Mathlib

theorem algebra_326366 (x y : ℤ) :
    y^4 + 2 * x^4 + 1 = 4 * x^2 * y ↔ (x = 1 ∧ y = 1) ∨ (x = -1 ∧ y = 1) := by
  constructor
  · -- Forward implication.
    intro h
    have h1 : (y - x^2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (y^2 - 2 * x^2), sq_nonneg (y - x^2), sq_nonneg (y + x^2), sq_nonneg (x^2 - 1), sq_nonneg (x), sq_nonneg (y - 1), sq_nonneg (x^2 - 2), sq_nonneg (y + 1), sq_nonneg (y * (y - 2 * x^2) ), sq_nonneg ((x^2 * (x^2 - 1) ) ) ]
    have h2 : y = x^2 := by
      nlinarith 
    have h3 : x^4 = 1 := by
      rw [show y = x^2 by linarith [h2]] at h
      nlinarith [sq_nonneg (x^4 - 1), sq_nonneg (x^2 - 1), sq_nonneg (x^2), sq_nonneg (x ^ 2 - 1), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg ((x^2 - 1) * (x^2 + 1) ) ]
    have h4 : x^2 = 1 := by 
      have h5 : x^4 = 1 := h3
      have h6 : x^2 = 1 := by
        nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (x^2 + 1), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2) ]
      assumption
    have h5 : x = 1 ∨ x = -1 := by
      have h6 : x^2 = 1 := h4
      have : x = 1 ∨ x = -1 := by 
        have h3 : x^2 = 1 := h6
        have : x = 1 ∨ x = -1 := by 
          rw [sq_eq_one_iff] at h3 
          tauto 
        assumption 
      assumption 
    have h6 : y = 1 := by 
      have h7 : x^2 = 1 := h4
      nlinarith [h2, h7]
    rcases h5 with (h7 | h8)
    · -- If x = 1.
      left 
      constructor
      · linarith 
      · linarith [h6]
    · -- If x = -1.
      right 
      constructor 
      · linarith 
      · linarith [h6]
  · -- Backward implication.
    rintro (h | h)
    · -- (1, 1)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- (-1, 1)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num