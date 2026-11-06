import Mathlib


theorem algebra_264120 (k : ℝ) (α β : ℝ) (h₁ : α ≠ β) (h₂ : 7 * α ^ 2 - (k + 13) * α + k ^ 2 - k - 2 = 0)
    (h₃ : 7 * β ^ 2 - (k + 13) * β + k ^ 2 - k - 2 = 0) (h₄ : 0 < α ∧ α < 1) (h₅ : 1 < β ∧ β < 2) :
    3 < k ∧ k < 4 ∨ -2 < k ∧ k < -1 := by
  have h4 : 0 < α := h₄.1
  have h5 : α < 1 := h₄.2
  have h6 : 1 < β := h₅.1
  have h7 : β < 2 := h₅.2
  have h8 : k ^ 2 - k - 2 > 0 := by
    nlinarith [sq_pos_of_pos (show 0 < α by linarith), sq_pos_of_pos (show 0 < β - 1 by linarith), sq_nonneg (α - 1), sq_nonneg (β - 1)]
  have h9 : k ^ 2 - 2 * k - 8 < 0 := by
    nlinarith [sq_pos_of_pos (show 0 < α by linarith), sq_pos_of_pos (show 0 < β - 1 by linarith), sq_nonneg (α - 1), sq_nonneg (β - 1)]
  have h10 : k ^ 2 - 3 * k > 0 := by
    nlinarith [sq_pos_of_pos (show 0 < β - 1 by linarith), sq_nonneg (α - 1), sq_nonneg (β - 1), sq_pos_of_pos (show 0 < β - 1 by linarith)]
  have h91 : -2 < k := by
    nlinarith
  have h92 : k < 4 := by
    nlinarith
  have h93 : k < -1 ∨ k > 2 := by
    by_contra h
    push_neg at h
    nlinarith
  have h94 : k < 0 ∨ k > 3 := by
    by_contra h
    push_neg at h
    nlinarith
  rcases h93 with h93 | h93
  · -- We need to derive $-2 < k ∧ k < -1$
    right
    constructor
    · -- $-2 < k$
      nlinarith
    · -- $k < -1$
      nlinarith
  · -- We need to derive $3 < k ∧ k < 4$
    left
    constructor
    · -- $3 < k$
      rcases h94 with h94 | h94
      · -- $k < 0$
        nlinarith
      · -- $k > 3$
        nlinarith
    · -- $k < 4$
      nlinarith