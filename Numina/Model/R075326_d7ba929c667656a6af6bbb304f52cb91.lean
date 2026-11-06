import Mathlib

theorem algebra_325140 (h : ∀ x y, x * (y + 1) = 1) :
    y = -x + Real.sqrt 2 - 1 ∨ y = -x - Real.sqrt 2 - 1 := by
  have h1 := h 0 0
  norm_num at h1
  all_goals
    norm_num at h1 ⊢
    all_goals
      exfalso
      exact h1