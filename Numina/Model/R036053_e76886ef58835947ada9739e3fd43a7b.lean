import Mathlib
theorem algebra_794 {f : ℝ → ℝ} (h : 7 = 3 * f (2 * 4) + 1) :
    ∃ x y, y = f x ∧ x + y = 10 := by
  have h1 : f (2 * (4 : ℝ)) = 2 := by
    norm_num at h ⊢
    linarith
  use 8, 2
  constructor
  · -- Show that 2 = f(8).
    rw [show f (8 : ℝ) = 2 by
      norm_num at h1 ⊢
      linarith
    ]
    all_goals norm_num
  · -- Show that 8 + 2 = 10.
    norm_num