import Mathlib

theorem algebra_208851 (a r : ℝ) (h₀ : a ≠ 0) (h₁ : r ≠ 0)
    (h₂ : a = 3) (h₃ : a * r = 6) :
    a * r^4 = 48 := by
  have hr : r = 2 := by
    rw [h₂] at h₃
    have : r = 2 := by
      linarith
    assumption

  rw [h₂, hr]
  norm_num
  all_goals nlinarith