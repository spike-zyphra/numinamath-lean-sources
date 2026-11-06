import Mathlib

theorem algebra_284233 {x : ℝ} (hx : x > 0) (h : 1 / x = 75 / (x + 3) ∧ 1 / x = 5 / 6 * (x - 3)) :
    x = 5 / 3 := by
  rcases h with ⟨h1, h2⟩
  have h3 : x + 3 ≠ 0 := by linarith
  have h4 : x ≠ 0 := by
    by_contra h'
    rw [h'] at h1 h2
    all_goals
      norm_num at h1 h2
  field_simp [h4] at h1 h2
  nlinarith [sq_nonneg (x - 3 / 74)]