import Mathlib

theorem algebra_176713 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h1 : 1 / x + 1 / y = 1 / 2.4) (h2 : 1 / (x * (1 / 4)) + 1 / (y * (1 / 4)) = 11 / 24) :
    x = 4 ∧ y = 4 := by
  have h3 : 1 / (x * (1 / 4)) + 1 / (y * (1 / 4)) = 4 * (1 / x + 1 / y) := by
    field_simp at *
    <;> ring_nf <;> field_simp <;> ring_nf
  rw [h3] at h2
  have h4 : (1 / x + 1 / y) = (5 / 12 : ℝ) := by
    have h5 : (1 / x + 1 / y) = (1 / (2.4 : ℝ)) := by linarith
    rw [h5]
    norm_num
  rw [h4] at h2
  norm_num at h2 ⊢
  all_goals
    linarith