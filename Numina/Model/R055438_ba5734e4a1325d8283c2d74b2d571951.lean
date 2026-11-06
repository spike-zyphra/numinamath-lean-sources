import Mathlib

theorem algebra_10432 {x : ℝ} (hx : x ≠ 0) (h : (1 / 2 - 1 / 3) = 1 / x) : x = 6 := by
  have h1 : (1 / 2 : ℝ) - 1 / 3 = 1 / 6 := by
    norm_num
  rw [h1] at h
  have h2 : x = 6 := by
    field_simp [hx] at h ⊢
    linarith
  exact h2