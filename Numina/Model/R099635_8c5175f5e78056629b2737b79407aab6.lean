import Mathlib

theorem algebra_1437 {x : ℝ} (hx : x ≠ 0) (h : -1 / (-x) = 1 / 19) : x = 19 := by
  have h1 : -1 / (-x) = 1 / x := by
    field_simp [hx]
    <;> ring
  rw [h1] at h
  have h2 : x = 19 := by
    field_simp [show x ≠ 0 by exact hx] at h ⊢
    linarith
  exact h2