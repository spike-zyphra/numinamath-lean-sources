import Mathlib

theorem algebra_59468 (x : ℝ) (hx : x > 0) (h : (1 - 100 / x / 100) * (1 + y / 100) = 1) :
    y = 100 / (x - 1) := by
  have hx1 : x ≠ 0 := by linarith
  have h1 : (1 - 100 / x / 100) = (1 - 1 / x) := by
    field_simp [hx1]
    <;> ring_nf
  rw [h1] at h
  have hx3 : x - 1 ≠ 0 := by
    by_contra h4
    have h5 : x = 1 := by linarith
    rw [h5] at h
    norm_num at h
    all_goals linarith
  field_simp [show x - 1 ≠ 0 by assumption, show x ≠ 0 by linarith] at h ⊢
  <;> linarith