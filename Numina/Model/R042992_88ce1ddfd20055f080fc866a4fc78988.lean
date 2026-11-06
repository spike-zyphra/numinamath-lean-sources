import Mathlib

theorem algebra_177010 (x : ℝ) (hx : x > 0) (h : 1800 / x = 1800 / (x * (1 - 20 / x)) + 1) :
    x = 100 := by
  have eq1 : x * (1 - 20 / x) = x - 20 := by
    field_simp
    <;> ring_nf

  have hx1 : x - 20 ≠ 0 := by
    by_contra h1
    have h2 : x = 20 := by linarith
    rw [h2] at h
    norm_num [h2] at h
    all_goals linarith

  have h1 : 1800 / (x * (1 - 20 / x)) = 1800 / (x - 20) := by
    rw [eq1]

  rw [h1] at h

  have h2 : x ≠ 0 := by linarith
  have h2a : x - 20 ≠ 0 := hx1

  field_simp [h2, h2a] at h

  have h3 : (x - 100) * (x + 20) = 0 := by
    nlinarith [sq_pos_of_pos hx, sq_nonneg (x - 20), sq_nonneg (x), sq_nonneg ((x - 100)), sq_nonneg (x + 20)]

  cases' (mul_eq_zero.mp h3) with h4 h5

  · -- x - 100 = 0
    linarith

  · -- x + 20 = 0
    linarith