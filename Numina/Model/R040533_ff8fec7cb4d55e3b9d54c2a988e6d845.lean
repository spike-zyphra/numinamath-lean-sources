import Mathlib

theorem algebra_94802 {x y : ℝ} (hy : y = x + 1 / x) :
    x ^ 4 + x ^ 3 - 4 * x ^ 2 + x + 1 = 0 → x ^ 2 * (y ^ 2 + y - 6) = 0 := by
  intro h
  have hx : x ≠ 0 := by
    by_contra h1
    have h0 : x = 0 := by linarith
    rw [h0] at h
    norm_num at h
  have h_eq : x ^ 2 * (y ^ 2 + y - 6) = x ^ 4 + x ^ 3 - 4 * x ^ 2 + x + 1 := by
    rw [hy]
    field_simp [hx]
    ring
  rw [h_eq]
  all_goals linarith [h]