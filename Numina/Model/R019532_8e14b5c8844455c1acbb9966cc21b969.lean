import Mathlib

theorem algebra_168063 (x y : ℝ) (hx : x = 1.25 * y) (hy : y ≠ 0)
    (h : x - z = y + z) (hz : 0 < z) :
    z / x = 1 / 10 := by
  have h1 : z = (x - y) / 2 := by
    linarith
  have hy2 : y = 4 / 5 * x := by
    have h2 : x = 1.25 * y := hx
    ring_nf at h2
    linarith
  have h2 : z = 1 / 10 * x := by
    rw [h1]
    rw [hy2]
    ring_nf
  have hx2 : x ≠ 0 := by
    by_contra h3
    have h4 : x = 0 := by linarith
    have h5 : y = 0 := by
      have h2 : x = 1.25 * y := hx
      rw [h4] at h2
      norm_num at h2
      all_goals linarith
    have h6 : y ≠ 0 := hy
    contradiction
  have h3 : z / x = 1 / 10 := by
    have h4 : z = 1 / 10 * x := h2
    have h5 : x ≠ 0 := hx2
    have h6 : z / x = (1 / 10 * x) / x := by rw [h4]
    rw [h6]
    field_simp [h5]
    <;> ring
  exact h3