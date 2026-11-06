import Mathlib

theorem algebra_20219 {x y z w : ℝ} (hxy : x / y = 3) (hyz : y / z = 8) (hzw : z / w = 1 / 2) :
    w / x = 1 / 12 := by
  have h1 : y ≠ 0 := by
    by_contra h
    rw [h] at hxy
    norm_num at hxy
  have hx_eq : x = 3 * y := by
    have h2 : y ≠ 0 := h1
    field_simp [h2] at hxy ⊢
    linarith

  have h2 : z ≠ 0 := by
    by_contra h
    rw [h] at hyz
    norm_num at hyz
  have hy_eq : y = 8 * z := by
    have h3 : z ≠ 0 := h2
    field_simp [h3] at hyz ⊢
    linarith
  have hx_eq' : x = 24 * z := by
    rw [hx_eq]
    rw [hy_eq]
    all_goals ring
  have h3 : w ≠ 0 := by
    by_contra h
    rw [h] at hzw
    norm_num at hzw
  -- From hzw: z / w = 1 / 2, we can multiply both sides by w (since w ≠ 0) to get z = (1 / 2) * w, or w = 2 * z.
  have hw_eq : w = 2 * z := by
    have h4 : w ≠ 0 := h3
    field_simp [h4] at hzw ⊢
    linarith

  have h4 : x ≠ 0 := by
    intro h
    have h5 : z = 0 := by
      nlinarith [hx_eq', h, hy_eq]
    have h6 : z = 0 := h5
    contradiction

  have hw_eq' : w = 2 * z := hw_eq
  have h5 : w / x = (2 * z) / (24 * z) := by
    rw [show w = 2 * z by linarith [hw_eq'], show x = 24 * z by linarith [hx_eq']]
    all_goals linarith
  have h6 : (2 * z) / (24 * z) = 1 / 12 := by
    have h7 : z ≠ 0 := h2
    field_simp [h7]
    <;> ring
  rw [h5, h6]