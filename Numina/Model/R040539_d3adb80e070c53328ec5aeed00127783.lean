import Mathlib

theorem algebra_269352 (d : ℝ) (h : d = 120) :
    {(c_f, c_r) : ℝ × ℝ | c_f > 0 ∧ c_r > 0 ∧
      d / c_f = d / c_r + 6 ∧ 
      d / (c_f * (1 + 1 / 4)) = d / (c_r * (1 + 1 / 5)) + 4} =
    {(4, 5)} := by 
  rw [h]
  ext ⟨c_f, c_r⟩
  simp [-one_div]
  constructor
  · -- Assume (c_f, c_r) is in the set.
    rintro ⟨hc_f, hc_r, h1, h2⟩
    field_simp at h1 h2
    have h3 : c_r = 5 / 4 * c_f := by
      nlinarith [sq_pos_of_pos hc_f, sq_pos_of_pos hc_r, mul_pos hc_f hc_r]
    have h4 : c_f = 4 := by
      nlinarith [sq_pos_of_pos hc_f, sq_pos_of_pos hc_r, mul_pos hc_f hc_r, h3]
    have h5 : c_r = 5 := by
      rw [h4] at h3
      linarith
    simp [h4, h5]
  · -- Show that (4, 5) is in the set.
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num