import Mathlib

theorem algebra_276602 :
    {(x, y) : ℝ × ℝ | x > 0 ∧ y > 0 ∧ x * y / 100 = 425 ∧ (6/5 * x) * (y - 1/2) / 100 = 459} = {(8500, 5)} := by

  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume ⟨x, y⟩ satisfies the conditions
    rintro ⟨hx, hy, h1, h2⟩
    have h3 : x * y = 42500 := by
      linarith
    have h4 : x * (y - 1/2) = 38250 := by
      nlinarith
    have h5 : x = 8500 := by
      have eq1 : x * y = 42500 := h3
      have eq2 : x * (y - 1/2) = 38250 := h4
      nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy]
    have h6 : y = 5 := by
      rw [h5] at h3
      nlinarith
    simp [h5, h6]
  · -- Show that (8500, 5) satisfies the conditions
    rintro (⟨rfl, rfl⟩)
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num