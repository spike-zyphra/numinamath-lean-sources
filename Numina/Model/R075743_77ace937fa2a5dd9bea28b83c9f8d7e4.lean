import Mathlib

theorem algebra_95465 (d v : ℝ) (h : d > 0) (h1 : v > 0) (h2 : d / v = 60) (h3 : d / (v + w) = 24) :
    d / w = 40 := by
  have h4 : v ≠ 0 := by linarith

  have h5 : d = 60 * v := by
    have h6 : d = 60 * v := by
      have eq1 : d / v = 60 := h2
      field_simp [h4] at eq1 ⊢
      linarith
    exact h6

  have h6 : v + w ≠ 0 := by
    by_contra h7
    have h7' : d / (v + w) = 0 := by
      rw [h7]
      norm_num
      <;> linarith
    linarith [h3, h7']

  have h7 : d = 24 * (v + w) := by
    have h8 : d / (v + w) = 24 := h3
    field_simp [h6] at h8 ⊢
    linarith

  have h8 : w = (3 / 2) * v := by
    linarith [h5, h7]

  have h9 : w ≠ 0 := by
    by_contra h10
    have h10' : w = 0 := by linarith [h10]
    rw [h10'] at h8
    linarith [h8, h1]

  have eq1 : d / w = 40 := by
    have h12 : w ≠ 0 := h9
    have h13 : d = 40 * w := by
      rw [h5]
      have h11 : (3 / 2) * v = w := by linarith [h8]
      linarith [h11]
    rw [h13]
    field_simp [h12]
    <;> nlinarith [h8, h1]

  exact eq1