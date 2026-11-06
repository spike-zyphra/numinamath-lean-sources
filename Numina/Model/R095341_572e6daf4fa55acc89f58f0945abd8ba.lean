import Mathlib

theorem algebra_16362 {A B C : ℝ} (h : A / B = 2) (h' : B / C = 1 / 4) :
    (3 * A + 2 * B) / (4 * C - A) = 4 / 7 := by

  have h1 : B ≠ 0 := by
    by_contra h1
    rw [h1] at h
    norm_num at h

  have h2 : C ≠ 0 := by
    by_contra h2
    rw [h2] at h'
    norm_num at h'

  have hA : A = 2 * B := by
    have h1' : B ≠ 0 := h1
    field_simp [h1'] at h
    linarith

  have hC : C = 4 * B := by
    have h2' : C ≠ 0 := h2
    field_simp [h2'] at h'
    linarith

  have h3 : 4 * C - A ≠ 0 := by
    intro h4
    have h4 : 14 * B = 0 := by
      rw [show C = 4 * B by linarith [hC], show A = 2 * B by linarith [hA]] at h4
      nlinarith
    have h5 : B = 0 := by
      linarith
    contradiction

  have h4 : 3 * A + 2 * B = 8 * B := by
    rw [show A = 2 * B by linarith [hA]]
    linarith

  have h5 : 4 * C - A = 14 * B := by
    rw [show C = 4 * B by linarith [hC], show A = 2 * B by linarith [hA]]
    linarith

  rw [h4, h5]
  have h8 : B ≠ 0 := h1
  field_simp [h8]
  <;> nlinarith