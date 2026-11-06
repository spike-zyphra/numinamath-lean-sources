import Mathlib

theorem algebra_8051 {x : ℝ} (hx : x ≠ 0) (h : x / (x^2 - 3 * x + 1) = 1) :
    x^3 / (x^6 - x^3 + 1) = 1 / 51 := by
  have h1 : x^2 - 3 * x + 1 ≠ 0 := by
    by_contra h2
    have h3 : x / (x^2 - 3 * x + 1) = 0 := by
      field_simp [h2]
    linarith [h, h3]
  have h2 : x = x^2 - 3 * x + 1 := by
    have h3 : x^2 - 3 * x + 1 ≠ 0 := h1
    field_simp [h3] at h
    linarith
  have h3 : x^2 = 4 * x - 1 := by
    linarith [h2]
  have hx3 : x^3 = 15 * x - 4 := by
    calc
      x^3 = x * x^2 := by ring
      _ = x * (4 * x - 1) := by rw [h3]
      _ = 4 * x^2 - x := by ring
      _ = 4 * (4 * x - 1) - x := by rw [h3]
      _ = 15 * x - 4 := by ring
  have hx4 : x^4 = 56 * x - 15 := by
    calc
      x^4 = (x^2) ^ 2 := by ring
      _ = (4 * x - 1) ^ 2 := by rw [h3]
      _ = 16 * x^2 - 8 * x + 1 := by ring
      _ = 16 * (4 * x - 1) - 8 * x + 1 := by rw [h3]
      _ = 56 * x - 15 := by ring
  have hx6 : x^6 = 780 * x - 209 := by
    calc
      x^6 = (x^2) * x^4 := by ring
      _ = (4 * x - 1) * (56 * x - 15) := by
        rw [h3]
        rw [hx4]
      _ = 224 * x^2 - 116 * x + 15 := by ring
      _ = 224 * (4 * x - 1) - 116 * x + 15 := by
        rw [h3]
      _ = 780 * x - 209 := by ring
  have hden : x^6 - x^3 + 1 = 765 * x - 204 := by
    rw [hx6, hx3]
    ring
  have h4 : 765 * x - 204 ≠ 0 := by
    by_contra h5
    have h6 : 15 * x - 4 = 0 := by
      linarith
    have h5x : 15 * x - 4 = 0 := by
      linarith
    have h6x : x = 4 / 15 := by linarith
    rw [h6x] at h2
    nlinarith
  have h5 : 15 * x - 4 ≠ 0 := by
    by_contra h6
    have h6x : x = 4 / 15 := by linarith
    rw [h6x] at h2
    nlinarith
  rw [hden, hx3]
  field_simp [show 765 * x - 204 ≠ 0 by simpa using h4, show 15 * x - 4 ≠ 0 by simpa using h5]
  <;> nlinarith