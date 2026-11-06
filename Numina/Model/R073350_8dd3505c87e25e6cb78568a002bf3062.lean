import Mathlib

theorem algebra_322688 {a : ℝ} (ha : a^2 - 3 * a + 1 = 0) :
    (2 * a^5 - 5 * a^4 + 2 * a^3 - 8 * a^2) / (a^2 + 1) = -1 := by

  have h1 : a^2 = 3 * a - 1 := by linarith

  have h2 : a^3 = 8 * a - 3 := by
    calc
      a^3 = a * a^2 := by ring
      _ = a * (3 * a - 1) := by rw [h1]
      _ = 3 * a^2 - a := by ring
      _ = 3 * (3 * a - 1) - a := by rw [h1]
      _ = 8 * a - 3 := by ring

  have h3 : a^4 = 21 * a - 8 := by
    calc
      a^4 = (a^2) ^ 2 := by ring
      _ = (3 * a - 1) ^ 2 := by rw [h1]
      _ = 9 * (a^2) - 6 * a + 1 := by ring
      _ = 9 * (3 * a - 1) - 6 * a + 1 := by rw [h1]
      _ = 21 * a - 8 := by ring

  have h4 : a^5 = 55 * a - 21 := by
    calc
      a^5 = a * a^4 := by ring
      _ = a * (21 * a - 8) := by rw [h3]
      _ = 21 * a^2 - 8 * a := by ring
      _ = 21 * (3 * a - 1) - 8 * a := by rw [h1]
      _ = 55 * a - 21 := by ring

  have h5 : 2 * a^5 - 5 * a^4 + 2 * a^3 - 8 * a^2 = -3 * a := by
    rw [h4, h3, h2, h1]
    ring_nf <;> nlinarith

  have h6 : a^2 + 1 = 3 * a := by
    nlinarith [h1]

  rw [h5, h6]

  have h7 : 3 * a ≠ 0 := by
    by_contra h8
    have : a = 0 := by linarith
    rw [this] at ha
    nlinarith

  field_simp [h7]
  <;> nlinarith