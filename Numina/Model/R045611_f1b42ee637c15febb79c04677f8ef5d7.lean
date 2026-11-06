import Mathlib

theorem algebra_194 {a : ℝ} (ha : a ^ 2 + a - 1 / 4 = 0) :
    (a ^ 3 - 1) / (a ^ 5 + a ^ 4 - a ^ 3 - a ^ 2) = 20 := by
  have h1 : a ^ 2 = 1 / 4 - a := by linarith
  have h2 : a ^ 3 = 5 / 4 * a - 1 / 4 := by
    calc
      a ^ 3 = a * a ^ 2 := by ring
      _ = a * (1 / 4 - a) := by rw [h1]
      _ = a / 4 - a ^ 2 := by ring
      _ = a / 4 - (1 / 4 - a) := by rw [h1]
      _ = 5 / 4 * a - 1 / 4 := by ring
  have h3 : a ^ 4 = 5 / 16 - 3 / 2 * a := by
    calc
      a ^ 4 = (a ^ 2) ^ 2 := by ring
      _ = (1 / 4 - a) ^ 2 := by rw [h1]
      _ = 1 / 16 - 2 * (1 / 4) * a + a ^ 2 := by ring
      _ = 1 / 16 - a / 2 + (1 / 4 - a) := by rw [h1]; ring
      _ = 5 / 16 - 3 / 2 * a := by ring
  have h4 : a ^ 5 = 29 / 16 * a - 6 / 16 := by
    calc
      a ^ 5 = a * a ^ 4 := by ring
      _ = a * (5 / 16 - 3 / 2 * a) := by rw [h3]
      _ = 5 / 16 * a - 3 / 2 * a ^ 2 := by ring
      _ = 5 / 16 * a - 3 / 2 * (1 / 4 - a) := by rw [h1]
      _ = 29 / 16 * a - 6 / 16 := by ring
  have h5 : a ^ 5 + a ^ 4 - a ^ 3 - a ^ 2 = (a - 1) / 16 := by
    rw [h4, h3, h2, h1]
    ring_nf
  have h6 : a - 1 ≠ 0 := by
    by_contra h
    have h7 : a = 1 := by linarith [h]
    rw [h7] at ha
    norm_num at ha
  have eq1 : (a ^ 3 - 1) / (a ^ 5 + a ^ 4 - a ^ 3 - a ^ 2) = 16 * ((a ^ 3 - 1) / (a - 1)) := by
    rw [h5]
    field_simp [h6]
    <;> ring_nf
  have eq2 : (a ^ 3 - 1) / (a - 1) = a ^ 2 + a + 1 := by
    have h8 : a - 1 ≠ 0 := h6
    have h9 : a ^ 3 - 1 = (a - 1) * (a ^ 2 + a + 1) := by ring
    rw [h9]
    field_simp [h8]
    <;> ring_nf
  rw [eq1, eq2]
  have h10 : a ^ 2 + a = 1 / 4 := by
    linarith [ha]
  have h11 : a ^ 2 + a + 1 = 5 / 4 := by
    linarith [h10]
  rw [h11]
  all_goals norm_num