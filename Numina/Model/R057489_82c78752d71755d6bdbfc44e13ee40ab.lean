import Mathlib

theorem algebra_220233 {a m n : ℝ} (ha : a = m * n) :
    IsSquare ((m - n) ^ 2 / 4 + a) ∧ IsSquare ((m + n) ^ 2 / 4 - a) := by
  have h1 : (m - n) ^ 2 / 4 + a = ( (m + n) / 2 ) ^ 2 := by
    rw [ha]
    ring_nf
  have h2 : (m + n) ^ 2 / 4 - a = ( (m - n) / 2 ) ^ 2 := by
    rw [ha]
    ring_nf
  constructor
  · -- Show that (m - n)^2 / 4 + a is a square
    rw [h1]
    exact ⟨( (m + n) / 2 ), by ring⟩
  · -- Show that (m + n)^2 / 4 - a is a square
    rw [h2]
    exact ⟨( (m - n) / 2 ), by ring⟩