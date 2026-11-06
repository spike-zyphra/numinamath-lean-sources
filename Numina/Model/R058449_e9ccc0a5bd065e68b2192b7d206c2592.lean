import Mathlib

theorem calculus_61109 {I : ℝ} (hI : I > 0) (r : ℝ) (hr : r > 0)
    (h : I = 2 * π * r ^ 5 / 5) :
    ∃ I' : ℝ, I' = 2 * π * (2 * r) ^ 5 / 5 ∧ I' = 32 * I := by
  use 2 * π * (2 * r) ^ 5 / 5
  constructor
  · -- First equality is by definition
    rfl
  · -- Show that I' equals 32 * I
    rw [h]
    ring_nf
    <;> field_simp
    <;> ring