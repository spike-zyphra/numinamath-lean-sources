import Mathlib

open Real

theorem algebra_12303 (s r : ℝ) (hs : 0 < s) (hr : 0 < r) (h : 4 * s = 2 * π * r) : s ^ 2 / (π * r ^ 2) = π / 4 := by
  have h1 : 2 * s = π * r := by
    linarith [h]
  have h2 : s = (π * r) / 2 := by
    linarith [h1]
  have h3 : s ^ 2 = (π ^ 2 * r ^ 2) / 4 := by
    rw [h2]
    ring_nf
  have h4 : π * r ^ 2 ≠ 0 := by
    positivity
  rw [h3]
  field_simp [h4]
  <;> ring_nf <;> field_simp [Real.pi_pos] <;> ring