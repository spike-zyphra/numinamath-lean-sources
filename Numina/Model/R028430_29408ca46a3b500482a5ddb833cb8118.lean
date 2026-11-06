import Mathlib

theorem algebra_128012 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b ≠ 0)
    (h : a * b - a ^ 2 ≠ 0) :
    (a ^ 2 - b ^ 2) / (a * b) - (a * b - b ^ 2) / (a * b - a ^ 2) = a / b := by
  have eq2 : (a * b - b ^ 2) / (a * b - a ^ 2) = - (b / a) := by 
    have h5 : a * b - a ^ 2 ≠ 0 := h
    have h6 : a ≠ 0 := ha
    field_simp [(show a * b - a ^ 2 ≠ 0 by assumption), (show a ≠ 0 by assumption)]
    <;> ring_nf
    <;> field_simp
    <;> ring
  rw [eq2]
  field_simp [(show a * b ≠ 0 by assumption), (show a ≠ 0 by assumption), (show b ≠ 0 by assumption)]
  <;> ring_nf
  <;> field_simp
  <;> ring