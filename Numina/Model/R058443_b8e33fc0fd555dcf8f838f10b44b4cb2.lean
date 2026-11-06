import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_19642 {r : ℝ} (hr : r = 2) :
    (π * (4 ^ 2 / 2) - π * r ^ 2) / (π * (4 ^ 2 / 2)) = 1 / 2 := by 
  rw [hr]
  have h1 : π * ((4 : ℝ) ^ 2 / 2) = 8 * π := by 
    ring_nf
  have h2 : π * ((2 : ℝ) ^ 2) = 4 * π := by 
    ring_nf
  rw [h1, h2]
  have h3 : (8 * π - 4 * π) = 4 * π := by 
    linarith [Real.pi_pos]
  rw [h3]
  have h4 : π ≠ 0 := by 
    exact Real.pi_ne_zero
  field_simp [h4]
  <;> linarith [Real.pi_pos]