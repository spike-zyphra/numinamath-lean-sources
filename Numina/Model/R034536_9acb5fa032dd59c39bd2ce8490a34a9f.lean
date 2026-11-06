import Mathlib

open Real

theorem inequalities_259353 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x * y = 4) :
    1 / (x + 3) + 1 / (y + 3) ≤ 2 / 5 ∧
    (1 / (x + 3) + 1 / (y + 3) = 2 / 5 ↔ x = y) := by

  have h2 : x + y ≥ 4 := by 
    nlinarith [show x * y = 4 by linarith, sq_nonneg (x - y)]

  have h3 : 1 / (x + 3) + 1 / (y + 3) ≤ 2 / 5 := by
    have hx3 : 0 < x + 3 := by linarith
    have hy3 : 0 < y + 3 := by linarith
    have pos1 : 0 < (x + 3) * (y + 3) := by positivity
    have h4 : (1 / (x + 3) + 1 / (y + 3) - 2 / 5) ≤ 0 := by
      have pos1 : 0 < 5 * ((x + 3) * (y + 3)) := by positivity
      have h4' : (1 / (x + 3) + 1 / (y + 3) - 2 / 5) = (5 * (y + 3) + 5 * (x + 3) - 2 * ((x + 3) * (y + 3)) ) / (5 * ((x + 3) * (y + 3)) ) := by
        field_simp
        <;> ring
      rw [h4']
      apply div_nonpos_of_nonpos_of_nonneg
      nlinarith [show (x + 3) * (y + 3) = x * y + 3 * x + 3 * y + 9 by ring, hxy, sq_nonneg (x - y)]
      all_goals positivity
    linarith

  constructor
  · -- Show 1 / (x + 3) + 1 / (y + 3) ≤ 2 / 5
    linarith [h3]
  · -- Show (1 / (x + 3) + 1 / (y + 3) = 2 / 5) ↔ (x = y)
    constructor
    · -- Forward: if equality holds, then x = y
      intro heq
      have hx3 : 0 < x + 3 := by linarith
      have hy3 : 0 < y + 3 := by linarith
      field_simp at heq ⊢
      <;> nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 4), hxy, mul_pos hx hy]
    · -- Backward: if x = y, then equality holds
      intro heq
      rw [show y = x by linarith [heq]]
      field_simp at *
      <;> nlinarith [sq_nonneg (x - 2), hxy, heq]