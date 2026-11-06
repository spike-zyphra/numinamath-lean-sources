import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_133941 {x y : ℝ} (hx : x ∈ Icc 1 2) (hy : y ∈ Icc 1 2)
  (h : 1 - sqrt (x - 1) = sqrt (y - 1)) :
  x + y ≤ 3 := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  have h1 : 0 ≤ x - 1 := by linarith
  have h2 : 0 ≤ y - 1 := by linarith

  have h3 : (1 - sqrt (x - 1)) ^ 2 = (sqrt (y - 1)) ^ 2 := by
    rw [h]

  have h4 : (1 - sqrt (x - 1)) ^ 2 = 1 - 2 * sqrt (x - 1) + (x - 1) := by
    ring_nf
    <;> rw [Real.sq_sqrt (by linarith)]
    all_goals linarith

  have h5 : (sqrt (y - 1)) ^ 2 = y - 1 := by
    rw [Real.sq_sqrt]
    linarith

  rw [h4, h5] at h3

  have h6 : y = x + 1 - 2 * sqrt (x - 1) := by
    linarith
  
  have h7 : x + y = 2 * x + 1 - 2 * sqrt (x - 1) := by
    linarith [h6]

  nlinarith [sq_nonneg (sqrt (x - 1)), sq_nonneg (sqrt (x - 1) - 1), Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ x - 1 by linarith), h, Real.sqrt_nonneg (y - 1), Real.sq_sqrt (show 0 ≤ y - 1 by linarith)]