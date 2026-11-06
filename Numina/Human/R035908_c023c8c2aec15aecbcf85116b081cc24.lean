import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_126413 (x : ℝ) (a b : ℝ) :
  (sin x + a * cos x) * (sin x + b * cos x) ≤ 1 + ((a + b) / 2) ^ 2 := by 
  have h1 : (sin x + a * cos x) * (sin x + b * cos x) = 
    (sin x + (a + b) / 2 * cos x) ^ 2 - ((a - b) ^ 2) / 4 * cos x ^ 2 := by 
    ring_nf
    <;> simp [sin_sq, cos_sq]
    <;> ring
  rw [h1]
  have h2 : (sin x + (a + b) / 2 * cos x) ^ 2 ≤ 1 + ((a + b) / 2) ^ 2 := by
    nlinarith [sq_nonneg (sin x), sq_nonneg (cos x - (a + b) / 2 * sin x), Real.sin_sq_add_cos_sq x]
  nlinarith [sq_nonneg ((a - b) * cos x), h2]