import Mathlib

open Real Set
open scoped Real

theorem inequalities_262485 (a b c : ℝ) (x : ℝ) :
  -sin ((b - c) / 2) ^ 2 ≤ cos (a * x + b) * cos (a * x + c) ∧
  cos (a * x + b) * cos (a * x + c) ≤ cos ((b - c) / 2) ^ 2 := by
  have h1 : cos (a * x + b) * cos (a * x + c) = 
    (1 / 2) * (cos (2 * a * x + b + c) + cos (b - c)) := by 
    rw [cos_add_cos]
    ring
  constructor
  · -- We need to prove -sin²((b - c) / 2) ≤ cos(a*x+b) * cos(a*x+c)
    rw [h1]
    have h8 : sin ((b - c) / 2) ^ 2 = (1 - cos (b - c)) / 2 := by 
      have h9 : sin ((b - c) / 2) ^ 2 = (1 - cos (b - c)) / 2 := by 
        have h10 : sin ((b - c) / 2) ^ 2 = (1 - cos (b - c)) / 2 := by 
          rw [sin_sq_eq_half_sub]
          ring_nf
        linarith
      linarith
    rw [h8]
    have h5a : cos (b - c) ≤ 1 := by
      apply cos_le_one
    have h6a : cos (2 * a * x + b + c) ≥ -1 := by
      apply neg_one_le_cos
    nlinarith [Real.cos_le_one (2 * a * x + b + c), Real.neg_one_le_cos (b - c)]
  · -- We need to prove cos(a*x+b) * cos(a*x+c) ≤ cos²((b-c)/2)
    rw [h1] 
    have h2a : cos ((b - c) / 2) ^ 2 = (1 + cos (b - c)) / 2 := by 
      have h3a : cos ((b - c) / 2) ^ 2 = (1 + cos (b - c)) / 2 := by 
        have h4a : cos ((b - c) / 2) ^ 2 = (1 + cos (b - c)) / 2 := by 
          rw [cos_sq]
          ring_nf
        linarith
      linarith
    rw [h2a]
    have h5a : cos (b - c) ≤ 1 := by
      apply cos_le_one
    have h5b : cos (2 * a * x + b + c) ≤ 1 := by
      apply cos_le_one
    nlinarith [cos_le_one (b - c), cos_le_one (2 * a * x + b + c), Real.sin_sq_add_cos_sq (b - c), Real.sin_sq_add_cos_sq (2 * a * x + b + c), Real.sin_sq_add_cos_sq ((b - c) / 2), Real.sin_sq_le_one (b - c), Real.sin_sq_le_one (2 * a * x + b + c)]