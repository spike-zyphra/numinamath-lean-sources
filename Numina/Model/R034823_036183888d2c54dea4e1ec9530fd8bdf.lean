import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_215950 {r h : ℝ} (A V : ℝ)
    (hr : r > 0) (hh : h > 0)
    (hA : A = π * r * (r + sqrt (h^2 + r^2))) 
    (hV : V = π * r^2 * h / 3) :
  A^3 ≥ 72 * π * V^2 := by
  rw [hA, hV]
  have h1 : sqrt (h^2 + r^2) ≥ 0 := by positivity
  have h4 : (π * r * (r + sqrt (h^2 + r^2)) ) ^ 3 ≥ 8 * π^3 * r^4 * h^2 := by
    have h5 : (sqrt (h^2 + r^2)) ^ 2 = h^2 + r^2 := by
      rw [Real.sq_sqrt]
      positivity
    have h6 : (r + sqrt (h^2 + r^2)) ^ 3 ≥ 8 * r * h^2 := by
      nlinarith [sq_nonneg (sqrt (h^2 + r^2) - 3 * r), sq_nonneg (h ^ 2 - 8 * r ^ 2), Real.sqrt_nonneg (h ^ 2 + r ^ 2), sq_nonneg (sqrt (h ^ 2 + r ^ 2) - r), 
          Real.sq_sqrt (show (0 : ℝ) ≤ h ^ 2 + r ^ 2 by positivity), sq_nonneg ( (h ^ 2 + r ^ 2) - 9 * r ^ 2 ), sq_nonneg (r - h / 2)
         ]
    have h7 : (π * r * (r + sqrt (h^2 + r^2)) ) ^ 3 ≥ 8 * π^3 * r^4 * h^2 := by
      calc
        (π * r * (r + sqrt (h^2 + r^2)) ) ^ 3 = π ^ 3 * r^3 * (r + sqrt (h^2 + r^2)) ^ 3 := by
          ring_nf
        _ ≥ π ^ 3 * r^3 * (8 * r * h^2) := by
          apply mul_le_mul_of_nonneg_left
          nlinarith [h6]
          all_goals positivity
        _ = 8 * π ^ 3 * r^4 * h^2 := by
          ring
    linarith
  nlinarith [h4]