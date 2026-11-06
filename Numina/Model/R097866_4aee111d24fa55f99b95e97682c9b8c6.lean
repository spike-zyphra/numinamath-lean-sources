import Mathlib

open Real

theorem inequalities_110777 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x * y = 1) :
    (x + 1) * (y + 1) ≥ 4 ∧ ((x + 1) * (y + 1) = 4 ↔ x = y) := by
  have h1 : (x + 1) * (y + 1) ≥ 4 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1),
      hxy, mul_pos hx hy]
  have h2 : (x + 1) * (y + 1) = 4 ↔ x = y := by
    constructor
    · -- Assume (x + 1) * (y + 1) = 4, prove x = y
      intro h_eq
      have h_eq2 : x + y = 2 := by
        nlinarith [hxy, h_eq]
      have h_eq3 : (x - 1) * (y - 1) = 0 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1),
          hxy, h_eq2, mul_pos hx hy]
      have h_eq4 : x = 1 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1),
          hxy, h_eq2, mul_pos hx hy]
      have h_eq5 : y = 1 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1),
          hxy, h_eq2, mul_pos hx hy]
      linarith
    · -- Assume x = y, prove (x + 1) * (y + 1) = 4
      intro h_eq
      rw [show y = x by linarith [h_eq]] 
      nlinarith [sq_nonneg (x - 1), hxy, mul_pos hx (show 0 < x by linarith), sq_nonneg (x - 1)]
  constructor
  · exact h1
  · exact h2