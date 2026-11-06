import Mathlib

theorem algebra_186817 (x : ℝ) (hx : 0 ≤ x + 1) (h : Real.sqrt (3 * x + 7) - Real.sqrt (x + 1) = 2) :
    x = -1 ∨ x = 3 := by
  have h1 : Real.sqrt (3 * x + 7) = 2 + Real.sqrt (x + 1) := by
    linarith

  have h3 : 0 ≤ 3 * x + 7 := by
    by_contra h4
    push_neg at h4
    have h4' : Real.sqrt (3 * x + 7) = 0 := by
      rw [Real.sqrt_eq_zero'.mpr]
      linarith
      all_goals linarith
    rw [h4'] at h1
    have h5 : Real.sqrt (x + 1) = -2 := by
      nlinarith
    have h6 : 0 ≤ Real.sqrt (x + 1) := by
      apply Real.sqrt_nonneg
    nlinarith

  have h4 : Real.sqrt (3 * x + 7) ^ 2 = (2 + Real.sqrt (x + 1)) ^ 2 := by
    rw [h1]

  have h5 : Real.sqrt (3 * x + 7) ^ 2 = 3 * x + 7 := by
    apply Real.sq_sqrt
    linarith

  have h6 : (2 + Real.sqrt (x + 1)) ^ 2 = 4 + 4 * Real.sqrt (x + 1) + (Real.sqrt (x + 1) ^ 2) := by
    ring

  have h7 : Real.sqrt (x + 1) ^ 2 = x + 1 := by
    apply Real.sq_sqrt
    linarith

  rw [h6, h7] at h4
  rw [h5] at h4

  have h8 : 2 * x + 2 = 4 * Real.sqrt (x + 1) := by
    nlinarith

  have h9 : x + 1 = 2 * Real.sqrt (x + 1) := by
    nlinarith

  have h10 : (x + 1) ^ 2 = 4 * (Real.sqrt (x + 1) ^ 2) := by
    calc
      (x + 1) ^ 2 = (2 * Real.sqrt (x + 1)) ^ 2 := by
        rw [show 2 * Real.sqrt (x + 1) = x + 1 by nlinarith [h9] ]
      _ = 4 * (Real.sqrt (x + 1) ^ 2) := by
        ring

  rw [h7] at h10

  have h11 : (x + 1) * (x - 3) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp h11) with h12 h13
  · -- x + 1 = 0
    left
    linarith
  · -- x - 3 = 0
    right
    linarith