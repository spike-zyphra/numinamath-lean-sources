import Mathlib

theorem algebra_186861 (x : ℝ) (hx : 3 * x ^ 2 + 5 * x + 7 ≥ 0 ∧ 3 * x ^ 2 + 5 * x + 2 ≥ 0) :
    Real.sqrt (3 * x ^ 2 + 5 * x + 7) - Real.sqrt (3 * x ^ 2 + 5 * x + 2) = 1 ↔
    x = -2 ∨ x = 1 / 3 := by
  constructor
  · -- Forward direction: if sqrt(3x^2 + 5x + 7) - sqrt(3x^2 + 5x + 2) = 1, then x = -2 or x = 1/3
    intro h
    have h1 : Real.sqrt (3 * x ^ 2 + 5 * x + 7) = 1 + Real.sqrt (3 * x ^ 2 + 5 * x + 2) := by linarith
    have h2 : Real.sqrt (3 * x ^ 2 + 5 * x + 7) ^ 2 = (1 + Real.sqrt (3 * x ^ 2 + 5 * x + 2)) ^ 2 := by
      rw [h1]
    have h3 : Real.sqrt (3 * x ^ 2 + 5 * x + 7) ^ 2 = 3 * x ^ 2 + 5 * x + 7 := by
      exact Real.sq_sqrt (show 3 * x ^ 2 + 5 * x + 7 ≥ 0 by linarith [hx.left])
    have h4 : Real.sqrt (3 * x ^ 2 + 5 * x + 2) ^ 2 = 3 * x ^ 2 + 5 * x + 2 := by
      exact Real.sq_sqrt (show 3 * x ^ 2 + 5 * x + 2 ≥ 0 by linarith [hx.right])
    rw [h3] at h2
    have h5 : (1 + Real.sqrt (3 * x ^ 2 + 5 * x + 2)) ^ 2 = 1 + 2 * Real.sqrt (3 * x ^ 2 + 5 * x + 2) + Real.sqrt (3 * x ^ 2 + 5 * x + 2) ^ 2 := by ring
    rw [h5] at h2
    rw [h4] at h2
    have h6 : Real.sqrt (3 * x ^ 2 + 5 * x + 2) = 2 := by nlinarith
    have h7 : 3 * x ^ 2 + 5 * x + 2 = 4 := by
      have h8 : Real.sqrt (3 * x ^ 2 + 5 * x + 2) ≥ 0 := Real.sqrt_nonneg (3 * x ^ 2 + 5 * x + 2)
      nlinarith [h6, h4]
    have h10 : 3 * x ^ 2 + 5 * x - 2 = 0 := by
      linarith
    have h11 : (x - 1 / 3) * (x + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h11) with h12 h13
    · 
      right
      linarith
    · 
      left
      linarith
  · -- Backward direction: if x = -2 or x = 1/3, then sqrt(3x^2 + 5x + 7) - sqrt(3x^2 + 5x + 2) = 1
    rintro (h | h)
    · 
      have h1 : x = -2 := h
      rw [h1]
      have h2 : Real.sqrt (3 * (-2) ^ 2 + 5 * (-2) + 7) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> linarith
      have h3 : Real.sqrt (3 * (-2) ^ 2 + 5 * (-2) + 2) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> linarith
      rw [h2, h3]
      all_goals norm_num
    · 
      have h1 : x = 1 / 3 := h
      rw [h1]
      have h2 : Real.sqrt (3 * (1 / 3) ^ 2 + 5 * (1 / 3) + 7) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> linarith
      have h3 : Real.sqrt (3 * (1 / 3) ^ 2 + 5 * (1 / 3) + 2) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> linarith
      rw [h2, h3]
      all_goals norm_num