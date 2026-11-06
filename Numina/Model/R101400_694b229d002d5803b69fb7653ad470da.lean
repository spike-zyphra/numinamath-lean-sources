import Mathlib

theorem algebra_143830 (x : ℝ) :
    Real.sqrt (x^2 + 4) - Real.sqrt (4 * x) = 0 ↔ x = 2 := by
  constructor
  · -- Forward direction: if sqrt(x^2 + 4) - sqrt(4 * x) = 0, then x = 2
    intro h_eq
    have h1 : Real.sqrt (x ^ 2 + 4) = Real.sqrt (4 * x) := by linarith
    have h2 : x ^ 2 + 4 ≥ 0 := by nlinarith [sq_nonneg x]
    have h3 : 4 * x ≥ 0 := by
      by_contra h
      push_neg at h
      have h4 : Real.sqrt (4 * x) = 0 := by
        rw [Real.sqrt_eq_zero'.mpr]
        linarith
        all_goals nlinarith
      rw [h4] at h1
      have h5 : Real.sqrt (x ^ 2 + 4) = 0 := h1
      have h8 : x ^ 2 + 4 = 0 := by
        rw [Real.sqrt_eq_zero (by nlinarith)] at h5
        linarith
      nlinarith [sq_nonneg x]
    have h5 : x ^ 2 + 4 = 4 * x := by
      rw [Real.sqrt_inj (by nlinarith) (by nlinarith) ] at h1
      nlinarith
    have h6 : (x - 2) ^ 2 = 0 := by nlinarith
    have h7 : x - 2 = 0 := by
      nlinarith
    linarith
  · -- Backward direction: if x = 2, then sqrt(x^2 + 4) - sqrt(4 * x) = 0
    intro h_eq
    rw [h_eq]
    have h_eq2 : Real.sqrt ((2 : ℝ) ^ 2 + 4) = Real.sqrt (4 * (2 : ℝ)) := by
      norm_num
    linarith [h_eq2]