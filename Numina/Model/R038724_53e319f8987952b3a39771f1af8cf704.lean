import Mathlib

theorem algebra_217185 (x y z : ℝ) :
    (x + y = Real.sqrt 28 ∧ x * y - 2 * z ^ 2 = 7) ↔ (x, y, z) = (Real.sqrt 7, Real.sqrt 7, 0) := by
  constructor
  · -- Assume (x + y = Real.sqrt 28 ∧ x * y - 2 * z ^ 2 = 7), prove (x, y, z) = (Real.sqrt 7, Real.sqrt 7, 0)
    rintro ⟨h1, h2⟩
    have h3 : Real.sqrt 28 = 2 * Real.sqrt 7 := by
      calc
        Real.sqrt 28 = Real.sqrt (2 ^ 2 * 7) := by norm_num
        _ = (2 : ℝ) * Real.sqrt 7 := by
          rw [Real.sqrt_mul (by norm_num)]
          rw [Real.sqrt_sq (by norm_num)]
    have h4 : z = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (z), sq_nonneg (x - Real.sqrt 7), sq_nonneg (y - Real.sqrt 7), Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
    rw [h3] at h1
    have h7 : x * y = 7 := by
      have h7 : z = 0 := h4
      rw [h7] at h2
      linarith [h2]
    have h8 : y = 2 * Real.sqrt 7 - x := by
      linarith [h1]
    rw [show y = 2 * Real.sqrt 7 - x by linarith [h1]] at h7
    have h10 : x ^ 2 - 2 * Real.sqrt 7 * x + 7 = 0 := by
      nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
    have h11 : (x - Real.sqrt 7) ^ 2 = 0 := by
      nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
    have h12 : x - Real.sqrt 7 = 0 := by
      apply pow_eq_zero 
      exact h11
    have h5 : x = Real.sqrt 7 := by
      linarith [h12]
    have h6 : y = Real.sqrt 7 := by
      rw [h5] at h1
      nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
    simp [h5, h6, h4]
  · -- Assume (x, y, z) = (Real.sqrt 7, Real.sqrt 7, 0), prove (x + y = Real.sqrt 28 ∧ x * y - 2 * z ^ 2 = 7)
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · -- Prove x + y = Real.sqrt 28
      have h1 : Real.sqrt 28 = 2 * Real.sqrt 7 := by
        calc
          Real.sqrt 28 = Real.sqrt (2 ^ 2 * 7) := by norm_num
          _ = (2 : ℝ) * Real.sqrt 7 := by
            rw [Real.sqrt_mul (by norm_num)]
            rw [Real.sqrt_sq (by norm_num)]
      nlinarith [h1, Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
    · -- Prove x * y - 2 * z ^ 2 = 7
      nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]