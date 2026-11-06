import Mathlib

theorem algebra_187257 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h1 : Real.sqrt (y / x) - 2 * Real.sqrt (x / y) = 1) (h2 : Real.sqrt (5 * x + y) + Real.sqrt (5 * x - y) = 4) :
    x = 1 ∧ y = 4 := by
  have h5 : Real.sqrt (y / x) * Real.sqrt (x / y) = 1 := by
    have h6 : Real.sqrt (y / x) * Real.sqrt (x / y) = Real.sqrt ((y / x) * (x / y)) := by
      rw [← Real.sqrt_mul (by
        have h7 : 0 < y / x := by
          apply div_pos
          linarith
          linarith
        have h8 : 0 < x / y := by
          apply div_pos
          linarith
          linarith
        positivity
      )]
    have h7 : (y / x) * (x / y) = 1 := by
      field_simp
      all_goals nlinarith
    rw [h6, h7]
    norm_num
  have eq1 : Real.sqrt (y / x) = 1 + 2 * Real.sqrt (x / y) := by
    linarith
  have eq2 : (1 + 2 * Real.sqrt (x / y)) * Real.sqrt (x / y) = 1 := by
    have h8 : Real.sqrt (y / x) * Real.sqrt (x / y) = 1 := h5
    rw [eq1] at h8
    linarith
  have h8 : (Real.sqrt (x / y) - 1 / 2) * (Real.sqrt (x / y) + 1) = 0 := by
    nlinarith [eq2, sq_nonneg (Real.sqrt (x / y) + 1), sq_nonneg (Real.sqrt (x / y) - 1 / 2)]
  cases' (mul_eq_zero.1 h8) with h9 h10
  · -- First case: Real.sqrt (x / y) - 1 / 2 = 0
    have h11 : Real.sqrt (x / y) = 1 / 2 := by linarith
    have h12 : (x / y) = (1 / 4) := by
      calc
        x / y = (Real.sqrt (x / y)) ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        _ = (1 / 2) ^ 2 := by
          rw [h11]
        _ = 1 / 4 := by norm_num
    have h13 : y = 4 * x := by
      field_simp at h12 ⊢
      nlinarith
    have h14 : Real.sqrt (5 * x + y) + Real.sqrt (5 * x - y) = 4 := h2
    rw [show 5 * x + y = 9 * x by nlinarith [h13]] at h14
    rw [show 5 * x - y = x by nlinarith [h13]] at h14
    have h15 : Real.sqrt (9 * x) = 3 * Real.sqrt x := by
      have h11 : Real.sqrt (9 * x) = Real.sqrt (9 * x) := by rfl
      have h12 : Real.sqrt (9 * x) = Real.sqrt (9) * Real.sqrt x := by
        rw [Real.sqrt_mul (by nlinarith)]
      have h13 : Real.sqrt (9 : ℝ) = (3 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h12, h13]
    rw [show Real.sqrt (9 * x) = 3 * Real.sqrt x by
      have h15 : Real.sqrt (9 * x) = 3 * Real.sqrt x := h15
      linarith [h15]
    ] at h14
    have h16 : Real.sqrt x = 1 := by
      nlinarith [h14, Real.sqrt_nonneg x]
    have h17 : x = 1 := by
      calc
        x = (Real.sqrt x) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (1 : ℝ) ^ 2 := by
          rw [h16]
        _ = (1 : ℝ) := by norm_num
    have h18 : y = 4 := by
      nlinarith [h13, h17]
    exact ⟨h17, h18⟩
  · -- Second case: Real.sqrt (x / y) + 1 = 0
    have h13 : Real.sqrt (x / y) = -1 := by linarith
    have h14 : Real.sqrt (x / y) ≥ 0 := by
      apply Real.sqrt_nonneg
    nlinarith [h13, h14]