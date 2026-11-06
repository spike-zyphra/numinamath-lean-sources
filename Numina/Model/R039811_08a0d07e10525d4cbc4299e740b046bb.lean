import Mathlib

theorem algebra_245625 {x : ℝ} (hx : x ≥ -1) (h : (x + Real.sqrt (x + 1)) / (x - Real.sqrt (x + 1)) = 11 / 5) :
    x = 8 := by
  have h1 : x - Real.sqrt (x + 1) ≠ 0 := by
    by_contra h1
    have h2 : (x + Real.sqrt (x + 1)) / (x - Real.sqrt (x + 1)) = 0 := by
      rw [h1]
      norm_num
    linarith [h, h2]

  have h2 : 5 * (x + Real.sqrt (x + 1)) = 11 * (x - Real.sqrt (x + 1)) := by
    have h3 : x - Real.sqrt (x + 1) ≠ 0 := h1
    field_simp [h3] at h
    nlinarith

  have h3 : 8 * Real.sqrt (x + 1) = 3 * x := by
    nlinarith [h2]

  have h4 : (8 * Real.sqrt (x + 1)) ^ 2 = (3 * x) ^ 2 := by
    rw [h3]

  have h5 : (8 * Real.sqrt (x + 1)) ^ 2 = 64 * (x + 1) := by
    calc
      (8 * Real.sqrt (x + 1)) ^ 2 = 8^2 * (Real.sqrt (x + 1) ^ 2) := by ring
      _ = 64 * (x + 1) := by
        have h6 : Real.sqrt (x + 1) ^ 2 = x + 1 := by
          rw [Real.sq_sqrt]
          linarith
        nlinarith [h6]

  have h6 : (3 * x) ^ 2 = 9 * x^2 := by
    nlinarith

  rw [h5, h6] at h4

  have h7 : 9 * x^2 - 64 * x - 64 = 0 := by
    nlinarith [h4]

  have h8 : (x - 8) * (x + 8 / 9) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp h8) with h9 h10
  · -- h9: x - 8 = 0, so x = 8
    linarith
  · -- h10: x + 8 / 9 = 0, so x = -8/9. Now need to verify in original equation.
    have h10' : x = -8 / 9 := by nlinarith
    have h11 : Real.sqrt (x + 1) = (1: ℝ) / 3 := by
      rw [h10']
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    have h12 : (x + Real.sqrt (x + 1)) / (x - Real.sqrt (x + 1)) ≠ 11 / 5 := by
      rw [h11]
      rw [h10']
      norm_num
      all_goals linarith
    have h12' : (x + Real.sqrt (x + 1)) / (x - Real.sqrt (x + 1)) = 11 / 5 := h
    contradiction