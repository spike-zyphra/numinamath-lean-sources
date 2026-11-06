import Mathlib

theorem inequalities_304554 (x : ℝ) (hx : 0 < x) : 2 * Real.sqrt x ≥ 3 - 1 / x ↔ x > 0 := by
  constructor
  · -- Assume 2 * Real.sqrt x ≥ 3 - 1 / x, prove x > 0
    intro h
    exact hx
  · -- Assume x > 0, prove 2 * Real.sqrt x ≥ 3 - 1 / x
    intro h
    have h1 : 0 < x := hx
    have h2 : Real.sqrt x > 0 := by
      apply Real.sqrt_pos.2
      linarith
    have h3 : 2 * Real.sqrt x ≥ 3 - 1 / x := by
      have h4 : 2 * x * Real.sqrt x + 1 ≥ 3 * x := by
        have h5 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
        nlinarith [sq_nonneg (Real.sqrt x - 1), sq_nonneg (2 * Real.sqrt x + 1), sq_nonneg (x - 1), sq_nonneg (Real.sqrt x ^ 2 - 1), Real.sqrt_nonneg x, mul_pos (show 0 < x by linarith) (show 0 < Real.sqrt x by nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith)]), Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith)]
      have h7 : 0 < x := h1
      have h6 : 2 * Real.sqrt x ≥ 3 - 1 / (x) := by
        have h9 : x > 0 := by linarith
        have h20 : 2 * x * Real.sqrt x + 1 ≥ 3 * x := by linarith
        have h21 : (2 * x * Real.sqrt x + 1 : ℝ) / x ≥ (3 * x : ℝ) / x := by
          apply (div_le_div_right (by linarith)).mpr
          nlinarith
        have h22 : (2 * x * Real.sqrt x + 1 : ℝ) / x = 2 * Real.sqrt x + 1 / x := by
          field_simp [h9]
          <;> ring
        have h23 : (3 * x : ℝ) / x = 3 := by
          field_simp [h9]
          <;> nlinarith
        have h24 : 2 * Real.sqrt x + 1 / x ≥ 3 := by
          rw [h22] at h21
          rw [h23] at h21
          linarith
        linarith
      linarith
    linarith