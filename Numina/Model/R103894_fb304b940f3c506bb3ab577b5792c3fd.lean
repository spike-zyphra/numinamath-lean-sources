import Mathlib

theorem algebra_320252 (x : ℝ) (hx : 1 ≤ x ∧ x ≤ 2) : Real.sqrt (x + 2 * Real.sqrt (x - 1)) + Real.sqrt (x - 2 * Real.sqrt (x - 1)) = 2 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : 0 ≤ (x - 1 : ℝ) := by linarith
  have h2 : Real.sqrt (x + 2 * Real.sqrt (x - 1)) = Real.sqrt (x - 1) + 1 := by
    have h3 : 0 ≤ Real.sqrt (x - 1) := Real.sqrt_nonneg (x - 1)
    have eq1 : (Real.sqrt (x - 1) + 1) ^ 2 = x + 2 * Real.sqrt (x - 1) := by
      nlinarith [Real.sq_sqrt h1, sq_nonneg (Real.sqrt (x - 1) - 1)]
    have h4 : Real.sqrt (x + 2 * Real.sqrt (x - 1)) = Real.sqrt ((Real.sqrt (x - 1) + 1) ^ 2) := by
      rw [eq1]
      all_goals ring_nf <;> nlinarith [Real.sqrt_nonneg (x + 2 * Real.sqrt (x - 1))]
    rw [h4]
    have h5 : Real.sqrt ((Real.sqrt (x - 1) + 1) ^ 2) = Real.sqrt (x - 1) + 1 := by
      rw [Real.sqrt_sq (show 0 ≤ (Real.sqrt (x - 1) + 1 : ℝ) by positivity)]
    linarith [h5]
  have h3 : Real.sqrt (x - 2 * Real.sqrt (x - 1)) = 1 - Real.sqrt (x - 1) := by
    have h4 : Real.sqrt (x - 1) ≤ (1 : ℝ) := by
      have h1' : x - 1 ≤ (1 : ℝ) := by linarith
      have h5 : Real.sqrt (x - 1) ≤ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h6 : Real.sqrt (1 : ℝ) = (1 : ℝ) := Real.sqrt_one
      rw [h6] at h5
      linarith [h5]
    have eq1 : (Real.sqrt (x - 1) - 1 : ℝ) ^ 2 = x - 2 * Real.sqrt (x - 1) := by
      nlinarith [Real.sq_sqrt h1, sq_nonneg (Real.sqrt (x - 1) - 1)]
    have h5 : Real.sqrt (x - 2 * Real.sqrt (x - 1)) = Real.sqrt ((Real.sqrt (x - 1) - 1 : ℝ) ^ 2) := by
      rw [eq1]
      all_goals ring_nf <;> nlinarith [Real.sqrt_nonneg (x - 2 * Real.sqrt (x - 1))]
    rw [h5]
    have h6 : Real.sqrt ((Real.sqrt (x - 1) - 1 : ℝ) ^ 2) = (1 - Real.sqrt (x - 1) : ℝ) := by
      have hsq_nonneg : (0 : ℝ) ≤ (Real.sqrt (x - 1) - 1 : ℝ) ^ 2 := by nlinarith
      have h7 : Real.sqrt ((Real.sqrt (x - 1) - 1) ^ 2) = |(Real.sqrt (x - 1) - 1 : ℝ)| := by 
        rw [Real.sqrt_sq_eq_abs]
      rw [h7]
      have h8 : (Real.sqrt (x - 1) : ℝ) ≤ (1 : ℝ) := h4
      have h9 : (Real.sqrt (x - 1) - 1 : ℝ) ≤ (0 : ℝ) := by nlinarith
      rw [abs_of_nonpos h9]
      all_goals ring_nf <;> nlinarith
    linarith [h6, Real.sqrt_nonneg (x - 2 * Real.sqrt (x - 1))]
  linarith [h2, h3]