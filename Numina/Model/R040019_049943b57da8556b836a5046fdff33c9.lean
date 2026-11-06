import Mathlib

theorem algebra_313774 (x : ℝ) (hx : x ∈ Set.Icc 1 2) :
    Real.sqrt (x + 2 * Real.sqrt (x - 1)) + Real.sqrt (x - 2 * Real.sqrt (x - 1)) = 2 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : x - 1 ≥ 0 := by linarith
  have h2 : Real.sqrt (x - 1) ≥ 0 := by apply Real.sqrt_nonneg
  have h3 : (Real.sqrt (x - 1)) ^ 2 = x - 1 := Real.sq_sqrt (by linarith)
  have h4 : x + 2 * Real.sqrt (x - 1) = (Real.sqrt (x - 1) + 1) ^ 2 := by 
    nlinarith [h3]
  have h5 : x - 2 * Real.sqrt (x - 1) = (Real.sqrt (x - 1) - 1) ^ 2 := by
    nlinarith [h3]
  have h6 : Real.sqrt (x + 2 * Real.sqrt (x - 1)) = Real.sqrt (x - 1) + 1 := by
    rw [h4]
    have h7 : 0 ≤ Real.sqrt (x - 1) + 1 := by
      linarith [h2]
    rw [Real.sqrt_sq (by linarith)]
  have h8 : Real.sqrt (x - 2 * Real.sqrt (x - 1)) = 1 - Real.sqrt (x - 1) := by
    rw [h5]
    have h9 : Real.sqrt ((Real.sqrt (x - 1) - 1) ^ 2) = |Real.sqrt (x - 1) - 1| := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h9]
    have h10 : Real.sqrt (x - 1) ≤ 1 := by
      have h11 : x - 1 ≤ 1 := by linarith
      have h12 : Real.sqrt (x - 1) ≤ Real.sqrt (1) := by
        apply Real.sqrt_le_sqrt
        linarith
      have h13 : Real.sqrt (1) = (1 : ℝ) := Real.sqrt_one
      linarith [h12, h13]
    have h14 : Real.sqrt (x - 1) - 1 ≤ 0 := by
      linarith [h10]
    rw [abs_of_nonpos (by linarith [h14])]
    all_goals 
      linarith
  rw [h6, h8]
  linarith