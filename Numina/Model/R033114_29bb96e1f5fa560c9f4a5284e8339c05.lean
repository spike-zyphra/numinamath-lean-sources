import Mathlib

theorem algebra_220335 (x : ℝ) (hx : 0 ≤ x - 1) :
    Real.sqrt (x + 2 * Real.sqrt (x - 1)) + Real.sqrt (x - 2 * Real.sqrt (x - 1)) =
    if x ∈ Set.Icc 1 2 then 2 else 2 * Real.sqrt (x - 1) := by

  have h1 : Real.sqrt (x + 2 * Real.sqrt (x - 1)) = Real.sqrt (x - 1) + 1 := by
    have h2 : (Real.sqrt (x - 1) + 1 : ℝ) ^ 2 = x + 2 * Real.sqrt (x - 1) := by
      have h3 : Real.sqrt (x - 1) ^ 2 = x - 1 := Real.sq_sqrt (by linarith)
      nlinarith
    have h4 : 0 ≤ Real.sqrt (x - 1) + 1 := by
      have h5 : 0 ≤ Real.sqrt (x - 1) := Real.sqrt_nonneg (x - 1)
      linarith
    rw [←h2]
    field_simp [h4]

  have h2 : Real.sqrt (x - 2 * Real.sqrt (x - 1)) = abs (Real.sqrt (x - 1) - 1) := by
    have h3 : x - 2 * Real.sqrt (x - 1) = (Real.sqrt (x - 1) - 1) ^ 2 := by
      have h4 : Real.sqrt (x - 1) ^ 2 = x - 1 := Real.sq_sqrt (by linarith)
      nlinarith
    rw [h3]
    have h4 : Real.sqrt ((Real.sqrt (x - 1) - 1) ^ 2) = abs (Real.sqrt (x - 1) - 1) := by 
      rw [Real.sqrt_sq_eq_abs]
    exact h4

  rw [h1, h2]

  by_cases h3 : x ≤ 2
  · -- 1 ≤ x ≤ 2, so |Real.sqrt (x-1) -1|=1 - Real.sqrt (x-1)
    have h4 : x ≥ 1 := by
      nlinarith

    have h5 : Real.sqrt (x - 1) ≤ 1 := by
      have h6 : x - 1 ≤ 1 := by
        nlinarith
      have h7 : Real.sqrt (x - 1) ≤ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h8 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
      have h9 : Real.sqrt (x - 1) ≤ (1 : ℝ) := by
        nlinarith [h7, h8]
      linarith

    have h7 : abs (Real.sqrt (x - 1) - 1) = 1 - Real.sqrt (x - 1) := by
      rw [abs_of_nonpos (by
        have : Real.sqrt (x - 1) - 1 ≤ 0 := by
          linarith
        linarith
      )]
      all_goals linarith

    rw [h7]
    have h8 : (Real.sqrt (x - 1) : ℝ) + 1 + (1 - Real.sqrt (x - 1)) = 2 := by nlinarith

    have h9 : x ≥ 1 := by
      nlinarith
    have h10 : x ∈ Set.Icc 1 2 := by
      constructor
      · -- Show that 1 ≤ x
        linarith
      · -- Show that x ≤ 2
        linarith

    simp [h10] at *
    all_goals linarith

  · -- x > 2
    have h4 : x > 2 := by
      by_contra h
      push_neg at h
      have : x ≤ 2 := by linarith
      contradiction

    have h5 : Real.sqrt (x - 1) ≥ 1 := by 
      have h6 : x - 1 ≥ 1 := by
        nlinarith
      have h7 : Real.sqrt (x - 1) ≥ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h8 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
      nlinarith [h7, h8]

    have h7 : abs (Real.sqrt (x - 1) - 1) = Real.sqrt (x - 1) - 1 := by
      rw [abs_of_nonneg (by
        have : Real.sqrt (x - 1) - 1 ≥ 0 := by
          nlinarith
        linarith
      )]
      all_goals linarith

    rw [h7]
    have h8 : (Real.sqrt (x - 1) : ℝ) + 1 + (Real.sqrt (x - 1) - 1) = 2 * Real.sqrt (x - 1) := by nlinarith

    have h9 : x ≥ 2 := by
      nlinarith
    have h10 : x ∉ Set.Icc 1 2 := by
      intro h
      have h11 : x ≤ (2 : ℝ) := by
        have h12 : x ∈ Set.Icc 1 2 := h
        have h13 : x ≤ 2 := by
          exact h12.2
        nlinarith
      nlinarith

    simp [h10] at *
    all_goals linarith