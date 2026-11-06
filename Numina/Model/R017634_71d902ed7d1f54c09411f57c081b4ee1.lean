import Mathlib

theorem algebra_113939 (a : ℚ) :
    ∃ q : ℚ, (1 / Real.sqrt (9 + 4 * Real.sqrt 5) + 1 / Real.sqrt (9 - 4 * Real.sqrt 5)) * a + Real.sqrt 5 = q ↔
    a = -1 / 2 := by

  use (0 : ℚ)
  have h1 : Real.sqrt (9 + 4 * Real.sqrt 5) = Real.sqrt 5 + 2 := by
    have h2 : (Real.sqrt 5 + 2 : ℝ) ^ 2 = 9 + 4 * Real.sqrt 5 := by
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)]
    have h3 : Real.sqrt (9 + 4 * Real.sqrt 5) = Real.sqrt 5 + 2 := by
      rw [←h2]
      field_simp
    exact h3
  have h3 : Real.sqrt (9 - 4 * Real.sqrt 5) = Real.sqrt 5 - 2 := by
    have h41 : (Real.sqrt 5 - 2 : ℝ) ^ 2 = 9 - 4 * Real.sqrt 5 := by
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)]
    have h42 : Real.sqrt 5 ≥ 2 := by
      by_contra h
      push_neg at h
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)]
    have h43 : (Real.sqrt 5 - 2 : ℝ) ≥ 0 := by
      linarith
    have h44 : Real.sqrt ((Real.sqrt 5 - 2 : ℝ) ^ 2) = (Real.sqrt 5 - 2 : ℝ) := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg h43]
    have h46 : (9 - 4 * Real.sqrt 5 : ℝ) = (Real.sqrt 5 - 2) ^ 2 := by
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)]
    rw [h46]
    exact h44
  have h5 : (1 / Real.sqrt (9 + 4 * Real.sqrt 5) + 1 / Real.sqrt (9 - 4 * Real.sqrt 5) : ℝ) = 2 * Real.sqrt 5 := by
    rw [h1, h3]
    field_simp [(show (Real.sqrt 5 + 2 : ℝ) ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
    ), (show (Real.sqrt 5 - 2 : ℝ) ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
    )
    ]
    <;> nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
  constructor
  · -- Assume the expression equals 0, prove a = -1/2
    intro h
    -- Now multiply the equation with sqrt(5) to make it rational
    have eq2 : (1 / Real.sqrt (9 + 4 * Real.sqrt 5) + 1 / Real.sqrt (9 - 4 * Real.sqrt 5) : ℝ) * (a : ℝ) + Real.sqrt 5 = (0 : ℝ) := by
      simpa using h
    rw [h5] at eq2
    -- Equation becomes: 2 * sqrt(5) * a + sqrt(5) = 0
    have h7 : Real.sqrt (5 : ℝ) > 0 := by
      positivity
    -- Now equation can be written as sqrt(5) * (2*a + 1) = 0
    have h9 : Real.sqrt (5 : ℝ) * (2 * (a : ℝ) + 1) = 0 := by
      nlinarith
    -- Since sqrt(5) > 0, so Real.sqrt (5) ≠0
    have h10 : 2 * (a : ℝ) + 1 = (0 : ℝ) := by
      apply (mul_left_inj' (ne_of_gt h7)).mp
      linarith
    have h11 : (a : ℝ) = (-1 / 2 : ℝ) := by
      linarith
    have h12 : a = (-1 / 2 : ℚ) := by
      exact_mod_cast h11
    assumption
  · -- Assume a = -1/2 prove the expression equals 0
    intro ha
    have h7 : (a : ℝ) = (-1 / 2 : ℝ) := by
      exact_mod_cast ha
    rw [h5, h7]
    nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]