import Mathlib

theorem algebra_319163 {a : ℝ} (h : ∀ x, (x - a) * (x - 8) - 1 = 0 → x = a ∨ x = 8) :
    a = 8 := by 
  by_contra ha
  -- Note that a ≠ 8
  have ha1 : a ≠ 8 := by
    intro h1
    apply ha
    linarith
  -- Find a root of the quadratic equation
  have h1 := h ((a + 8 + Real.sqrt (a ^ 2 - 16 * a + 68)) / 2) 
  have h2 : ((a + 8 + Real.sqrt (a ^ 2 - 16 * a + 68)) / 2 - a) * ((a + 8 + Real.sqrt (a ^ 2 - 16 * a + 68)) / 2 - 8) - 1 = 0 := by
    have h3 : a ^ 2 - 16 * a + 68 > 0 := by
      nlinarith [ sq_nonneg (a - 8) ]
    nlinarith [ Real.sqrt_pos.2 (show a ^ 2 - 16 * a + 68 > 0 by nlinarith [ sq_nonneg (a - 8) ]), 
      Real.sq_sqrt (show a ^ 2 - 16 * a + 68 ≥ 0 by nlinarith [ sq_nonneg (a - 8) ]) ]
  specialize h1 h2 
  have h5 : (a + 8 + Real.sqrt (a ^ 2 - 16 * a + 68)) / 2 = a ∨ (a + 8 + Real.sqrt (a ^ 2 - 16 * a + 68)) / 2 = 8 := by 
    simpa using h1
  rcases h5 with h6 | h7 
  · -- Case where the first root equals a
    nlinarith [ Real.sqrt_pos.2 (show a ^ 2 - 16 * a + 68 > 0 by nlinarith [ sq_nonneg (a - 8) ]), 
      Real.sq_sqrt (show a ^ 2 - 16 * a + 68 ≥ 0 by nlinarith [ sq_nonneg (a - 8) ]) ]
  · -- Case where the first root equals 8
    nlinarith [ Real.sqrt_pos.2 (show a ^ 2 - 16 * a + 68 > 0 by nlinarith [ sq_nonneg (a - 8) ]), 
      Real.sq_sqrt (show a ^ 2 - 16 * a + 68 ≥ 0 by nlinarith [ sq_nonneg (a - 8) ]) ]