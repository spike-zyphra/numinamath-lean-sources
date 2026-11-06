import Mathlib

theorem algebra_106556 {f : ℝ → ℝ}
    (h : ∀ x, f (x ^ 2 + x) + 2 * f (x ^ 2 - 3 * x + 2) = 9 * x ^ 2 - 15 * x) :
    f 50 = 146 := by
  have eq1 := h ((-1 + Real.sqrt 201) / 2)
  have eq2 := h ((-1 - Real.sqrt 201) / 2)
  have eq3 := h ((3 + Real.sqrt 201) / 2)
  have eq4 := h ((3 - Real.sqrt 201) / 2)
  -- Simplify the expressions in the four substitutions.

  have eq6 : ((-1 + Real.sqrt 201) / 2) ^ 2 + ((-1 + Real.sqrt 201) / 2) = (50 : ℝ) := by
    nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < 201 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 201 by norm_num) ]
  have eq7 : ((-1 + Real.sqrt 201) / 2) ^ 2 - 3 * ((-1 + Real.sqrt 201) / 2) + (2 : ℝ) = (54 - 2 * Real.sqrt 201 : ℝ) := by
    nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < 201 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 201 by norm_num) ]
  have eq8 : ((-1 - Real.sqrt 201) / 2 : ℝ) ^ 2 + ((-1 - Real.sqrt 201) / 2) = (50 : ℝ) := by
    nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < 201 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 201 by norm_num) ]
  have eq9 : ((-1 - Real.sqrt 201) / 2 : ℝ) ^ 2 - 3 * ((-1 - Real.sqrt 201) / 2) + (2 : ℝ) = (54 + 2 * Real.sqrt 201 : ℝ) := by
    nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < 201 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 201 by norm_num) ]
  have eq10 : ((3 + Real.sqrt 201) / 2) ^ 2 - 3 * ((3 + Real.sqrt 201) / 2) + (2 : ℝ) = (50 : ℝ) := by
    nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < 201 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 201 by norm_num) ]
  have eq11 : ((3 + Real.sqrt 201) / 2) ^ 2 + ((3 + Real.sqrt 201) / 2) = (54 + 2 * Real.sqrt 201 : ℝ) := by
    nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < 201 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 201 by norm_num) ]
  have eq12 : ((3 - Real.sqrt 201) / 2) ^ 2 - 3 * ((3 - Real.sqrt 201) / 2) + (2 : ℝ) = (50 : ℝ) := by
    nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < 201 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 201 by norm_num) ]
  have eq13 : ((3 - Real.sqrt 201) / 2) ^ 2 + ((3 - Real.sqrt 201) / 2) = (54 - 2 * Real.sqrt 201 : ℝ) := by
    nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < 201 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 201 by norm_num) ]
  -- Rewrite the substitutions with the simplified expressions.
  norm_num [eq6, eq7] at eq1
  norm_num [eq8, eq9] at eq2
  norm_num [eq10, eq11] at eq3
  norm_num [eq12, eq13] at eq4
  -- Now we prove the goal f 50 = 146 by solving this system.
  have eq14 : Real.sqrt 201 ^ 2 = (201 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  -- This linear solver completes the proof solving.
  ring_nf at eq1 eq2 eq3 eq4
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (201 : ℝ) by norm_num), eq14, sq_nonneg (Real.sqrt (201 : ℝ) ) ]