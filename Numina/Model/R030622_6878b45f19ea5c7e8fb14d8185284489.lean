import Mathlib

theorem algebra_96860 {x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0)
(h1 : Real.logb 2 (x * y * z - 3 + Real.logb 5 x) = 5)
(h2 : Real.logb 3 (x * y * z - 3 + Real.logb 5 y) = 4)
(h3 : Real.logb 4 (x * y * z - 3 + Real.logb 5 z) = 4)
(h1Valid: x * y * z - 3 + Real.logb 5 x > 0)
(h2Valid: x * y * z - 3 + Real.logb 5 y > 0)
(h3Valid: x * y * z - 3 + Real.logb 5 z > 0)
: abs (Real.logb 5 x) + abs (Real.logb 5 y) + abs (Real.logb 5 z) = 265 := by

  have h1' : x * y * z - 3 + Real.logb 5 x = (32 : ℝ) := by
    have h1Valid' : x * y * z - 3 + Real.logb 5 x > 0 := h1Valid
    rw [Real.logb_eq_iff_rpow_eq] at h1
    · nlinarith
    all_goals linarith

  have h2' : x * y * z - 3 + Real.logb 5 y = (81 : ℝ) := by
    have h2Valid' : x * y * z - 3 + Real.logb 5 y > 0 := h2Valid
    rw [Real.logb_eq_iff_rpow_eq] at h2
    · nlinarith
    all_goals linarith

  have h3' : x * y * z - 3 + Real.logb 5 z = (256 : ℝ) := by
    have h3Valid' : x * y * z - 3 + Real.logb 5 z > 0 := h3Valid
    rw [Real.logb_eq_iff_rpow_eq] at h3
    · nlinarith
    all_goals linarith

  have eq1 : Real.logb 5 x = 35 - (x * y * z) := by
    linarith

  have eq2 : Real.logb 5 y = 84 - (x * y * z) := by
    linarith

  have eq3 : Real.logb 5 z = 259 - (x * y * z) := by
    linarith

  have eq4 : Real.logb 5 x + Real.logb 5 y + Real.logb 5 z = (378 : ℝ) - 3 * (x * y * z) := by
    linarith [eq1, eq2, eq3]

  have eq5 : Real.logb 5 x + Real.logb 5 y + Real.logb 5 z = Real.logb 5 (x * y * z) := by
    simp [Real.logb_mul, hx.ne.symm, hy.ne.symm, hz.ne.symm]

  have eq6 : Real.logb 5 (x * y * z) = (378 : ℝ) - 3 * (x * y * z) := by
    linarith [eq4, eq5]

  have h4 : x * y * z = 125 := by
    by_cases h : x * y * z < (125 : ℝ)
    · -- Assume $t < 125$
      have h5 : Real.logb (5 : ℝ) (x * y * z) < (3 : ℝ) := by
        have h7 : x * y * z < (125 : ℝ) := by linarith
        have h6 : Real.logb (5 : ℝ) (x * y * z) < Real.logb (5 : ℝ) (125 : ℝ) := by
          apply Real.logb_lt_logb
          all_goals
            norm_num
            all_goals nlinarith [show 0 < x * y * z by positivity, show x * y * z < (125 : ℝ) by linarith, show 0 < (125 : ℝ) by norm_num]
        have h8 : Real.logb (5 : ℝ) (125 : ℝ) = 3 := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        linarith [h6, h8]

      have h9 : 3 * (x * y * z) + Real.logb (5 : ℝ) (x * y * z) < (378 : ℝ) := by
        nlinarith [h5, show (x * y * z) < (125 : ℝ) by linarith]

      nlinarith [eq6, h9]

    · -- Assume $t \geq 125$
      by_cases h : x * y * z > (125 : ℝ)
      · -- Assume $t > 125$
        have h5 : Real.logb (5 : ℝ) (x * y * z) > (3 : ℝ) := by
          have h7 : x * y * z > (125 : ℝ) := by linarith
          have h6 : Real.logb (5 : ℝ) (125 : ℝ) < Real.logb (5 : ℝ) (x * y * z) := by
            apply Real.logb_lt_logb
            all_goals
              norm_num
              all_goals nlinarith [show 0 < x * y * z by positivity, show x * y * z > (125 : ℝ) by linarith, show 0 < (125 : ℝ) by norm_num]

          have h8 : Real.logb (5 : ℝ) (125 : ℝ) = 3 := by
            rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
          linarith [h6, h8]

        have h9 : 3 * (x * y * z) + Real.logb (5 : ℝ) (x * y * z) > (378 : ℝ) := by
          nlinarith [h5, show (x * y * z) > (125 : ℝ) by linarith]

        nlinarith [eq6, h9]

      · -- $t \leq 125$ and $t \geq 125$ implies $t = 125$
        have h7 : x * y * z = (125 : ℝ) := by linarith
        linarith

  have h5x : Real.logb 5 x = -90 := by
    rw [eq1]
    linarith

  have h5y : Real.logb 5 y = -41 := by
    rw [eq2]
    linarith

  have h5z : Real.logb 5 z = 134 := by
    rw [eq3]
    linarith

  rw [h5x, h5y, h5z]
  norm_num [abs_of_nonneg, abs_of_nonpos]