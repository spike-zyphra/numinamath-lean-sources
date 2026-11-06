import Mathlib

theorem algebra_3014 : ⌊Real.sqrt 15 + Real.sqrt 13⌋ = 7 := by
  -- Show that $7 \leq \sqrt{15} + \sqrt{13}$ and $\sqrt{15} + \sqrt{13} < 8$
  have h1 : 7 ≤ Real.sqrt 15 + Real.sqrt 13 := by
    nlinarith [Real.sqrt_nonneg 15, Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (15 : ℝ) by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num), sq_nonneg (Real.sqrt 15 - (7 - Real.sqrt 13)), sq_nonneg (Real.sqrt 13 - 3.6), sq_nonneg (Real.sqrt 15 - 3.8), Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num),
          Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (15 : ℝ) by norm_num), Real.sqrt_nonneg (13), Real.sqrt_nonneg (15), show Real.sqrt 13 > 0 by positivity, show Real.sqrt 15 > 0 by positivity]

  have h2 : Real.sqrt 15 + Real.sqrt 13 < 8 := by
    nlinarith [Real.sqrt_nonneg 15, Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (15 : ℝ) by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num), sq_nonneg (Real.sqrt 15 - (8 - Real.sqrt 13)), sq_nonneg (Real.sqrt 13 - 3.8), sq_nonneg (Real.sqrt 15 - 3.9), Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num),
          Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (15 : ℝ) by norm_num), Real.sqrt_nonneg (13), Real.sqrt_nonneg (15), show Real.sqrt 13 > 0 by positivity, show Real.sqrt 15 > 0 by positivity]

  -- Now we use these inequalities to conclude that the floor is 7
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> try tauto
  all_goals nlinarith