import Mathlib

theorem algebra_267826 : (|7 - Real.sqrt 50| < |7 - Real.sqrt 60| ∧ |7 - Real.sqrt 50| < |7 - Real.sqrt 70| ∧
    |7 - Real.sqrt 50| < |7 - Real.sqrt 80| ∧ |7 - Real.sqrt 50| < |7 - Real.sqrt 40|) := by
  have h1 : 7 - Real.sqrt 50 < 0 := by
    have h2 : Real.sqrt 50 > 7 := by
      have h1 : Real.sqrt 49 < Real.sqrt 50 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h2 : Real.sqrt 49 = 7 := Real.sqrt_eq_cases.mpr (by norm_num)
      linarith
    linarith
  have h3 : 7 - Real.sqrt 60 < 0 := by
    have h4 : Real.sqrt 60 > 7 := by
      have h1 : Real.sqrt 49 < Real.sqrt 60 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h2 : Real.sqrt 49 = 7 := Real.sqrt_eq_cases.mpr (by norm_num)
      linarith
    linarith
  have h5 : 7 - Real.sqrt 70 < 0 := by
    have h6 : Real.sqrt 70 > 7 := by
      have h1 : Real.sqrt 49 < Real.sqrt 70 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h2 : Real.sqrt 49 = 7 := Real.sqrt_eq_cases.mpr (by norm_num)
      linarith
    linarith
  have h7 : 7 - Real.sqrt 80 < 0 := by
    have h8 : Real.sqrt 80 > 7 := by
      have h1 : Real.sqrt 49 < Real.sqrt 80 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h2 : Real.sqrt 49 = 7 := Real.sqrt_eq_cases.mpr (by norm_num)
      linarith
    linarith
  have h9 : 7 - Real.sqrt 40 > 0 := by
    have h10 : Real.sqrt 40 < 7 := by
      have h1 : Real.sqrt 40 < Real.sqrt 49 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h2 : Real.sqrt 49 = 7 := Real.sqrt_eq_cases.mpr (by norm_num)
      linarith
    linarith
  -- Now we can express the absolute values as:
  -- |7 - sqrt(50)| = sqrt(50) - 7
  have h15 : |(7 : ℝ) - Real.sqrt 50| = Real.sqrt 50 - 7 := by
    rw [abs_of_neg (h1)]
    all_goals linarith
  -- |7 - sqrt(60)| = sqrt(60) - 7
  have h16 : |(7 : ℝ) - Real.sqrt 60| = Real.sqrt 60 - 7 := by
    rw [abs_of_neg (h3)]
    all_goals linarith
  -- |7 - sqrt(70)| = sqrt(70) - 7
  have h17 : |(7 : ℝ) - Real.sqrt 70| = Real.sqrt 70 - 7 := by
    rw [abs_of_neg (h5)]
    all_goals linarith
  -- |7 - sqrt(80)| = sqrt(80) - 7
  have h18 : |(7 : ℝ) - Real.sqrt 80| = Real.sqrt 80 - 7 := by
    rw [abs_of_neg (h7)]
    all_goals linarith
  -- |7 - sqrt(40)| = 7 - sqrt(40)
  have h19 : |(7 : ℝ) - Real.sqrt 40| = 7 - Real.sqrt 40 := by
    rw [abs_of_pos (h9)]
    all_goals linarith
  -- Now we need to show:
  -- 1. sqrt(50) - 7 < sqrt(60) - 7
  have h11 : Real.sqrt 50 < Real.sqrt 60 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- 2. sqrt(50) - 7 < sqrt(70) - 7
  have h12 : Real.sqrt 50 < Real.sqrt 70 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- 3. sqrt(50) - 7 < sqrt(80) - 7
  have h13 : Real.sqrt 50 < Real.sqrt 80 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- 4. sqrt(50) + sqrt(40) < 14
  have h14 : Real.sqrt 50 + Real.sqrt 40 < 14 := by
    nlinarith [Real.sqrt_nonneg 50, Real.sqrt_nonneg 40,
      Real.sq_sqrt (show (50 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (40 : ℝ) ≥ 0 by norm_num),
      Real.sqrt_le_sqrt (show (40 : ℝ) ≤ (49 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (50 : ℝ) ≤ (81 : ℝ) by norm_num)]
  -- Now proving the inequalities
  have h20 : |(7 : ℝ) - Real.sqrt 50| < |(7 : ℝ) - Real.sqrt 60| := by
    rw [h15, h16]
    linarith [h11]
  have h21 : |(7 : ℝ) - Real.sqrt 50| < |(7 : ℝ) - Real.sqrt 70| := by
    rw [h15, h17]
    linarith [h12]
  have h22 : |(7 : ℝ) - Real.sqrt 50| < |(7 : ℝ) - Real.sqrt 80| := by
    rw [h15, h18]
    linarith [h13]
  -- For the last inequality: |7 - sqrt(50)| < |7 - sqrt(40)|
  have h23 : |(7 : ℝ) - Real.sqrt 50| < |(7 : ℝ) - Real.sqrt 40| := by
    rw [h15, h19]
    nlinarith [h14]
  -- Thus the theorem is the combination of these four inequalities:
  exact ⟨h20, h21, h22, h23⟩