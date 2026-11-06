import Mathlib

theorem number_theory_288325 :
    min (min (min (min (2010 : ℝ) (2010 / 2009)) (2009 / 2010)) (2009 ^ ((1 : ℝ) / 200))) (2010 ^ ((1 : ℝ) / 209)) = 2009 / 2010 := by
  have h1 : (2009 / 2010 : ℝ) ≤ (2010 : ℝ) := by
    norm_num
  have h2 : (2009 / 2010 : ℝ) ≤ (2010 / 2009 : ℝ) := by
    norm_num
  have h3 : (2009 / 2010 : ℝ) ≤ (2009 : ℝ) ^ ((1 : ℝ) / 200) := by
    have h4 : (2009 : ℝ) ^ ((1 : ℝ) / 200) ≥ 1 := by
      have h5 : (2009 : ℝ) ≥ 1 := by norm_num
      have h6 : (2009 : ℝ) ^ ((1 : ℝ) / 200) ≥ (1 : ℝ) := by
        apply Real.one_le_rpow
        all_goals linarith
      linarith
    have h7 : (2009 / 2010 : ℝ) < (1 : ℝ) := by
      norm_num
    nlinarith
  have h4 : (2009 / 2010 : ℝ) ≤ (2010 : ℝ) ^ ((1 : ℝ) / 209) := by
    have h8 : (2010 : ℝ) ^ ((1 : ℝ) / 209) ≥ 1 := by
      have h9 : (2010 : ℝ) ≥ 1 := by norm_num
      have h10 : (2010 : ℝ) ^ ((1 : ℝ) / 209) ≥ (1 : ℝ) := by
        apply Real.one_le_rpow
        all_goals linarith
      linarith
    have h11 : (2009 / 2010 : ℝ) < (1 : ℝ) := by
      norm_num
    nlinarith
  norm_num [min_eq_left_of_lt, min_eq_right_of_lt, h1, h2, h3, h4]