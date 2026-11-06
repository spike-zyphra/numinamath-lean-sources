import Mathlib

theorem number_theory_193438 :
    ∃ (x : ℚ), |x - Real.sqrt 2| ≤ 0.0001 ∧
    ∃ (x : ℚ), |x - (2 + Real.sqrt 5)| ≤ 0.0001 ∧
    ∃ (x : ℚ), |x - (3 + Real.sqrt 7)| ≤ 0.0001 := by 
  use (99 : ℚ) / 70
  constructor
  · -- Show that |(99 / 70 : ℚ) - Real.sqrt 2| ≤ 0.0001 
    have h1 : |((99 : ℚ) / 70 : ℝ) - Real.sqrt 2| ≤ (0.0001 : ℝ) := by
      have h1a : Real.sqrt 2 = Real.sqrt (2 : ℝ) := by norm_num
      have h2 : |((99 : ℚ) / 70 : ℝ) - Real.sqrt 2| = |( (99 : ℝ) / (70 : ℝ) - Real.sqrt 2)| := by 
        norm_num
      rw [h2]
      have h3 : - (0.0001 : ℝ) ≤ ((99 : ℝ) / (70 : ℝ) - Real.sqrt 2) := by
        nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg ((99 : ℝ) / (70 : ℝ) - Real.sqrt 2), sq_nonneg ((99 : ℝ) / (70 : ℝ) + Real.sqrt 2)]
      have h4 : ((99 : ℝ) / (70 : ℝ) - Real.sqrt 2) ≤ (0.0001 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg ((99 : ℝ) / (70 : ℝ) - Real.sqrt 2), sq_nonneg ((99 : ℝ) / (70 : ℝ) + Real.sqrt 2)]
      apply abs_le.mpr
      constructor <;> linarith
    exact_mod_cast h1
  · -- Show that ∃ (x : ℚ), |x - (2 + Real.sqrt 5)| ≤ 0.0001 ∧ ∃ (x : ℚ), |x - (3 + Real.sqrt 7)| ≤ 0.0001 
    use (305 : ℚ) / 72
    constructor 
    · -- Show that |(305 / 72 : ℚ) - (2 + Real.sqrt 5)| ≤ 0.0001
      have h3a : |((305 : ℚ) / 72 : ℝ) - (2 + Real.sqrt 5)| ≤ (0.0001 : ℝ) := by
        have h5a : |((305 : ℚ) / 72 : ℝ) - (2 + Real.sqrt 5)| = |( (305 / 72 : ℝ) - (2 + Real.sqrt 5) )| := by 
          norm_num
        rw [h5a]
        have h6 : - (0.0001 : ℝ) ≤ ((305 / 72 : ℝ) - (2 + Real.sqrt 5)) := by
          nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg ((305 / 72 : ℝ) - (2 + Real.sqrt 5)), sq_nonneg ((305 / 72 : ℝ) + (2 + Real.sqrt 5))]
        have h7 : ((305 / 72 : ℝ) - (2 + Real.sqrt 5)) ≤ (0.0001 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg ((305 / 72 : ℝ) - (2 + Real.sqrt 5)), sq_nonneg ((305 / 72 : ℝ) + (2 + Real.sqrt 5))]
        apply abs_le.mpr
        constructor <;> linarith
      exact_mod_cast h3a
    · -- Show that ∃ (x : ℚ), |x - (3 + Real.sqrt 7)| ≤ 0.0001 
      use (271 : ℚ) / 48 
      have h9 : |( (271 : ℚ) / 48 : ℝ) - (3 + Real.sqrt 7)| ≤ (0.0001 : ℝ) := by 
        have h8a : |( (271 : ℚ) / 48 : ℝ) - (3 + Real.sqrt 7)| = |( (271 / 48 : ℝ) - (3 + Real.sqrt 7) )| := by 
          norm_num
        rw [h8a]
        have h10 : - (0.0001 : ℝ) ≤ ((271 / 48 : ℝ) - (3 + Real.sqrt 7)) := by
          nlinarith [Real.sqrt_nonneg (7 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), sq_nonneg ((271 / 48 : ℝ) - (3 + Real.sqrt 7)), sq_nonneg ((271 / 48 : ℝ) + (3 + Real.sqrt 7))]
        have h11 : ((271 / 48 : ℝ) - (3 + Real.sqrt 7) ) ≤ (0.0001 : ℝ) := by 
          nlinarith [Real.sqrt_nonneg (7 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), sq_nonneg ((271 / 48 : ℝ) - (3 + Real.sqrt 7)), sq_nonneg ((271 / 48 : ℝ) + (3 + Real.sqrt 7))]
        apply abs_le.mpr
        constructor <;> linarith 
      exact_mod_cast h9