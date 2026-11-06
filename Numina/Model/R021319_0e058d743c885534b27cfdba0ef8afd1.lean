import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_326984 :
  IsLeast {x | ∃ t : ℝ, x = sqrt (4 * t^2 + 4 * t + 1) + sqrt (4 * t^2 - 7984 * t + 1996^2)} 1997 := by

  constructor
  · -- First part: Show that 1997 is in the set
    use 998
    have h1 : (4 * (998 : ℝ) ^ 2 + 4 * (998 : ℝ) + 1) = (1997 : ℝ) ^ 2 := by
      norm_num
    have h2 : sqrt (4 * (998 : ℝ) ^ 2 + 4 * (998 : ℝ) + 1) = (1997 : ℝ) := by
      rw [h1]
      exact Real.sqrt_sq (by norm_num)
    have h3 : (4 * (998 : ℝ) ^ 2 - 7984 * (998 : ℝ) + (1996 : ℝ) ^ 2) = (0 : ℝ) := by
      norm_num
    have h4 : sqrt (4 * (998 : ℝ) ^ 2 - 7984 * (998 : ℝ) + (1996 : ℝ) ^ 2) = (0 : ℝ) := by
      rw [h3]
      simp
    rw [h2, h4]
    all_goals norm_num
  · -- Second part: Show that no element less than 1997 is in the set
    intro x hx
    rcases hx with ⟨t, ht⟩

    have eq1 : sqrt (4 * t^2 + 4 * t + 1) = |2 * t + 1| := by
      have eq2 : (4 * t^2 + 4 * t + 1 : ℝ) = (2 * t + 1) ^ 2 := by
        ring
      rw [eq2]
      rw [Real.sqrt_sq_eq_abs]

    have eq3 : sqrt (4 * t^2 - 7984 * t + (1996 : ℝ) ^ 2) = |2 * (t - 998)| := by
      have eq4 : (4 * t^2 - 7984 * t + (1996 : ℝ) ^ 2) = (2 * (t - 998)) ^ 2 := by
        nlinarith
      rw [eq4]
      rw [Real.sqrt_sq_eq_abs]

    have h6 : x = |2 * t + 1| + |2 * (t - 998)| := by 
      rw [ht, eq1, eq3]
      all_goals norm_num
    have h7 : x ≥ 1997 := by 
      rw [h6]
      by_cases h1 : 2 * t + 1 ≥ 0
      · -- Case 1: 2t+1 ≥ 0
        rw [abs_of_nonneg h1]
        by_cases h2 : 2 * (t - 998) ≥ 0
        · -- Case 1a: 2(t-998) ≥0
          rw [abs_of_nonneg h2]
          linarith 
        · -- Case 1b: 2(t-998) <0
          rw [abs_of_neg (show 2 * (t - 998) < 0 by linarith)]
          linarith
      · -- Case 2: 2t+1 <0
        rw [abs_of_neg (show 2 * t + 1 < 0 by linarith)]
        by_cases h2 : 2 * (t - 998) ≥ 0
        · -- Case 2a: 2(t-998) ≥0. This is impossible 
          rw [abs_of_nonneg h2]
          nlinarith 
        · -- Case 2b: 2(t-998) <0 
          rw [abs_of_neg (show 2 * (t - 998) < 0 by linarith)]
          linarith 
    linarith