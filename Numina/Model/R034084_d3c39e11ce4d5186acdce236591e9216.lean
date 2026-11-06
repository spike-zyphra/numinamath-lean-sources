import Mathlib

open Real

theorem inequalities_131075 {p q r : ℝ} (hp : p = 7 - sqrt 47) (hq : q = 5 - sqrt 23)
    (hr : r = 2 - sqrt 2) : p < q ∧ q < r := by
  have hp2 : p < q := by
    rw [hp, hq]
    have h1 : (7 - Real.sqrt 47 : ℝ) < (5 - Real.sqrt 23 : ℝ) := by
      have h2 : (2 + Real.sqrt 23 : ℝ) < Real.sqrt 47 := by
        nlinarith [Real.sqrt_nonneg 23, Real.sqrt_nonneg 47, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (23 : ℝ) by nlinarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (47 : ℝ) by nlinarith), 
          sq_nonneg ((2 + Real.sqrt 23) - Real.sqrt 47), 
          sq_nonneg ((Real.sqrt 23) - 5), 
          Real.sqrt_nonneg 23, Real.sqrt_nonneg 47]
      nlinarith
    exact_mod_cast h1
  have hq2 : q < r := by
    rw [hq, hr]
    have h3 : (5 - Real.sqrt 23 : ℝ) < (2 - Real.sqrt 2 : ℝ) := by
      have h4 : (3 + Real.sqrt 2 : ℝ) < Real.sqrt 23 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 23, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by nlinarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (23 : ℝ) by nlinarith), 
          sq_nonneg ((3 + Real.sqrt 2) - Real.sqrt 23), 
          sq_nonneg ((Real.sqrt 2 - 2) : ℝ), 
          Real.sqrt_nonneg 2, Real.sqrt_nonneg 23]
      nlinarith
    exact_mod_cast h3
  constructor
  · exact hp2
  · exact hq2