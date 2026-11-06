import Mathlib

open Real

theorem algebra_198764 (x : ℤ) (hx : x ≥ 3 + sqrt (3 + sqrt (3 + sqrt (3 + sqrt (3 + sqrt 3))))) :
    x ≥ 6 := by 
  by_contra h
  push_neg at h
  have h1 : x ≤ 5 := by
    omega
  have h2 : (x : ℝ) ≤ (5 : ℝ) := by exact_mod_cast h1
  have h3 : 3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt 3)) )) > 5 := by
    have h17 : Real.sqrt (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt 3)))) > 2 := by
      have h18 : 3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt 3))) > 4 := by
        have h19 : Real.sqrt (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt 3))) > Real.sqrt 3 := by
          have h19 : 3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt 3)) > (3 : ℝ) := by
            have h20 : Real.sqrt (3 + Real.sqrt (3 + Real.sqrt 3)) > 0 := by
              positivity
            nlinarith [Real.sqrt_nonneg (3 + Real.sqrt (3 + Real.sqrt 3)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 + Real.sqrt (3 + Real.sqrt 3)) by positivity ), Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by positivity ) ]
          have h21 : Real.sqrt (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt 3))) > Real.sqrt (3 : ℝ) := by
            apply Real.sqrt_lt_sqrt
            all_goals nlinarith [Real.sqrt_nonneg (3 + Real.sqrt (3 + Real.sqrt 3)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 + Real.sqrt (3 + Real.sqrt 3)) by positivity ), Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by positivity ) ]
          linarith
        nlinarith [Real.sqrt_nonneg (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt 3))), Real.sq_sqrt (show (0 : ℝ) ≤ (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt 3)) ) by positivity ), Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by positivity ) ]
      have h16 : Real.sqrt (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt 3)))) > 2 := by
        nlinarith [Real.sqrt_nonneg (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt 3)) ) ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt 3)) ) ) by positivity ) ]
      linarith
    nlinarith [Real.sqrt_nonneg (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt 3)) ) ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt 3)) ) ) by positivity ) ]
  have h4 : (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt 3)) )) ) > (5 : ℝ) := h3
  have h5 : (x : ℝ) ≥ (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt (3 + Real.sqrt 3)) )) ) := by exact_mod_cast hx
  nlinarith