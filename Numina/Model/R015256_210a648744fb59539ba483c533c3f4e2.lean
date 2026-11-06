import Mathlib

theorem algebra_216875 (f : ℝ → ℝ) (hf : f = fun x => abs (x ^ 2 - 1) - (1 / 10) * (x + (9 / 10))) :
    Set.ncard {x | f x = 0} = 2 := by
  have h1 : {x | f x = 0} = { (1 + Real.sqrt 437) / 20, ( -1 + Real.sqrt 365) / 20 } := by
    ext x
    simp [hf]
    constructor
    · -- Assume f x = 0
      intro h_eq
      have h_eq0 : abs (x ^ 2 - 1) = (1 / 10) * (x + (9 / 10)) := by linarith
      by_cases h : x ^ 2 - 1 ≥ 0
      · -- Case 1: x ^ 2 - 1 ≥ 0
        have h2 : abs (x ^ 2 - 1) = x ^ 2 - 1 := abs_of_nonneg h
        rw [h2] at h_eq0
        have h3 : 100 * x ^ 2 - 10 * x - 109 = 0 := by
          nlinarith
        have h4 : (x - (1 + Real.sqrt 437) / 20) * (x - (1 - Real.sqrt 437) / 20) = 0 := by
          nlinarith [Real.sqrt_nonneg 437, Real.sq_sqrt (show (437 : ℝ) ≥ 0 by norm_num)]
        cases' (mul_eq_zero.1 h4) with h5 h6
        · -- Case where x = (1 + Real.sqrt 437) / 20
          left
          linarith
        · -- Case where x = (1 - Real.sqrt 437) / 20
          nlinarith [Real.sqrt_nonneg 437, Real.sq_sqrt (show (437 : ℝ) ≥ 0 by norm_num)]
      · -- Case 2: x ^ 2 - 1 < 0
        have h2 : abs (x ^ 2 - 1) = 1 - x ^ 2 := by
          rw [abs_of_neg (show x ^ 2 - 1 < (0 : ℝ) by nlinarith)]
          all_goals linarith
        rw [h2] at h_eq0
        have h4 : 100 * x ^ 2 + 10 * x - 91 = 0 := by
          nlinarith
        have h5 : (x - (-1 + Real.sqrt 365) / 20) * (x - (-1 - Real.sqrt 365) / 20) = 0 := by
          nlinarith [Real.sqrt_nonneg 365, Real.sq_sqrt (show (365 : ℝ) ≥ 0 by norm_num)]
        cases' (mul_eq_zero.1 h5) with h6 h7
        · -- Case where x = (-1 + Real.sqrt 365) / 20
          right
          linarith
        · -- Case where x = (-1 - Real.sqrt 365) / 20
          nlinarith [Real.sqrt_nonneg 365, Real.sq_sqrt (show (365 : ℝ) ≥ 0 by norm_num)]
    · -- Show that the two roots satisfy f x = 0
      rintro (h_eq | h_eq)
      · -- Case 1: x = (1 + Real.sqrt 437) / 20
        have h1 : x ^ 2 - 1 ≥ 0 := by
          nlinarith [Real.sqrt_nonneg 437, Real.sq_sqrt (show (437 : ℝ) ≥ 0 by norm_num)]
        have h2 : abs (x ^ 2 - 1) = x ^ 2 - 1 := abs_of_nonneg h1
        rw [h2]
        nlinarith [Real.sqrt_nonneg 437, Real.sq_sqrt (show (437 : ℝ) ≥ 0 by norm_num)]
      · -- Case 2: x = ( -1 + Real.sqrt 365 ) / 20
        have h1 : x ^ 2 - 1 < 0 := by
          nlinarith [Real.sqrt_nonneg 365, Real.sq_sqrt (show (365 : ℝ) ≥ 0 by norm_num)]
        have h2 : abs (x ^ 2 - 1) = 1 - x ^ 2 := by
          rw [abs_of_neg h1]
          all_goals linarith
        rw [h2]
        nlinarith [Real.sqrt_nonneg 365, Real.sq_sqrt (show (365 : ℝ) ≥ 0 by norm_num)]
  rw [h1]
  have h2 : ( (1 + Real.sqrt 437) / 20 : ℝ ) ≠ ( ( -1 + Real.sqrt 365 ) / 20 ) := by
    nlinarith [Real.sqrt_nonneg 437, Real.sqrt_nonneg 365, Real.sq_sqrt (show (437 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (365 : ℝ) ≥ 0 by norm_num), sq_pos_of_pos (show 0 < Real.sqrt 437 by positivity), sq_pos_of_pos (show 0 < Real.sqrt 365 by positivity) ]
  rw [Set.ncard_pair h2]
  all_goals norm_num