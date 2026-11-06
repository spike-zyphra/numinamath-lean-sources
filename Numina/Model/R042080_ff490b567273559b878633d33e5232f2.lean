import Mathlib
theorem algebra_212740 (a b c x : ℝ) (hx : x ≤ 0) (ha : a - x = 2019) (hb : b + abs x = 2020)
    (hc : c + Real.sqrt (x^2) = 2021) (habc : a * b * c = 24) :
    ((a / (b * c) + b / (c * a) + c / (a * b) - 1 / a - 1 / b - 1 / c) ^ ((1 : ℝ) / 3)) =
    1 / 2 := by

  have h1 : a = x + 2019 := by linarith
  have h2 : abs x = -x := by
    rw [abs_of_nonpos (show x ≤ 0 by linarith)]
  have h3 : b = x + 2020 := by
    linarith [hb, h2]
  have h4 : Real.sqrt (x ^ 2) = -x := by
    have h5 : Real.sqrt (x ^ 2) = abs x := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h5]
    rw [abs_of_nonpos (show x ≤ 0 by linarith)]
  have h6 : c = x + 2021 := by
    linarith [hc, h4]

  -- Solving for x
  have eq2 : x = -2017 := by
    have eq1 : a * b * c = 24 := habc
    rw [show a = x + 2019 by linarith [h1], show b = x + 2020 by linarith [h3], show c = x + 2021 by linarith [h6]] at eq1
    have eq3 : (x + 2020 - 3) * ((x + 2020) ^ 2 + 3 * (x + 2020) + 8) = 0 := by
      nlinarith [sq_nonneg (x + 2020 - 3), sq_nonneg (x + 2020 + 3 / 2)]
    cases' (mul_eq_zero.mp eq3) with eq4 eq5
    · -- Case $x + 2020 - 3 = 0$, so $x + 2020 = 3$, and $x = -2017$
      linarith 
    · -- Show the quadratic is not satisfied
      nlinarith [sq_nonneg ((x + 2020) + 3 / 2)]

  -- Computing A, B, c
  have ha1 : a = 2 := by
    rw [eq2] at h1
    linarith
  have hb1 : b = 3 := by 
    rw [eq2] at h3 
    linarith 
  have hc1 : c = 4 := by 
    rw [eq2] at h6 
    linarith

  -- Computing the value inside the cube root
  have h7 : a / (b * c) + b / (c * a) + c / (a * b) - 1 / a - 1 / b - 1 / c = (1 : ℝ) / 8 := by 
    rw [ha1, hb1, hc1]
    norm_num

  -- Computing the cube root of the value
  rw [h7]
  have h8 : (( (1 : ℝ) / 8 ) : ℝ) ^ ((1 : ℝ) / 3) = (1 / 2 : ℝ) := by 
    have h9 : ((1 / 8 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) = (1 / 2 : ℝ) := by 
      rw [show (1 / 8 : ℝ) = (1 / 2 : ℝ) ^ (3 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      norm_num 
      all_goals norm_num 
    linarith
  exact h8