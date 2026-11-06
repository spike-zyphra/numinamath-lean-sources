import Mathlib

open Real

theorem algebra_128589 :
    (min (min (min (min (sqrt 2018 / 2017) (sqrt 2016 / 2015)) (sqrt 2019 / 2018)) (sqrt 2017 / 2016)) (sqrt 2020 / 2019)) = sqrt 2020 / 2019 := by
  have h1 : sqrt 2018 / 2017 ≥ sqrt 2020 / 2019 := by
    have h2 : (sqrt 2018 / 2017) ≥ (sqrt 2020 / 2019) := by
      have h3 : sqrt 2018 * 2019 ≥ sqrt 2020 * 2017 := by
        have h4 : (sqrt 2018 * 2019) ^ 2 ≥ (sqrt 2020 * 2017) ^ 2 := by
          have h5 : (sqrt 2018) ^ 2 = (2018 : ℝ) := by
            exact sq_sqrt (by linarith)
          have h6 : (sqrt 2020) ^ 2 = (2020 : ℝ) := by 
            exact sq_sqrt (by linarith)
          nlinarith [Real.sqrt_nonneg (2018 : ℝ), Real.sqrt_nonneg (2020 : ℝ), 
            sq_nonneg (sqrt 2018 - sqrt 2020)]
        have h7 : sqrt 2018 * 2019 ≥ 0 := by 
          positivity
        have h8 : sqrt 2020 * 2017 ≥ 0 := by
          positivity
        nlinarith
      linarith
    linarith
  have h2 : sqrt 2016 / 2015 ≥ sqrt 2020 / 2019 := by
    have h2 : (sqrt 2016 / 2015) ≥ (sqrt 2020 / 2019) := by
      have h3 : sqrt 2016 * 2019 ≥ sqrt 2020 * 2015 := by
        have h4 : (sqrt 2016 * 2019) ^ 2 ≥ (sqrt 2020 * 2015) ^ 2 := by
          have h5 : (sqrt 2016) ^ 2 = (2016 : ℝ) := by 
            exact sq_sqrt (by linarith)
          have h6 : (sqrt 2020) ^ 2 = (2020 : ℝ) := by 
            exact sq_sqrt (by linarith)
          nlinarith [Real.sqrt_nonneg (2016 : ℝ), Real.sqrt_nonneg (2020 : ℝ), 
            sq_nonneg (sqrt 2016 - sqrt 2020)]
        have h7 : sqrt 2016 * 2019 ≥ 0 := by
          positivity
        have h8 : sqrt 2020 * 2015 ≥ 0 := by
          positivity
        nlinarith
      linarith
    linarith
  have h3 : sqrt 2019 / 2018 ≥ sqrt 2020 / 2019 := by
    have h2 : (sqrt 2019 / 2018) ≥ (sqrt 2020 / 2019) := by
      have h3 : sqrt 2019 * 2019 ≥ sqrt 2020 * 2018 := by
        have h4 : (sqrt 2019 * 2019) ^ 2 ≥ (sqrt 2020 * 2018) ^ 2 := by
          have h5 : (sqrt 2019) ^ 2 = (2019 : ℝ) := by 
            exact sq_sqrt (by linarith)
          have h6 : (sqrt 2020) ^ 2 = (2020 : ℝ) := by 
            exact sq_sqrt (by linarith)
          nlinarith [Real.sqrt_nonneg (2019 : ℝ), Real.sqrt_nonneg (2020 : ℝ), 
            sq_nonneg (sqrt 2019 - sqrt 2020)]
        have h7 : sqrt 2019 * 2019 ≥ 0 := by
          positivity
        have h8 : sqrt 2020 * 2018 ≥ 0 := by
          positivity
        nlinarith
      linarith
    linarith
  have h4 : sqrt 2017 / 2016 ≥ sqrt 2020 / 2019 := by
    have h2 : (sqrt 2017 / 2016) ≥ (sqrt 2020 / 2019) := by
      have h3 : sqrt 2017 * 2019 ≥ sqrt 2020 * 2016 := by
        have h4 : (sqrt 2017 * 2019) ^ 2 ≥ (sqrt 2020 * 2016) ^ 2 := by
          have h5 : (sqrt 2017) ^ 2 = (2017 : ℝ) := by
            exact sq_sqrt (by linarith)
          have h6 : (sqrt 2020) ^ 2 = (2020 : ℝ) := by 
            exact sq_sqrt (by linarith)
          nlinarith [Real.sqrt_nonneg (2017 : ℝ), Real.sqrt_nonneg (2020 : ℝ), 
            sq_nonneg (sqrt 2017 - sqrt 2020)]
        have h7 : sqrt 2017 * 2019 ≥ 0 := by
          positivity
        have h8 : sqrt 2020 * 2016 ≥ 0 := by 
          positivity
        nlinarith
      linarith
    linarith
  norm_num [min_eq_right, h1, h2, h3, h4]