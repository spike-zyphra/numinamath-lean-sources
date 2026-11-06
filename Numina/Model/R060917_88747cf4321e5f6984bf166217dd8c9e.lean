import Mathlib

theorem algebra_226546 : (Real.sqrt 2021 - Real.sqrt 2020)^3 + (Real.sqrt 2020 - Real.sqrt 2019)^3 + (Real.sqrt 2019 - Real.sqrt 2021)^3 < 0 := by
  have h1 : Real.sqrt 2021 > Real.sqrt 2020 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h2 : Real.sqrt 2020 > Real.sqrt 2019 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h3 : Real.sqrt 2021 > 0 := by positivity
  have h4 : Real.sqrt 2020 > 0 := by positivity
  have h5 : Real.sqrt 2019 > 0 := by positivity
  have h6 : Real.sqrt 2021 - Real.sqrt 2020 > 0 := by linarith [h1]
  have h7 : Real.sqrt 2020 - Real.sqrt 2019 > 0 := by linarith [h2]
  have h8 : Real.sqrt 2021 - Real.sqrt 2019 > 0 := by linarith [h1, h2]
  have h9 : (√2021 - √2020) * (√2020 - √2019) > 0 := mul_pos h6 h7
  have h10 : (√2021 - √2020) * (√2020 - √2019) * (√2021 - √2019) > 0 := by
    apply mul_pos h9
    linarith
  have h_mine : (Real.sqrt 2021 - Real.sqrt 2020)^3 + (Real.sqrt 2020 - Real.sqrt 2019)^3 + (Real.sqrt 2019 - Real.sqrt 2021)^3 =
    -3 * ((Real.sqrt 2021 - Real.sqrt 2020) * (Real.sqrt 2020 - Real.sqrt 2019) * (Real.sqrt 2021 - Real.sqrt 2019)) := by
    ring_nf
    <;> nlinarith [sq_nonneg (Real.sqrt 2021 - Real.sqrt 2020), sq_nonneg (Real.sqrt 2020 - Real.sqrt 2019), sq_nonneg (Real.sqrt 2021 - Real.sqrt 2019),
        Real.sqrt_nonneg 2021, Real.sqrt_nonneg 2020, Real.sqrt_nonneg 2019,
        Real.sq_sqrt (show (2021 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (2020 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (2019 : ℝ) ≥ 0 by norm_num)]
  rw [h_mine]
  nlinarith