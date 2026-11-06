import Mathlib

theorem algebra_309311 {f : ℝ → ℝ} (hf : f = fun x => (2 * x^5 + 2 * x^4 - 53 * x^3 - 57 * x + 54)^2006)
    (x : ℝ) (hx : x = (Real.sqrt 111 - 1) / 2) : f x = 1 := by
  rw [hf, hx]
  have h1 : Real.sqrt 111 ^ 2 = 111 := by 
    exact Real.sq_sqrt (by norm_num)
  have h3 : 2 * ((Real.sqrt 111 - 1: ℝ) / 2) ^ 2 + 2 * ((Real.sqrt 111 - 1: ℝ) / 2) = 55 := by
    nlinarith [h1]
  have eq1 : (2 * ((Real.sqrt 111 - 1: ℝ) / 2) ^ 5 + 2 * ((Real.sqrt 111 - 1: ℝ) / 2) ^ 4 - 53 * ((Real.sqrt 111 - 1: ℝ) / 2) ^ 3 - 57 * ((Real.sqrt 111 - 1: ℝ) / 2) + 54) = -1 := by
    nlinarith [sq_nonneg ((Real.sqrt 111 - 1: ℝ) / 2), sq_nonneg ((Real.sqrt 111 - 1: ℝ) / 2 + 1/2), sq_nonneg ((Real.sqrt 111 - 1: ℝ) / 2 ^ 2), sq_nonneg ((Real.sqrt 111 - 1: ℝ) / 2 ^ 3), sq_nonneg (Real.sqrt 111 - 11), Real.sqrt_nonneg 111, sq_nonneg ((Real.sqrt 111 - 1: ℝ) / 2 - (Real.sqrt 111 -1)/2), sq_nonneg ((Real.sqrt 111 - 1)/2 + 1/2), sq_nonneg ((Real.sqrt 111) ^ 2 - 111), sq_nonneg (2 * ((Real.sqrt 111 - 1: ℝ) / 2) + 1 - Real.sqrt 111), sq_nonneg (Real.sqrt 111 ^ 2 - 111), sq_nonneg ((Real.sqrt 111 ^ 2) - 111)
  ]
  norm_num [eq1]