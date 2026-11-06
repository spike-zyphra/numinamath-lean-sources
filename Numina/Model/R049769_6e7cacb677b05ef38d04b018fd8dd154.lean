import Mathlib

theorem algebra_4721 {x : ℝ} (hx : x = (1 + √2018) / 2) :
    (4 * x ^ 3 - 2021 * x - 2018) ^ 325 = -1 := by

  have h1 : x = (1 + Real.sqrt 2018) / 2 := hx

  have h2 : x - 1 / 2 = Real.sqrt 2018 / 2 := by
    rw [h1]
    ring_nf

  have h3 : (x - 1 / 2) ^ 2 = (Real.sqrt 2018 / 2) ^ 2 := by
    rw [h2]

  have h4 : (Real.sqrt 2018 / 2) ^ 2 = (Real.sqrt 2018) ^ 2 / 4 := by
    ring_nf

  have h5 : (Real.sqrt 2018) ^ 2 = 2018 := by
    rw [Real.sq_sqrt]
    norm_num

  have eq1 : 4 * x ^ 2 - 4 * x - 2017 = 0 := by
    nlinarith [h3, h4, h5]

  have eq2 : 4 * x ^ 2 = 4 * x + 2017 := by
    linarith [eq1]

  have eq3 : 4 * x ^ 3 = 2021 * x + 2017 := by
    have h4 : x ^ 2 = (4 * x + 2017) / 4 := by
      linarith [eq2]
    have h5 : x ^ 3 = x * ( (4 * x + 2017) / 4 ) := by
      calc
        x ^ 3 = x * x ^ 2 := by ring
        _ = x * ( (4 * x + 2017) / 4 ) := by rw [h4]
    calc
      4 * x ^ 3 = 4 * (x * ( (4 * x + 2017) / 4 )) := by rw [h5]
      _ = x * (4 * x + 2017) := by ring
      _ = 2021 * x + 2017 := by
        nlinarith [eq2]

  have eq4 : 4 * x ^ 3 - 2021 * x - 2018 = -1 := by
    linarith [eq3]

  rw [eq4]
  norm_num