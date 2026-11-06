import Mathlib

theorem algebra_179717 {x : ℝ} (hx : x = (1 + 2 * Real.sqrt 505) / 2) :
    (4 * x^3 - 2023 * x - 2018)^2020 = 1 := by
  have h1 : 2 * x - 1 = 2 * Real.sqrt 505 := by
    rw [hx]
    ring_nf
  have h2 : (2 * x - 1) ^ 2 = 2020 := by
    rw [h1]
    have h3 : (2 * Real.sqrt 505) ^ 2 = 2020 := by
      calc
        (2 * Real.sqrt 505) ^ 2 = 4 * (Real.sqrt 505 ^ 2) := by ring
        _ = 4 * 505 := by rw [Real.sq_sqrt]; all_goals norm_num
        _ = 2020 := by norm_num
    linarith
  have h3 : 4 * x ^ 2 - 4 * x - 2019 = 0 := by
    nlinarith
  have h4 : 4 * x ^ 2 = 4 * x + 2019 := by
    linarith
  have h5 : 4 * x ^ 3 = 2023 * x + 2019 := by
    have h6 : 4 * x^3 = x * (4 * x^2) := by ring
    rw [h6]
    rw [show 4 * x ^ 2 = 4 * x + 2019 by linarith [h4]]
    nlinarith [h4]
  have h7 : (4 * x ^ 3 - 2023 * x - 2018) = 1 := by
    nlinarith [h5]
  rw [h7]
  all_goals norm_num