import Mathlib

open Real

theorem inequalities_278505 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (α : ℝ) :
    x ^ sin α ^ 2 * y ^ cos α ^ 2 < x + y := by

  have h1 : sin α ^ 2 + cos α ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq α

  have h2 : x ^ sin α ^ 2 * y ^ cos α ^ 2 ≤ sin α ^ 2 * x + cos α ^ 2 * y := by
    have h4 : 0 ≤ sin α ^ 2 := by positivity
    have h5 : 0 ≤ cos α ^ 2 := by positivity
    have h17 : sin α ^ 2 + cos α ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq α
    have h18 : x ^ sin α ^ 2 * y ^ cos α ^ 2 ≤ sin α ^ 2 * x + cos α ^ 2 * y := by
      apply Real.geom_mean_le_arith_mean2_weighted
      all_goals
        try nlinarith
        try positivity
    linarith

  have h3 : sin α ^ 2 * x + cos α ^ 2 * y < x + y := by
    have h10 : sin α ^ 2 + cos α ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq α
    have h11 : x * cos α ^ 2 + y * sin α ^ 2 > 0 := by
      have h4 : cos α ^ 2 ≥ 0 := by positivity
      have h5 : sin α ^ 2 ≥ 0 := by positivity
      have h9 : x * cos α ^ 2 + y * sin α ^ 2 > 0 := by
        by_contra h
        push_neg at h
        have h9 : x * cos α ^ 2 + y * sin α ^ 2 = 0 := by
          nlinarith [show x * cos α ^ 2 ≥ 0 by positivity, show y * sin α ^ 2 ≥ 0 by positivity]
        have h10 : x * cos α ^ 2 = 0 := by
          nlinarith [show x * cos α ^ 2 ≥ 0 by positivity, show y * sin α ^ 2 ≥ 0 by positivity]
        have h11 : cos α ^ 2 = 0 := by
          nlinarith
        have h12 : sin α ^ 2 = 1 := by
          nlinarith [h11, show sin α ^ 2 + cos α ^ 2 = 1 by exact Real.sin_sq_add_cos_sq α]
        have h13 : y * sin α ^ 2 = y := by
          rw [h12]
          all_goals
            ring
        have h14 : y = 0 := by
          nlinarith [h9, h13, show y * sin α ^ 2 ≥ 0 by positivity]
        linarith
      linarith

    have h12 : sin α ^ 2 * x + cos α ^ 2 * y < x + y := by
      nlinarith [show x * cos α ^ 2 + y * sin α ^ 2 > 0 by linarith [h11], show sin α ^ 2 + cos α ^ 2 = 1 by exact Real.sin_sq_add_cos_sq α]
    linarith

  linarith [h2, h3]