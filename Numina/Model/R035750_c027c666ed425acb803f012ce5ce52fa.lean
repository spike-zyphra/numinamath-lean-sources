import Mathlib

open Real

theorem algebra_170516 {x : ℝ} (hx : 0 < x) (h : x = sqrt (2 + sqrt (2 + sqrt (2 + sqrt (2 + x))))) :
    x = 2 := by
  have h1 : 0 ≤ x := by linarith
  have h2 : x ≤ 2 := by
    by_contra h13
    push_neg at h13
    have h14 : sqrt (2 + sqrt (2 + sqrt (2 + sqrt (2 + x)))) < x := by
      nlinarith [ Real.sqrt_nonneg (2 + sqrt (2 + sqrt (2 + sqrt (2 + x)))),
          Real.sqrt_nonneg (2 + sqrt (2 + sqrt (2 + x))), Real.sqrt_nonneg (2 + sqrt (2 + x)),
          Real.sqrt_nonneg (2 + x), Real.sqrt_nonneg (2 + sqrt (2 + sqrt (2 + sqrt (2 + x)))),
          sq_nonneg (x - 2),
          sq_nonneg (sqrt (2 + sqrt (2 + sqrt (2 + sqrt (2 + x)))) - 2),
          sq_nonneg (sqrt (2 + sqrt (2 + sqrt (2 + x))) - 2),
          sq_nonneg (sqrt (2 + sqrt (2 + x)) - 2),
          sq_nonneg (sqrt (2 + x) - 2),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 + sqrt (2 + sqrt (2 + sqrt (2 + x)))) by positivity),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 + sqrt (2 + sqrt (2 + x))) by positivity),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 + sqrt (2 + x)) by positivity),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 + x) by positivity),
          h13, h, sq_nonneg (x - 2)]
    nlinarith [ Real.sqrt_nonneg (2 + sqrt (2 + sqrt (2 + sqrt (2 + x)))),
          Real.sqrt_nonneg (2 + sqrt (2 + sqrt (2 + x))), Real.sqrt_nonneg (2 + sqrt (2 + x)),
          Real.sqrt_nonneg (2 + x), Real.sqrt_nonneg (2 + sqrt (2 + sqrt (2 + sqrt (2 + x)))),
          sq_nonneg (x - 2),
          sq_nonneg (sqrt (2 + sqrt (2 + sqrt (2 + sqrt (2 + x)))) - 2),
          sq_nonneg (sqrt (2 + sqrt (2 + sqrt (2 + x))) - 2),
          sq_nonneg (sqrt (2 + sqrt (2 + x)) - 2),
          sq_nonneg (sqrt (2 + x) - 2),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 + sqrt (2 + sqrt (2 + sqrt (2 + x)))) by positivity),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 + sqrt (2 + sqrt (2 + x))) by positivity),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 + sqrt (2 + x)) by positivity),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 + x) by positivity),
          h13, h, sq_nonneg (x - 2)]
  have h3 : x ≥ 2 := by
    by_contra h13
    push_neg at h13
    have h14 : sqrt (2 + sqrt (2 + sqrt (2 + sqrt (2 + x)))) < 2 := by
      have h11 : sqrt (2 + sqrt (2 + sqrt (2 + x))) < 2 := by
        have h14 : sqrt (2 + sqrt (2 + x)) < 2 := by
          have h18 : sqrt (2 + x) < 2 := by
            have h230 : (2 + x) < 4 := by
              nlinarith
            have h360 : sqrt (2 + x) < 2 := by
              nlinarith [ Real.sqrt_nonneg (2 + x), Real.sq_sqrt (show (0 : ℝ) ≤ (2 + x) by positivity) ]
            nlinarith
          have h130 : sqrt (2 + sqrt (2 + x)) < 2 := by
            nlinarith [ Real.sqrt_nonneg (2 + sqrt (2 + x)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 + sqrt (2 + x)) by positivity) ]
          nlinarith
        have h130 : sqrt (2 + sqrt (2 + sqrt (2 + x))) < 2 := by
          nlinarith [ Real.sqrt_nonneg (2 + sqrt (2 + sqrt (2 + x))), Real.sq_sqrt (show (0 : ℝ) ≤ (2 + sqrt (2 + sqrt (2 + x))) by positivity) ]
        nlinarith
      have h130 : sqrt (2 + sqrt (2 + sqrt (2 + sqrt (2 + x)))) < 2 := by
        nlinarith [ Real.sqrt_nonneg (2 + sqrt (2 + sqrt (2 + sqrt (2 + x)))),
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 + sqrt (2 + sqrt (2 + sqrt (2 + x)))) by positivity) ]
      nlinarith
    nlinarith [ Real.sqrt_nonneg (2 + sqrt (2 + sqrt (2 + sqrt (2 + x)))),
          Real.sqrt_nonneg (2 + sqrt (2 + sqrt (2 + x))), Real.sqrt_nonneg (2 + sqrt (2 + x)),
          Real.sqrt_nonneg (2 + x), Real.sqrt_nonneg (2 + sqrt (2 + sqrt (2 + sqrt (2 + x)))),
          sq_nonneg (x - 2),
          sq_nonneg (sqrt (2 + sqrt (2 + sqrt (2 + sqrt (2 + x)))) - 2),
          sq_nonneg (sqrt (2 + sqrt (2 + sqrt (2 + x))) - 2),
          sq_nonneg (sqrt (2 + sqrt (2 + x)) - 2),
          sq_nonneg (sqrt (2 + x) - 2),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 + sqrt (2 + sqrt (2 + sqrt (2 + x)))) by positivity),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 + sqrt (2 + sqrt (2 + x))) by positivity),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 + sqrt (2 + x)) by positivity),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 + x) by positivity),
          h13, h, sq_nonneg (x - 2)]
  linarith