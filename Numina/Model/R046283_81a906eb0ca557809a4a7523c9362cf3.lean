import Mathlib

theorem algebra_94128 (x : ℝ) (hx : x < 0) :
    ¬ x / |x| > 0 ∧
    ¬ - x^2 > 0 ∧
    ¬ - (2 : ℝ)^x > 0 ∧
    -(x^(-1 : ℝ)) > 0 := by

  have h1 : |x| = -x := by
    rw [abs_of_neg hx]

  have h3 : ¬ x / |x| > 0 := by
    have h2 : x / |x| ≤ 0 := by
      rw [h1]
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show x ≤ 0
        linarith
      · -- Show -x ≥ 0
        linarith
    intro h
    linarith

  have h4 : ¬ -x^2 > 0 := by
    by_contra h
    have : x^2 < 0 := by linarith
    have : x^2 ≥ 0 := sq_nonneg x
    linarith

  have h5 : ¬ - (2 : ℝ)^x > 0 := by
    by_contra h
    have : (2 : ℝ) ^ x > 0 := by positivity
    have : - (2 : ℝ) ^ x < 0 := by linarith
    linarith

  have h6 : -(x^(-1 : ℝ)) > 0 := by
    have h7 : x^(-1 : ℝ) = 1 / x := by
      simp [Real.rpow_neg_one]
    rw [h7]
    have h8 : 1 / x < 0 := by
      apply div_neg_of_pos_of_neg
      norm_num
      linarith
    linarith

  constructor
  · exact h3
  constructor
  · exact h4
  constructor
  · exact h5
  · exact h6