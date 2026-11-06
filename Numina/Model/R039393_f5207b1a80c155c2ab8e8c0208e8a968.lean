import Mathlib

theorem algebra_228856 (x y : ℤ) (h : 3*x^2+5*y^2=345) :
    x+y ≤ 13 ∧ ∃ x y, 3*x^2+5*y^2=345 ∧ x+y=13 := by

  have h1 : x ≤ 10 := by
    nlinarith [h, sq_nonneg (x), sq_nonneg (y)]

  have h2 : x ≥ -10 := by
    nlinarith [h, sq_nonneg (x), sq_nonneg (y)]

  have h3 : y ≤ 8 := by
    nlinarith [h, sq_nonneg (x), sq_nonneg (y)]

  have h4 : y ≥ -8 := by
    nlinarith [h, sq_nonneg (x), sq_nonneg (y)]

  constructor
  · -- First part: show that for all integer solutions, x+y ≤ 13
    have h5 : x + y ≤ 13 := by
      interval_cases x <;> interval_cases y
      <;> omega
    linarith
  · -- Second part: show that there exists a solution with x+y = 13
    use 10, 3
    all_goals norm_num