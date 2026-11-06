import Mathlib

theorem algebra_34720 (x y : ℤ) (hx : 0 < x) (hy : 0 < y)
    (h : x^3 + y^3 = 4 * (x^2 * y + x * y^2 - 5)) :
    (x, y) = (1, 3) ∨ (x, y) = (3, 1) := by

  have h1 : (x + y) * (x^2 - 5 * x * y + y^2) = -20 := by
    nlinarith [h]

  have h2 : 0 < x + y := by
    nlinarith

  have h3 : (x + y) ∣ -20 := by
    use x^2 - 5 * x * y + y^2
    all_goals linarith [h1]

  have h4 : (x + y) ∣ 20 := by
    exact Int.dvd_neg.mp h3

  have h5 : (x + y) ≤ 20 := by 
    have h6 : (x + y) ∣ 20 := h4
    have h7 : (x + y) ≤ 20 := by
      apply Int.le_of_dvd (by norm_num) h6
    linarith

  have h6 : x ≤ 20 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 4), sq_nonneg (x - 3), sq_nonneg (y - 1)]

  have h7 : y ≤ 20 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 4), sq_nonneg (y - 3), sq_nonneg (x - 1)]

  interval_cases x <;> interval_cases y 
    <;> norm_num at h1 h 
    <;> tauto