import Mathlib

theorem algebra_9203 {x y : ℝ} (hx : x^4 + x^2 = 3) (hy : y^4 - y^2 = 3) : x^4 + y^4 = 7 := by 
  have h1 : x^4 = 3 - x^2 := by
    linarith

  have h2 : y^4 = 3 + y^2 := by
    linarith
  
  have h3 : (x^2 + y^2) * (x^2 - y^2 + 1) = 0 := by 
    nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x + y), sq_nonneg (x - y)]

  cases' (mul_eq_zero.1 h3) with h4 h5
  · -- Case $x^2 + y^2 = 0$
    have h41 : x^2 = 0 := by 
      nlinarith [sq_nonneg x, sq_nonneg y]
    have h42 : y^2 = 0 := by 
      nlinarith [sq_nonneg x, sq_nonneg y]
    nlinarith [sq_nonneg x, sq_nonneg y, h41, h42]
  · -- Case $x^2 - y^2 + 1 = 0$
    have h6 : x^2 = y^2 - 1 := by 
      linarith

    have h7 : y^2 - x^2 = 1 := by 
      nlinarith [h6]

    nlinarith [h1, h2, h7, sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x + y)]
  all_goals nlinarith