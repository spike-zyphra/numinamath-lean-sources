import Mathlib

theorem algebra_285508 {a b c x : ℝ} (ha : a + x ^ 2 = 2006) (hb : b + x ^ 2 = 2007)
    (hc : c + x ^ 2 = 2008) (habc : a * b * c = 3) :
    a / (b * c) + b / (c * a) + c / (a * b) - 1 / a - 1 / b - 1 / c = 1 := by 

  have h1 : b = a + 1 := by
    have h2 : b - a = 1 := by
      nlinarith 
    linarith

  have h2 : c = a + 2 := by
    have h3 : c - a = 2 := by
      nlinarith 
    linarith

  have h4 : a ≠ 0 := by 
    by_contra h
    rw [h] at habc 
    nlinarith

  have h5 : b ≠ 0 := by 
    by_contra h 
    rw [h] at habc 
    nlinarith

  have h6 : c ≠ 0 := by 
    by_contra h 
    rw [h] at habc 
    nlinarith

  have eq2 : a / (b * c) + b / (c * a) + c / (a * b) - 1 / a - 1 / b - 1 / c =
      ( a^2 + b^2 + c^2 - ( b * c + a * c + a * b ) ) / ( a * b * c ) := by
    field_simp [show a ≠ 0 by exact h4, show b ≠ 0 by exact h5, show c ≠ 0 by exact h6]
    ring

  have eq3 : a^2 + b^2 + c^2 - ( b * c + a * c + a * b ) = 3 := by
    rw [show b = a + 1 by linarith [h1], show c = a + 2 by linarith [h2]]
    nlinarith [ sq_nonneg (a + 1), sq_nonneg (a - 1), sq_nonneg (a + 2) ]

  rw [eq2, eq3, habc]
  all_goals norm_num