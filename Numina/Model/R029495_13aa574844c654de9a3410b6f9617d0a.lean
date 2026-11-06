import Mathlib

theorem algebra_98546 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
(h2x : 2*x+y/2≠0) :
((2*x+y/2)^(-1 : ℤ)) * (((2*x)^(-1 : ℤ)) + ((y/2)^(-1 : ℤ))) =
((x*y)^(-1 : ℤ)) := by
  have h1 : ((2 * x + y / 2) ^ (-1 : ℤ)) = (1 / (2 * x + y / 2)) := by 
    simp [zpow_neg_one]
  have h2 : ((2 * x) ^ (-1 : ℤ)) = (1 / (2 * x)) := by 
    simp [zpow_neg_one]
  have h3 : ((y / 2) ^ (-1 : ℤ)) = (1 / (y / 2)) := by 
    simp [zpow_neg_one]
  have h4 : ((x * y) ^ (-1 : ℤ)) = (1 / (x * y)) := by 
    simp [zpow_neg_one]
  rw [h1, h2, h3, h4]
  have h5 : 1 / (y / 2) = 2 / y := by 
    field_simp [hy]
  have eq1 : (1 / (2 * x + y / 2)) * ((1 / (2 * x) ) + (1 / (y / 2))) = (1 / (x * y)) := by
    rw [h5]
    have eq3 : 2 * x + y / 2 = (4 * x + y) / 2 := by 
      ring
    have eq4 : (4 * x + y) ≠ 0 := by
      by_contra h
      have h8 : (2 * x + y / 2 : ℝ ) = 0 := by
        have h9 : (4 * x + y) = 0 := h
        have h10 : (2 * x + y / 2 : ℝ ) = 0 := by
          linarith [h9]
        assumption
      contradiction
    rw [eq3] 
    field_simp [show 2 * x ≠ 0 by 
      intro h'
      apply hx 
      linarith 
    , show y ≠ 0 by 
      exact hy 
    , eq4 
    , show x * y ≠ 0 by 
      apply mul_ne_zero 
      exact hx 
      exact hy 
    ]
    <;> ring
  linarith [eq1]