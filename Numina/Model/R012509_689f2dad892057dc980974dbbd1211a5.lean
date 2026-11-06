import Mathlib

theorem algebra_603367 (x y : ℝ) (h : x^2 + y^2 - 4 * x - 6 * y + 9 = 0) :
    19 ≤ x^2 + y^2 + 12 * x + 6 * y ∧ x^2 + y^2 + 12 * x + 6 * y ≤ 99 := by 
  have h1 : (x - 2) ^ 2 + (y - 3) ^ 2 = 4 := by
    nlinarith 
  have h2 : 19 ≤ x^2 + y^2 + 12 * x + 6 * y := by 
    nlinarith [sq_nonneg (x - 2 - (y - 3) * (16 / 12)), sq_nonneg ((y - 3) - (x - 2) * (12 / 16)), 
          sq_nonneg (x + 6 - (y + 3) * (16 / 12)), sq_nonneg ((y + 3) - (x + 6) * (12 / 16)), 
          sq_nonneg (x + 6 - 2), sq_nonneg (y + 3 + 3), 
          sq_nonneg (x - 2 - (y - 3)), sq_nonneg (y - 3 - (x - 2) * 3 / 4),
          sq_nonneg ((x - 2) * 5), sq_nonneg ((y - 3) * 2),
          mul_nonneg (sq_nonneg (x - 2)) (sq_nonneg (y - 3))
          ]
  have h3 : x^2 + y^2 + 12 * x + 6 * y ≤ 99 := by 
    nlinarith [sq_nonneg (x - 2 - (y - 3) * (16 / 12)), sq_nonneg ((y - 3) - (x - 2) * (12 / 16)), 
          sq_nonneg (x + 6 - (y + 3) * (16 / 12)), sq_nonneg ((y + 3) - (x + 6) * (12 / 16)), 
          sq_nonneg (x + 6 - 2), sq_nonneg (y + 3 + 3), 
          sq_nonneg (x - 2 - (y - 3)), sq_nonneg (y - 3 - (x - 2) * 3 / 4),
          sq_nonneg ((x - 2) * 5), sq_nonneg ((y - 3) * 2),
          mul_nonneg (sq_nonneg (x - 2)) (sq_nonneg (y - 3))
          ]
  exact ⟨h2, h3⟩