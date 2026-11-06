import Mathlib


theorem algebra_290119 {x y z : ℝ} (h : (x^2 - x + 3) * (y^2 - 6 * y + 41) * (2 * z^2 - z + 1) = 77) :
    x * y / z = 6 := by
  have h1 : x^2 - x + 3 ≥ 11 / 4 := by
    nlinarith [sq_nonneg (x - 1 / 2)]
  have h2 : y^2 - 6 * y + 41 ≥ 32 := by
    nlinarith [sq_nonneg (y - 3)]
  have h3 : 2 * z^2 - z + 1 ≥ 7 / 8 := by
    nlinarith [sq_nonneg (z - 1 / 4)]

  have eq1 : x^2 - x + 3 = 11 / 4 := by
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 3), sq_nonneg (z - 1 / 4), 
      mul_nonneg (sq_nonneg (x - 1 / 2)) (sq_nonneg (y - 3)), 
      mul_nonneg (sq_nonneg (y - 3)) (sq_nonneg (z - 1 / 4)), 
      mul_nonneg (sq_nonneg (x - 1 / 2)) (sq_nonneg (z - 1 / 4))]
  have eq2 : y^2 - 6 * y + 41 = 32 := by
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 3), sq_nonneg (z - 1 / 4), 
      mul_nonneg (sq_nonneg (x - 1 / 2)) (sq_nonneg (y - 3)), 
      mul_nonneg (sq_nonneg (y - 3)) (sq_nonneg (z - 1 / 4)), 
      mul_nonneg (sq_nonneg (x - 1 / 2)) (sq_nonneg (z - 1 / 4))]
  have eq3 : 2 * z^2 - z + 1 = 7 / 8 := by
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 3), sq_nonneg (z - 1 / 4), 
      mul_nonneg (sq_nonneg (x - 1 / 2)) (sq_nonneg (y - 3)), 
      mul_nonneg (sq_nonneg (y - 3)) (sq_nonneg (z - 1 / 4)), 
      mul_nonneg (sq_nonneg (x - 1 / 2)) (sq_nonneg (z - 1 / 4))]

  have hx : x = 1 / 2 := by
    nlinarith [sq_nonneg (x - 1 / 2)]
  have hy : y = 3 := by
    nlinarith [sq_nonneg (y - 3)]
  have hz : z = 1 / 4 := by
    nlinarith [sq_nonneg (z - 1 / 4)]

  have h4 : x * y / z = 6 := by
    rw [hx, hy, hz]
    norm_num

  exact h4