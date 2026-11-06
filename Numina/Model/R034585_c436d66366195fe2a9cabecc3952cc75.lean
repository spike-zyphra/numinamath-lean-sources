import Mathlib

theorem inequalities_281426:
  IsGreatest {m | ∀ x y z : ℝ, x + y + z = 0 → m * x^2 * y^2 * z^2 ≤ (x^2 + y^2 + z^2)^3} 54 := by
  constructor
  · -- Show 54 is in the set
    intro x y z h
    have h1 : z = -x - y := by linarith
    rw [h1] at *
    have eq1 : (x ^ 2 + y ^ 2 + (-x - y) ^ 2 ) = 2 * (x^2 + y^2 + x * y) := by 
      nlinarith 
    nlinarith [sq_nonneg (x * y - (x * (-x - y))), sq_nonneg (y * (-x - y) - (x * (-x - y))), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x + (-x - y)), sq_nonneg (y + (-x - y)), sq_nonneg (x * y), sq_nonneg ((x + y) * (x - y)), sq_nonneg ((x - (-x - y)) * (y - (-x - y))), sq_nonneg (x * (x + y) - y * (x + y)), sq_nonneg ((x + y) * (x * y)), sq_nonneg (x * (x + y) * y), sq_nonneg ((x * (-x - y)) * (y * (-x - y))), sq_nonneg ((x * y) * (x * y)), sq_nonneg ((x + y) * (x + y)), sq_nonneg ((x - (-x - y)) * (x - (-x - y))), sq_nonneg ((y - (-x - y)) * (y - (-x - y)))]
  · -- Show 54 is the greatest
    intro m hm
    have h2 := hm 1 1 (-2 : ℝ) (by norm_num)
    norm_num at h2 
    nlinarith