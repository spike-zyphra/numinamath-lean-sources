import Mathlib

theorem inequalities_605796 :
  IsGreatest {x * y | (x : ℝ) (y : ℝ) (_ : x > 0) (_ : y > 0) (_ : x ^ 3 + y ^ 3 ≤ x ^ 2 + y ^ 2)} 1 := by

  constructor
  · -- First, show that 1 is in the set.
    use 1, 1, by norm_num, by norm_num, by norm_num
    all_goals norm_num
  · -- Now, show it's the greatest element.
    intro r hr
    rcases hr with ⟨x, y, hx, hy, h, hr⟩
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1),
              sq_nonneg (x^2 - y^2), sq_nonneg (x^3 - y^3),
              mul_pos hx hy, sq_nonneg (x * y - 1),
              mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith)]