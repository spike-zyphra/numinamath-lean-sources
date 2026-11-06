import Mathlib

/- A basketball team's players were successful on 50% of their
two-point shots and 40% of their three-point shots, which resulted
in 54 points. They attempted 50% more two-point shots than
three-point shots. How many three-point shots did they attempt?
(A) 10(B) 15(C) 20(D) 25(E) 30-/
theorem algebra_94314 (x y : ℝ)
(h1 : (1 / 2 : ℝ) * 2 * x + (2 / 5 : ℝ) * 3 * y = 54) (h2 : x = (3 / 2 : ℝ) * y) :
y = 20 := by {
  -- We prove this by plugging h2 into h1 and then rearranging and solving
  -- the equation in one variable that arises.
  rw [h2] at h1
  norm_num at h1
  rw [←right_distrib] at h1
  norm_num at h1
  calc y = (10 / 27) * 27 / 10 * y := by norm_num
       _ = (10 / 27) * (27 / 10 * y) := by rw [mul_div_assoc,mul_assoc]
       _ = (10 / 27) * 54 := by rw [h1]
       _ = 20 := by norm_num

}