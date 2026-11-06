import Mathlib

open Real Set

/-- Points A and B lie on the graph of y=log⁡_2 x. The midpoint of AB is (6,2).
    What is the positive difference between the x-coordinates of AA and BB?
    (A) 211(B) 43(C) 8(D) 45(E) 9 -/
theorem algebra_95732 {f : ℝ → ℝ} (hf : f = λ x => logb 2 x)
    (Ax Bx : ℝ) (hAx : Ax > 0) (hBx : Bx > 0) (hABx : (Ax + Bx) / 2 = 6) (hABy : (f Ax + f Bx)/2 = 2) :
    abs (Bx - Ax) = 4 * sqrt 5 := by
  -- Denote by x_A and x_B the respective x-coordinates.
  obtain rfl := hf
  -- From the midpoint equation, we get x_B = 12 - x_A.
  obtain rfl : Bx = 12 - Ax := by linarith
  -- Hence we can substitute the y-coordinate equation for (log_2 x_A + log_2 (12 - x_A))/2 = 4,
  simp at hABy
  -- or equivalently, log_2 (x_A * (12 - x_A)) = 4
  rw[← logb_mul hAx.ne.symm hBx.ne.symm , div_eq_iff (by simp),
  -- hence 16 = x_A * (12 - x_A).
     logb_eq_iff_rpow_eq (by simp) (by simp) (mul_pos hAx hBx)] at hABy
  -- This yields a quadratic equation x_A^2 - 12 x_A + 16 = 0
  have : 1 * (Ax * Ax) + (-12) * Ax + 16 = 0 := by
    rw[mul_sub, ← pow_two, ← neg_inj, neg_sub, Eq.comm, eq_neg_iff_add_eq_zero, mul_comm] at hABy
    rw[← hABy]
    norm_num
    ring
  -- which has two real solutions x_A = (12 ± √80)/3.
  rw[quadratic_eq_zero_iff (s := sqrt 80) ?quad1 ?quad2] at this
  -- We need to show that for both of these x_A, |12 - x_A^2| = 4 √5.
  -- But in both cases, this follows from a simple computation combined with the fact that √80 = 4√5.
  rcases this with (rfl|rfl)
  · convert_to |12 - (- -12 + 4 * √5) / (2 * 1) - (- -12 + 4 * √5) / (2 * 1)| = 4 * √5 using 5
    · congr 1
      rw[sqrt_eq_iff_eq_sq, mul_pow, sq_sqrt] <;> norm_num
    · rw[sqrt_eq_iff_eq_sq, mul_pow, sq_sqrt] <;> norm_num
    · ring_nf
      rw[abs_neg]
      rw[abs_eq_self]
      norm_num
  · convert_to |12 - (- -12 - 4 * √5) / (2 * 1) - (- -12 - 4 * √5) / (2 * 1)| = 4 * √5 using 5
    · congr 1
      rw[sqrt_eq_iff_eq_sq, mul_pow, sq_sqrt] <;> norm_num
    · rw[sqrt_eq_iff_eq_sq, mul_pow, sq_sqrt] <;> norm_num
    · ring_nf
      rw[abs_eq_self]
      norm_num
  · case quad1 => norm_num
  · case quad2 => unfold discrim; norm_num