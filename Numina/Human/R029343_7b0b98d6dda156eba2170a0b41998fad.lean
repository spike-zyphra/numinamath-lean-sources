import Mathlib

/-Given real numbers $x$ and $y$ satisfy $x^4 + x^2 = 3$, $y^4 - y^2 = 3$. Find the value of $x^4 + y^4$.-/
theorem algebra_9203 {x y : ℝ} (hx : x^4 + x^2 = 3) (hy : y^4 - y^2 = 3) : x^4 + y^4 = 7 := by 
  -- since $x^4+x^2>0$, $x\neq0$.
  have x_neq_zero : x ≠ 0 := by by_contra p; rw [p] at hx; absurd hx; norm_num 
  -- subtracting the two equations we get $(x^2+y^2)(x^2-y^2+1)=0.$
  have zero : (x ^ 2 + y ^ 2) * (x ^ 2 - y ^ 2 + 1) = 0 := by
    have : (x ^ 2 + y ^ 2) * (x ^ 2 - y ^ 2 + 1) = (x ^ 4 + x ^ 2) - (y ^ 4 - y ^ 2) := by ring
    rw [this, hx, hy]; norm_num
  -- as $x\neq0$ therefore $x^2>0$ and $y^2\geqslant0$, $x^2+y^2\neq0$.
  have : x ^ 2 + y ^ 2 ≠ 0 := by 
    have : y ^ 2 ≥ 0 := sq_nonneg y
    have : x ^ 2 > 0 := pow_two_pos_of_ne_zero x_neq_zero
    linarith
  -- from the above equation we get $x^2-y^2+1$ must be zero
  have : x ^ 2 - y ^ 2 + 1 = 0 := eq_zero_of_ne_zero_of_mul_left_eq_zero this zero
  -- adding up the two original equations and we get $(x^4+y^4)+(x^2-y^2)=6$.
  have : (x ^ 4 + y ^ 4) + (x ^ 2 - y ^ 2) = 6 := by linarith
  -- pluging above result into this equation and the desired result follows.
  linarith