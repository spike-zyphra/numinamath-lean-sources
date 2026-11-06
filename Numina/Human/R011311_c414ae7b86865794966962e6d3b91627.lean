import Mathlib

/- Let $a, b, x, y, z$ be strictly positive real numbers, show that


$$

\frac{x}{a y+b z}+\frac{y}{a z+b x}+\frac{z}{a x+b y} \geq \frac{3}{a+b}

$$
 -/
theorem inequalities_103533 (a b x y z : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    3 / (a + b) ≤ x / (a * y + b * z) + y / (a * z + b * x) +
    z / (a * x + b * y) := by
  calc x / (a * y + b * z) + y / (a * z + b * x) + z / (a * x + b * y)
  -- we need squares for titu's lemma
  _ = (x/x) * (x / (a * y + b * z)) + (y/y) * (y / (a * z + b * x)) + (z/z) * (z / (a * x + b * y)) := by  rw [div_self (by linarith), one_mul, div_self (by linarith), one_mul, div_self (by linarith), one_mul]
  _ = x^2 / (a*x*y+b*x*z) + y^2 / (a*y*z+b*y*x) + z^2 / (a*x*z+b*y*z) := by rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm]; ring_nf
  _ ≥ (x+y+z)^2/ (a*x*y+b*x*z + a*y*z+b*y*x + a*x*z+b*y*z) := by
    -- now we use titu's lemma
    have h1:=Finset.sq_sum_div_le_sum_sq_div (Finset.range 3) (fun i => [x, y, z][i]!) (g:=fun i => [a*x*y+b*x*z, a*y*z+b*y*x, a*x*z+b*y*z][i]!) (by
      simp; intro i hi
      match i with
      | 0 => simp; apply add_pos; apply mul_pos; apply mul_pos; linarith; linarith; linarith; apply mul_pos; apply mul_pos; linarith; linarith; linarith
      | 1 => simp; apply add_pos; apply mul_pos; apply mul_pos; linarith; linarith; linarith; apply mul_pos; apply mul_pos; linarith; linarith; linarith
      | 2 => simp; apply add_pos; apply mul_pos; apply mul_pos; linarith; linarith; linarith; apply mul_pos; apply mul_pos; linarith; linarith; linarith
    )
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h1
    simp at h1 ⊢
    -- simplify to get to the goal
    convert_to (x + y + z) ^ 2 / (a * x * y + b * x * z + (a * y * z + b * y * x) + (a * x * z + b * y * z)) ≤ x ^ 2 / (a * x * y + b * x * z) + y ^ 2 / (a * y * z + b * y * x) + z ^ 2 / (a * x * z + b * y * z)
    ring_nf
    assumption
  _ = (x+y+z)^2/((a+b)*(x*y+y*z+x*z)) := by ring_nf
  _ ≥ 3*(x*y+y*z+x*z)/((a+b)*(x*y+y*z+x*z)) := by
    simp;
    gcongr ?_ / ((a + b) * (x * y + y * z + x * z))
    -- this is a trivial completing the square exercise
    nlinarith [sq_nonneg (x-y), sq_nonneg (y-z), sq_nonneg (z-x)]
  _ = 3 / (a+b) := by rw [← mul_div, mul_comm (a+b), ← div_div, div_self (by positivity), mul_div, mul_one]