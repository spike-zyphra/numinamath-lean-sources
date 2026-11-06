import Mathlib

/- Brenda and Sally run in opposite directions on a circular track, starting at [diametrically](https://artofproblemsolving.com/wiki/index.php/Diameter) opposite points.  They first meet after Brenda has run 100 meters.  They next meet after Sally has run 150 meters past their first meeting point.  Each girl runs at a constant speed.  What is the length of the track in meters?
$\mathrm{(A) \ } 250 \qquad \mathrm{(B) \ } 300 \qquad \mathrm{(C) \ } 350 \qquad \mathrm{(D) \ }  400\qquad \mathrm{(E) \ } 500$ -/
-- Let `v_B` and `v_S` be Brenda's and Sally's velocities. Let `t_0` and `t_1` be the time at the first and second times they meet. Let `x` be the track length
theorem algebra_1149 (x: ℝ) (h: x > 150) (p: 100 / (x - 150) = (x/2 - 100) / 150): x = 350 := by
  -- 100 * 150 = (x / 2 - 100) * (x - 150)
  rw [div_eq_div_iff (by linarith) (by linarith)] at p
  -- 100 * 150 - 15000 = (x / 2 - 100) * (x - 150) - 15000
  apply_fun (· - 15000) at p
  -- 0 = -(x * 175) + x ^ 2 * (1 / 2)
  ring_nf at p

  have q: 0 = x * (-175 + x/2) := by rw [p]; ring
  symm at q

  -- From q, we derive that x = 0 ∨ -175 + x / 2 = 0
  rw [mul_eq_zero] at q
  cases q with
  | inl s =>
    -- x = 0: not a valid solution
    rw [s] at h; linarith
  | inr s =>
    -- -175 + x / 2 = 0: we can deduce that x = 350
    linarith