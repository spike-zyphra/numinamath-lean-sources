import Mathlib

/- Driving at a constant speed, Sharon usually takes
180 minutes to drive from her house to her mother's house. One day Sharon begins the drive at her usual speed, but after driving
1/3 of the way, she hits a bad snowstorm and reduces her speed by
20 miles per hour. This time the trip takes her a total of
276 minutes. How many miles is the drive from Sharon's house to her mother's house?
(A) 132
(B) 135
(C) 138
(D) 141
(E) 144 -/
theorem algebra_97483 (x v : ℝ) (h : x > 0) (h1 : v > 0) (h1': v-(20/60) > 0)
(h2 : 180 = x/v)
(h3 : 276 = (x/3)/v + (2*x/3)/(v-(20/60))) :
  x = 135 := by
  -- from first equation we get v (in miles per minute)
  apply congr_arg (fun x => 1/180 * (x * v)) at h2
  rw [div_mul_cancel₀] at h2; rotate_left; linarith
  ring_nf at h2; simp at h2
  -- we substitute into second equation and solve for x
  rw [h2] at h3
  ring_nf at h3; rw [mul_inv_cancel₀ (by linarith)] at h3
  apply congr_arg (fun x => (-60+x)*(3/2)) at h3
  norm_num at h3; ring_nf at h3
  apply congr_arg (fun t => t*((-1 / 3 + x * (1 / 180)))) at h3
  rw [mul_assoc, inv_mul_cancel₀ (by linarith)] at h3
  ring_nf at h3; norm_num at h3
  linarith