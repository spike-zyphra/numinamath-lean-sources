import Mathlib

/- 13. Xiao Li drives from location A to location B. After 2 hours, the car breaks down at location C. It takes 40 minutes to repair the car, and after the repair, the speed is only 75% of the normal speed, resulting in arriving at B 2 hours later than the planned time. If the car breaks down 72 kilometers past location C at location D, with the repair time and the speed after repair still being 40 minutes and 75% of the normal speed, respectively, then he arrives only 1.5 hours later than the planned time. Therefore, the distance between A and B is $\qquad$ kilometers. -/
theorem algebra_108945 (t_ab t_ac t_ad t_ab' t_ab'' t_cb' t_db' ab ac cb db cd v: ℝ) (ht_ac : t_ac = 2)
    (ht_ab : t_ab = ab / v) (ht_cb' : t_cb' = cb / (0.75*v)) (hcb : cb = ab - ac) (hac : ac = 2 * v)
    (ht_ab' : t_ab' = t_ab + 2 - 2/3) (ht_ab'₂ : t_ab' = t_ac + t_cb') (hcd : cd = 72)
    (ht_ad : t_ad = t_ac + cd/v) (hdb : db = cb - cd) (ht_db' : t_db' = db / (0.75*v))
    (ht_ab'' : t_ab'' = t_ab + 1.5 - 2/3) (ht_ab''₂ : t_ab'' = t_ad + t_db') (hv : v ≠ 0) : ab = 288 := by
  --Rewrite cb in terms of ab and v
  rw[hac] at hcb
  --Rewrite the time to travel cb at reduced speed in terms of ab and v
  rw [hcb] at ht_cb'
  --Rewrite the time to travel ab at reduced speed in terms of ab and v
  rw[ht_ac, ht_cb'] at ht_ab'₂
  --Match the two times equations in one
  have eq1 : 2 + (ab - 2 * v) / (0.75 * v) = t_ab + 2 - 2/3 := by linarith
  --Rewrite db in terms of ab and v
  rw [hcb, hcd] at hdb
  --Rewrite the time to travel db at reduced speed in terms of ab and v
  rw [hdb] at ht_db'
  --Rewrite the time to travel ab at reduced speed in the second scenario in terms of ab and v
  rw [ht_ad, ht_ac, hcd, ht_db'] at ht_ab''₂
  --Match the two times equations of the second scenario in one
  have eq2 : 2 + 72/v + (ab - 2*v - 72) / (0.75 * v) = t_ab + 1.5 - 2/3 := by linarith
  --Subtract the two times equations previously defined
  have eq3 : (2 + 72/v + (ab - 2*v - 72) / (0.75 * v)) - (2 + (ab - 2 * v) / (0.75 * v))
    = (t_ab + 1.5 - 2/3) - (t_ab + 2 - 2/3) := by linarith
  --Simply the new equation
  ring_nf at eq3
  field_simp at eq3
  --Calculate the velocity
  norm_num at eq3
  --Rewrite the first time equation in terms of ab and t_ab
  rw [← eq3] at eq1
  --Simplify the equation
  ring_nf at eq1
  --Rewrite the first time equation in terms of t_ab
  rw [ht_ab, ← eq3] at eq1
  --Solve the equation by linear arithmetic
  linarith