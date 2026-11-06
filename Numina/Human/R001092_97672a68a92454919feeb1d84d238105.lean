import Mathlib

open Real

/- The diameter of a circle is 16. By what number must the radius be decreased in order to decrease the area of the circle by $48\pi$? -/
theorem algebra_20412 {radius diameter decreasedradius : ℝ} (hr2 : 0 < decreasedradius) (hdr : diameter = 2 * radius) (hd : diameter = 16) (h : π * radius ^ 2 - π * decreasedradius ^ 2 = 48 * π) : radius - decreasedradius = 4 := by
  -- $radius = 8$
  have hr : radius = 8 := by
    linarith
  rw [← mul_sub, mul_comm, hr] at h
  apply eq_div_of_mul_eq at h
  field_simp at h
  apply eq_add_of_sub_eq at h
  rw [add_comm] at h
  apply sub_eq_of_eq_add at h
  -- $decreasedradius = 4$
  have hdreq : decreasedradius = 4 := by
    have sqeq : decreasedradius ^ 2 = 4 ^ 2 := by
      rw [← h]
      ring
    apply eq_or_eq_neg_of_sq_eq_sq at sqeq
    rcases sqeq with eq | eq
    exact eq
    linarith
  -- so the radius must be decreased by $4$
  rw [hr, hdreq]
  ring
  exact pi_ne_zero