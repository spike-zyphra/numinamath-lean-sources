import Mathlib
open Real

/- Two geometric sequences a1, a2, a3, ... and b1, b2, b3, ... have the same common ratio, with a1 = 27, b1 = 99, and a15 = b11. Find a9. -/
theorem algebra_95318 (a b r:ℚ) (ha:a=27) (hb:b=99) (hr:r≠0) (h:a*r^14=b*r^10) : a*r^8=363 := by
  -- obtain the expression of r^4
  rw [ha,hb,((by simp):14=4+10),pow_add,← mul_assoc] at h
  simp [hr] at h
  rw [mul_comm,← div_left_inj' ((by linarith):a≠0),ha] at h
  simp at h
  -- solve by calculation
  rw [((by simp):8=4+4),pow_add,h,ha]
  field_simp;norm_num