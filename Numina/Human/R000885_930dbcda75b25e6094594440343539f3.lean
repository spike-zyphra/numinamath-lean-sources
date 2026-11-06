import Mathlib

/- In Heidi's history class, the only grades that count toward the semester average are the $6$ tests she has already taken and the upcoming final exam. The final exam counts as two tests. Heidi has determined that if she earns $99$ points on the final she will have exactly a $90$-point average for the semester. On average, how many points has Heidi scored on each test prior to the final exam? -/
theorem algebra_18844 (x : ℝ) (h : (6 * x + 2 * 99) / 8 = 90) : x = 87 := by
  -- We solve for $x$
  field_simp at h
  apply eq_sub_of_add_eq at h
  apply congrArg (fun x ↦ x / 6) at h
  norm_num at h
  exact h