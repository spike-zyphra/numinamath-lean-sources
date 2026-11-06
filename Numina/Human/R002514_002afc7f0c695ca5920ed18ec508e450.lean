import Mathlib
open Real

/- Shelby drives her scooter at a speed of 30 miles per hour if it is not raining, and
20 miles per hour if it is raining. Today she drove in the sun in the morning and in
the rain in the evening, for a total of 16 miles in 40 minutes. How many minutes did
she drive in the rain?
(A) 18 (B) 21 (C) 24 (D) 27 (E) 30 -/
theorem algebra_94456 (x y : ℚ)
(h₁ : 30 * x + 20 * y = 16) (h₂ : x + y = 2/3) :
y * 60 = 24 := by
  -- eliminate x
  rw [← @sub_left_inj _ _ y,← add_sub] at h₂;simp at h₂
  rw [h₂] at h₁
  -- solve by calculation
  field_simp at h₁;linarith