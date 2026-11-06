import Mathlib

/- The gravitational force that Earth exerts on an object is inversely proportional to the square of the distance between the center of the Earth and the object. When Bill is on the surface of Earth, 4,000 miles from the center, the gravitational force is 600 Newtons. What is the gravitational force (in Newtons) that the Earth exerts on him when he's standing on the moon, 240,000 miles from the center of the earth? Express your answer as a fraction. -/
theorem algebra_11763 {F : ℝ → ℝ} (k : ℝ) (hF : F = fun d => k / d ^ 2) (h : F 4000 = 600) (d : ℝ) (hd : d = 240000) :
    F d = 1 / 6 := by
  -- Use F(4000) = 600 to determine k.
  rw [hd, hF]
  rw [hF] at h
  simp at h 
  simp [-one_div]
  field_simp at h ⊢
  linarith only [h]
  