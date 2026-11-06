import Mathlib

-- A freight train leaves the town of Jenkinsville at 1:00 PM traveling due east at constant speed. Jim, a hobo, sneaks onto the train and falls asleep.
-- At the same time, Julie leaves Jenkinsville on her bicycle, traveling along a straight road in a northeasterly direction (but not due northeast) at 10 miles per hour.
-- At 1:12 PM, Jim rolls over in his sleep and falls from the train onto the side of the tracks.
-- He wakes up and immediately begins walking at 3.5 miles per hour directly towards the road on which Julie is riding.
-- Jim reaches the road at 2:12 PM, just as Julie is riding by. What is the speed of the train in miles per hour?
theorem algebra_611230 (v₁ t₁ t₂ v₂ t₃ v₃ t₄ : ℝ) (ht₁ : t₁ = 1) (hv₂ : v₂ = 10) (ht₂ : t₂ = 1) (hv₃ : v₃ = 3.5) (ht₃ : t₃ = 1 + 12 / 60) (ht₄ : t₄ = 2 + 12 / 60)
  (hv₁ : v₁ > 0) (h : ((t₃ - t₁) * v₁) ^ 2 = ((t₄ - t₂) * v₂) ^ 2 + ((t₄ - t₃) * v₃) ^ 2) : v₁ = 62.5 := by
  rw [ht₁, hv₂, ht₂, hv₃, ht₃, ht₄] at h
  norm_num at h
  rw [pow_two] at h
  apply (Real.sqrt_eq_iff_mul_self_eq_of_pos (by simp [hv₁])).mpr at h
  replace h : 5 * √(625 / 4) = 5 * (1/5 * v₁) := by rw [← h]
  rw [← mul_assoc] at h ;norm_num at h
  have h1 : √ 4 = 2 := by refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_ ;simp ;norm_num
  have h2 : √ 625 = 25 := by refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_ ;simp ;norm_num
  rw [← h,h1,h2] ;norm_num
  