import Mathlib
theorem algebra_20418 {f t : ℝ → ℝ} (hf : f = fun x => x ^ 2 - 3) (ht : t = fun x => 9 + 2 * f x) :
    t (f (-2)) = 5 := by 
  have h1 : f (-2) = 1 := by 
    rw [hf]
    norm_num
  have h2 : f 1 = -2 := by 
    rw [hf]
    norm_num
  rw [h1]
  rw [ht]
  simp [h2]
  all_goals norm_num