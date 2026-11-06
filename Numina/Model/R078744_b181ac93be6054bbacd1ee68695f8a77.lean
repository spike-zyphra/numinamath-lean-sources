import Mathlib

theorem algebra_235014 {f g : ℝ → ℝ} (hg : g = fun x => 1 - x^2)
    (hf : ∀ x ≠ 0, f (g x) = (1 - x^2) / x^2) :
    f (1 / 2) = 1 := by 
  have h1 : g (Real.sqrt (1 / 2)) = 1 - (Real.sqrt (1 / 2)) ^ 2 := by
    rw [hg]
  have h2 : (Real.sqrt (1 / 2)) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have h3 : g (Real.sqrt (1 / 2)) = 1 / 2 := by
    rw [h1]
    rw [h2]
    all_goals norm_num
  have h4 : Real.sqrt (1 / 2) ≠ 0 := by
    have h5 : Real.sqrt (1 / 2) > 0 := Real.sqrt_pos.mpr (by norm_num)
    linarith [h5]
  have h5 : f (g (Real.sqrt (1 / 2))) = (1 - (Real.sqrt (1 / 2)) ^ 2) / ((Real.sqrt (1 / 2)) ^ 2) := hf (Real.sqrt (1 / 2)) h4
  have h6 : f (g (Real.sqrt (1 / 2))) = f (1 / 2) := by
    rw [h3]
  have h7 : (1 - (Real.sqrt (1 / 2)) ^ 2) / ((Real.sqrt (1 / 2)) ^ 2) = 1 := by
    have h8 : (Real.sqrt (1 / 2)) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
    rw [h8]
    norm_num
  rw [h6] at h5
  rw [h7] at h5
  linarith [h5]