import Mathlib

theorem algebra_9400 {f g : ℝ → ℝ} (hodd : ∀ x, f (-x) = - f x) (hg : g = fun x => f x + 9) (hg2 : g (-2) = 3) :
    f 2 = 6 := by
  have h1 : g (-2) = f (-2) + 9 := by
    rw [hg]
  rw [h1] at hg2 -- now we have f(-2) + 9 = 3
  have h2 : f (-2) = -6 := by
    linarith
  have h3 : f (-2) = - f 2 := hodd 2 
  rw [h2] at h3
  linarith