import Mathlib


theorem algebra_9187
    {f : ℝ → ℝ}
    (hodd : ∀ x, f (-x) = - f (x))
    (hfpos : ∀ x > 0, f x = Real.sqrt x) :
    f (-9) = -3 := by
  have h1 : f 9 = Real.sqrt 9 := hfpos 9 (by norm_num)
  have h2 : Real.sqrt 9 = 3 := by
    rw [Real.sqrt_eq_cases]
    norm_num
  have h3 : f 9 = 3 := by 
    rw [h1]
    exact h2
  have h4 : f (-9) = -f 9 := hodd 9
  rw [h3] at h4
  linarith