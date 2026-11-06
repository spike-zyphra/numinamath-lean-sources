import Mathlib

theorem algebra_276169 {f : ℤ → ℤ} (h : ∀ x y, 0 < x → 0 < y → f (x + y) = f x + f y + 2 * x * y)
    (h1 : f 1 = 4) : f 8 = 88 := by

  have h2 : f 2 = 10 := by
    specialize h 1 1 (by norm_num) (by norm_num)
    norm_num [h1] at h 
    linarith
  
  have h4 : f 4 = 28 := by 
    specialize h 2 2 (by norm_num) (by norm_num)
    norm_num [h2] at h
    linarith
  
  have h8 : f 8 = 88 := by 
    specialize h 4 4 (by norm_num) (by norm_num)
    norm_num [h4] at h
    linarith
  
  exact h8