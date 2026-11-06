import Mathlib

theorem algebra_9313 {f : ℝ → ℝ} (hf : ∀ x, x ≥ 6 → f x = x - 3)
    (hf' : ∀ x, x < 6 → f x = f (f (x + 5))) : f 5 = 4 := by 
  have h1 : f 5 = f (f 10) := by 
    rw [show f 5 = f (f (5 + 5)) by
      apply hf' 5
      norm_num]
    all_goals norm_num
  have h2 : f 10 = 7 := by 
    specialize hf 10 (by norm_num)
    rw [hf]
    norm_num
  have h3 : f 7 = 4 := by 
    specialize hf 7 (by norm_num)
    rw [hf]
    norm_num
  rw [show f (f 10) = f 7 by 
      rw [h2]
      all_goals norm_num
    ] at h1
  rw [show f 7 = 4 by 
      exact h3
    ] at h1
  exact h1