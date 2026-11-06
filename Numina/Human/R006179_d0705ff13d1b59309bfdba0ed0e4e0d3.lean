import Mathlib

theorem algebra_1837 {f : ℝ→ℝ} 
    (hf : ∀x, f x = 9/5 * x + 32) : 
    {x : ℝ | f x = x} = {-40} := by
  ext x
  simp
  constructor
  · intro hx
    rw [hf] at hx
    linarith
  · intro hx
    rw [hx, hf]
    norm_num
