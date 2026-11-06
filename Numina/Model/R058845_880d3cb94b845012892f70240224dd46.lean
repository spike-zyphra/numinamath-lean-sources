import Mathlib

theorem algebra_95393 {f : ℝ → ℝ} (hf : ∀ x, f x = 4 ^ x) :
    ∀ x, f (x + 1) - f x = 3 * f x := by 
  intro x
  have hfx : f x = (4 : ℝ) ^ x := by 
    apply hf
  have hfx1 : f (x + 1) = (4 : ℝ) ^ (x + 1) := by 
    apply hf 
  rw [hfx1, hfx]
  have h : (4 : ℝ) ^ (x + 1) = (4 : ℝ) ^ x * (4 : ℝ) := by 
    rw [Real.rpow_add]
    norm_num 
    all_goals linarith 
  rw [h]
  ring_nf 
  <;> all_goals linarith 
  all_goals norm_num