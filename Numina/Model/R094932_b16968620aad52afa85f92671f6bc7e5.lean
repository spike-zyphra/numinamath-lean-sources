import Mathlib

theorem algebra_200990 (a b c : ℤ) (h₀ : a = 8) (h₁ : b = 0) (h₂ : c = 8) : a + b = c := by 
  rw [h₀, h₁, h₂]
  all_goals norm_num
  <;> try omega