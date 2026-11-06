import Mathlib.Tactic

  theorem algebra_7611 (total_cans : ℕ) (capacity : ℕ) (h₀ : total_cans = 12) (h₁ : capacity = 12) :
  (total_cans / 2) * (capacity / 2) + (total_cans / 3) * (capacity / 3) + (total_cans - (total_cans / 2) - (total_cans / 3)) * (capacity / 6) = 56 := by 
  subst h₀
  subst h₁
  all_goals norm_num