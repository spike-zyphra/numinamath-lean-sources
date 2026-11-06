import Mathlib

theorem algebra_12677 {f : ℕ → ℝ} (h : ∀ a b n : ℕ, 0 < a → 0 < b → 0 < n → a + b = 2 ^ n → f a + f b = n ^ 2) :
    f 2002 = 96 := by 
  have eq1 := h 2002 46 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have eq2 := h 46 18 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have eq3 := h 18 14 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have eq4 := h 14 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have eq5 := h 2 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at eq1 eq2 eq3 eq4 eq5
  linarith