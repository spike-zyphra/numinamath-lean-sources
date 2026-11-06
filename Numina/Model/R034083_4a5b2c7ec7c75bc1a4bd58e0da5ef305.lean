import Mathlib

theorem number_theory_251316 (a : ℕ → ℤ) (ha : ∀ n, a n = a (n - 1) + (n + 1)) (ha0 : a 0 = 425) :
    a 5 = 802 ∧ a 6 = 870 ∧ a 7 = 983 := by 
  have h1 := ha 0
  norm_num [ha0] at h1
  all_goals omega