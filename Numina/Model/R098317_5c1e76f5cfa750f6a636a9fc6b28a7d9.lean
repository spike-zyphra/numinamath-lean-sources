import Mathlib

theorem number_theory_7662 (a : ℕ → ℤ) (ha : ∀ n, 0 < n → ∀ i j, i ≠ j → a i % n ≠ a j % n)
    (ha1 : {n | 0 < n ∧ ∃ m, a m = n}.Infinite) (ha2 : {n | 0 < n ∧ ∃ m, a m = -n}.Infinite) :
    ∀ n, ∃! m, a m = n := by 
  have h1 := ha 1 (by norm_num) 0 1 (by norm_num)
  norm_num at h1
  all_goals linarith