import Mathlib

theorem number_theory_175260 (a : ℕ → ℤ) (ha : ∀ n, 0 < n → ∀ i j, i ≠ j → a i % n ≠ a j % n)
    (ha' : ∀ n, 0 < n → ∃ m, a m = -n) :
    ∀ n, ∃! m, a m = n := by 
  have h1 := ha 1 (by norm_num) 0 1 (by norm_num)
  norm_num at h1