import Mathlib

theorem number_theory_127205 (a : ℕ → ℤ) (ha : ∀ n, 0 < n → ∀ i j, i ≠ j → a i % n ≠ a j % n)
    (ha' : {n | 0 < a n}.Infinite) (ha'' : {n | a n < 0}.Infinite) :
    ∀ m, ∃! n, a n = m := by 
  have h1 := ha 1 (by norm_num) 0 1 (by norm_num)
  norm_num at h1