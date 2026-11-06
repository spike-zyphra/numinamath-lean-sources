import Mathlib

theorem number_theory_315517 (a : ℕ → ℤ) (ha : ∀ n, 0 < n → ∀ i j, i ≠ j → a i % n ≠ a j % n)
    (hpos : {x | ∃ n, a n = x ∧ 0 < x}.Infinite) (hneg : {x | ∃ n, a n = x ∧ x < 0}.Infinite) :
    ∀ x, ∃! n, a n = x := by 
  have h1 := ha 1 (by norm_num) 0 1 (by norm_num)
  norm_num at h1
  all_goals trivial