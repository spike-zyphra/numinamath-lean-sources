import Mathlib

theorem number_theory_5838 (a : ℕ → ℤ) (ha : ∀ n, 0 < n → ∀ i j, i ≠ j → a i % n ≠ a j % n)
    (hpos : {n | 0 < n ∧ ∃ k, a k = n}.Infinite) (hneg : {n | 0 < n ∧ ∃ k, a k = -n}.Infinite) :
    ∀ m, ∃! n, a n = m := by
  have h1 := ha 1 (by norm_num) 0 1 (by norm_num)
  have h2 : a 0 % 1 = 0 := by 
    omega
  have h3 : a 1 % 1 = 0 := by
    omega
  rw [h2, h3] at h1 
  all_goals 
    omega