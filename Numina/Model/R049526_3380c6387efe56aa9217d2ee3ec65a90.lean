import Mathlib

theorem number_theory_193156 (a : ℕ → ℕ) (ha : a 0 = 61)
    (h : ∀ n, a (n + 1) = (Nat.digits 10 (a n)).prod + 13) :
    a 60 = 16 := by
  norm_num [ha, h]