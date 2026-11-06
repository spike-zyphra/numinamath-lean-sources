import Mathlib

def f (a b : ℕ) := max (a - b) (b - a)

theorem number_theory_264949 (a : ℕ → ℕ)
    (h₀ : a 0 = 88) (h₁ : a 1 = 24)
    (h₂ : ∀ n, a (n + 2) = f (a n) (a (n + 1))) :
    ∑ i in Finset.range 100, a i = 760 := by
  norm_num [Finset.sum_range_succ, h₀, h₁, h₂, f]