import Mathlib

theorem number_theory_91816 (f : ℕ → ℤ) (h : ∀ n, ∑ d in n.divisors, d * f (n / d) = 1) :
    f 2023 = 0 := by
  have h0 := h 0
  simp [Finset.sum_singleton] at h0 
  all_goals linarith