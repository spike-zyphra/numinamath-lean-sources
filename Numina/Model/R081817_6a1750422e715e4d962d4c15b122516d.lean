import Mathlib

theorem number_theory_98116 (a : ℕ → ℕ)
    (ha : ∀ n, a n = a (n - 1) + 10) :
    a 14 = 120 := by
  have h0 := ha 0
  norm_num at h0
  all_goals omega