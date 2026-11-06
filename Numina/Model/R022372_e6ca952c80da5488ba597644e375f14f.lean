import Mathlib

theorem number_theory_13028 {n : ℕ} (hn : n > 10 ∧ n < 100) (h : n % 3 = 1) (h' : n % 4 = 1) (h'' : n % 5 = 1) :
    n = 61 := by
  have h1 : n > 10 := hn.1
  have h2 : n < 100 := hn.2
  interval_cases n <;> norm_num at h h' h'' ⊢ <;> omega