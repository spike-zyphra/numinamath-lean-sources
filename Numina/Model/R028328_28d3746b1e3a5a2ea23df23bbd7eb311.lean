import Mathlib

theorem number_theory_229932 {n : ℕ} (h : n < 100) (h' : 1722 / n = 42) :
    1722 / (10 * (n % 10) + (n / 10)) = 123 := by
  interval_cases n <;> norm_num at h' ⊢ <;> try { omega }