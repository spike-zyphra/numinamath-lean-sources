import Mathlib

theorem number_theory_293568 (k m n : ℤ) (hk : k > 0) (hm : m > 0) (hn : n > 0)
    (h : m^2 + n = k^2 + k) : m ≤ n := by
  have h₁ : m < k + 1 := by nlinarith
  nlinarith
