import Mathlib

theorem number_theory_298575 (m : ℕ) (h : ∀ n, m ∣ 1992^n - 999 * n - 1) :
    m ≤ 999 := by
  have h1 := h 1
  have h2 := h 0
  norm_num at h1 h2
  have h3 : m ∣ 992 := by
    exact h1
  have h4 : m ≤ 992 := by
    exact Nat.le_of_dvd (by norm_num) h3
  linarith