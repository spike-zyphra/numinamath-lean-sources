import Mathlib

theorem number_theory_607434 (k m n : ℤ) (h₀ : 0 < k) (h₁ : 0 < m) (h₂ : 0 < n)
    (h₃ : m^2 + n = k^2 + k) : m ≤ n := by
  by_contra h
  push_neg at h
  have h4 : k >= m := by
    by_contra h'
    push_neg at h'
    have h5 : k ≤ m - 1 := by omega
    nlinarith
  have h5 : n >= m := by
    have h7 : k^2 + k >= m^2 + m := by
      nlinarith [show k ≥ m from h4, show m ≥ 1 by omega, show k ≥ 1 by omega]
    nlinarith
  linarith