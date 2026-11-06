import Mathlib

theorem number_theory_292821 (m n k : ℕ) (h₀ : 0 < m) (h₁ : 0 < n) (h₂ : 0 < k)
    (h₃ : m^2 + n = k^2 + k) : m ≤ n := by
  have h4 : m ≤ k := by
    by_contra h
    push_neg at h
    have h5 : m ≥ k + 1 := by omega
    have h6 : m^2 ≥ (k + 1) ^2 := by
      nlinarith [h5, show 0 < k from h₂]
    have h7 : m^2 + n = k^2 + k := by linarith [h₃]
    have h8 : k^2 + k ≥ m^2 := by
      nlinarith [show n > 0 by omega, h7]
    have h9 : m^2 > k^2 + k := by
      nlinarith [h6, show (k : ℕ) ≥ 1 by omega]
    nlinarith
  have h10 : n ≥ k := by
    nlinarith [h₃, h4, h₀, h₁, h₂]
  have h11 : m ≤ n := by
    linarith [h10, h4]
  exact h11