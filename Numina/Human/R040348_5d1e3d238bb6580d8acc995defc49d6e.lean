import Mathlib

theorem number_theory_98368 (n d : ℕ) (h₀ : 0 < n) (h₁ : 0 ≤ d ∧ d < n ∧ d ≤ 9)
    (h₂ : Nat.ofDigits n [d, 2, 3] = 263) (h₃ : Nat.ofDigits n [4, 2, 3] =
    Nat.ofDigits 6 [1, d, 1, 1]) : n + d = 11 := by
  simp [Nat.ofDigits, List.foldl] at h₂ h₃
  nlinarith [h₀, h₁.2, sq_nonneg (n - 9), sq_nonneg (n - 10), sq_nonneg (d - 5)]