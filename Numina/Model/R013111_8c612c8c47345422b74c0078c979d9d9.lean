import Mathlib

theorem number_theory_159488 (n : ℕ) (h₀ : n < 10000000) (h₁ : n - (Nat.digits 10 n).sum + 1 = 9875352) :
    n - (Nat.digits 10 n).sum + 2 = 9875357 := by
  have h₁' : n ≥ (Nat.digits 10 n).sum := by
    by_contra h
    push_neg at h
    have h3 : (Nat.digits 10 n).sum > n := by linarith
    have h4 : n - (Nat.digits 10 n).sum = 0 := by
      omega
    omega
  have h₂ : n - (Nat.digits 10 n).sum = 9875351 := by
    omega
  have h₃ : n ≥ (Nat.digits 10 n).sum := h₁'
  have h₄ : n = (Nat.digits 10 n).sum + 9875351 := by
    omega
  have h₆ : (n : ℕ) % 9 = (Nat.digits 10 n).sum % 9 := by
    rw [Nat.modEq_nine_digits_sum (n)]
  omega