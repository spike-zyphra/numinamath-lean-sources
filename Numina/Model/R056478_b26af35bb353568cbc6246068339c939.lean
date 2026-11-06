import Mathlib

theorem number_theory_203608 (p v : ℕ) (hp : p > 0) (hv : v > 0)
    (h1 : p = 2 * v) (h2 : p * v = 7 * (p - v)) :
    v * (p - v) = 3 * p := by 
  rw [h1] at h2
  by_cases h : v ≤ 3
  .
    interval_cases v <;> omega
  .
    push_neg at h
    have h3 : v ≥ 4 := by omega
    have h4 : 2 * v ^ 2 = 7 * v := by 
      zify at h2 ⊢
      rw [Nat.cast_sub (by omega)] at h2
      ring_nf at h2 ⊢
      omega
    nlinarith [sq_nonneg (v : ℕ), sq_nonneg (2 : ℕ), sq_nonneg (7 : ℕ)]