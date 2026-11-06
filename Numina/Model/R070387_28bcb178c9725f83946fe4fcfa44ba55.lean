import Mathlib

theorem algebra_21445 {n : ℕ} (h : n ≠ 0) (h1 : 144 / n = 10 + n) :
    n = 8 := by
  have h2 : n ≤ 144 := by
    by_contra h'
    push_neg at h'
    have : 144 / n = 0 := by
      rw [Nat.div_eq_zero_iff]
      omega
    rw [this] at h1
    omega
  interval_cases n <;> omega