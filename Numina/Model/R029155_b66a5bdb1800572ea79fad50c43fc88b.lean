import Mathlib

theorem algebra_222063 {n : ℕ} (hn : n > 0) (h : (n - 3) * 60 + 3 * (800 / n) = 800) :
    n = 5 := by
  have h1 : n ≤ 800 := by
    by_contra h2
    push_neg at h2
    have h3 : 800 / n = 0 := by
      rw [Nat.div_eq_zero_iff]
      omega
    rw [h3] at h
    omega
  interval_cases n <;> norm_num at h <;> omega