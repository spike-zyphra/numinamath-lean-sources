import Mathlib

theorem algebra_221750 {n : ℕ} (hn : n > 0) (h : (n - 2) * (10 + (175 / n)) = 175) :
    n = 7 := by
  have h1 : n ≤ 175 := by
    by_contra h2
    push_neg at h2
    have h3 : 175 / n = 0 := by
      rw [Nat.div_eq_zero_iff]
      omega
    rw [h3] at h
    have h4 : (n - 2) * 10 = 175 := by
      omega
    have h5 : n ≤ 19 := by
      omega
    omega
  interval_cases n <;> norm_num at h ⊢ <;> omega