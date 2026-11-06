import Mathlib

theorem algebra_184341 {n : ℕ} (hn : n > 0) (h : 6480 * n = 11200 / (n + 3)) :
    n = 5 := by
  have h1 : n + 3 ≤ 11200 := by
    by_contra h2
    push_neg at h2
    have h3 : n + 3 > 11200 := by 
      omega
    have h4 : 11200 / (n + 3) = 0 := by
      rw [Nat.div_eq_zero_iff]
      omega
    rw [h4] at h
    have h5 : 6480 * n = 0 := by 
      omega
    nlinarith
  have h2 : n ≤ 11197 := by
    omega
  interval_cases n <;> norm_num at h <;> omega