import Mathlib

theorem algebra_20354 {n : ℕ} (hn : n ≠ 0) (h : n * (n - 1) / 2 = 55) : n = 11 := by 
  have h1 : n ≤ 11 := by 
    by_contra h2
    push_neg at h2
    have h2 : n ≥ 12 := by omega
    have h3 : n * (n - 1) / 2 > 55 := by
      have h4 : n ≥ 12 := h2
      have h5 : n - 1 ≥ 11 := by
        omega
      have h6 : n * (n - 1) ≥ 132 := by
        have h7 : n ≥ 12 := h4
        have h8 : n - 1 ≥ 11 := by omega
        have h9 : n * (n - 1) ≥ 12 * 11 := by
          nlinarith
        omega
      omega
    omega
  have h2 : n ≥ 11 := by 
    by_contra h2
    push_neg at h2
    have h2 : n ≤ 10 := by omega
    interval_cases n <;> omega
  have h3 : n = 11 := by 
    omega
  exact h3