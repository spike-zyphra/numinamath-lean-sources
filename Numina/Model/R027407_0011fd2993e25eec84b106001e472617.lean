import Mathlib

theorem algebra_239971 {n : ℕ} (hn : n > 0) (h : n * (n + 1) / 2 = n * (n + 2) / 2 + 100) :
    n = 10 := by 
  have h1 : n ≤ 200 := by
    by_contra h2
    push_neg at h2
    have h2' : n * (n + 2) / 2 > n * (n + 1) / 2 := by
      have h3 : n + 1 < n + 2 := by
        omega
      have h4 : n * (n + 1) < n * (n + 2) := by 
        nlinarith
      have h5 : n * (n + 2) ≥ n * (n + 1) + 2 := by 
        nlinarith
      omega
    omega 
  interval_cases n <;> omega