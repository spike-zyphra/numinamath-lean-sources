import Mathlib

theorem algebra_263013 {n : ℕ} (hn : n > 0) (h1 : (n / 10) * (n + 15) = n * 3) :
    n = 900 := by 
  have h2 : n ≤ 30 := by
    by_contra h
    push_neg at h
    have h3 : n ≥ 31 := by omega
    have h4 : (n / 10) * (n + 15) ≥ (3) * (n + 15) := by
      have h5 : n / 10 ≥ 3 := by
        omega
      nlinarith
    have h6 : (n / 10) * (n + 15) > n * 3 := by
      have h5 : (n / 10) * (n + 15) ≥ (3) * (n + 15) := by
        have h7 : n / 10 ≥ 3 := by
          omega
        nlinarith
      have h8 : (3) * (n + 15) > n * 3 := by
        nlinarith
      nlinarith
    nlinarith
  interval_cases n <;> omega