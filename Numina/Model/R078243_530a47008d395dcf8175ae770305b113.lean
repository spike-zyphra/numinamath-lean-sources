import Mathlib

theorem number_theory_176193 (n : ℕ) (h₀ : n * (n + 1) * (n + 2) * (n + 3) = 93024) :
    n = 16 := by 
  have h1 : n ≤ 19 := by
    by_contra h
    push_neg at h
    have h2 : n ≥ 20 := by omega
    have h3 : n * (n + 1) * (n + 2) * (n + 3) ≥ 212520 := by
      have h4 : n ≥ 20 := h2
      have h5 : (n : ℕ) * (n + 1) * (n + 2) * (n + 3) ≥ 20 * 21 * 22 * 23 := by
        have h11 : (n : ℕ) * (n + 1) ≥ 20 * 21 := by
          have hn : n ≥ 20 := h4
          have hn1 : n + 1 ≥ 21 := by omega
          nlinarith
        have h14 : (n : ℕ) * (n + 1) * (n + 2) ≥ 20 * 21 * 22 := by
          have h17 : (n + 2 : ℕ) ≥ 22 := by omega
          have h19 : ((n : ℕ) * (n + 1)) * (n + 2) ≥ (20 * 21) * 22 := by
            nlinarith
          linarith
        have h18 : (n + 3 : ℕ) ≥ 23 := by omega
        have h19 : ((n : ℕ) * (n + 1) * (n + 2)) * (n + 3) ≥ (20 * 21 * 22) * 23 := by
          nlinarith
        linarith
      linarith
    linarith
  interval_cases n <;> omega