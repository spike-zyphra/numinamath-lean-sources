import Mathlib

theorem number_theory_15305 (n : ℕ) (h₀ : n > 0) (h₁ : (n * (n + 1) * (n + 2) * (n + 3)) = 840) :
    n + 3 = 7 := by
  have h2 : n ≤ 7 := by
    by_contra h
    push_neg at h
    have h3 : (n * (n + 1) * (n + 2) * (n + 3)) ≥ 8 * 9 * 10 * 11 := by
      have h4 : n ≥ 8 := by linarith
      have h5 : n + 1 ≥ 9 := by linarith
      have h6 : n + 2 ≥ 10 := by linarith
      have h7 : n + 3 ≥ 11 := by linarith
      have h8 : (n : ℕ) * (n + 1) ≥ 8 * 9 := by
        nlinarith
      have h9 : (n + 2 : ℕ) * (n + 3) ≥ 10 * 11 := by
        nlinarith
      nlinarith [h8, h9]
    norm_num at h3 h₁
    omega
  interval_cases n <;> omega