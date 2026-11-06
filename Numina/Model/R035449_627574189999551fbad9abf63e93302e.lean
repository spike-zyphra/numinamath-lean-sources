import Mathlib

theorem number_theory_158838 (a b c d : ℕ) (ha : 0 < a) (hb : b = 2 * a ^ 2)
    (hc : c = 2 * b ^ 2) (hd : d = 2 * c ^ 2) (h : a * 100 + b * 10 + c = d) :
    a = 1 := by
  rw [hd, hc, hb] at h
  have h1 : a ≤ 10 := by
    by_contra h1
    push_neg at h1
    have h2 : a * 100 + (2 * a ^ 2) * 10 + (2 * (2 * a ^ 2) ^ 2) < 2 * (2 * (2 * a ^ 2) ^ 2) ^ 2 := by
      have h3 : a ≥ 11 := by omega
      have h4 : 2 * (2 * (2 * a ^ 2) ^ 2) ^ 2 > a * 100 + (2 * a ^ 2) * 10 + (2 * (2 * a ^ 2) ^ 2) := by
        have ha11 : a ≥ 11 := by linarith
        have h6 : (2 * (2 * a ^ 2) ^ 2 : ℕ) ≥ 1 := by nlinarith
        have h7 : a * 100 + (2 * a ^ 2) * 10 + (2 * (2 * a ^ 2) ^ 2) < 2 * (2 * (2 * a ^ 2) ^ 2) ^ 2 := by
          nlinarith [sq_nonneg (a : ℕ), sq_nonneg ((a : ℕ) ^ 2), sq_nonneg ((2 * a ^ 2 : ℕ)), sq_nonneg ((2 * (2 * a ^ 2) ^ 2 : ℕ)), sq_nonneg ((a : ℕ) - 1 : ℤ), sq_nonneg ((a : ℕ) ^ 2 - 1 : ℤ)]
        linarith
      nlinarith
    nlinarith
  interval_cases a <;> omega