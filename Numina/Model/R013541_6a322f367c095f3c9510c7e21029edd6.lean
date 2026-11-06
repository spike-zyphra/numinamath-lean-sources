import Mathlib

theorem number_theory_169946 (n : ℕ) (hn : n > 0) :
    ¬∃ a b, a > 0 ∧ b > 0 ∧ a * b = n^2 + n + 1 ∧ |(a : ℝ) - b| < 2 * Real.sqrt n := by
  rintro ⟨a, b, ha, hb, h1, h2⟩
  have h3 : (a : ℝ) > (0 : ℝ) := by exact_mod_cast (show (a : ℕ) > 0 by linarith)
  have h4 : (b : ℝ) > (0 : ℝ) := by exact_mod_cast (show (b : ℕ) > 0 by linarith)
  have h5 : (a - b : ℝ) ^ 2 < (4 * (n : ℝ) ) := by
    have h6 : |(a : ℝ) - (b : ℝ)| < 2 * Real.sqrt (n : ℝ) := by simpa using h2
    have h7 : ((a : ℝ) - (b : ℝ)) ^ 2 < (2 * Real.sqrt (n : ℝ)) ^ 2 := by
      nlinarith [abs_lt.mp h6, sq_nonneg ((a : ℝ) - (b : ℝ)), Real.sqrt_nonneg (n : ℝ)]
    have h8 : (2 * Real.sqrt (n : ℝ) ) ^ 2 = 4 * (n : ℝ) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity)]
    linarith [h7, h8]
  have h8 : (a * b : ℝ) = (n^2 + n + 1 : ℝ) := by exact_mod_cast h1
  have h9 : (a + b : ℝ) ^ 2 = (a - b : ℝ) ^ 2 + 4 * (a * b : ℝ) := by
    nlinarith
  rw [h8] at h9
  have h10 : (a + b : ℝ) ^ 2 < (4 * ((n : ℝ) + 1) ^ 2 : ℝ) := by
    nlinarith [h5, h9]
  have h11 : (a + b : ℝ) ^ 2 > (2 * (n : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg ((a - (b : ℝ)) : ℝ), h8, h9]
  have h12 : (2 * (n : ℝ) + 1) ^ 2 < (a + b : ℝ) ^ 2 := by linarith [h11]
  have h13 : (a + b : ℝ) < (2 * (n : ℝ) + 2 : ℝ) := by nlinarith [sq_nonneg ((a + b : ℝ) - (2 * (n : ℝ) + 2) : ℝ), h12, h10]
  have h14 : a + b > 2 * n + 1 := by
    by_contra h
    push_neg at h
    have h15 : a + b ≤ 2 * n + 1 := by omega
    have h16 : (a + b : ℝ) ≤ (2 * n + 1 : ℝ) := by exact_mod_cast h15
    nlinarith
  have h15 : a + b < 2 * n + 2 := by
    by_contra h
    push_neg at h
    have h18 : a + b ≥ 2 * n + 2 := by omega
    have h19 : (a + b : ℝ) ≥ (2 * n + 2 : ℝ) := by exact_mod_cast h18
    nlinarith
  exfalso
  omega