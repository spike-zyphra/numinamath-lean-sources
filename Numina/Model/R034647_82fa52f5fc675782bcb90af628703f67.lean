import Mathlib

theorem number_theory_604522 (n : ℤ) (hn : n > 0) :
    ¬∃ (a b : ℤ), a > 0 ∧ b > 0 ∧ a * b = n^2 + n + 1 ∧ |(a : ℝ) - b| < 2 * Real.sqrt n := by
  rintro ⟨a, b, ha, hb, heq, h⟩
  have h1 : (a : ℝ) > 0 := by exact_mod_cast ha
  have h2 : (b : ℝ) > 0 := by exact_mod_cast hb
  have h3 : (a : ℝ) * (b : ℝ) = (n : ℝ) ^ 2 + (n : ℝ) + 1 := by
    exact_mod_cast heq
  have h4 : |(a : ℝ) - (b : ℝ)| < 2 * Real.sqrt n := by
    simpa using h
  have h5 : (a : ℝ) - (b : ℝ) > - 2 * Real.sqrt n := by
    cases' abs_lt.mp h4 with h6 h7
    linarith
  have h6 : (a : ℝ) - (b : ℝ) < 2 * Real.sqrt n := by 
    cases' abs_lt.mp h4 with h6 h7
    linarith
  have h7 : ((a - b) : ℝ) ^ 2 < 4 * (n : ℝ) := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (n : ℝ) by exact_mod_cast show 0 < n by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by exact_mod_cast show 0 ≤ n by linarith), sq_nonneg ((a : ℝ) - (b : ℝ) + (2 * Real.sqrt n)), sq_nonneg ((b : ℝ) - (a : ℝ) + (2 * Real.sqrt n))]
  have h8 : ((a + b) : ℝ) ^ 2 < 4 * ((n + 1) : ℝ) ^ 2 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (n : ℝ) by exact_mod_cast show 0 < n by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by exact_mod_cast show 0 ≤ n by linarith), h7, heq]
  have h9 : (a + b : ℝ) < 2 * ((n + 1) : ℝ) := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (n : ℝ) by exact_mod_cast show 0 < n by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by exact_mod_cast show 0 ≤ n by linarith), h7]
  have h10 : (a + b : ℤ) < 2 * (n + 1) := by
    exact_mod_cast h9
  nlinarith [show 0 ≤ (a : ℤ) by linarith, show 0 ≤ (b : ℤ) by linarith, sq_nonneg ((a - b) : ℤ), sq_nonneg ((a - (n + 1)) : ℤ), sq_nonneg ((b - (n + 1)) : ℤ)]