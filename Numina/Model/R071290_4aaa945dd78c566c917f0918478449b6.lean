import Mathlib

open Real

theorem inequalities_245533 (n : ℕ) (hn : n > 0) :
    1 / 2 ≤ n / (n + 1 : ℝ) ∧ n / (n + 1 : ℝ) < 1 := by
  have h1 : (1 : ℝ) / 2 ≤ (n : ℝ) / (n + 1 : ℝ) := by
    have hn1 : (n : ℝ) > 0 := by exact_mod_cast (show (n : ℕ) > 0 by linarith)
    have h2 : (n + 1 : ℝ) > 0 := by nlinarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [show (n : ℝ) ≥ 1 by exact_mod_cast (show n ≥ 1 by linarith)]
  
  have h2 : (n : ℝ) / (n + 1 : ℝ) < (1 : ℝ) := by
    have hn1 : (n : ℝ) > 0 := by exact_mod_cast (show (n : ℕ) > 0 by linarith)
    have h2 : (n + 1 : ℝ) > 0 := by nlinarith
    have h4 : (n : ℝ) / (n + 1 : ℝ) < (1 : ℝ) := by
      have pos1 : (n + 1 : ℝ) > 0 := by nlinarith
      have h5 : (n : ℝ) < (n + 1 : ℝ) := by nlinarith
      apply (div_lt_iff (by positivity)).mpr
      nlinarith
    exact h4
  
  exact ⟨h1, h2⟩