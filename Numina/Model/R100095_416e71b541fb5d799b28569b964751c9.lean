import Mathlib

theorem inequalities_245007 (n : ℤ) :
    3 * (n - 5 / 3 : ℝ) - 2 * (4 * n + 1 : ℝ) > 6 * n + 5 ↔ n ≤ -2 := by
  constructor
  · -- Forward direction: if inequality holds, then n ≤ -2.
    intro h
    have h1 : (n : ℝ) < -12 / 11 := by
      norm_num at h ⊢
      linarith
    have h2 : n ≤ -2 := by
      by_contra h2
      push_neg at h2
      have h3 : n ≥ -1 := by omega
      have h4 : (n : ℝ) ≥ (-1 : ℝ) := by exact_mod_cast h3
      linarith
    linarith
  · -- Backward direction: if n ≤ -2, then inequality holds.
    intro h
    have h1 : (n : ℝ) ≤ (-2 : ℝ) := by exact_mod_cast h
    have h2 : (n : ℝ) < -12 / 11 := by
      have h3 : (n : ℝ) ≤ (-2 : ℝ) := by exact_mod_cast h
      linarith
    norm_num at h2 ⊢
    linarith