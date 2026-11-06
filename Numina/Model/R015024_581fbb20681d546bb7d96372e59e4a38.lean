import Mathlib

theorem algebra_15343 (n : ℕ) : (1/3 : ℚ) + n/7 < 1 ↔ n ≤ 4 := by 
  constructor
  · -- Assume (1/3 : ℚ) + n/7 < 1, prove n ≤ 4
    intro h
    have h1 : (n : ℚ) < (14 / 3 : ℚ) := by
      linarith
    have h2 : n ≤ 4 := by
      by_contra h3
      push_neg at h3
      have h3' : n ≥ 5 := by omega
      have h4 : (n : ℚ) ≥ (5 : ℚ) := by exact_mod_cast h3'
      linarith
    exact h2
  · -- Assume n ≤ 4, prove (1/3 : ℚ) + n/7 < 1
    intro h
    have h2 : n ≤ 4 := by
      omega
    have h3 : (n : ℚ) ≤ (4 : ℚ) := by exact_mod_cast h2
    linarith