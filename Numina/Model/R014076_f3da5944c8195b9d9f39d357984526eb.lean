import Mathlib

theorem algebra_17048 (n : ℕ) (h : n ≤ 500) :
    (n / 500 : ℝ) * 100 ≥ 85 ↔ n ≥ 425 := by
  constructor
  · -- Assume (n / 500) * 100 >= 85, prove n >= 425
    intro h1
    have h2 : (n : ℝ) / (500 : ℝ) * 100 ≥ (85 : ℝ) := by 
      simpa using h1
    have h3 : (n : ℝ) ≥ (425 : ℝ) := by
      linarith
    have h4 : n ≥ 425 := by
      by_contra h4
      push_neg at h4
      have h5 : n ≤ 424 := by 
        omega
      have h6 : (n : ℝ) ≤ (424 : ℝ) := by
        exact_mod_cast h5
      linarith
    exact h4
  · -- Assume n >= 425, prove (n / 500) * 100 >= 85
    intro h1
    have h2 : (n : ℝ) ≥ (425 : ℝ) := by 
      exact_mod_cast h1
    have h3 : (n : ℝ) / (500 : ℝ) * 100 ≥ (85 : ℝ) := by 
      linarith
    simpa using h3