import Mathlib

theorem inequalities_229567 (a : ℝ) :
    (∀ x : ℝ, |x - 3| + |x + 2| > a) ↔ a < 5 := by
  constructor
  · -- Assume that for all x, |x - 3| + |x + 2| > a, prove that a < 5
    intro h
    have h0 := h 0
    norm_num at h0
    linarith
  · -- Assume a < 5, prove that ∀ x : ℝ, |x - 3| + |x + 2| > a
    intro ha x
    have h : |x - 3| + |x + 2| ≥ 5 := by
      cases' abs_cases (x - 3) with h1 h1
      · -- Case where x ≥ 3, so |x - 3| = x - 3
        cases' abs_cases (x + 2) with h2 h2
        · -- Case where x + 2 ≥ 0 (x ≥ -2), so |x + 2| = x + 2
          linarith
        · -- Case where x + 2 < 0 (x < -2), so |x + 2| = -(x + 2)
          linarith
      · -- Case where x < 3, so |x - 3| = 3 - x
        cases' abs_cases (x + 2) with h2 h2
        · -- Case where x + 2 ≥ 0 (x ≥ -2), so |x + 2| = x + 2
          linarith
        · -- Case where x + 2 < 0 (x < -2), so |x + 2| = -(x + 2)
          linarith
    linarith