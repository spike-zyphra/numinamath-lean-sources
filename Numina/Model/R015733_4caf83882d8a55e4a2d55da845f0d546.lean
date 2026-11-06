import Mathlib

theorem algebra_21058 (x : ℝ) (hx : x ≠ -3) : (2 * x - 5) / (x + 3) ≥ 2 ↔ x < -3 := by
  constructor
  · -- Assume $\frac{2x-5}{x+3} \ge 2$ prove $x < -3$
    intro h
    by_cases h1 : x + 3 > 0
    · -- If x + 3 > 0, multiply both sides by x + 3
      have h2 : 2 * x - 5 ≥ 2 * (x + 3) := by
        have h3 : (x + 3) > 0 := h1
        have h4 : (2 * x - 5) / (x + 3) ≥ 2 := h
        have h5 : 2 * x - 5 ≥ 2 * (x + 3) := by
          have h6 : (2 * x - 5) / (x + 3) ≥ 2 := h4
          apply (le_div_iff₀ h3).mp at h6
          nlinarith
        linarith
      nlinarith
    by_cases h2 : x + 3 < 0
    · -- If x + 3 < 0, multiply both sides by x + 3 and reverse inequality
      have : x < -3 := by linarith
      assumption
    · -- x + 3 = 0, which is a contradiction
      have h3 : x + 3 = 0 := by linarith
      have h4 : x = -3 := by linarith
      contradiction
  · -- Assume x < -3 prove $\frac{2x-5}{x+3} \ge 2$
    intro h
    have h1 : x + 3 < 0 := by linarith
    have h4 : (2 * x - 5) / (x + 3) ≥ 2 := by
      apply (le_div_iff_of_neg' (by linarith)).mpr
      nlinarith
    linarith