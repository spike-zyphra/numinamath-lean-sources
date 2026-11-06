import Mathlib

theorem inequalities_170536 (x : ℝ) (hx : x ≠ 3) : |(3 * x + 1) / (x - 3)| < 3 ↔ x < 4 / 3 := by
  constructor
  · -- First direction: |(3 * x + 1) / (x - 3)| < 3 → x < 4 / 3
    intro h
    have h1 : -3 < (3 * x + 1) / (x - 3) := by
      linarith [abs_lt.mp h]
    have h2 : (3 * x + 1) / (x - 3) < 3 := by
      linarith [abs_lt.mp h]
    by_cases h3 : x - 3 > 0
    · -- Assume x - 3 > 0, i.e., x > 3
      have h4 : x > 3 := by linarith
      have h5 : (3 * x + 1) / (x - 3) < 3 := h2
      have h6 : 3 * x + 1 < 3 * (x - 3) := by
        apply (div_lt_iff (by linarith)).mp at h5
        linarith
      nlinarith
    by_cases h3 : x - 3 < 0
    · -- Assume x - 3 < 0, i.e., x < 3
      have h4 : x < 3 := by linarith
      have h7 : -3 < (3 * x + 1) / (x - 3) := h1
      have h8 : -3 * (x - 3) > 3 * x + 1 := by
        apply (lt_div_iff_of_neg' (by linarith)).mp at h7
        linarith
      linarith
    have h4 : x - 3 ≠ 0 := by
      intro h5
      apply hx
      linarith
    have h8 : x - 3 < 0 := by
      by_contra h9
      push_neg at h9
      have h9 : x - 3 = 0 := by
        linarith [show x - 3 ≥ 0 from by nlinarith, show x - 3 ≤ 0 by nlinarith]
      contradiction
    all_goals linarith
  · -- Second direction: x < 4/3 → |(3 * x + 1) / (x - 3)| < 3
    intro h
    have h1 : x < 4 / 3 := h
    have h2 : x < 3 := by linarith
    have h3 : x - 3 < 0 := by linarith
    have h4 : -3 < (3 * x + 1) / (x - 3) := by
      apply (lt_div_iff_of_neg' (by linarith)).mpr
      nlinarith
    have h5 : (3 * x + 1) / (x - 3) < 3 := by
      apply (div_lt_iff_of_neg' (by linarith)).mpr
      nlinarith
    rw [abs_lt]
    constructor <;> linarith