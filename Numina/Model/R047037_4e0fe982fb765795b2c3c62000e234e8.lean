import Mathlib

open Real

theorem inequalities_227990 (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (hsum : r + s = 1) :
    r ^ r * s ^ s + r ^ s * s ^ r ≤ 1 := by
  have h1 : s = 1 - r := by linarith
  have h2 : r ^ r * s ^ s ≤ r * r + s * s := by
    have h3 : s = 1 - r := h1
    rw [h3]
    have h4 : 0 < (1 - r : ℝ) := by
      nlinarith
    have h10 : r ^ r * (1 - r : ℝ) ^ (1 - r : ℝ) ≤ r * r + (1 - r : ℝ) * (1 - r : ℝ) := by
      have h11 : r ≥ 0 := by linarith
      have h12 : (1 - r : ℝ) ≥ 0 := by nlinarith
      have h13 : r + (1 - r : ℝ) = 1 := by linarith
      have h14 : r ^ r * (1 - r : ℝ) ^ (1 - r : ℝ) ≤ r * r + (1 - r : ℝ) * (1 - r : ℝ) := by
        have h18 : r ^ r * (1 - r : ℝ) ^ (1 - r : ℝ) ≤ r * r + (1 - r : ℝ) * (1 - r : ℝ) := by
          apply Real.geom_mean_le_arith_mean2_weighted
          all_goals
            try linarith
        linarith
      linarith
    linarith
  have h3 : r ^ s * s ^ r ≤ 2 * r * s := by
    have h3 : s = 1 - r := h1
    rw [h3]
    have h4 : 0 < (1 - r : ℝ) := by
      nlinarith
    have h10 : r ^ (1 - r : ℝ) * (1 - r : ℝ) ^ r ≤ 2 * r * (1 - r : ℝ) := by
      have h11 : r ^ (1 - r : ℝ) * (1 - r : ℝ) ^ r ≤ (1 - r : ℝ) * r + r * (1 - r : ℝ) := by
        have h12 : r ^ (1 - r : ℝ) * (1 - r : ℝ) ^ r ≤ (1 - r : ℝ) * r + r * (1 - r : ℝ) := by
          have h13 : r ^ (1 - r : ℝ) * (1 - r : ℝ) ^ r ≤ (1 - r : ℝ) * r + r * (1 - r : ℝ) := by
            apply Real.geom_mean_le_arith_mean2_weighted
            all_goals
              try linarith
          linarith
        linarith
      have h14 : (1 - r : ℝ) * r + r * (1 - r : ℝ) = 2 * r * (1 - r : ℝ) := by
        ring_nf
      nlinarith [h14]
    linarith
  have h30 : r ^ r * s ^ s + r ^ s * s ^ r ≤ r * r + s * s + 2 * r * s := by
    linarith [h2, h3]
  have h31 : r * r + s * s + 2 * r * s = 1 := by
    have h27 : s = 1 - r := h1
    rw [h27]
    have h13 : 0 < (1 - r : ℝ) := by nlinarith
    nlinarith [hsum]
  linarith [h31, h30]