import Mathlib

theorem inequalities_90793 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a < 1) (h2 : b < 1) (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hsum : p + q = 1) :
    a ^ p * b ^ q + (1 - a) ^ p * (1 - b) ^ q ≤ 1 := by
  have hq1 : q = 1 - p := by linarith
  rw [hq1]
  have h3 : 0 ≤ 1 - a := by linarith
  have h4 : 0 ≤ 1 - b := by linarith
  have h5 : a ^ p * b ^ (1 - p) ≤ p * a + (1 - p) * b := by
    apply Real.geom_mean_le_arith_mean2_weighted
    all_goals
      try linarith
  have h6 : (1 - a) ^ p * (1 - b) ^ (1 - p) ≤ p * (1 - a) + (1 - p) * (1 - b) := by
    apply Real.geom_mean_le_arith_mean2_weighted
    all_goals
      try linarith
  have h7 : a ^ p * b ^ (1 - p) + (1 - a) ^ p * (1 - b) ^ (1 - p) ≤ p * a + (1 - p) * b + (p * (1 - a) + (1 - p) * (1 - b)) := by
    linarith [h5, h6]
  have h8 : p * a + (1 - p) * b + (p * (1 - a) + (1 - p) * (1 - b)) = 1 := by
    nlinarith
  linarith [h7, h8]