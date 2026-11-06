import Mathlib

theorem inequalities_37343 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    a ^ a * b ^ b + a ^ b * b ^ a ≤ 1 := by
  have hb1 : b = 1 - a := by linarith
  rw [hb1]
  have h1 : a ^ a * (1 - a) ^ (1 - a) ≤ a * a + (1 - a) * (1 - a) := by
    have h2 : 0 ≤ a := by linarith
    have h3 : 0 ≤ 1 - a := by nlinarith
    have h4 : a + (1 - a) = 1 := by linarith
    apply Real.geom_mean_le_arith_mean2_weighted
    all_goals
      try linarith
      try positivity
  have h2 : a ^ (1 - a) * (1 - a) ^ a ≤ (1 - a) * a + a * (1 - a) := by
    have h10 : 0 ≤ a := by linarith
    have h11 : 0 ≤ 1 - a := by nlinarith
    have h12 : (1 - a) + a = 1 := by linarith
    apply Real.geom_mean_le_arith_mean2_weighted
    all_goals
      try linarith
      try positivity
  have h3 : a ^ a * (1 - a) ^ (1 - a) + a ^ (1 - a) * (1 - a) ^ a ≤ 1 := by
    have h10 : a ^ a * (1 - a) ^ (1 - a) ≤ a * a + (1 - a) * (1 - a) := h1
    have h11 : a ^ (1 - a) * (1 - a) ^ a ≤ (1 - a) * a + a * (1 - a) := h2
    have h12 : a ^ a * (1 - a) ^ (1 - a) + a ^ (1 - a) * (1 - a) ^ a ≤ (a * a + (1 - a) * (1 - a)) + ((1 - a) * a + a * (1 - a) ) := by
      linarith
    have h13 : (a * a + (1 - a) * (1 - a)) + ((1 - a) * a + a * (1 - a) ) = 1 := by
      nlinarith
    nlinarith
  simpa using h3