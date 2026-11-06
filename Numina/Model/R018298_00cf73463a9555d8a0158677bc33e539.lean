import Mathlib

open Real

theorem inequalities_259411 (a b c d : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)
    (hc : 0 < c ∧ c < 1) (hd : 0 < d ∧ d < 1) (h : a + b + c + d = 2) :
    sqrt ((1 - a) * (1 - b) * (1 - c) * (1 - d)) ≤ (a * c + b * d) / 2 := by
  have ha1 : 0 < a := ha.1
  have ha2 : a < 1 := ha.2
  have hb1 : 0 < b := hb.1
  have hb2 : b < 1 := hb.2
  have hc1 : 0 < c := hc.1
  have hc2 : c < 1 := hc.2
  have hd1 : 0 < d := hd.1
  have hd2 : d < 1 := hd.2
  have h1 : (1 - a) * (1 - b) * (1 - c) * (1 - d) ≥ 0 := by
    apply mul_nonneg
    apply mul_nonneg
    apply mul_nonneg
    all_goals
      nlinarith
  have h2 : (a * c + b * d) / 2 ≥ 0 := by nlinarith
  have h3 : sqrt ((1 - a) * (1 - b) * (1 - c) * (1 - d)) ≤ (a * c + b * d) / 2 := by
    have h4 : sqrt ((1 - a) * (1 - b) * (1 - c) * (1 - d)) ^ 2 = (1 - a) * (1 - b) * (1 - c) * (1 - d) := by
      rw [Real.sq_sqrt]
      nlinarith
    have h5 : ((a * c + b * d) / 2) ^ 2 ≥ (1 - a) * (1 - b) * (1 - c) * (1 - d) := by
      nlinarith [sq_nonneg (a * c - b * d), sq_nonneg ((a * c + b * d) / 2 - (1 - a) * (1 - c)), sq_nonneg ((1 - b) * (1 - d) - (a * c + b * d) / 2), sq_nonneg (a + c - 1), sq_nonneg (b + d - 1)]
    nlinarith [h4, h5, Real.sqrt_nonneg ((1 - a) * (1 - b) * (1 - c) * (1 - d)), show (a * c + b * d) / 2 ≥ 0 by nlinarith]
  exact h3