import Mathlib

theorem inequalities_28417 (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    1 / (1 + a + b) ≤ 1 - (a + b) / 2 + a * b / 3 := by
  have ha0 : 0 ≤ a := ha.1
  have ha1 : a ≤ 1 := ha.2
  have hb0 : 0 ≤ b := hb.1
  have hb1 : b ≤ 1 := hb.2
  have h1 : 0 < 1 + a + b := by
    linarith
  have h7 : 1 ≤ (1 - (a + b)/2 + a * b / 3) * (1 + a + b) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1/2), sq_nonneg (b - 1/2), 
      mul_nonneg (show 0 ≤ a from by linarith) (show 0 ≤ b from by linarith),
      mul_nonneg (show 0 ≤ a from by linarith) (show 0 ≤ (1 - a) from by linarith),
      mul_nonneg (show 0 ≤ b from by linarith) (show 0 ≤ (1 - b) from by linarith),
      mul_nonneg (show 0 ≤ (a + b) from by linarith) (show 0 ≤ (1 - a) from by linarith),
      mul_nonneg (show 0 ≤ (a + b) from by linarith) (show 0 ≤ (1 - b) from by linarith)
    ]
  have h8 : (1 / (1 + a + b)) ≤ 1 - (a + b) / 2 + a * b / 3 := by
    have h9 : 0 < (1 + a + b) := by linarith
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith
  linarith [h8]