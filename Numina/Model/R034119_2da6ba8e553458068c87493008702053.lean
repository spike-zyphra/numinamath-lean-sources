import Mathlib

theorem inequalities_315493 (a b c : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) :
    (a + b + c) * (1 - a * b * c) ≤ 2 := by
  have h1 : 0 ≤ a * b * c := by
    apply mul_nonneg
    apply mul_nonneg
    all_goals
      nlinarith
  have h2 : a * b * c ≤ 1 := by
    have ha2 : a ≤ 1 := ha.2
    have hb2 : b ≤ 1 := hb.2
    have hc2 : c ≤ 1 := hc.2
    have ha1 : 0 ≤ a := ha.1
    have hb1 : 0 ≤ b := hb.1
    have hc1 : 0 ≤ c := hc.1
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1), 
      mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hc1), 
      mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hc1), 
      mul_nonneg (sub_nonneg.mpr (show 0 ≤ 1 - a by linarith)) (sub_nonneg.mpr (show 0 ≤ 1 - b by linarith)), 
      mul_nonneg (sub_nonneg.mpr (show 0 ≤ 1 - a by linarith)) (sub_nonneg.mpr (show 0 ≤ 1 - c by linarith)), 
      mul_nonneg (sub_nonneg.mpr (show 0 ≤ 1 - b by linarith)) (sub_nonneg.mpr (show 0 ≤ 1 - c by linarith))
    ]
  have h3 : a + b + c ≤ 3 := by
    nlinarith
  have h4 : a * b * c ≤ a := by
    have h1 : 0 ≤ a := ha.1
    have h2 : a ≤ 1 := ha.2
    have h3 : 0 ≤ b * c := mul_nonneg hb.1 hc.1
    have h4 : b * c ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) (sub_nonneg.mpr hc.2), mul_nonneg (sub_nonneg.mpr (show 0 ≤ 1 - b by linarith)) (sub_nonneg.mpr (show 0 ≤ 1 - c by linarith))]
    nlinarith
  have h5 : a * b * c ≤ b := by
    have h1 : 0 ≤ b := hb.1
    have h2 : b ≤ 1 := hb.2
    have h3 : 0 ≤ a * c := mul_nonneg ha.1 hc.1
    have h4 : a * c ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hc.2), mul_nonneg (sub_nonneg.mpr (show 0 ≤ 1 - a by linarith)) (sub_nonneg.mpr (show 0 ≤ 1 - c by linarith))]
    nlinarith
  have h6 : a * b * c ≤ c := by
    have h1 : 0 ≤ c := hc.1
    have h2 : c ≤ 1 := hc.2
    have h3 : 0 ≤ a * b := mul_nonneg ha.1 hb.1
    have h4 : a * b ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2), mul_nonneg (sub_nonneg.mpr (show 0 ≤ 1 - a by linarith)) (sub_nonneg.mpr (show 0 ≤ 1 - b by linarith))]
    nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr ha.1) (sub_nonneg.mpr hb.1), 
    mul_nonneg (sub_nonneg.mpr ha.1) (sub_nonneg.mpr hc.1), 
    mul_nonneg (sub_nonneg.mpr hb.1) (sub_nonneg.mpr hc.1), 
    mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2), 
    mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hc.2), 
    mul_nonneg (sub_nonneg.mpr hb.2) (sub_nonneg.mpr hc.2), 
    mul_nonneg (sub_nonneg.mpr ha.1) (sub_nonneg.mpr (show 0 ≤ 1 - a by linarith)), 
    mul_nonneg (sub_nonneg.mpr hb.1) (sub_nonneg.mpr (show 0 ≤ 1 - b by linarith)), 
    mul_nonneg (sub_nonneg.mpr hc.1) (sub_nonneg.mpr (show 0 ≤ 1 - c by linarith)), 
    mul_nonneg (sub_nonneg.mpr ha.1) (sub_nonneg.mpr ha.2), 
    mul_nonneg (sub_nonneg.mpr hb.1) (sub_nonneg.mpr hb.2), 
    mul_nonneg (sub_nonneg.mpr hc.1) (sub_nonneg.mpr hc.2), 
    sq_nonneg (a * b - 0), sq_nonneg (a * c - 0), sq_nonneg (b * c - 0)
  ]