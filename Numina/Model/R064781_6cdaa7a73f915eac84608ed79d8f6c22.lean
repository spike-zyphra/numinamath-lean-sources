import Mathlib

theorem number_theory_137628 {R1 R2 : ℕ} {F1 F2 : ℝ}
    (hR1 : R1 > 0) (hR2 : R2 > 0)
    (hF1 : F1 > 0) (hF2 : F2 > 0)
    (h1 : F1 = 33 * 71 / R1) (h2 : F2 = 33 * 71 / R2)
    (h3 : F1 = 37 / 99) (h4 : F2 = 73 / 99)
    (h5 : F1 = 25 / 49) (h6 : F2 = 52 / 49) :
    R1 + R2 = 19 := by
  norm_num at h3 h5 h4 h6
  all_goals 
    try { linarith }
    all_goals tauto