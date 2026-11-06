import Mathlib

theorem algebra_301953 {a1 a2 b1 b2 : ℝ} (ha12 : a1 ≠ a2)
    (h1 : (a1 + b1) * (a1 + b2) = 1) (h2 : (a2 + b1) * (a2 + b2) = 1) :
    (a1 + b1) * (a2 + b1) = -1 ∧ (a1 + b2) * (a2 + b2) = -1 := by 
  have h3 : (a1 - a2) * (a1 + a2 + b1 + b2) = 0 := by
    nlinarith 
  have h4 : a1 + a2 + b1 + b2 = 0 := by 
    apply (mul_right_inj' (sub_ne_zero.mpr ha12)).mp 
    linarith 
  have eq1 : (a1 + b1) * (a2 + b1) = -1 := by
    have eq7 : b2 = -a1 - a2 - b1 := by 
      linarith [h4]
    have eq8 : (a1 + b1) * (a1 + (-a1 - a2 - b1)) = 1 := by
      rw [eq7] at h1 
      linarith 
    have eq6 : (a1 + b1) * (-a2 - b1) = 1 := by 
      nlinarith
    linarith [eq6]
  have eq2 : (a1 + b2) * (a2 + b2) = -1 := by
    have eq8 : b1 = -a1 - a2 - b2 := by 
      linarith [h4]
    have eq9 : (a2 + (-a1 - a2 - b2)) * (a2 + b2) = 1 := by 
      rw [eq8] at h2 
      linarith 
    have eq10 : (-a1 - b2) * (a2 + b2) = 1 := by
      nlinarith 
    linarith [eq10]
  constructor 
  · exact eq1 
  · exact eq2