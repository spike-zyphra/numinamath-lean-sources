import Mathlib

theorem algebra_197207 (vbus vcar : ℝ) (h : vbus > 0) (h' : vcar > 0)
    (h1 : 180 / vbus = 180 / vcar + 1.25) (h2 : 180 / vbus + 15 / 60 = 180 / vcar - 1.25) :
    vbus = 15 ∧ vcar = 15 := by

  have h3 : 180 / vcar + 1.5 = 180 / vcar - 1.25 := by
    have eq1 : 180 / vbus = 180 / vcar + 1.25 := h1
    rw [show 180 / vbus = 180 / vcar + 1.25 by linarith] at h2
    norm_num at h2 ⊢
    linarith
  have h4 : (1.5 : ℝ) = (-1.25 : ℝ) := by
    linarith [h3]
  norm_num at h4
  all_goals
    try { linarith }
    <;> try { nlinarith }