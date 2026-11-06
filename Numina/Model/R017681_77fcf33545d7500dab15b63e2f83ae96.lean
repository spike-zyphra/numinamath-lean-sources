import Mathlib

theorem algebra_202117 (a b : ℝ) (ha : a > 0) (hb : b > 0)
    (h1 : a * 100 = b * 24) (h2 : a * 11.5 = b * 5.2) :
    a / b = 1.8 := by

  have eq1 : a * 100 = b * 24 := by linarith
  have eq2 : a * 11.5 = b * 5.2 := by linarith [h2]

  have h3 : a * ( (100 / 24 : ℝ) - (11.5 / 5.2 : ℝ) ) = 0 := by
    have eq3 : b = (100 / 24 : ℝ) * a := by
      nlinarith
    have eq4 : b = (11.5 / 5.2 : ℝ) * a := by
      nlinarith
    rw [eq3] at eq4
    nlinarith
    <;> nlinarith
    all_goals nlinarith


  have h4 : a > 0 := ha
  have h8 : a * ( (100 / 24 : ℝ) - (11.5 / 5.2 : ℝ) ) = 0 := h3

  -- From h7 and h4 contradicts
  have h5 : ( (100 / 24 : ℝ) - (11.5 / 5.2 : ℝ) ) = 0 := by
    apply (mul_left_inj' (show a ≠ 0 by linarith)).mp
    linarith
    <;> nlinarith


  norm_num at h5
  all_goals linarith