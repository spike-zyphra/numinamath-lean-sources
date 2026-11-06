import Mathlib

theorem inequalities_600818 (a1 a2 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (h : a1 + a2 = 1) :
    (1 + a1) / (1 - a1) * (1 + a2) / (1 - a2) ≥ 3^2 := by
  have ha2' : a2 = 1 - a1 := by linarith
  rw [ha2']
  have h1 : 0 < a1 := by assumption
  have h2 : 0 < (1 - a1) := by 
    nlinarith [show a1 > 0 from by linarith, show a2 > 0 from by linarith, h]
  have h5 : 0 < 1 - a1 := by linarith
  have h6 : 0 < a1 := by 
    nlinarith [show a1 > 0 from by linarith, show a2 > 0 from by linarith, h]
  have denominators_pos : 0 < (1 - a1) * (1 - (1 - a1)) := by
    apply mul_pos
    all_goals linarith
  have h7 : (1 + a1) / (1 - a1) * (1 + (1 - a1)) / (1 - (1 - a1)) - (3 : ℝ)^2 ≥ 0 := by
    have h9 : (1 + a1) / (1 - a1) * (1 + (1 - a1)) / (1 - (1 - a1)) - (3 : ℝ)^2 =
      ((1 + a1) * (1 + (1 - a1)) - (9 : ℝ) * ((1 - a1) * (1 - (1 - a1)))) / ((1 - a1) * (1 - (1 - a1))) := by
      field_simp
      <;> ring
    rw [h9]
    have denominators_pos : 0 < (1 - a1) * (1 - (1 - a1)) := by
      apply mul_pos
      all_goals linarith
    have h10 : ((1 + a1) * (1 + (1 - a1)) - (9 : ℝ) * ((1 - a1) * (1 - (1 - a1)))) ≥ 0 := by
      nlinarith [sq_nonneg (a1 - 1 / 2)]
    apply div_nonneg
    linarith
    linarith
  linarith