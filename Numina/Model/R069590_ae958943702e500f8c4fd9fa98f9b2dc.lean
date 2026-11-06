import Mathlib

theorem algebra_224405 (v w : ℝ) (h : v > 0) (h' : w > 0)
    (h'' : v^2 - w^2 > 0) :
    20 * v / (v^2 - w^2) > 20 / v := by
  have pos1 : v > 0 := h
  have pos2 : v^2 - w^2 > 0 := h''
  have pos3 : v * (v^2 - w^2) > 0 := by
    apply mul_pos
    linarith
    linarith
  have h1 : 20 * w ^ 2 > 0 := by
    nlinarith [sq_pos_of_pos h']
  have h3 : 20 * v / (v^2 - w^2) - 20 / v > 0 := by
    have pos4 : v > 0 := h
    have pos5 : v^2 - w^2 > 0 := h''
    have pos6 : v * (v^2 - w^2) > 0 := by
      apply mul_pos
      linarith
      linarith
    have pos7 : 20 * w ^ 2 > 0 := by
      nlinarith [sq_pos_of_pos h']
    have h4 : 20 * v / (v^2 - w^2) - 20 / v = (20 * w^2) / (v * (v^2 - w^2)) := by
      field_simp
      <;> ring_nf <;> field_simp <;> linarith
    rw [h4]
    apply div_pos
    linarith
    all_goals nlinarith [sq_pos_of_pos h, sq_pos_of_pos h', pos2]
  linarith