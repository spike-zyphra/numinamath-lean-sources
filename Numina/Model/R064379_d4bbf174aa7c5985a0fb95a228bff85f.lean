import Mathlib

theorem algebra_180370 (p1 p2 p3 : ℝ)
    (h1 : 0 < p1 ∧ 0 < p2 ∧ 0 < p3)
    (h2 : 1 / p1 + 1 / p2 = 1 / 30)
    (h3 : 1 / p1 + 1 / p3 = 1 / 40)
    (h4 : 1 / p2 + 1 / p3 = 1 / 24) :
    p1 = 120 ∧ p2 = 40 ∧ p3 = 60 := by
  have hp1_pos : 0 < p1 := h1.1
  have hp2_pos : 0 < p2 := h1.2.1
  have hp3_pos : 0 < p3 := h1.2.2

  field_simp [hp1_pos, hp2_pos, hp3_pos] at h2 h3 h4

  have h5 : p1 = 120 := by
    nlinarith [sq_pos_of_pos hp1_pos, sq_pos_of_pos hp2_pos, sq_pos_of_pos hp3_pos,
      mul_pos hp1_pos hp2_pos, mul_pos hp1_pos hp3_pos, mul_pos hp2_pos hp3_pos]

  have h6 : p2 = 40 := by
    nlinarith [sq_pos_of_pos hp1_pos, sq_pos_of_pos hp2_pos, sq_pos_of_pos hp3_pos,
      mul_pos hp1_pos hp2_pos, mul_pos hp1_pos hp3_pos, mul_pos hp2_pos hp3_pos]

  have h7 : p3 = 60 := by
    nlinarith [sq_pos_of_pos hp1_pos, sq_pos_of_pos hp2_pos, sq_pos_of_pos hp3_pos,
      mul_pos hp1_pos hp2_pos, mul_pos hp1_pos hp3_pos, mul_pos hp2_pos hp3_pos]

  exact ⟨h5, h6, h7⟩