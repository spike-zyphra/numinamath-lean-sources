import Mathlib

theorem algebra_309776 : Real.arctan (1/3) + Real.arctan (1/5) + Real.arctan (1/7) + Real.arctan (1/8) = Real.pi/4 := by
  have h1 : Real.arctan (1/3) + Real.arctan (1/5) = Real.arctan (4/7) := by
    rw [Real.arctan_add]
    all_goals norm_num
  have h2 : Real.arctan (4/7) + Real.arctan (1/7) = Real.arctan (7/9) := by
    rw [Real.arctan_add]
    all_goals norm_num
  have h3 : Real.arctan (7/9) + Real.arctan (1/8) = Real.pi/4 := by
    rw [Real.arctan_add]
    norm_num
    all_goals norm_num [Real.pi_pos, Real.arctan_lt_pi_div_two, Real.neg_pi_div_two_lt_arctan]
    <;> ring_nf <;> norm_num
  linarith [h1, h2, h3]