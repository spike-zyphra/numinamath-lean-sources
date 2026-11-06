import Mathlib

theorem algebra_279538 (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    1 < (a^2 / (a^2 + b^2 + c^2) + b^2 / (b^2 + c^2 + d^2) +
        c^2 / (c^2 + d^2 + a^2) + d^2 / (d^2 + a^2 + b^2)) ∧
    (a^2 / (a^2 + b^2 + c^2) + b^2 / (b^2 + c^2 + d^2) +
        c^2 / (c^2 + d^2 + a^2) + d^2 / (d^2 + a^2 + b^2)) < 2 := by
  constructor
  · -- Prove the lower bound: 1 < P
    have h1 : a^2 / (a^2 + b^2 + c^2) + b^2 / (b^2 + c^2 + d^2) + c^2 / (c^2 + d^2 + a^2) + d^2 / (d^2 + a^2 + b^2) > 1 := by 
      have h2 : a^2 / (a^2 + b^2 + c^2) > a^2 / (a^2 + b^2 + c^2 + d^2) := by 
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr 
        nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_pos_of_ne_zero hd]
      have h3 : b^2 / (b^2 + c^2 + d^2) > b^2 / (a^2 + b^2 + c^2 + d^2) := by 
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr 
        nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_pos_of_ne_zero hd]
      have h4 : c^2 / (c^2 + d^2 + a^2) > c^2 / (a^2 + b^2 + c^2 + d^2) := by 
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr 
        nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_pos_of_ne_zero hd]
      have h5 : d^2 / (d^2 + a^2 + b^2) > d^2 / (a^2 + b^2 + c^2 + d^2) := by 
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr 
        nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_pos_of_ne_zero hd]
      have h6 : a^2 / (a^2 + b^2 + c^2) + b^2 / (b^2 + c^2 + d^2) + c^2 / (c^2 + d^2 + a^2) + d^2 / (d^2 + a^2 + b^2) > a^2 / (a^2 + b^2 + c^2 + d^2) + b^2 / (a^2 + b^2 + c^2 + d^2) + c^2 / (a^2 + b^2 + c^2 + d^2) + d^2 / (a^2 + b^2 + c^2 + d^2) := by 
        linarith [h2, h3, h4, h5]
      have h7 : a^2 / (a^2 + b^2 + c^2 + d^2) + b^2 / (a^2 + b^2 + c^2 + d^2) + c^2 / (a^2 + b^2 + c^2 + d^2) + d^2 / (a^2 + b^2 + c^2 + d^2) = 1 := by 
        field_simp 
        <;> ring
      linarith [h7, h6]
    linarith 
  · -- Prove the upper bound: P < 2 
    have h1 : a^2 / (a^2 + b^2 + c^2) + b^2 / (b^2 + c^2 + d^2) + c^2 / (c^2 + d^2 + a^2) + d^2 / (d^2 + a^2 + b^2) < 2 := by 
      have h2 : a^2 / (a^2 + b^2 + c^2) < (a^2 + d^2) / (a^2 + b^2 + c^2 + d^2) := by 
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr 
        nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_pos_of_ne_zero hd]
      have h3 : b^2 / (b^2 + c^2 + d^2) < (b^2 + a^2) / (a^2 + b^2 + c^2 + d^2) := by 
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr 
        nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_pos_of_ne_zero hd]
      have h4 : c^2 / (c^2 + d^2 + a^2) < (c^2 + b^2) / (a^2 + b^2 + c^2 + d^2) := by 
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr 
        nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_pos_of_ne_zero hd]
      have h5 : d^2 / (d^2 + a^2 + b^2) < (d^2 + c^2) / (a^2 + b^2 + c^2 + d^2) := by 
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr 
        nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_pos_of_ne_zero hd]
      have h6 : a^2 / (a^2 + b^2 + c^2) + b^2 / (b^2 + c^2 + d^2) + c^2 / (c^2 + d^2 + a^2) + d^2 / (d^2 + a^2 + b^2) < (a^2 + d^2) / (a^2 + b^2 + c^2 + d^2) + (b^2 + a^2) / (a^2 + b^2 + c^2 + d^2) + (c^2 + b^2) / (a^2 + b^2 + c^2 + d^2) + (d^2 + c^2) / (a^2 + b^2 + c^2 + d^2) := by 
        linarith [h2, h3, h4, h5]
      have h8 : (a^2 + d^2) / (a^2 + b^2 + c^2 + d^2) + (b^2 + a^2) / (a^2 + b^2 + c^2 + d^2) + (c^2 + b^2) / (a^2 + b^2 + c^2 + d^2) + (d^2 + c^2) / (a^2 + b^2 + c^2 + d^2) = 2 := by 
        field_simp 
        <;> ring
      linarith [h6, h8]
    linarith