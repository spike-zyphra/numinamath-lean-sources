import Mathlib

theorem inequalities_599672 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a < 1) (h2 : b < 1) :
    a / (1 - a ^ 2) + b / (1 - b ^ 2) ≥ (a + b) / (1 - a * b) := by
  have h3 : 0 < 1 - a ^ 2 := by
    nlinarith
  have h4 : 0 < 1 - b ^ 2 := by
    nlinarith
  have h5 : 0 < 1 - a * b := by
    nlinarith
  have h6 : 0 < (1 - a ^ 2) * (1 - b ^ 2) * (1 - a * b) := by
    positivity

  have h7 : a / (1 - a ^ 2) + b / (1 - b ^ 2) - (a + b) / (1 - a * b) ≥ 0 := by
    have h8 : a / (1 - a ^ 2) + b / (1 - b ^ 2) - (a + b) / (1 - a * b) =
        ( (a * (1 - b ^ 2) * (1 - a * b) + b * (1 - a ^ 2) * (1 - a * b) - (a + b) * (1 - a ^ 2) * (1 - b ^ 2) ) / ( (1 - a ^ 2) * (1 - b ^ 2) * (1 - a * b) ) ) := by
      field_simp [(show 1 - a ^ 2 ≠ 0 by nlinarith), (show 1 - b ^ 2 ≠ 0 by nlinarith), (show 1 - a * b ≠ 0 by nlinarith)]
      <;> ring
      <;> field_simp [(show 1 - a ^ 2 ≠ 0 by nlinarith), (show 1 - b ^ 2 ≠ 0 by nlinarith), (show 1 - a * b ≠ 0 by nlinarith)]
      <;> ring
      <;> field_simp [(show 1 - a ^ 2 ≠ 0 by nlinarith), (show 1 - b ^ 2 ≠ 0 by nlinarith), (show 1 - a * b ≠ 0 by nlinarith)]
    rw [h8]

    have h9 : ( a * (1 - b ^ 2) * (1 - a * b) + b * (1 - a ^ 2) * (1 - a * b) - (a + b) * (1 - a ^ 2) * (1 - b ^ 2) ) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - a * b), sq_nonneg (a * b - a * b), sq_nonneg (a * b - 0), sq_nonneg ((a - b) * (a * b)), 
        mul_pos ha hb, mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), 
        mul_pos ha (sub_pos.mpr h2), 
        mul_pos hb (sub_pos.mpr h1), 
        mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2)]
    
    apply div_nonneg
    linarith
    positivity
  
  linarith