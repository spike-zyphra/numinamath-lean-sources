import Mathlib

theorem algebra_278233 {N b a : ℝ} (hb : b > 0 ∧ b ≠ 1) (ha : a > 0 ∧ a ≠ 1)
    (hN : N > 0) :
    Real.logb b N = Real.logb a N / Real.logb a b := by 
  have h1 : Real.logb b N = Real.log N / Real.log b := by
    rw [Real.logb]
  have h2 : Real.logb a N = Real.log N / Real.log a := by 
    rw [Real.logb]
  have h3 : Real.logb a b = Real.log b / Real.log a := by 
    rw [Real.logb]
    all_goals 
      try linarith
      <;> try tauto
  rw [h1, h2, h3]
  have ha1 : Real.log a ≠ 0 := by 
    apply Real.log_ne_zero_of_pos_of_ne_one 
    linarith 
    exact ha.right 
  have hb1 : Real.log b ≠ 0 := by 
    apply Real.log_ne_zero_of_pos_of_ne_one 
    linarith 
    exact hb.right 
  field_simp [ha1, hb1]
  all_goals 
    try linarith 
    <;> try tauto
  all_goals 
    try linarith 
    <;> try tauto