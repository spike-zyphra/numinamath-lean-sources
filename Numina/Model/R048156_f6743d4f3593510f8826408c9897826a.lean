import Mathlib
open Real

theorem algebra_95797 (x : ℝ) (h : x^2 + 2 * x * Real.sqrt 3 + 3 = 0) :
x = -Real.sqrt 3 ∧ Irrational x := by
  have h1 : x^2 + 2 * x * Real.sqrt 3 + 3 = (x + Real.sqrt 3) ^2 := by
    nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have h2 : (x + Real.sqrt 3) ^2 = 0 := by
    linarith [h, h1]
  have h3 : x + Real.sqrt 3 = 0 := by
    apply pow_eq_zero 
    exact h2
  have h4 : x = -Real.sqrt 3 := by
    linarith 
  have h5 : Irrational x := by 
    rw [h4] 
    have h6 : Irrational (-Real.sqrt 3) := by 
      have h7 : Irrational (Real.sqrt 3) := by 
        native_decide
      have h8 : Irrational (-Real.sqrt 3) := by 
        simpa using h7 
      exact h8 
    exact h6 
  constructor 
  · exact h4 
  · exact h5