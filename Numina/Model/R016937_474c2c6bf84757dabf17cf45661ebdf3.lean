import Mathlib

theorem algebra_153560 (x a b c : ℝ) (hx : 0 < x) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : Real.log x = Real.log a + Real.log b - Real.log c) :
    x = a * b / c := by

  have h1 : Real.log a + Real.log b = Real.log (a * b) := by 
    rw [Real.log_mul (by linarith) (by linarith)]

  have h2 : Real.log a + Real.log b - Real.log c = Real.log ( (a * b) / c ) := by 
    rw [h1]
    have h3 : Real.log ( (a * b) / c ) = Real.log (a * b) - Real.log c := by 
      rw [Real.log_div (by positivity) (by positivity)]
    linarith [h3]

  have h3 : Real.log x = Real.log ( (a * b) / c ) := by 
    linarith [h, h2]

  have h4 : x > 0 := hx
  have h5 : (a * b) / c > 0 := by 
    apply div_pos 
    · -- Show that a * b > 0 
      positivity 
    · -- Show that c > 0 
      linarith

  have h6 : x = (a * b) / c := by 
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr h4) (Set.mem_Ioi.mpr h5) h3

  exact h6