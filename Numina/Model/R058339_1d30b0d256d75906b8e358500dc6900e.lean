import Mathlib

theorem inequalities_179522 (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hy : 0 < y)
    (h : a / b < x / y) :
    a / b < (a + x) / (b + y) ∧ (a + x) / (b + y) < x / y := by
  have h1 : a * y < b * x := by
    have pos1 : 0 < b := hb
    have pos2 : 0 < y := hy
    apply (div_lt_div_iff (by positivity) (by positivity)).mp at h 
    nlinarith
  
  have h2 : a / b < (a + x) / (b + y) := by
    have pos1 : 0 < b := hb
    have pos2 : 0 < b + y := by linarith
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h1, mul_pos ha hb, mul_pos hx hy]

  have h3 : (a + x) / (b + y) < x / y := by
    have pos1 : 0 < b + y := by linarith
    have pos2 : 0 < y := hy
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h1, mul_pos ha hb, mul_pos hx hy]

  exact ⟨h2, h3⟩