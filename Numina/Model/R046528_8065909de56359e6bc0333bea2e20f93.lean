import Mathlib 
theorem algebra_96632 (a b c d e f : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (had : a < d) (hbe : b > e) (hfc : f < c) :
    (a / b : ℝ) - c < (d / e : ℝ) - f := by
  have h1 : (a : ℝ) > 0 := by exact_mod_cast ha
  have h2 : (b : ℝ) > 0 := by exact_mod_cast hb
  have h3 : (c : ℝ) > 0 := by exact_mod_cast hc
  have h4 : (d : ℝ) > 0 := by exact_mod_cast hd
  have h5 : (e : ℝ) > 0 := by exact_mod_cast he
  have h6 : (f : ℝ) > 0 := by exact_mod_cast hf
  have h7 : (f : ℝ) < (c : ℝ) := by exact_mod_cast hfc
  have h8 : (a / b : ℝ) < (d / e : ℝ) := by
    have h11 : (a : ℝ) < (d : ℝ) := by exact_mod_cast had
    have h22 : (b : ℝ) > (e : ℝ) := by exact_mod_cast hbe
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    nlinarith
  linarith [h7, h8]