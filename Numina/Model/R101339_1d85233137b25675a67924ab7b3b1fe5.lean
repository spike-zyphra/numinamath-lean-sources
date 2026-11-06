import Mathlib

theorem inequalities_132722 (a b c d : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hle : (a / b : ℝ) ≤ (c / d : ℝ)) (hbound : (c / d : ℝ) ≤ 1) :
    (a + c) / (b + d) ≤ (c / d : ℝ) := by 
  have h1 : (a : ℝ) * (d : ℝ) ≤ (c : ℝ) * (b : ℝ) := by 
    have h2 : (a / b : ℝ) ≤ (c / d : ℝ) := hle 
    have h4 : (b : ℝ) > 0 := by exact_mod_cast (show (b : ℝ) > 0 by exact_mod_cast hb)
    have h5 : (d : ℝ) > 0 := by exact_mod_cast (show (d : ℝ) > 0 by exact_mod_cast hd)
    have h3 : (a : ℝ) * (d : ℝ) ≤ (c : ℝ) * (b : ℝ) := by 
      have h6 : (a / b : ℝ) ≤ (c / d : ℝ) := h2 
      apply (div_le_div_iff (by positivity) (by positivity)).mp at h6 
      nlinarith 
    linarith 
  have h2 : (a + c : ℝ) / (b + d : ℝ) ≤ (c : ℝ) / (d : ℝ) := by 
    have h7 : (b + d : ℝ) > 0 := by 
      positivity 
    have h8 : (d : ℝ) > 0 := by 
      positivity 
    apply (div_le_div_iff (by positivity) (by positivity)).mpr 
    nlinarith [show (a : ℝ) * (d : ℝ) ≤ (c : ℝ) * (b : ℝ) by linarith [h1], 
      show (d : ℝ) > 0 by positivity, show (b : ℝ) > 0 by positivity]
  exact_mod_cast h2