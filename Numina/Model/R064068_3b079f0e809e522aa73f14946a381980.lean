import Mathlib

theorem algebra_18831 (a b c : ℤ) (ha : a = 2003) (hb : b = 2004) (hc : c = 2003 * 2004) :
    Real.sqrt (a^2 + b^2 + c^2) = 4014013 := by
  have ha2 : (a : ℝ) = (2003 : ℝ) := by exact_mod_cast ha
  have hb2 : (b : ℝ) = (2004 : ℝ) := by exact_mod_cast hb
  have hc2 : (c : ℝ) = (2003 * 2004 : ℝ) := by exact_mod_cast hc

  have h1 : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2 = (4014013 : ℝ) ^ 2 := by
    rw [ha2, hb2, hc2]
    norm_num

  rw [h1]
  exact Real.sqrt_sq (by norm_num)