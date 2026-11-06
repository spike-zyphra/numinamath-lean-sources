import Mathlib

theorem algebra_120230 {c m : ℝ} (hc : c > 0) (hm : m > 0)
    (h1 : c + 2 * m = 0.6) (h2 : c + 5 * m = 0.975) :
    c = 0.35 := by
  have eq1 : 3 * m = (0.375 : ℝ) := by
    calc
      3 * m = (c + 5 * m) - (c + 2 * m) := by ring
      _ = 0.975 - 0.6 := by rw [h2, h1]
      _ = (0.375 : ℝ) := by norm_num
  
  have hm' : m = (0.125 : ℝ) := by
    nlinarith
  
  have hc' : c = (0.35 : ℝ) := by
    nlinarith [h1, hm']
  
  exact_mod_cast hc'