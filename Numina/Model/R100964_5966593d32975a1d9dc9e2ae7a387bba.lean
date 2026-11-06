import Mathlib

theorem algebra_274827 (m n : ℤ) (hm : 0 < m) (hn : m < n) :
    (m + 3 : ℝ) / (n + 3) > m / n := by 
  have h1 : (m : ℝ) > 0 := by exact_mod_cast hm
  have h2 : (m : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h3 : (n : ℝ) > 0 := by linarith
  have h4 : (n : ℝ) + 3 > 0 := by linarith
  have h5 : (m / n : ℝ) < ((m + 3 : ℝ) / (n + 3)) := by
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    nlinarith
  linarith