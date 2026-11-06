import Mathlib

theorem other_37313
  (a : ℤ → ℤ)
  (ha1 : a 1 = 1)
  (ha2 : a 2 = 5)
  (han : ∀ n ≥ 2, a (n + 1) - 2 * a n + a (n - 1) = 7)
  : a 17 = 905 := by
  have ha3 : a 3 = 16 := by
    have eq1 := han 2 (by norm_num)
    norm_num [ha1, ha2] at eq1
    linarith
  
  have ha4 : a 4 = 34 := by
    have eq1 := han 3 (by norm_num)
    norm_num [ha2, ha3] at eq1
    linarith
  
  have ha5 : a 5 = 59 := by
    have eq1 := han 4 (by norm_num)
    norm_num [ha3, ha4] at eq1
    linarith
  
  have ha6 : a 6 = 91 := by
    have eq1 := han 5 (by norm_num)
    norm_num [ha4, ha5] at eq1
    linarith
  
  have ha7 : a 7 = 130 := by
    have eq1 := han 6 (by norm_num)
    norm_num [ha5, ha6] at eq1
    linarith
  
  have ha8 : a 8 = 176 := by
    have eq1 := han 7 (by norm_num)
    norm_num [ha6, ha7] at eq1
    linarith
  
  have ha9 : a 9 = 229 := by
    have eq1 := han 8 (by norm_num)
    norm_num [ha7, ha8] at eq1
    linarith
  
  have ha10 : a 10 = 289 := by
    have eq1 := han 9 (by norm_num)
    norm_num [ha8, ha9] at eq1
    linarith
  
  have ha11 : a 11 = 356 := by
    have eq1 := han 10 (by norm_num)
    norm_num [ha9, ha10] at eq1
    linarith
  
  have ha12 : a 12 = 430 := by
    have eq1 := han 11 (by norm_num)
    norm_num [ha10, ha11] at eq1
    linarith
  
  have ha13 : a 13 = 511 := by
    have eq1 := han 12 (by norm_num)
    norm_num [ha11, ha12] at eq1
    linarith
  
  have ha14 : a 14 = 599 := by
    have eq1 := han 13 (by norm_num)
    norm_num [ha12, ha13] at eq1
    linarith
  
  have ha15 : a 15 = 694 := by
    have eq1 := han 14 (by norm_num)
    norm_num [ha13, ha14] at eq1
    linarith
  
  have ha16 : a 16 = 796 := by
    have eq1 := han 15 (by norm_num)
    norm_num [ha14, ha15] at eq1
    linarith
  
  have ha17 : a 17 = 905 := by
    have eq1 := han 16 (by norm_num)
    norm_num [ha15, ha16] at eq1
    linarith
  
  exact ha17