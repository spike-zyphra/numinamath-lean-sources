import Mathlib

theorem algebra_10425 {a : ℕ → ℤ} (ha1 : a 1 = 1) (ha2 : a 2 = 4) (ha3 : a 3 = 10)
    (han : ∀ n ≥ 2, (a (n + 1)) ^ 2 - 2 * (a n) ^ 2 = a n * a (n + 2) - 2 * a (n - 1) * a (n + 1)) :
    a 21 % 10 = 6 := by
  have ha4 : a 4 = 22 := by
    have eq1 := han 2 (by norm_num)
    simp [ha1, ha2, ha3] at eq1
    nlinarith
  have ha5 : a 5 = 46 := by
    have eq1 := han 3 (by norm_num)
    simp [ha2, ha3, ha4] at eq1
    nlinarith
  have ha6 : a 6 = 94 := by
    have eq1 := han 4 (by norm_num)
    simp [ha3, ha4, ha5] at eq1
    nlinarith
  have ha7 : a 7 = 190 := by
    have eq1 := han 5 (by norm_num)
    simp [ha4, ha5, ha6] at eq1
    nlinarith
  have ha8 : a 8 = 382 := by
    have eq1 := han 6 (by norm_num)
    simp [ha5, ha6, ha7] at eq1
    nlinarith
  have ha9 : a 9 = 766 := by
    have eq1 := han 7 (by norm_num)
    simp [ha6, ha7, ha8] at eq1
    nlinarith
  have ha10 : a 10 = 1534 := by
    have eq1 := han 8 (by norm_num)
    simp [ha7, ha8, ha9] at eq1
    nlinarith
  have ha11 : a 11 = 3070 := by
    have eq1 := han 9 (by norm_num)
    simp [ha8, ha9, ha10] at eq1
    nlinarith
  have ha12 : a 12 = 6142 := by
    have eq1 := han 10 (by norm_num)
    simp [ha9, ha10, ha11] at eq1
    nlinarith
  have ha13 : a 13 = 12286 := by
    have eq1 := han 11 (by norm_num)
    simp [ha10, ha11, ha12] at eq1
    nlinarith
  have ha14 : a 14 = 24574 := by
    have eq1 := han 12 (by norm_num)
    simp [ha11, ha12, ha13] at eq1
    nlinarith
  have ha15 : a 15 = 49150 := by
    have eq1 := han 13 (by norm_num)
    simp [ha12, ha13, ha14] at eq1
    nlinarith
  have ha16 : a 16 = 98302 := by
    have eq1 := han 14 (by norm_num)
    simp [ha13, ha14, ha15] at eq1
    nlinarith
  have ha17 : a 17 = 196606 := by
    have eq1 := han 15 (by norm_num)
    simp [ha14, ha15, ha16] at eq1
    nlinarith
  have ha18 : a 18 = 393214 := by
    have eq1 := han 16 (by norm_num)
    simp [ha15, ha16, ha17] at eq1
    nlinarith
  have ha19 : a 19 = 786430 := by
    have eq1 := han 17 (by norm_num)
    simp [ha16, ha17, ha18] at eq1
    nlinarith
  have ha20 : a 20 = 1572862 := by
    have eq1 := han 18 (by norm_num)
    simp [ha17, ha18, ha19] at eq1
    nlinarith
  have ha21 : a 21 = 3145726 := by
    have eq1 := han 19 (by norm_num)
    simp [ha18, ha19, ha20] at eq1
    nlinarith
  norm_num [ha21]