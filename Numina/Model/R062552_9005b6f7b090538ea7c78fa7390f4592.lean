import Mathlib

theorem algebra_8943 {a : ℕ → ℤ} (ha1 : a 1 = 3) (ha2 : a 2 = 5)
    (han : ∀ n > 0, a (n + 2) = 2 * a n - a (n + 1) + 2 ^ (n + 1)) :
    a 10 = 685 := by
  have ha3 : a 3 = 5 := by
    specialize han 1 (by norm_num)
    norm_num [ha1, ha2] at han
    linarith

  have ha4 : a 4 = 13 := by
    specialize han 2 (by norm_num)
    norm_num [ha2, ha3] at han
    linarith

  have ha5 : a 5 = 13 := by
    specialize han 3 (by norm_num)
    norm_num [ha3, ha4] at han
    linarith

  have ha6 : a 6 = 45 := by
    specialize han 4 (by norm_num)
    norm_num [ha4, ha5] at han
    linarith

  have ha7 : a 7 = 45 := by
    specialize han 5 (by norm_num)
    norm_num [ha5, ha6] at han
    linarith

  have ha8 : a 8 = 173 := by
    specialize han 6 (by norm_num)
    norm_num [ha6, ha7] at han
    linarith

  have ha9 : a 9 = 173 := by
    specialize han 7 (by norm_num)
    norm_num [ha7, ha8] at han
    linarith

  have ha10 : a 10 = 685 := by
    specialize han 8 (by norm_num)
    norm_num [ha8, ha9] at han
    linarith

  exact ha10