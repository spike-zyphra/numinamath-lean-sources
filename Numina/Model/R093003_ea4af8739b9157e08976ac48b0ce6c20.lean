import Mathlib

theorem algebra_9708 (a : ℕ+ → ℤ) (ha1 : a 1 = 2) (ha2 : a 2 = 5)
  (han : ∀ n, a (n + 2) = 7 * a (n + 1) - 10 * a n) :
  a 10 - 5 * a 9 = -1280 := by

  have ha3 : a 3 = 15 := by 
    have h1 : a 3 = 7 * a 2 - 10 * a 1 := han 1
    rw [ha1, ha2] at h1
    linarith
  
  have ha4 : a 4 = 55 := by
    have h1 : a 4 = 7 * a 3 - 10 * a 2 := han 2
    rw [show a 3 = 15 by linarith [ha3], ha2] at h1
    linarith

  have ha5 : a 5 = 235 := by 
    have h1 : a 5 = 7 * a 4 - 10 * a 3 := han 3
    rw [show a 4 = 55 by linarith [ha4], show a 3 = 15 by linarith [ha3]] at h1
    linarith

  have ha6 : a 6 = 1095 := by 
    have h1 : a 6 = 7 * a 5 - 10 * a 4 := han 4
    rw [show a 5 = 235 by linarith [ha5], show a 4 = 55 by linarith [ha4]] at h1
    linarith

  have ha7 : a 7 = 5315 := by 
    have h1 : a 7 = 7 * a 6 - 10 * a 5 := han 5
    rw [show a 6 = 1095 by linarith [ha6], show a 5 = 235 by linarith [ha5]] at h1
    linarith

  have ha8 : a 8 = 26255 := by 
    have h1 : a 8 = 7 * a 7 - 10 * a 6 := han 6
    rw [show a 7 = 5315 by linarith [ha7], show a 6 = 1095 by linarith [ha6]] at h1
    linarith

  have ha9 : a 9 = 130635 := by 
    have h1 : a 9 = 7 * a 8 - 10 * a 7 := han 7
    rw [show a 8 = 26255 by linarith [ha8], show a 7 = 5315 by linarith [ha7]] at h1
    linarith

  have ha10 : a 10 = 651895 := by 
    have h1 : a 10 = 7 * a 9 - 10 * a 8 := han 8
    rw [show a 9 = 130635 by linarith [ha9], show a 8 = 26255 by linarith [ha8]] at h1
    linarith
  
  rw [show a 10 = 651895 by linarith [ha10], show a 9 = 130635 by linarith [ha9]]
  all_goals norm_num