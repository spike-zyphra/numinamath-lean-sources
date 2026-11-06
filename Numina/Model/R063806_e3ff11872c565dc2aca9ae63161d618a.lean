import Mathlib

theorem algebra_9673 {a : ℕ → ℝ} (ha1 : a 1 = 6) (ha2 : a 2 = 8)
    (han : ∀ n > 0, a (n + 2) = (a (n + 1))^2 / a n) :
    a 20 / a 23 = 27 / 64 := by

  have ha3 : a 3 = (a 2) ^ 2 / a 1 := han 1 (by norm_num)
  rw [ha1, ha2] at ha3
  norm_num at ha3

  have ha4 : a 4 = (a 3) ^ 2 / a 2 := han 2 (by norm_num)
  rw [ha3, ha2] at ha4
  norm_num at ha4

  have ha5 : a 5 = (a 4) ^ 2 / a 3 := han 3 (by norm_num)
  rw [ha4, ha3] at ha5
  norm_num at ha5

  have ha6 : a 6 = (a 5) ^ 2 / a 4 := han 4 (by norm_num)
  rw [ha5, ha4] at ha6
  norm_num at ha6

  have ha7 : a 7 = (a 6) ^ 2 / a 5 := han 5 (by norm_num)
  rw [ha6, ha5] at ha7
  norm_num at ha7

  have ha8 : a 8 = (a 7) ^ 2 / a 6 := han 6 (by norm_num)
  rw [ha7, ha6] at ha8
  norm_num at ha8

  have ha9 : a 9 = (a 8) ^ 2 / a 7 := han 7 (by norm_num)
  rw [ha8, ha7] at ha9
  norm_num at ha9

  have ha10 : a 10 = (a 9) ^ 2 / a 8 := han 8 (by norm_num)
  rw [ha9, ha8] at ha10
  norm_num at ha10

  have ha11 : a 11 = (a 10) ^ 2 / a 9 := han 9 (by norm_num)
  rw [ha10, ha9] at ha11
  norm_num at ha11

  have ha12 : a 12 = (a 11) ^ 2 / a 10 := han 10 (by norm_num)
  rw [ha11, ha10] at ha12
  norm_num at ha12

  have ha13 : a 13 = (a 12) ^ 2 / a 11 := han 11 (by norm_num)
  rw [ha12, ha11] at ha13
  norm_num at ha13

  have ha14 : a 14 = (a 13) ^ 2 / a 12 := han 12 (by norm_num)
  rw [ha13, ha12] at ha14
  norm_num at ha14

  have ha15 : a 15 = (a 14) ^ 2 / a 13 := han 13 (by norm_num)
  rw [ha14, ha13] at ha15
  norm_num at ha15

  have ha16 : a 16 = (a 15) ^ 2 / a 14 := han 14 (by norm_num)
  rw [ha15, ha14] at ha16
  norm_num at ha16

  have ha17 : a 17 = (a 16) ^ 2 / a 15 := han 15 (by norm_num)
  rw [ha16, ha15] at ha17
  norm_num at ha17

  have ha18 : a 18 = (a 17) ^ 2 / a 16 := han 16 (by norm_num)
  rw [ha17, ha16] at ha18
  norm_num at ha18

  have ha19 : a 19 = (a 18) ^ 2 / a 17 := han 17 (by norm_num)
  rw [ha18, ha17] at ha19
  norm_num at ha19

  have ha20 : a 20 = (a 19) ^ 2 / a 18 := han 18 (by norm_num)
  rw [ha19, ha18] at ha20
  norm_num at ha20

  have ha21 : a 21 = (a 20) ^ 2 / a 19 := han 19 (by norm_num)
  rw [ha20, ha19] at ha21
  norm_num at ha21

  have ha22 : a 22 = (a 21) ^ 2 / a 20 := han 20 (by norm_num)
  rw [ha21, ha20] at ha22
  norm_num at ha22

  have ha23 : a 23 = (a 22) ^ 2 / a 21 := han 21 (by norm_num)
  rw [ha22, ha21] at ha23
  norm_num at ha23

  rw [ha20, ha23]
  norm_num