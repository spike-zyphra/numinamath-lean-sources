import Mathlib

theorem algebra_311243 (a : ℕ → ℝ)
    (h₀ : a 0 = 105)
    (h₁ : a 1 = 85)
    (h₂ : ∀ n, a (n + 2) = (a n + a (n + 1)) / 2) :
    ⌊a 18⌋ = 91 := by

  have ha2 : a 2 = (a 0 + a 1) / 2 := h₂ 0
  rw [h₀, h₁] at ha2
  norm_num at ha2

  have ha3 : a 3 = (a 1 + a 2) / 2 := h₂ 1
  rw [h₁, ha2] at ha3
  norm_num at ha3

  have ha4 : a 4 = (a 2 + a 3) / 2 := h₂ 2
  rw [ha2, ha3] at ha4
  norm_num at ha4

  have ha5 : a 5 = (a 3 + a 4) / 2 := h₂ 3
  rw [ha3, ha4] at ha5
  norm_num at ha5

  have ha6 : a 6 = (a 4 + a 5) / 2 := h₂ 4
  rw [ha4, ha5] at ha6
  norm_num at ha6

  have ha7 : a 7 = (a 5 + a 6) / 2 := h₂ 5
  rw [ha5, ha6] at ha7
  norm_num at ha7

  have ha8 : a 8 = (a 6 + a 7) / 2 := h₂ 6
  rw [ha6, ha7] at ha8
  norm_num at ha8

  have ha9 : a 9 = (a 7 + a 8) / 2 := h₂ 7
  rw [ha7, ha8] at ha9
  norm_num at ha9

  have ha10 : a 10 = (a 8 + a 9) / 2 := h₂ 8
  rw [ha8, ha9] at ha10
  norm_num at ha10

  have ha11 : a 11 = (a 9 + a 10) / 2 := h₂ 9
  rw [ha9, ha10] at ha11
  norm_num at ha11

  have ha12 : a 12 = (a 10 + a 11) / 2 := h₂ 10
  rw [ha10, ha11] at ha12
  norm_num at ha12

  have ha13 : a 13 = (a 11 + a 12) / 2 := h₂ 11
  rw [ha11, ha12] at ha13
  norm_num at ha13

  have ha14 : a 14 = (a 12 + a 13) / 2 := h₂ 12
  rw [ha12, ha13] at ha14
  norm_num at ha14

  have ha15 : a 15 = (a 13 + a 14) / 2 := h₂ 13
  rw [ha13, ha14] at ha15
  norm_num at ha15

  have ha16 : a 16 = (a 14 + a 15) / 2 := h₂ 14
  rw [ha14, ha15] at ha16
  norm_num at ha16

  have ha17 : a 17 = (a 15 + a 16) / 2 := h₂ 15
  rw [ha15, ha16] at ha17
  norm_num at ha17

  have ha18 : a 18 = (a 16 + a 17) / 2 := h₂ 16
  rw [ha16, ha17] at ha18

  norm_num [Int.floor_eq_iff, ha18]