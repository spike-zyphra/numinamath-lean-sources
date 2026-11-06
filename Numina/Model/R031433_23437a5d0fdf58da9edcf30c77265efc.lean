import Mathlib


open Finset


theorem algebra_268448 {a b : ℕ → ℝ} (ha1 : a 1 = 1)
    (hroots : ∀ n > 0, a n + a (n + 1) = -3 * n ∧ a n * a (n + 1) = b n)
    : ∑ k in Finset.Icc 1 20, b k = 6385 := by


  have h1 : a 1 = 1 := ha1

  have ha2 : a 2 = -4 := by
    have h11 := (hroots 1 (by norm_num)).left
    norm_num [h1] at h11
    linarith

  have hb1 : b 1 = -4 := by
    have h11 := (hroots 1 (by norm_num)).right
    norm_num [h1, ha2] at h11
    linarith

  have ha3 : a 3 = -2 := by
    have h22 := (hroots 2 (by norm_num)).left
    norm_num [ha2] at h22
    linarith

  have hb2 : b 2 = 8 := by
    have h22 := (hroots 2 (by norm_num)).right
    norm_num [ha2, ha3] at h22
    linarith

  have ha4 : a 4 = -7 := by
    have h33 := (hroots 3 (by norm_num)).left
    norm_num [ha3] at h33
    linarith

  have hb3 : b 3 = 14 := by
    have h33 := (hroots 3 (by norm_num)).right
    norm_num [ha3, ha4] at h33
    linarith

  have ha5 : a 5 = -5 := by
    have h44 := (hroots 4 (by norm_num)).left
    norm_num [ha4] at h44
    linarith

  have hb4 : b 4 = 35 := by
    have h44 := (hroots 4 (by norm_num)).right
    norm_num [ha4, ha5] at h44
    linarith

  have ha6 : a 6 = -10 := by
    have h55 := (hroots 5 (by norm_num)).left
    norm_num [ha5] at h55
    linarith

  have hb5 : b 5 = 50 := by
    have h55 := (hroots 5 (by norm_num)).right
    norm_num [ha5, ha6] at h55
    linarith

  have ha7 : a 7 = -8 := by
    have h66 := (hroots 6 (by norm_num)).left
    norm_num [ha6] at h66
    linarith

  have hb6 : b 6 = 80 := by
    have h66 := (hroots 6 (by norm_num)).right
    norm_num [ha6, ha7] at h66
    linarith

  have ha8 : a 8 = -13 := by
    have h77 := (hroots 7 (by norm_num)).left
    norm_num [ha7] at h77
    linarith

  have hb7 : b 7 = 104 := by
    have h77 := (hroots 7 (by norm_num)).right
    norm_num [ha7, ha8] at h77
    linarith

  have ha9 : a 9 = -11 := by
    have h88 := (hroots 8 (by norm_num)).left
    norm_num [ha8] at h88
    linarith

  have hb8 : b 8 = 143 := by
    have h88 := (hroots 8 (by norm_num)).right
    norm_num [ha8, ha9] at h88
    linarith

  have ha10 : a 10 = -16 := by
    have h99 := (hroots 9 (by norm_num)).left
    norm_num [ha9] at h99
    linarith

  have hb9 : b 9 = 176 := by
    have h99 := (hroots 9 (by norm_num)).right
    norm_num [ha9, ha10] at h99
    linarith

  have ha11 : a 11 = -14 := by
    have h1010 := (hroots 10 (by norm_num)).left
    norm_num [ha10] at h1010
    linarith

  have hb10 : b 10 = 224 := by
    have h1010 := (hroots 10 (by norm_num)).right
    norm_num [ha10, ha11] at h1010
    linarith

  have ha12 : a 12 = -19 := by
    have h1111 := (hroots 11 (by norm_num)).left
    norm_num [ha11] at h1111
    linarith

  have hb11 : b 11 = 266 := by
    have h1111 := (hroots 11 (by norm_num)).right
    norm_num [ha11, ha12] at h1111
    linarith

  have ha13 : a 13 = -17 := by
    have h1212 := (hroots 12 (by norm_num)).left
    norm_num [ha12] at h1212
    linarith

  have hb12 : b 12 = 323 := by
    have h1212 := (hroots 12 (by norm_num)).right
    norm_num [ha12, ha13] at h1212
    linarith

  have ha14 : a 14 = -22 := by
    have h1313 := (hroots 13 (by norm_num)).left
    norm_num [ha13] at h1313
    linarith

  have hb13 : b 13 = 374 := by
    have h1313 := (hroots 13 (by norm_num)).right
    norm_num [ha13, ha14] at h1313
    linarith

  have ha15 : a 15 = -20 := by
    have h1414 := (hroots 14 (by norm_num)).left
    norm_num [ha14] at h1414
    linarith

  have hb14 : b 14 = 440 := by
    have h1414 := (hroots 14 (by norm_num)).right
    norm_num [ha14, ha15] at h1414
    linarith

  have ha16 : a 16 = -25 := by
    have h1515 := (hroots 15 (by norm_num)).left
    norm_num [ha15] at h1515
    linarith

  have hb15 : b 15 = 500 := by
    have h1515 := (hroots 15 (by norm_num)).right
    norm_num [ha15, ha16] at h1515
    linarith

  have ha17 : a 17 = -23 := by
    have h1616 := (hroots 16 (by norm_num)).left
    norm_num [ha16] at h1616
    linarith

  have hb16 : b 16 = 575 := by
    have h1616 := (hroots 16 (by norm_num)).right
    norm_num [ha16, ha17] at h1616
    linarith

  have ha18 : a 18 = -28 := by
    have h1717 := (hroots 17 (by norm_num)).left
    norm_num [ha17] at h1717
    linarith

  have hb17 : b 17 = 644 := by
    have h1717 := (hroots 17 (by norm_num)).right
    norm_num [ha17, ha18] at h1717
    linarith

  have ha19 : a 19 = -26 := by
    have h1818 := (hroots 18 (by norm_num)).left
    norm_num [ha18] at h1818
    linarith

  have hb18 : b 18 = 728 := by
    have h1818 := (hroots 18 (by norm_num)).right
    norm_num [ha18, ha19] at h1818
    linarith

  have ha20 : a 20 = -31 := by
    have h1919 := (hroots 19 (by norm_num)).left
    norm_num [ha19] at h1919
    linarith

  have hb19 : b 19 = 806 := by
    have h1919 := (hroots 19 (by norm_num)).right
    norm_num [ha19, ha20] at h1919
    linarith

  have hb20 : b 20 = 899 := by
    have h2020 := (hroots 20 (by norm_num)).right
    have ha21 : a 21 = -29 := by
      have h2020_left := (hroots 20 (by norm_num)).left
      norm_num [ha20] at h2020_left
      linarith
    norm_num [ha20, ha21] at h2020
    linarith

  norm_num [Finset.sum_Icc_succ_top, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19, hb20]