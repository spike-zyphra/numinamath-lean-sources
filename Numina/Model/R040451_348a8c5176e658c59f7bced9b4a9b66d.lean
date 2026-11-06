import Mathlib

open Finset

theorem algebra_313904 {a b : ℕ → ℝ} (ha1 : a 1 = 1)
    (hroots : ∀ n > 0, a n + a (n + 1) = -3 * n ∧ a n * a (n + 1) = b n)
    : ∑ k in Finset.range 20, b (k + 1) = 6385 := by

  have h1 : ∀ n > 0, a n + a (n + 1) = -3 * n := by
    intro n hn
    have h2 := (hroots n hn).1
    simpa using h2

  have h2 : ∀ n > 0, a n * a (n + 1) = b n := by
    intro n hn
    have h3 := (hroots n hn).2
    simpa using h3

  -- Compute the first 20 terms of b
  have ha2 : a 2 = -4 := by
    have h3 := h1 1 (by norm_num)
    norm_num at h3
    rw [ha1] at h3
    linarith

  have hb1 : b 1 = -4 := by
    have h3 := h2 1 (by norm_num)
    norm_num at h3
    rw [ha1, show a 2 = -4 by linarith [ha2]] at h3
    linarith

  -- Compute a_3 and b_2
  have ha3 : a 3 = -2 := by
    have h3 := h1 2 (by norm_num)
    norm_num at h3
    rw [show a 2 = -4 by linarith [ha2]] at h3
    linarith

  have hb2 : b 2 = 8 := by
    have h3 := h2 2 (by norm_num)
    norm_num at h3
    rw [show a 2 = -4 by linarith [ha2], show a 3 = -2 by linarith [ha3]] at h3
    linarith

  -- Compute a_4 and b_3
  have ha4 : a 4 = -7 := by
    have h3 := h1 3 (by norm_num)
    norm_num at h3
    rw [show a 3 = -2 by linarith [ha3]] at h3
    linarith

  have hb3 : b 3 = 14 := by
    have h3 := h2 3 (by norm_num)
    norm_num at h3
    rw [show a 3 = -2 by linarith [ha3], show a 4 = -7 by linarith [ha4]] at h3
    linarith

  -- Compute a_5 and b_4
  have ha5 : a 5 = -5 := by
    have h3 := h1 4 (by norm_num)
    norm_num at h3
    rw [show a 4 = -7 by linarith [ha4]] at h3
    linarith

  have hb4 : b 4 = 35 := by
    have h3 := h2 4 (by norm_num)
    norm_num at h3
    rw [show a 4 = -7 by linarith [ha4], show a 5 = -5 by linarith [ha5]] at h3
    linarith

  -- Compute a_6 and b_5
  have ha6 : a 6 = -10 := by
    have h3 := h1 5 (by norm_num)
    norm_num at h3
    rw [show a 5 = -5 by linarith [ha5]] at h3
    linarith

  have hb5 : b 5 = 50 := by
    have h3 := h2 5 (by norm_num)
    norm_num at h3
    rw [show a 5 = -5 by linarith [ha5], show a 6 = -10 by linarith [ha6]] at h3
    linarith

  -- Compute a_7 and b_6
  have ha7 : a 7 = -8 := by
    have h3 := h1 6 (by norm_num)
    norm_num at h3
    rw [show a 6 = -10 by linarith [ha6]] at h3
    linarith

  have hb6 : b 6 = 80 := by
    have h3 := h2 6 (by norm_num)
    norm_num at h3
    rw [show a 6 = -10 by linarith [ha6], show a 7 = -8 by linarith [ha7]] at h3
    linarith

  -- Compute a_8 and b_7
  have ha8 : a 8 = -13 := by
    have h3 := h1 7 (by norm_num)
    norm_num at h3
    rw [show a 7 = -8 by linarith [ha7]] at h3
    linarith

  have hb7 : b 7 = 104 := by
    have h3 := h2 7 (by norm_num)
    norm_num at h3
    rw [show a 7 = -8 by linarith [ha7], show a 8 = -13 by linarith [ha8]] at h3
    linarith

  -- Compute a_9 and b_8
  have ha9 : a 9 = -11 := by
    have h3 := h1 8 (by norm_num)
    norm_num at h3
    rw [show a 8 = -13 by linarith [ha8]] at h3
    linarith

  have hb8 : b 8 = 143 := by
    have h3 := h2 8 (by norm_num)
    norm_num at h3
    rw [show a 8 = -13 by linarith [ha8], show a 9 = -11 by linarith [ha9]] at h3
    linarith

  -- Compute a_10 and b_9
  have ha10 : a 10 = -16 := by
    have h3 := h1 9 (by norm_num)
    norm_num at h3
    rw [show a 9 = -11 by linarith [ha9]] at h3
    linarith

  have hb9 : b 9 = 176 := by
    have h3 := h2 9 (by norm_num)
    norm_num at h3
    rw [show a 9 = -11 by linarith [ha9], show a 10 = -16 by linarith [ha10]] at h3
    linarith

  -- Compute a_11 and b_10
  have ha11 : a 11 = -14 := by
    have h3 := h1 10 (by norm_num)
    norm_num at h3
    rw [show a 10 = -16 by linarith [ha10]] at h3
    linarith

  have hb10 : b 10 = 224 := by
    have h3 := h2 10 (by norm_num)
    norm_num at h3
    rw [show a 10 = -16 by linarith [ha10], show a 11 = -14 by linarith [ha11]] at h3
    linarith

  -- Compute a_12 and b_11
  have ha12 : a 12 = -19 := by
    have h3 := h1 11 (by norm_num)
    norm_num at h3
    rw [show a 11 = -14 by linarith [ha11]] at h3
    linarith

  have hb11 : b 11 = 266 := by
    have h3 := h2 11 (by norm_num)
    norm_num at h3
    rw [show a 11 = -14 by linarith [ha11], show a 12 = -19 by linarith [ha12]] at h3
    linarith

  -- Compute a_13 and b_12
  have ha13 : a 13 = -17 := by
    have h3 := h1 12 (by norm_num)
    norm_num at h3
    rw [show a 12 = -19 by linarith [ha12]] at h3
    linarith

  have hb12 : b 12 = 323 := by
    have h3 := h2 12 (by norm_num)
    norm_num at h3
    rw [show a 12 = -19 by linarith [ha12], show a 13 = -17 by linarith [ha13]] at h3
    linarith

  -- Compute a_14 and b_13
  have ha14 : a 14 = -22 := by
    have h3 := h1 13 (by norm_num)
    norm_num at h3
    rw [show a 13 = -17 by linarith [ha13]] at h3
    linarith

  have hb13 : b 13 = 374 := by
    have h3 := h2 13 (by norm_num)
    norm_num at h3
    rw [show a 13 = -17 by linarith [ha13], show a 14 = -22 by linarith [ha14]] at h3
    linarith

  -- Compute a_15 and b_14
  have ha15 : a 15 = -20 := by
    have h3 := h1 14 (by norm_num)
    norm_num at h3
    rw [show a 14 = -22 by linarith [ha14]] at h3
    linarith

  have hb14 : b 14 = 440 := by
    have h3 := h2 14 (by norm_num)
    norm_num at h3
    rw [show a 14 = -22 by linarith [ha14], show a 15 = -20 by linarith [ha15]] at h3
    linarith

  -- Compute a_16 and b_15
  have ha16 : a 16 = -25 := by
    have h3 := h1 15 (by norm_num)
    norm_num at h3
    rw [show a 15 = -20 by linarith [ha15]] at h3
    linarith

  have hb15 : b 15 = 500 := by
    have h3 := h2 15 (by norm_num)
    norm_num at h3
    rw [show a 15 = -20 by linarith [ha15], show a 16 = -25 by linarith [ha16]] at h3
    linarith

  -- Compute a_17 and b_16
  have ha17 : a 17 = -23 := by
    have h3 := h1 16 (by norm_num)
    norm_num at h3
    rw [show a 16 = -25 by linarith [ha16]] at h3
    linarith

  have hb16 : b 16 = 575 := by
    have h3 := h2 16 (by norm_num)
    norm_num at h3
    rw [show a 16 = -25 by linarith [ha16], show a 17 = -23 by linarith [ha17]] at h3
    linarith

  -- Compute a_18 and b_17
  have ha18 : a 18 = -28 := by
    have h3 := h1 17 (by norm_num)
    norm_num at h3
    rw [show a 17 = -23 by linarith [ha17]] at h3
    linarith

  have hb17 : b 17 = 644 := by
    have h3 := h2 17 (by norm_num)
    norm_num at h3
    rw [show a 17 = -23 by linarith [ha17], show a 18 = -28 by linarith [ha18]] at h3
    linarith

  -- Compute a_19 and b_18
  have ha19 : a 19 = -26 := by
    have h3 := h1 18 (by norm_num)
    norm_num at h3
    rw [show a 18 = -28 by linarith [ha18]] at h3
    linarith

  have hb18 : b 18 = 728 := by
    have h3 := h2 18 (by norm_num)
    norm_num at h3
    rw [show a 18 = -28 by linarith [ha18], show a 19 = -26 by linarith [ha19]] at h3
    linarith

  -- Compute a_20 and b_19
  have ha20 : a 20 = -31 := by
    have h3 := h1 19 (by norm_num)
    norm_num at h3
    rw [show a 19 = -26 by linarith [ha19]] at h3
    linarith

  have hb19 : b 19 = 806 := by
    have h3 := h2 19 (by norm_num)
    norm_num at h3
    rw [show a 19 = -26 by linarith [ha19], show a 20 = -31 by linarith [ha20]] at h3
    linarith

  -- Compute a_21 and b_20
  have ha21 : a 21 = -29 := by
    have h3 := h1 20 (by norm_num)
    norm_num at h3
    rw [show a 20 = -31 by linarith [ha20]] at h3
    linarith

  have hb20 : b 20 = 899 := by
    have h3 := h2 20 (by norm_num)
    norm_num at h3
    rw [show a 20 = -31 by linarith [ha20], show a 21 = -29 by linarith [ha21]] at h3
    linarith

  -- Compute the sum
  norm_num [Finset.sum_range_succ, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19, hb20]
  all_goals linarith