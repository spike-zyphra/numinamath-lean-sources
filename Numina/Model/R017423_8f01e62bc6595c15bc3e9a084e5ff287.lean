import Mathlib

theorem algebra_249303 {a b : ℕ → ℝ} (ha1 : a 1 = 1)
    (hroots : ∀ n : ℕ, n > 0 → a n + a (n + 1) = -3 * n ∧ a n * a (n + 1) = b n)
    : ∑ k in Finset.Icc 1 20, b k = 6385 := by
  have h1 : ∀ n : ℕ, n > 0 → a n + a (n + 1) = -3 * n := by
    intro n hn
    exact (hroots n hn).left
  have h2 : ∀ n : ℕ, n > 0 → a n * a (n + 1) = b n := by 
    intro n hn
    exact (hroots n hn).right
  have ha2 : a 2 = -4 := by
    have eq1 := h1 1 (by norm_num)
    norm_num [ha1] at eq1 
    linarith
  have ha3 : a 3 = -2 := by 
    have eq1 := h1 2 (by norm_num)
    norm_num [ha2] at eq1 
    linarith
  have ha4 : a 4 = -7 := by 
    have eq1 := h1 3 (by norm_num)
    norm_num [ha3] at eq1 
    linarith
  have ha5 : a 5 = -5 := by 
    have eq1 := h1 4 (by norm_num)
    norm_num [ha4] at eq1 
    linarith
  have ha6 : a 6 = -10 := by 
    have eq1 := h1 5 (by norm_num)
    norm_num [ha5] at eq1 
    linarith
  have ha7 : a 7 = -8 := by 
    have eq1 := h1 6 (by norm_num)
    norm_num [ha6] at eq1 
    linarith
  have ha8 : a 8 = -13 := by 
    have eq1 := h1 7 (by norm_num)
    norm_num [ha7] at eq1 
    linarith
  have ha9 : a 9 = -11 := by 
    have eq1 := h1 8 (by norm_num)
    norm_num [ha8] at eq1 
    linarith
  have ha10 : a 10 = -16 := by 
    have eq1 := h1 9 (by norm_num)
    norm_num [ha9] at eq1 
    linarith
  have ha11 : a 11 = -14 := by 
    have eq1 := h1 10 (by norm_num)
    norm_num [ha10] at eq1 
    linarith
  have ha12 : a 12 = -19 := by 
    have eq1 := h1 11 (by norm_num)
    norm_num [ha11] at eq1 
    linarith
  have ha13 : a 13 = -17 := by 
    have eq1 := h1 12 (by norm_num)
    norm_num [ha12] at eq1 
    linarith
  have ha14 : a 14 = -22 := by 
    have eq1 := h1 13 (by norm_num)
    norm_num [ha13] at eq1 
    linarith
  have ha15 : a 15 = -20 := by 
    have eq1 := h1 14 (by norm_num)
    norm_num [ha14] at eq1 
    linarith
  have ha16 : a 16 = -25 := by 
    have eq1 := h1 15 (by norm_num)
    norm_num [ha15] at eq1 
    linarith
  have ha17 : a 17 = -23 := by 
    have eq1 := h1 16 (by norm_num)
    norm_num [ha16] at eq1 
    linarith
  have ha18 : a 18 = -28 := by 
    have eq1 := h1 17 (by norm_num)
    norm_num [ha17] at eq1 
    linarith
  have ha19 : a 19 = -26 := by 
    have eq1 := h1 18 (by norm_num)
    norm_num [ha18] at eq1 
    linarith
  have ha20 : a 20 = -31 := by 
    have eq1 := h1 19 (by norm_num)
    norm_num [ha19] at eq1 
    linarith
  have ha21 : a 21 = -29 := by 
    have eq1 := h1 20 (by norm_num)
    norm_num [ha20] at eq1 
    linarith
  have hb1 : b 1 = a 1 * a 2 := by
    specialize h2 1 (by norm_num)
    linarith
  have hb2 : b 2 = a 2 * a 3 := by 
    specialize h2 2 (by norm_num)
    linarith
  have hb3 : b 3 = a 3 * a 4 := by 
    specialize h2 3 (by norm_num)
    linarith
  have hb4 : b 4 = a 4 * a 5 := by 
    specialize h2 4 (by norm_num)
    linarith
  have hb5 : b 5 = a 5 * a 6 := by 
    specialize h2 5 (by norm_num)
    linarith
  have hb6 : b 6 = a 6 * a 7 := by 
    specialize h2 6 (by norm_num)
    linarith
  have hb7 : b 7 = a 7 * a 8 := by 
    specialize h2 7 (by norm_num)
    linarith
  have hb8 : b 8 = a 8 * a 9 := by 
    specialize h2 8 (by norm_num)
    linarith
  have hb9 : b 9 = a 9 * a 10 := by 
    specialize h2 9 (by norm_num)
    linarith
  have hb10 : b 10 = a 10 * a 11 := by 
    specialize h2 10 (by norm_num)
    linarith
  have hb11 : b 11 = a 11 * a 12 := by 
    specialize h2 11 (by norm_num)
    linarith
  have hb12 : b 12 = a 12 * a 13 := by 
    specialize h2 12 (by norm_num)
    linarith
  have hb13 : b 13 = a 13 * a 14 := by 
    specialize h2 13 (by norm_num)
    linarith
  have hb14 : b 14 = a 14 * a 15 := by 
    specialize h2 14 (by norm_num)
    linarith
  have hb15 : b 15 = a 15 * a 16 := by 
    specialize h2 15 (by norm_num)
    linarith
  have hb16 : b 16 = a 16 * a 17 := by 
    specialize h2 16 (by norm_num)
    linarith
  have hb17 : b 17 = a 17 * a 18 := by 
    specialize h2 17 (by norm_num)
    linarith
  have hb18 : b 18 = a 18 * a 19 := by 
    specialize h2 18 (by norm_num)
    linarith
  have hb19 : b 19 = a 19 * a 20 := by 
    specialize h2 19 (by norm_num)
    linarith
  have hb20 : b 20 = a 20 * a 21 := by 
    specialize h2 20 (by norm_num)
    linarith
  norm_num [Finset.sum_Icc_succ_top, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19, hb20, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21]