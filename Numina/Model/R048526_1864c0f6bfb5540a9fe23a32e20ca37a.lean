import Mathlib

theorem algebra_10764 {a b : ℕ → ℝ} {S T : ℕ → ℝ}
    (ha : ∃ d, ∀ n, a n = a 0 + d * n) (hb : ∃ d, ∀ n, b n = b 0 + d * n)
    (hS : ∀ n, S n = ∑ i in Finset.range n, a i) (hT : ∀ n, T n = ∑ i in Finset.range n, b i)
    (hST : ∀ n, S n / T n = (2 * n + 4) / (3 * n + 7)) :
    a 5 / b 7 = 11 / 23 := by
  rcases ha with ⟨d_a, had⟩
  rcases hb with ⟨d_b, hdb⟩
  have h1 := hST 0
  simp [hS, hT, Finset.sum_range_zero] at h1
  have h2 := hST 1
  simp [hS, hT, Finset.sum_range_succ, had 1, hdb 1] at h2
  have h3 : a 0 = 3 / 5 * b 0 := by
    norm_num at h2 ⊢
    linarith
  have h4 := hST 2
  simp [hS, hT, Finset.sum_range_succ, had 1, had 2, hdb 1, hdb 2] at h4
  have h5 := hST 3
  simp [hS, hT, Finset.sum_range_succ, had 1, had 2, had 3, hdb 1, hdb 2, hdb 3] at h5
  have h6 := hST 4
  simp [hS, hT, Finset.sum_range_succ, had 1, had 2, had 3, had 4, hdb 1, hdb 2, hdb 3, hdb 4] at h6
  have h7 := hST 5
  simp [hS, hT, Finset.sum_range_succ, had 1, had 2, had 3, had 4, had 5, hdb 1, hdb 2, hdb 3, hdb 4, hdb 5] at h7
  have ha5 : a 5 = a 0 + 5 * d_a := by
    linarith [had 5]
  have hb7 : b 7 = b 0 + 7 * d_b := by
    linarith [hdb 7]
  have h_eq1 : a 1 = a 0 + d_a := by linarith [had 1]
  have h_eq2 : a 2 = a 0 + 2 * d_a := by linarith [had 2]
  have h_eq3 : a 3 = a 0 + 3 * d_a := by linarith [had 3]
  have h_eq4 : a 4 = a 0 + 4 * d_a := by linarith [had 4]
  have h_eq5 : a 5 = a 0 + 5 * d_a := by linarith [had 5]
  have h_eq6 : b 1 = b 0 + d_b := by linarith [hdb 1]
  have h_eq7 : b 2 = b 0 + 2 * d_b := by linarith [hdb 2]
  have h_eq8 : b 3 = b 0 + 3 * d_b := by linarith [hdb 3]
  have h_eq9 : b 4 = b 0 + 4 * d_b := by linarith [hdb 4]
  have h_eq10 : b 5 = b 0 + 5 * d_b := by linarith [hdb 5]
  have h_eq11 : b 6 = b 0 + 6 * d_b := by linarith [hdb 6]
  have h_eq12 : b 7 = b 0 + 7 * d_b := by linarith [hdb 7]
  norm_num [h_eq1, h_eq2, h_eq3, h_eq4, h_eq5, h_eq6, h_eq7, h_eq8, h_eq9, h_eq10, h_eq11, h_eq12] at h4 h5 h6 h7
  norm_num [h3] at h4 h5 h6 h7
  have : a 5 / b 7 = 11 / 23 := by
    have ha5 : a 5 = a 0 + 5 * d_a := by linarith [had 5]
    have hb7 : b 7 = b 0 + 7 * d_b := by linarith [hdb 7]
    linarith [h3, h4, h5, h6, h7, ha5, hb7]
  exact this