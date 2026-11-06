import Mathlib

theorem algebra_186097 {a b : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hb : ∃ d, ∀ n, b n = b 0 + d * n) (h : ∀ n, (∑ i in Finset.range n, a i) / (∑ i in Finset.range n, b i) = (5 * n - 3) / (n + 9)) :
    a 6 / b 3 = 26 / 7 := by 
  rcases ha with ⟨d_a, had⟩
  rcases hb with ⟨d_b, hdb⟩
  have h0 := h 0
  norm_num [Finset.sum_range_zero] at h0
  all_goals 
    have eq1 := h 1
    norm_num [Finset.sum_range_succ, had 1, hdb 1] at eq1
    all_goals 
      have eq2 := h 2
      norm_num [Finset.sum_range_succ, had 1, had 2, hdb 1, hdb 2] at eq2
      all_goals 
        have eq3 := h 3
        norm_num [Finset.sum_range_succ, had 1, had 2, had 3, hdb 1, hdb 2, hdb 3] at eq3
        all_goals 
          have eq4 := h 4
          norm_num [Finset.sum_range_succ, had 1, had 2, had 3, had 4, hdb 1, hdb 2, hdb 3, hdb 4] at eq4
          all_goals 
            have h1 := had 6
            have h2 := had 3
            have h3 := hdb 3
            have eq_a6 : a 6 = a 0 + 6 * d_a := by
              specialize had 6
              ring_nf at had ⊢
              linarith
            have eq_b3 : b 3 = b 0 + 3 * d_b := by
              specialize hdb 3
              ring_nf at hdb ⊢
              linarith
            have h_eq1 : a 0 = 1 / 5 * b 0 := by
              field_simp [(show b 0 ≠ 0 by 
                by_contra h0
                rw [h0] at eq1
                linarith 
              )] at eq1 
              linarith 
            have h_eq2 : d_a = 5 * d_b := by 
              nlinarith [eq1, eq2, eq3, eq4]
            have h_eq3 : b 0 = 5 * d_b := by 
              nlinarith [eq1, eq2, eq3, eq4, h_eq1, h_eq2]
            have h_eq4 : a 0 = d_b := by 
              nlinarith [h_eq1, h_eq3]
            have h_eq5 : b 0 ≠ 0 := by 
              by_contra h0 
              rw [h0] at eq1 
              linarith 
            have h_eq6 : d_b ≠ 0 := by 
              by_contra h0 
              rw [h0] at h_eq3 
              have h0' : b 0 = 0 := by 
                linarith 
              contradiction 
            have eq_a6' : a 6 = 31 * d_b := by 
              rw [eq_a6] 
              nlinarith [h_eq4, h_eq2] 
            have eq_b3' : b 3 = 8 * d_b := by 
              rw [eq_b3] 
              nlinarith [h_eq3] 
            have h_eq7 : a 6 / b 3 = (31 * d_b) / (8 * d_b) := by 
              rw [eq_a6', eq_b3'] 
            have h_eq8 : (31 * d_b) / (8 * d_b) = 31 / 8 := by 
              have h0 : d_b ≠ 0 := h_eq6 
              field_simp [(show 8 * d_b ≠ 0 by 
                intro h0' 
                have : d_b = 0 := by 
                  nlinarith 
                contradiction 
              )] 
              all_goals 
                nlinarith 
            have h_eq9 : a 6 / b 3 = 31 / 8 := by 
              linarith [h_eq7, h_eq8] 
            linarith