import Mathlib

theorem algebra_135141 {a : ℕ → ℝ} (ha1 : a 1 = 3)
    (han : ∀ n ≥ 1, (3 - a (n + 1)) * (6 + a n) = 18) :
    ∀ n, ∑ k in Finset.Icc 1 n, (1 / a k) = (2 ^ (n + 1)) / 3 - (n + 2) / 3 := by
  intro n
  have h1 : ∀ (n : ℕ), a (n + 1) = 3 / (2 ^ (n + 1 : ℕ) - 1 : ℝ) := by
    intro n
    induction n with
    | zero =>
      norm_num [ha1]
    | succ n ih =>
      have eq1 := han (n + 1) (by linarith)
      rw [ih] at eq1
      have h6 : (2 : ℝ) ^ (n + 1 : ℕ) ≥ (2 : ℝ) := by
        have h7 : (n + 1 : ℕ) ≥ 1 := by linarith
        have h8 : (2 : ℝ) ^ (n + 1 : ℕ) ≥ (2 : ℝ) ^ (1 : ℕ) := by 
          apply pow_le_pow_right
          all_goals linarith
        norm_num at h8 ⊢
        linarith
      have h14 : (2 : ℝ) ^ (n + 1 : ℕ) - 1 ≠ 0 := by
        have h7 : (2 : ℝ) ^ (n + 1 : ℕ) ≥ (2 : ℝ) := h6
        nlinarith
      have eq2 : (3 - a (n + 1 + 1)) * (6 * ((2 : ℝ) ^ (n + 1 : ℕ) - 1) + 3) = 18 * ((2 : ℝ) ^ (n + 1 : ℕ) - 1) := by
        field_simp [(show (2 ^ (n + 1 : ℕ) - 1 : ℝ) ≠ 0 by
          exact h14
        )] at eq1 ⊢
        nlinarith
      have eq3 : a (n + 1 + 1) = 3 / (2 ^ ((n + 1 + 1 : ℕ)) - 1 : ℝ) := by
        have h10 : (6 * ((2 : ℝ) ^ (n + 1 : ℕ) - 1) + 3 : ℝ) ≠ 0 := by
          have h7 : (2 : ℝ) ^ (n + 1 : ℕ) ≥ (2 : ℝ) := h6
          nlinarith
        have eq4 : a (n + 1 + 1) * ((6 * ((2 : ℝ) ^ (n + 1 : ℕ) - 1) + 3 : ℝ)) = 9 := by
          nlinarith
        have h4 : (2 ^ (n + 1 + 1 : ℕ) - 1 : ℝ) ≠ 0 := by
          have h7 : (2 : ℝ) ^ (n + 1 + 1 : ℕ) ≥ (4 : ℝ) := by
            have h11 : (n + 1 + 1 : ℕ) ≥ 2 := by 
              omega
            have h12 : (2 : ℝ) ^ (n + 1 + 1 : ℕ) ≥ (2 : ℝ) ^ (2 : ℕ) := by
              apply pow_le_pow_right
              all_goals linarith
            norm_num at h12 ⊢
            linarith
          nlinarith
        have eq5 : a (n + 1 + 1) = 3 / (2 ^ (n + 1 + 1 : ℕ) - 1 : ℝ) := by
          field_simp [(show ((2 : ℝ) ^ (n + 1 + 1 : ℕ) - 1 : ℝ) ≠ 0 by exact h4), h10] at eq4 ⊢
          ring_nf at eq4 ⊢
          nlinarith [show (2 : ℝ) ^ (n + 1 : ℕ) ≥ (2 : ℝ) by linarith [h6]]
        exact eq5
      exact eq3
  have h2 : ∀ (n : ℕ), ∑ k in Finset.Icc 1 n, (1 / a k) = (2 ^ (n + 1) / 3 - (n + 2) / 3 : ℝ) := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      have h3 : a (n + 1) = 3 / (2 ^ (n + 1 : ℕ) - 1 : ℝ) := h1 (n)
      rw [h3]
      field_simp [(show (2 : ℝ) ^ (n + 1 : ℕ) - 1 ≠ 0 by
        have h3 : (2 : ℝ) ^ (n + 1 : ℕ) ≥ (2 : ℝ) := by
          have h4 : (n + 1 : ℕ) ≥ 1 := by omega
          have h5 : (2 : ℝ) ^ (n + 1 : ℕ) ≥ (2 : ℝ) ^ 1 := by
            apply pow_le_pow_right
            all_goals
              linarith
          norm_num at h5 ⊢
          linarith
        nlinarith
      )] at *
      ring_nf at *
  specialize h2 n
  simpa using h2