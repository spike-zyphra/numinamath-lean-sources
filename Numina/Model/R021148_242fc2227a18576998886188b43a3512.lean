import Mathlib

theorem algebra_54904 {n : ℕ} (hn : n > 0) (S : Finset ℝ)
    (hS : S.card = n) (h1 : (S.sum id + 1) / (n + 1) = (S.sum id) / n - 13)
    (h2 : (S.sum id + 2001) / (n + 1) = (S.sum id) / n + 27) :
    (S.sum id) / n = 651 := by

  have eq1 : (S.sum id + 1) * (n : ℝ) = (S.sum id) * ((n + 1 : ℝ) ) - 13 * ((n : ℝ) * ((n + 1 : ℝ)) ) := by
    have hne1 : (n + 1 : ℝ) ≠ 0 := by
      have hn' : (n : ℝ) > 0 := by
        exact_mod_cast (show n > 0 by linarith)
      nlinarith
    have hne2 : (n : ℝ) ≠ 0 := by
      have hn' : (n : ℝ) > 0 := by
        exact_mod_cast (show n > 0 by linarith)
      nlinarith
    field_simp [hne1, hne2] at h1 ⊢
    nlinarith [h1]

  have eq2 : (S.sum id + 2001) * (n : ℝ) = (S.sum id) * ((n + 1 : ℝ)) + 27 * ((n : ℝ) * ((n + 1 : ℝ)) ) := by
    have hne1 : (n + 1 : ℝ) ≠ 0 := by
      have hn' : (n : ℝ) > 0 := by
        exact_mod_cast (show n > 0 by linarith)
      nlinarith
    have hne2 : (n : ℝ) ≠ 0 := by
      have hn' : (n : ℝ) > 0 := by
        exact_mod_cast (show n > 0 by linarith)
      nlinarith
    field_simp [hne1, hne2] at h2 ⊢
    nlinarith [h2]

  have h3 : (n : ℝ) * (n - 49) = 0 := by
    nlinarith [sq_nonneg ((n : ℝ) - 49), sq_nonneg ((S.sum id) - 31899), sq_nonneg ((n : ℝ) - 49)]

  have h4 : (n : ℝ) = 0 ∨ (n : ℝ) = 49 := by
    cases (mul_eq_zero.mp h3) with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith

  cases h4 with
  | inl h =>
    have hn' : (n : ℝ) > 0 := by
      exact_mod_cast (show n > 0 by linarith)
    nlinarith
  | inr h =>
    have hn49 : (n : ℝ) = 49 := h
    have h5 : (S.sum id) = 31899 := by
      rw [hn49] at eq1
      nlinarith [sq_nonneg ((n : ℝ) - 49), sq_nonneg ((S.sum id) - 31899)]
    have h6 : (S.sum id) / (n : ℝ) = 651 := by
      rw [h5, hn49]
      norm_num
    linarith