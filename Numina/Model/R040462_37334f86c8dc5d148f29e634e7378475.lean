import Mathlib

theorem inequalities_131615 (a : ℕ → ℝ)
  (h₀ : a 1 = 0)
  (h₁ : ∀ n, a (n + 1) = a n + 1 ∨ a (n + 1) = -(a n + 1)) :
  ∀ n > 0, (1 / n) * ∑ i in Finset.Icc 1 n, a i ≥ -1 / 2 := by
  intro n hn
  have h4 : ∀ (m : ℕ), a (m + 1) ^ 2 = a m ^ 2 + 2 * a m + 1 := by 
    intro m
    have h5 : a (m + 1) = a m + 1 ∨ a (m + 1) = -(a m + 1) := h₁ m
    cases h5 with
    | inl h6 =>
      rw [h6]
      ring_nf
    | inr h7 =>
      rw [h7]
      ring_nf
      <;> nlinarith
  have h6 : ∀ n : ℕ, ∑ i in Finset.Icc 1 n, a i = (a (n + 1) ^ 2 - n) / 2 := by 
    intro n
    induction n with
    | zero =>
      simp [h₀]
      <;> linarith [h₀]
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      have h7 : a (n + 2) ^ 2 = a (n + 1) ^ 2 + 2 * a (n + 1) + 1 := by 
        specialize h4 (n + 1)
        simpa using h4
      field_simp at *
      nlinarith [h7]
      all_goals 
        linarith
  have h7 : ∀ n : ℕ, ∑ i in Finset.Icc 1 n, a i ≥ - (n : ℝ) / 2 := by 
    intro n
    have h8 : ∑ i in Finset.Icc 1 n, a i = (a (n + 1) ^ 2 - n) / 2 := h6 n
    rw [h8]
    have h9 : a (n + 1) ^ 2 ≥ 0 := by 
      exact sq_nonneg (a (n + 1))
    have h10 : (a (n + 1) ^ 2 - (n : ℝ)) / 2 ≥ - (n : ℝ) / 2 := by 
      linarith [h9]
    linarith [h10]
  specialize h7 n
  have h12 : (1 / (n : ℝ)) * ∑ i in Finset.Icc 1 n, a i ≥ -1 / 2 := by
    have h13 : ∑ i in Finset.Icc 1 n, a i ≥ - (n : ℝ) / 2 := by
      linarith [h7]
    have hn' : (n : ℝ) > 0 := by
      have hn_pos : n > 0 := hn
      exact_mod_cast (show 0 < n from hn_pos)
    have h14 : (1 / (n : ℝ)) * ∑ i in Finset.Icc 1 n, a i ≥ (1 / (n : ℝ)) * (- (n : ℝ) / 2) := by
      apply mul_le_mul_of_nonneg_left
      linarith [h13]
      all_goals
      positivity
    have h15 : (1 / (n : ℝ)) * (- (n : ℝ) / 2) = -1 / 2 := by
      field_simp
      <;> ring_nf <;> linarith
    linarith [h14, h15]
  linarith [h12]