import Mathlib

theorem algebra_165805 :
    ∀ (a₁ q : ℝ) (S : ℕ → ℝ),
    (q = 1 → ∀ n, S n = n * a₁) →
    (q ≠ 1 → ∀ n, S n = a₁ * (q^n - 1) / (q - 1)) →
    S 200 + 1 = (S 100 + 1)^2 → 
    S 600 + 1 = (S 300 + 1)^2 := by
  intro a₁ q S h1 h2 h
  by_cases hq : q = 1
  · -- when q = 1
    have h100 : S 100 = 100 * a₁ := by
      have h_eq : ∀ n, S n = n * a₁ := h1 hq
      specialize h_eq 100
      norm_num at h_eq ⊢
      linarith
    have h200 : S 200 = 200 * a₁ := by
      have h_eq : ∀ n, S n = n * a₁ := h1 hq
      specialize h_eq 200
      norm_num at h_eq ⊢
      linarith
    have ha1 : a₁ = 0 := by
      rw [h200, h100] at h
      nlinarith
    have h300 : S 300 = 300 * a₁ := by
      have h_eq : ∀ n, S n = n * a₁ := h1 hq
      specialize h_eq 300
      norm_num at h_eq ⊢
      linarith
    have h600 : S 600 = 600 * a₁ := by
      have h_eq : ∀ n, S n = n * a₁ := h1 hq
      specialize h_eq 600
      norm_num at h_eq ⊢
      linarith
    rw [h600, h300]
    rw [ha1]
    norm_num
  · -- when q ≠ 1
    have h100 : S 100 = a₁ * (q ^ 100 - 1) / (q - 1) := by
      have h_eq : ∀ n, S n = a₁ * (q ^ n - 1) / (q - 1) := h2 (show q ≠ 1 by tauto)
      specialize h_eq 100
      simpa using h_eq
    have h200 : S 200 = a₁ * (q ^ 200 - 1) / (q - 1) := by
      have h_eq : ∀ n, S n = a₁ * (q ^ n - 1) / (q - 1) := h2 (show q ≠ 1 by tauto)
      specialize h_eq 200
      simpa using h_eq
    have h300 : S 300 = a₁ * (q ^ 300 - 1) / (q - 1) := by
      have h_eq : ∀ n, S n = a₁ * (q ^ n - 1) / (q - 1) := h2 (show q ≠ 1 by tauto)
      specialize h_eq 300
      simpa using h_eq
    have h600 : S 600 = a₁ * (q ^ 600 - 1) / (q - 1) := by
      have h_eq : ∀ n, S n = a₁ * (q ^ n - 1) / (q - 1) := h2 (show q ≠ 1 by tauto)
      specialize h_eq 600
      simpa using h_eq
    rw [h200] at h
    rw [h100] at h
    rw [h600, h300]
    have h_eq : q - 1 ≠ 0 := by
      intro h_eq1
      apply hq
      linarith
    field_simp [h_eq] at h ⊢
    nlinarith [sq_pos_of_ne_zero (show (q - 1 : ℝ) ≠ 0 by exact h_eq), sq_nonneg (q ^ 100 - 1), sq_nonneg (q ^ 100), sq_nonneg (a₁ * (q ^ 100 - 1) * (q ^ 100 + 1)), sq_nonneg (q ^ 100 * (q ^ 100 - 1)), sq_nonneg ((q ^ 100) ^ 2), sq_nonneg (q ^ 100 - 1), sq_nonneg (q ^ 300 - 1), sq_nonneg (q ^ 300), sq_nonneg (a₁ * (q ^ 100 - 1) ^ 2)]