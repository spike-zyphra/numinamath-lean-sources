import Mathlib

theorem algebra_607977 {N : ℕ} {x : ℝ} (hx : 0 < x) (hN : 1 ≤ N) (h : (N * (1 + x) - (1 + x) * (1 - x)) / (N - 1) = (N * (1 - x) - (1 - x) * (1 + x)) / (N - 1) + x) : x ≤ 1 / 2 := by 
  have eq1 : (N = 0 ∨ N ≥ 1) := by 
    omega 
  cases eq1 with 
  | inl h1 =>
    exfalso 
    linarith 
  | inr h2 => 
    have h1 : N ≥ 1 := by 
      omega 
    have eq2 : (N = 1 ∨ N ≥ 2) := by 
      have h1 : N ≥ 1 := by 
        omega 
      by_cases h2 : N = 1 
      · left 
        omega 
      · right 
        have h3 : N ≥ 2 := by 
          omega 
        exact h3 
    cases eq2 with 
    | inl hN1 => 
      have eqN : (N : ℝ) = 1 := by 
        exact_mod_cast hN1 
      rw [show ↑N = 1 by exact_mod_cast hN1] at h 
      field_simp [(show ((↑N : ℝ) : ℝ) - 1 = (0 : ℝ) by 
          rw [show ↑N = 1 by exact_mod_cast hN1] 
          norm_num 
          )] at h ⊢ 
      all_goals 
        nlinarith 
    | inr hN2 => 
      have eqN : (N : ℝ) ≥ (2 : ℝ) := by 
        exact_mod_cast hN2 
      have h1 : (N * (1 + x) - (1 + x) * (1 - x)) / (N - 1) = (N * (1 - x) - (1 - x) * (1 + x)) / (N - 1) + x := h
      have h2 : ((N * (1 + x) - (1 + x) * (1 - x)) ) = (N * (1 - x) - (1 - x) * (1 + x)) + x * ((N - 1) : ℝ) := by 
        have hN3 : (N : ℝ) ≥ (2 : ℝ) := by 
          exact_mod_cast hN2 
        have hN3' : (N - 1 : ℝ) ≠ 0 := by 
          have hN4 : (N : ℝ) ≥ (2 : ℝ) := by 
            linarith [hN3]
          have : (N - 1 : ℝ) = (N : ℝ) - 1 := by 
            simp 
          rw [this] 
          linarith 
        have hN4 : (N * (1 + x) - (1 + x) * (1 - x)) / (N - 1) = (N * (1 - x) - (1 - x) * (1 + x)) / (N - 1) + x := h 
        have eq1 : (N * (1 + x) - (1 + x) * (1 - x)) / (N - 1) - (N * (1 - x) - (1 - x) * (1 + x)) / (N - 1) = x := by 
          linarith [hN4] 
        have eq2 : (N * (1 + x) - (1 + x) * (1 - x)) - (N * (1 - x) - (1 - x) * (1 + x)) = x * ((N - 1) : ℝ) := by 
          have h2 : (N * (1 + x) - (1 + x) * (1 - x)) / (N - 1) - (N * (1 - x) - (1 - x) * (1 + x)) / (N - 1) = x := eq1 
          have hN3' : (↑N - 1 : ℝ) ≠ 0 := hN3' 
          field_simp [hN3'] at h2 ⊢ 
          <;> linarith 
        linarith [eq2]
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg ((N * (1 + x) : ℝ) - (N * (1 - x) : ℝ)), sq_nonneg (x - 1 / 2), sq_nonneg (x), sq_nonneg ((N * (1 + x) : ℝ) - (N * (1 - x) : ℝ)), sq_nonneg ((N * (1 + x) : ℝ) - (N * (1 - x) : ℝ)), sq_nonneg ((N * (1 + x) : ℝ) - (N * (1 - x) : ℝ)), sq_nonneg ((N * (1 + x) : ℝ) - (N * (1 - x) : ℝ)), sq_nonneg ((N * (1 + x) : ℝ) - (N * (1 - x) : ℝ))]