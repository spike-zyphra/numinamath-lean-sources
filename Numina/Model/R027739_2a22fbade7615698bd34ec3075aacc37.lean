import Mathlib

theorem algebra_120874 (a : ℕ → ℤ)
    (h₀ : ∀ n ∈ Finset.Icc 1 5, a n = n ^ 2)
    (h₁ : ∀ n > 0, a (n + 5) + a (n + 1) = a (n + 4) + a n) :
    a 2023 = 17 := by
  have h1 : a 1 = 1 := by
    specialize h₀ 1 (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
    norm_num at h₀ ⊢
    linarith
  have h2 : a 2 = 4 := by
    specialize h₀ 2 (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
    norm_num at h₀ ⊢
    linarith
  have h3 : a 3 = 9 := by
    specialize h₀ 3 (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
    norm_num at h₀ ⊢
    linarith
  have h4 : a 4 = 16 := by
    specialize h₀ 4 (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
    norm_num at h₀ ⊢
    linarith
  have h5 : a 5 = 25 := by
    specialize h₀ 5 (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
    norm_num at h₀ ⊢
    linarith
  have h6 : a 6 = 22 := by
    specialize h₁ 1 (by norm_num)
    norm_num [h1, h2, h5] at h₁ ⊢
    linarith
  have h7 : a 7 = 17 := by
    specialize h₁ 2 (by norm_num)
    norm_num [h2, h3, h6] at h₁ ⊢
    linarith
  have h8 : a 8 = 10 := by
    specialize h₁ 3 (by norm_num)
    norm_num [h3, h4, h7] at h₁ ⊢
    linarith
  have h9 : a 9 = 1 := by
    specialize h₁ 4 (by norm_num)
    norm_num [h4, h5, h8] at h₁ ⊢
    linarith
  have h10 : a 10 = 4 := by
    specialize h₁ 5 (by norm_num)
    norm_num [h5, h6, h9] at h₁ ⊢
    linarith
  have h11 : ∀ n, a (8 * n + 7) = 17 := by
    intro n
    induction n with
    | zero =>
      norm_num [h7]
    | succ n ih =>
      have eq1 := h₁ (8 * n + 7) (by omega)
      have eq2 := h₁ (8 * n + 8) (by omega)
      have eq3 := h₁ (8 * n + 9) (by omega)
      have eq4 := h₁ (8 * n + 10) (by omega)
      have eq5 := h₁ (8 * n + 11) (by omega)
      have eq6 := h₁ (8 * n + 12) (by omega)
      have eq7 := h₁ (8 * n + 13) (by omega)
      have eq8 := h₁ (8 * n + 14) (by omega)
      simp [show 8 * (n + 1) + 7 = (8 * n + 15 : ℕ) by omega] at *
      norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 ih ⊢
      all_goals
        linarith [ih]
  have h2023 : a 2023 = 17 := by
    specialize h11 252
    norm_num at h11 ⊢
    linarith
  exact h2023