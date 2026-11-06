import Mathlib

theorem algebra_11999 {a : ℕ → ℝ} (ha1 : a 1 = 2) (han : ∀ n > 0, a n + a (n + 1) = 1)
    (S : ℕ → ℝ) (hS : ∀ n, S n = ∑ i in Finset.Icc 1 n, a i) :
    S 2017 - 2 * S 2018 + S 2019 = 3 := by

  have ha2 : a 2 = -1 := by
    have h := han 1 (by norm_num)
    norm_num [ha1] at h
    linarith

  have h1 : ∀ n : ℕ, a (2 * n + 1) = 2 := by
    intro n 
    induction n with 
    | zero => 
      norm_num [ha1]
    | succ n ih =>
      have h2 : a (2 * n + 2) = -1 := by 
        have h3 := han (2 * n + 1) (by linarith)
        simp [show 2 * n + 1 + 1 = 2 * n + 2 by ring] at h3 ⊢
        linarith [ih]
      have h3 : a (2 * n + 3) = 2 := by 
        have h5 := han (2 * n + 2) (by omega)
        simp [show 2 * n + 2 + 1 = 2 * n + 3 by ring] at h5 ⊢ 
        linarith [h2]
      simpa using h3

  have h2 : ∀ n : ℕ, a (2 * n + 2) = -1 := by
    intro n 
    induction n with 
    | zero => 
      norm_num [ha2]
    | succ n ih =>
      have h3 : a (2 * n + 1) = 2 := h1 n 
      have h5 : a (2 * n + 3) = 2 := h1 (n + 1)
      have h6 : a (2 * (n + 1) + 2) = -1 := by 
        have h6 := han (2 * n + 3) (by omega)
        simp [show 2 * (n + 1) + 2 = 2 * n + 4 from by omega, show 2 * n + 3 + 1 = 2 * n + 4 by ring] at h6 ⊢ 
        linarith [h5]
      simpa using h6

  have hS1 : ∀ n : ℕ, S (2 * n + 1) = (n : ℝ) + 2 := by
    intro n
    rw [hS (2 * n + 1)]
    have h4 : ∀ (n : ℕ), ∑ i in Finset.Icc 1 (2 * n + 1), a i = (n : ℝ) + 2 := by
      intro n 
      induction n with 
      | zero => 
        norm_num [ha1, Finset.sum_Icc_succ_top]
      | succ n ih =>
        rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega]
        rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
        have ha3 : a (2 * n + 2) = -1 := h2 n
        have ha4 : a (2 * n + 3) = 2 := by 
          specialize h1 (n + 1)
          simpa using h1 
        simp [ha3, ha4] at ih ⊢ 
        all_goals norm_num at ih ⊢ 
        all_goals nlinarith 
    specialize h4 n
    simpa using h4

  have hS2 : ∀ n : ℕ, S (2 * n + 2) = (n + 1 : ℝ) := by 
    intro n
    rw [hS (2 * n + 2)]
    have h5 : ∀ (n : ℕ), ∑ i in Finset.Icc 1 (2 * n + 2), a i = (n + 1 : ℝ) := by 
      intro n
      induction n with 
      | zero => 
        norm_num [ha1, ha2, Finset.sum_Icc_succ_top]
      | succ n ih =>
        rw [show 2 * (n + 1) + 2 = 2 * n + 4 by omega]
        rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
        have ha3 : a (2 * n + 3) = 2 := by 
          specialize h1 (n + 1)
          simpa using h1 
        have ha4 : a (2 * n + 4) = -1 := by 
          specialize h2 (n + 1)
          simpa using h2 
        simp [ha3, ha4] at ih ⊢ 
        all_goals norm_num at ih ⊢ 
        all_goals nlinarith 
    specialize h5 n 
    simpa using h5

  have h2017 : S 2017 = (1008 : ℝ) + 2 := by
    specialize hS1 1008 
    norm_num at hS1 ⊢ 
    linarith

  have h2018 : S 2018 = (1009 : ℝ) := by 
    specialize hS2 1008 
    norm_num at hS2 ⊢ 
    linarith

  have h2019 : S 2019 = (1009 : ℝ) + 2 := by 
    specialize hS1 1009 
    norm_num at hS1 ⊢ 
    linarith

  rw [h2017, h2018, h2019]
  norm_num