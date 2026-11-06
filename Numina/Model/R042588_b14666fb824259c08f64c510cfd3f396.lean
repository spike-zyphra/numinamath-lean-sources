import Mathlib

theorem algebra_283494 (n : ℕ) (hn : 2 ≤ n) :
    ∃ a : Finset.Icc 1 n → ℝ,
      ∃ r : ℕ → ℝ,
        (∀ i j, i < j → ∃! k, a j - a i = r k) ↔
    n = 2 ∨ n = 3 ∨ n = 4 := by 
  by_cases h : n = 2 ∨ n = 3 ∨ n = 4
  · -- Assume n = 2, 3, or 4.
    have h1 : n = 2 ∨ n = 3 ∨ n = 4 := h
    use (λ _ : Finset.Icc 1 n => (0 : ℝ))
    use (λ k : ℕ => (k : ℝ))
    constructor
    · -- (∀ i j, i < j → ∃! k, a j - a i = r k) → (n = 2 ∨ n = 3 ∨ n = 4)
      intro h2
      tauto
    · -- (n = 2 ∨ n = 3 ∨ n = 4) → (∀ i j, i < j → ∃! k, a j - a i = r k)
      intro h2
      intro i j h3
      use 0
      constructor
      · -- Show `a j - a i = r 0`
        simp
      · -- Show that k = 0 is unique
        intro k' hk
        simp at hk ⊢
        all_goals
          norm_cast at hk ⊢
          all_goals
            nlinarith
  · -- Assume n ≠ 2, 3, 4
    simp at h 
    use (λ _ : Finset.Icc 1 n => (0 : ℝ))
    use (λ _ : ℕ => (1 : ℝ))
    constructor
    · -- (∀ i j, i < j → ∃! k, a j - a i = r k) → (n = 2 ∨ n = 3 ∨ n = 4)
      intro h1
      have h5 : n ≥ 5 := by 
        omega 
      have h6 : (1 : ℕ) ∈ Finset.Icc 1 n := by 
        simp 
        all_goals 
          omega 
      have h7 : (2 : ℕ) ∈ Finset.Icc 1 n := by 
        simp 
        all_goals 
          omega 
      have h9 := h1 ⟨1, h6⟩ ⟨2, h7⟩ (by 
        have h8 : (1 : ℕ) < (2 : ℕ) := by norm_num 
        simp [h8] 
      )
      rcases h9 with ⟨k, ⟨hk1, hk2⟩⟩ 
      norm_num [Finset.mem_Icc] at hk1 ⊢ 
      all_goals 
        norm_num at hk1 ⊢ 
        all_goals 
          nlinarith 
    · -- (n = 2 ∨ n = 3 ∨ n = 4) → (∀ i j, i < j → ∃! k, a j - a i = r k)
      intro h2 
      exfalso
      tauto