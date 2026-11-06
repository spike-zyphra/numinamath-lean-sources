import Mathlib

theorem number_theory_171389 (n : ℕ) (h₀ : n > 100) :
    ∃ S : Finset ℕ, S ⊆ {n, n + 1, n + 2, n + 3} ∧ S.card = 3 ∧ ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a > 1 ∧ b > 1 ∧ c > 1 ∧ a * b * c = S.sum id := by 
  have h1 : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h1 with (h1 | h1)
  · -- Case n is even
    have h2 : n % 2 = 0 := h1
    use {n + 1, n + 2, n + 3}
    constructor
    · -- Show subset
      intro x hx
      simp at hx ⊢
      rcases hx with (rfl | rfl | rfl)
      all_goals
        simp [h₀]
    constructor 
    · -- Show card is 3 
      simp [Finset.card_insert_of_not_mem, Finset.card_singleton]
      all_goals omega
    use 2, 3, (n + 2) / 2
    constructor
    · -- Show a ≠ b
      norm_num
    constructor 
    · -- Show a ≠ c 
      omega
    constructor 
    · -- Show b ≠ c 
      omega
    constructor
    · -- Show a > 1
      norm_num 
    constructor 
    · -- Show b > 1 
      norm_num
    constructor 
    · -- Show c > 1 
      omega
    · -- Show a * b * c = S.sum id 
      have h3 : n % 2 = 0 := h2 
      have h4 : (n + 2) % 2 = 0 := by 
        omega
      have h5 : 2 * 3 * ((n + 2) / 2) = 3 * (n + 2) := by
        have h4' : (n + 2) % 2 = 0 := h4
        have h7 : ∃ k, (n + 2) = 2 * k := ⟨(n + 2) / 2, by omega⟩
        rcases h7 with ⟨k, hk⟩
        omega 
      have : ({n + 1, n + 2, n + 3} : Finset ℕ).sum id = 3 * (n + 2) := by
        simp [Finset.sum_insert, Finset.sum_singleton, Nat.add_assoc]
        all_goals ring
      omega
  · -- Case n is odd 
    have h2 : n % 2 = 1 := h1 
    use {n, n + 1, n + 2}
    constructor 
    · -- Show subset 
      intro x hx 
      simp at hx ⊢ 
      rcases hx with (rfl | rfl | rfl) 
      all_goals 
        simp [h₀]
    constructor 
    · -- Show card is 3 
      simp [Finset.card_insert_of_not_mem, Finset.card_singleton]
      all_goals omega
    use 2, 3, (n + 1) / 2
    constructor
    · -- Show a ≠ b 
      norm_num 
    constructor 
    · -- Show a ≠ c 
      omega
    constructor 
    · -- Show b ≠ c 
      omega
    constructor 
    · -- Show a > 1 
      norm_num 
    constructor 
    · -- Show b > 1 
      norm_num
    constructor 
    · -- Show c > 1 
      omega
    · -- Show a * b * c = S.sum id 
      have h7 : (n + 1) % 2 = 0 := by 
        omega 
      have h5 : 2 * 3 * ((n + 1) / 2) = 3 * (n + 1) := by 
        have h7' : (n + 1) % 2 = 0 := h7
        have h7' : ∃ k, (n + 1) = 2 * k := ⟨(n + 1) / 2, by omega⟩
        rcases h7' with ⟨k, hk⟩
        omega
      have : ({n, n + 1, n + 2} : Finset ℕ).sum id = 3 * (n + 1) := by
        simp [Finset.sum_insert, Finset.sum_singleton, Nat.add_assoc]
        all_goals ring
      omega