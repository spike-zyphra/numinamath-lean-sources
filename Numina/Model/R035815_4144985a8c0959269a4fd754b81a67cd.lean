import Mathlib

theorem number_theory_211284 (a : ℕ → ℕ)
    (h₀ : a 0 = 1)
    (h₁ : a 1 = 1)
    (h₂ : ∀ n > 2, ∃ m, IsLeast {x | ∀ i ∈ Finset.Icc 1 n, x ≠ a i ∧ ¬∃ j k, j ≠ i ∧ k ≠ i ∧ a j + a k = 2 * a i} m) :
    ∀ n, a n ≤ (n ^ 2 + 7) / 8 := by
  have h3 := h₂ 3 (by norm_num)
  rcases h3 with ⟨m, hm⟩
  have h4 : m ∈ {x | ∀ i ∈ Finset.Icc 1 3, x ≠ a i ∧ ¬∃ j k, j ≠ i ∧ k ≠ i ∧ a j + a k = 2 * a i} := by
    exact hm.left
  have h5 := h4 1 (by norm_num)
  rcases h5 with ⟨h6, h7⟩
  have h8 : a 1 = 1 := h₁
  rw [h8] at h7
  -- Show that the condition ¬∃ j k, ... is false because there exist j and k
  have h9 : ∃ j k, j ≠ 1 ∧ k ≠ 1 ∧ a j + a k = 2 * 1 := by 
    use 0, 0 
    constructor 
    · -- Show 0 ≠ 1
      norm_num 
    constructor 
    · -- Show 0 ≠ 1
      norm_num 
    · -- Show a 0 + a 0 = 2 * 1
      omega 
  have h13 : ¬∃ j k, j ≠ 1 ∧ k ≠ 1 ∧ a j + a k = 2 * 1 := h7 
  exfalso 
  exact h13 h9