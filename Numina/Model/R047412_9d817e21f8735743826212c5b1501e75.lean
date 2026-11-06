import Mathlib

theorem number_theory_38881 (f : ℕ → ℕ)
    (h₀ : ∀ n, IsLeast {x | 0 < x ∧ n ∣ ∑ i in Finset.Icc 1 x, i} (f n)) :
    ∀ n, f n = 2 * n - 1 ↔ ∃ m, n = 2 ^ m := by 
  intro n
  have h1 : f 0 ∈ {x | 0 < x ∧ (0 : ℕ) ∣ ∑ i in Finset.Icc 1 x, i} := by 
    have h3 : IsLeast {x | 0 < x ∧ (0 : ℕ) ∣ ∑ i in Finset.Icc 1 x, i} (f 0) := h₀ 0
    have h3' : f 0 ∈ {x | 0 < x ∧ (0 : ℕ) ∣ ∑ i in Finset.Icc 1 x, i} := h3.left
    simpa using h3'
  rcases h1 with ⟨h1a1, h1a2⟩ 
  have h2 : f 0 > 0 := by 
    omega
  have h3 : (0 : ℕ) ∣ ∑ i in Finset.Icc 1 (f 0), i := h1a2
  have h5 : ∑ i in Finset.Icc 1 (f 0), i = 0 := by 
    simpa using h3
  have h10 : ∑ i in Finset.Icc 1 (f 0), i > 0 := by
    have h8 : f 0 > 0 := h2
    apply Finset.sum_pos
    · 
      intro i hi
      simp at hi ⊢
      all_goals omega 
    · 
      use 1
      all_goals 
      have h8 : f 0 > 0 := h2
      simp at h8 ⊢
      all_goals omega 
  omega