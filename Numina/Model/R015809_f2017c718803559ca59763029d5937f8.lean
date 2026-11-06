import Mathlib

theorem algebra_214132 (f : ℕ → ℕ → ℕ) :
    (∀ A B, A ≠ B → f A B = |(A : ℤ) - B| * (A + B)) ∧
    (∀ A B C, f (A * C) (B * C) = (f A B) * (f C C)) ∧
    (∀ k, f (2 * k + 1) (2 * k + 1) = 2 * k + 1) ↔ False := by
  constructor
  · -- Assume all three properties hold, derive False
    intro h
    rcases h with ⟨h1, h2, h3⟩
    have h5 : f 0 3 = 9 := by 
      specialize h1 0 3 (by norm_num)
      norm_num at h1 ⊢
      all_goals try omega
    have h6 : f 0 1 = 1 := by 
      specialize h1 0 1 (by norm_num)
      norm_num at h1 ⊢
      all_goals try omega
    have h7 : f 3 3 = 3 := by
      specialize h3 1
      norm_num at h3 ⊢
      all_goals try linarith
    have h8 := h2 0 1 3
    have h9 : f (0 * 3) (1 * 3) = (f 0 1) * (f 3 3) := by 
      simpa using h8
    have h10 : f (0 * 3) (1 * 3) = f 0 3 := by 
      simp
    rw [h10] at h9
    rw [h6, h7] at h9
    linarith [h5, h9]
  · -- False implies anything
    intro h
    cases h