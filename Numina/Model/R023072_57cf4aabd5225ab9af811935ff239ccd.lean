import Mathlib

theorem number_theory_60894 (f : ℤ → ℤ) (h₀ : ∀ m n, f (m * n) = f m * f n)
    (h₁ : ∀ m, f m = -1 ∨ f m = 1) :
    ∃ a, 0 < a ∧ a ≤ 12 ∧ f a = 1 ∧ f (a + 1) = 1 := by
  have h2 : f 0 = 1 := by
    have h3 : f 0 = f 0 * f 0 := by
      specialize h₀ 0 0
      norm_num at h₀ 
      linarith 
    have h4 : f 0 = -1 ∨ f 0 = 1 := h₁ 0
    cases h4 with
    | inl h4 =>
      rw [h4] at h3
      all_goals omega
    | inr h4 =>
      exact h4
  have h3 : ∀ m : ℤ, f m = 1 := by
    intro m
    have h4 : f (m * 0) = f m * f 0 := by 
      apply h₀
    have h5 : f (m * 0) = 1 := by
      simp [h2]
    have h6 : f m * f 0 = f m := by
      calc
        f m * f 0 = f m * 1 := by rw [h2]
        _ = f m := by ring
    linarith [h4, h5, h6]
  use 1
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · 
    have h7 : f 1 = 1 := h3 1
    exact h7
  · 
    have h8 : f (1 + 1) = 1 := by
      have h4 : f (1 + 1) = 1 := h3 (1 + 1)
      linarith [h4]
    norm_num at h8 ⊢ 
    all_goals linarith [h8, h3 2]