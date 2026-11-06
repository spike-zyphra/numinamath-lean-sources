import Mathlib

theorem algebra_97167 {x y : ℝ} (h : x ^ 2 * (x + y + 1) = y ^ 2 * (x + y + 1)) :
    (y = x ∨ y = -x ∨ x + y + 1 = 0) ∧ (∀ x : ℝ, ¬ ∃ y, y = x ∧ y = -x ∧ x + y + 1 = 0)  := by

  have h1 : (x - y) * (x + y) * (x + y + 1) = 0 := by 
    ring_nf at h ⊢
    linarith


  have h2 : y = x ∨ y = -x ∨ x + y + 1 = 0 := by 
    cases (mul_eq_zero.mp h1) with
    | inl h11 =>
      cases (mul_eq_zero.mp h11) with 
      | inl h111 =>
        left
        linarith 
      | inr h112 =>
        right 
        left 
        linarith 
    | inr h12 => 
      right 
      right 
      linarith

  have h3 : ∀ x : ℝ, ¬ ∃ y, y = x ∧ y = -x ∧ x + y + 1 = 0 := by
    intro x 
    intro h
    rcases h with ⟨y, h1, h2, h3⟩ 
    have h4 : x = 0 := by
      nlinarith 
    have h5 : y = 0 := by 
      linarith [h1, h4] 
    rw [h4, h5] at h3 
    nlinarith

  constructor 
  · exact h2 
  · exact h3