import Mathlib

theorem calculus_22612 (k : ℝ) :
    (k ≠ -6 / 7) ∧
    (∀ x y, x * 3 + y * k = 0 ∧ x * 7 + y * (-2) = 0 → x = 0 ∧ y = 0) ↔
    k < -6 / 7 ∨ k > -6 / 7 := by 
  constructor
  · -- Forward direction: (k ≠ -6/7 ∧ ∀ x y, lin independence) implies k < -6/7 ∨ k > -6/7
    intro h
    rcases h with ⟨hk, _⟩
    by_contra h'
    push_neg at h'
    have h1 : k = -6/7 := by 
      linarith
    contradiction
  · -- Backward direction: k < -6/7 ∨ k > -6/7 implies (k ≠ -6/7 ∧ ∀ x y, lin independence)
    intro h
    have hk : k ≠ -6 / 7 := by 
      by_contra h1
      have : k = -6 / 7 := by linarith
      rcases h with (h11 | h11)
      · -- Case k < -6/7
        linarith 
      · -- Case k > -6/7
        linarith 
    constructor
    · exact hk 
    · -- Need to prove linear independence
      intro x y h
      rcases h with ⟨h21, h22⟩
      have eq1 : x * 3 + y * k = 0 := h21
      have eq2 : x * 7 + y * (-2) = 0 := h22
      have h_eq1 : (7 * k + 6) * y = 0 := by 
        nlinarith
      cases (mul_eq_zero.1 h_eq1) with
      | inl h_eq2 =>
        have : k = -6 / 7 := by linarith
        contradiction
      | inr h_eq3 =>
        have hy : y = 0 := h_eq3
        have hx : x = 0 := by 
          rw [show y = 0 by tauto] at eq2
          linarith 
        exact ⟨hx, hy⟩