import Mathlib

theorem algebra_224870 {a : ℤ} (h : ∃ x1 x2, x1 ≠ x2 ∧ (x1 - a) * (x1 - 8) - 1 = 0 ∧ (x2 - a) * (x2 - 8) - 1 = 0) :
    a = 8 := by
  rcases h with ⟨x1, x2, hx12, h1, h2⟩
  have eq1 : (x1 - a) * (x1 - 8) = 1 := by
    linarith
  have eq2 : (x2 - a) * (x2 - 8) = 1 := by
    linarith
  have h3 : (x1 - a) = 1 ∨ (x1 - a) = -1 := by
    apply Int.eq_one_or_neg_one_of_mul_eq_one
    exact eq1
  cases h3 with
  | inl h3 =>
    have h4 : (x1 - 8) = 1 := by 
      rw [h3] at eq1
      nlinarith
    have h5 : a = 8 := by 
      linarith
    linarith
  | inr h3 =>
    have h7 : (x1 - 8) = -1 := by 
      rw [h3] at eq1
      nlinarith
    have h5 : a = 8 := by 
      linarith
    linarith