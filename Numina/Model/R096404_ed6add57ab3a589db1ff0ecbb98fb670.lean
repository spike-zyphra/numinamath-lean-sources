import Mathlib

theorem algebra_244628 {a : ℤ} (ha : ∃ x1 x2 : ℤ, x1 ≠ x2 ∧ (x1 - a) * (x1 - 8) - 1 = 0 ∧ (x2 - a) * (x2 - 8) - 1 = 0) :
    a = 8 := by
  rcases ha with ⟨x1, x2, h12, h1, h2⟩
  have h1' : (x1 - a) * (x1 - 8) = 1 := by
    linarith
  have h2' : (x2 - a) * (x2 - 8) = 1 := by 
    linarith
  have h3 : (x1 - a) = 1 ∨ (x1 - a) = -1 := by 
    apply Int.eq_one_or_neg_one_of_mul_eq_one 
    exact h1'
  cases h3 with
  | inl h3l =>
    have h4 : x1 - 8 = 1 := by
      rw [h3l] at h1'
      linarith 
    have h5 : x1 = 9 := by 
      linarith 
    have h6 : a = 8 := by 
      linarith [h5, h3l] 
    linarith 
  | inr h3r =>
    have h4 : x1 - 8 = -1 := by 
      rw [h3r] at h1'
      linarith 
    have h5 : x1 = 7 := by 
      linarith 
    have h6 : a = 8 := by 
      linarith [h5, h3r] 
    linarith