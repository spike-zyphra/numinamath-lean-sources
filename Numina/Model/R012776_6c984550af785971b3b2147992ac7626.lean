import Mathlib

theorem algebra_307645 {a b c d : ℤ} (h : ∀ m n : ℤ, ∃ x y : ℤ, a * x + b * y = m ∧ c * x + d * y = n) :
    |a * d - b * c| = 1 := by
  have h1 := h 1 0
  rcases h1 with ⟨x0, y0, h_eq1, h_eq2⟩
  have h2 := h 0 1
  rcases h2 with ⟨x1, y1, h_eq3, h_eq4⟩
  have eq1 : a * x0 + b * y0 = 1 := by linarith
  have eq2 : c * x0 + d * y0 = 0 := by linarith
  have eq3 : a * x1 + b * y1 = 0 := by linarith
  have eq4 : c * x1 + d * y1 = 1 := by linarith
  have eq5 : (a * d - b * c) * (x0 * y1 - x1 * y0) = 1 := by
    nlinarith 
  have eq6 : a * d - b * c = 1 ∨ a * d - b * c = -1 := by
    have h1 : (a * d - b * c) * (x0 * y1 - x1 * y0) = 1 := eq5
    have h2 : a * d - b * c = 1 ∨ a * d - b * c = -1 := by
      apply Int.eq_one_or_neg_one_of_mul_eq_one 
      exact h1
    exact h2
  cases eq6 with
  | inl h_eq =>
    rw [h_eq]
    norm_num
  | inr h_eq =>
    rw [h_eq]
    norm_num